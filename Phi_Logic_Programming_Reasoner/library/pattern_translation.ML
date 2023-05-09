signature PATTERN_REWRITE = sig

datatype rewrite = By_Pattern of term list | By_ML of (Context.generic -> term -> term list)
val rewrite_eq : rewrite * rewrite -> bool

val add : (int * term * rewrite) list -> Context.generic -> Context.generic
val remove : int * term * rewrite -> Context.generic -> Context.generic
val translate : Context.generic -> term -> term list
val translate_by_unify : Context.generic -> term -> term list
val setup_attribute : binding -> string -> theory -> theory

end

structure PLP_Reasoner_Pattern_Parse_Sender_Qiyuan_Xu = Proof_Data (
  type T = (Context.generic -> term -> term list)
  val init = K (K (K []))
)

functor Pattern_Translation (Config : sig
  val parse_pattern : Proof.context -> string -> term
  val check_pattern : Proof.context -> term list -> term list
  val multi_translation_err_msg : string
end) : PATTERN_REWRITE = struct

datatype rewrite = By_Pattern of term list | By_ML of (Context.generic -> term -> term list)

fun rewrite_eq (By_Pattern tms1, By_Pattern tms2) = eq_list (op aconv) (tms1, tms2)
  | rewrite_eq (By_ML _, By_ML _ ) = true
  | rewrite_eq _ = false

fun pat_pat_eq ((p1,a1,b1),(p2,a2,b2)) = p1 = p2 andalso a1 aconv a2 andalso rewrite_eq (b1,b2)

fun export_rewrite ctxt ctxt' (n, tm, By_Pattern terms)
      = (case Variable.export_terms ctxt ctxt' (tm::terms)
           of (tm'::terms') => (n, tm', By_Pattern terms'))
  | export_rewrite ctxt ctxt' (n, tm, By_ML f)
      = (n, singleton (Variable.export_terms ctxt ctxt') tm, By_ML f)

structure Data = Generic_Data (
  type T = (int (*priority*) * term (*pattern P*) * rewrite (*the default pattern X*)) Net.net
  (*It gives the default pattern P of an introduction rule whose conclusion matches some pattern P.
    Larger priority is more prior.*)
  val empty = Net.empty
  val merge = Net.merge pat_pat_eq
)

fun add pat_pats ctxt =
      Data.map (fold (fn (n,p1,p2) =>
              Net.insert_term pat_pat_eq (p1,(n,p1,p2))) pat_pats) ctxt
      handle Net.INSERT => Exn.error ("Some pattern clashes with existing entries.")

fun remove (n,p1,p2) =
      Data.map (Net.delete_term_safe pat_pat_eq (p1,(n,p1,p2)))

fun calculate ctxt term (n, pat0, By_Pattern pat_ret0) =
     (let val ind = Term.maxidx_of_term term + 1
          val pat = Logic.incr_indexes ([],[],ind) pat0
          val pat_ret = map (Logic.incr_indexes ([],[],ind)) pat_ret0
          val s = Pattern.match (Context.theory_of ctxt) (pat, term) (Vartab.empty, Vartab.empty)
       in (SOME (n, map (Envir.subst_term s) pat_ret))
      end handle Pattern.MATCH => NONE)
  | calculate ctxt term (n, _, By_ML rewr) =
      (SOME (n, rewr ctxt term))

fun calculate_by_unify ctxt term (n, pat0, By_Pattern pat_ret0) =
     (let val ind = Term.maxidx_of_term term + 1
          val pat = Logic.incr_indexes ([],[],ind) pat0
          val pat_ret = map (Logic.incr_indexes ([],[],ind)) pat_ret0
       in Unify.unifiers (ctxt, Envir.empty (Term.maxidx_of_term pat), [(pat, term)])
               |> Seq.chop 2
               |> (fn ([],_) => NONE
                    | ([(s,_)],_) => SOME (n, map (Envir.subst_term (Envir.type_env s, Envir.term_env s)) pat_ret)
                    | _ => error (Pretty.string_of (Pretty.chunks [
                            Pretty.str "Multiple unifiers between:",
                            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt pat,
                            Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt term
                        ])))
      end handle Pattern.MATCH => NONE)
  | calculate_by_unify ctxt term (n, _, By_ML rewr) =
      (SOME (n, rewr ctxt term))


fun rewr_clash ctxt (n1,ret) (n2,ret2) =
  error (Pretty.string_of (Pretty.chunks (
        [Pretty.str "Multiple potential patterns are available:"] @
        (map (Syntax.pretty_term (Context.proof_of ctxt)) ret) @
        [Pretty.str "versus"] @
        (map (Syntax.pretty_term (Context.proof_of ctxt)) ret2) @
        [Pretty.str Config.multi_translation_err_msg]
     )))

fun get_distinct_seq ctxt (n,ret) seq =
  case Seq.pull seq
    of SOME ((n',ret'), seq') => if n' < n then ret
                                 else if eq_set (op aconv) (ret,ret')
                                 then get_distinct_seq ctxt (n,ret) seq'
                                 else rewr_clash ctxt (n,ret) (n',ret)
     | NONE => ret

fun gen_translate calc ctxt term =
  Net.match_term (Data.get ctxt) term
    |> sort (fn ((n1,_,_),(n2,_,_)) => int_ord (n2,n1))
    |> Seq.of_list
    |> Seq.map_filter (calc ctxt term)
    |> Seq.pull
    |> (fn SOME ((n,ret), seq) => get_distinct_seq ctxt (n,ret) seq
         | NONE => [])

val translate = gen_translate calculate
val translate_by_unify = gen_translate calculate_by_unify

fun parse_pats ctxt ((p1,p2),n) =
  let val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
      val (p1'::p2') = Config.check_pattern ctxt_p (Config.parse_pattern ctxt_p p1 ::
                                               map (Config.parse_pattern ctxt_p) p2)
   in (n,p1', By_Pattern p2')
  end

val term_pattern = Scan.peek (fn generic => Args.named_term (
      let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of generic)
       in singleton (Config.check_pattern ctxt) o Config.parse_pattern ctxt end))

fun app2 f [] [] = ()
  | app2 f (h1::L1) (h2::L2) = (f (h1,h2); app2 f L1 L2)

val pat2 =
   ((Scan.lift (Args.internal_term --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) --
     Scan.repeat1 Args.internal_term --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn ((p1,p2),n) => (n,p1, By_Pattern p2)))
|| ((Args.context -- Scan.lift (Parse.token Parse.embedded --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
                  -- Scan.repeat1 (Parse.token Parse.embedded) --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (ctxt,((tok_p1,tok_p2),n)) =>
    let val p1 = Token.inner_syntax_of tok_p1
        val p2 = map (Token.inner_syntax_of) tok_p2
        val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
        val (p1'::p2') = Config.check_pattern ctxt_p (Config.parse_pattern ctxt_p p1 ::
                                                 map (Config.parse_pattern ctxt_p) p2)
        val _ = Token.assign (SOME (Token.Term p1')) tok_p1
        val _ = app2 (fn (tok,p') => Token.assign (SOME (Token.Term p')) tok) tok_p2 p2'
     in (n,p1', By_Pattern p2')
     end))

val pat_ML = (Args.context -- term_pattern -- Scan.lift ((\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
                          |-- Parse.ML_source --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn ((ctxt,p1'),(src,n)) =>
    let val ctxt' = Context.Proof ctxt
            |> ML_Context.expression (Input.pos_of src)
              (ML_Lex.read "Theory.local_setup (PLP_Reasoner_Pattern_Parse_Sender_Qiyuan_Xu.put (" @
               ML_Lex.read_source src @
               ML_Lex.read "))")
     in (n,p1', By_ML (PLP_Reasoner_Pattern_Parse_Sender_Qiyuan_Xu.get (Context.the_proof ctxt')))
     end)

fun setup_attribute binding comment =
      Attrib.setup binding
        (Args.context -- Parse.enum1' "and" pat2 >> (fn (ctxt,pats) =>
                Thm.declaration_attribute (K (fn ctxt' =>
                    add pats ctxt'
                    )))) comment
   #> Attrib.setup (Binding.suffix_name "_ML" binding)
        (Args.context -- Parse.enum1' "and" pat_ML >> (fn (ctxt,pats) =>
                Thm.declaration_attribute (K (fn ctxt' =>
                    let val ctxt'' = Context.proof_of ctxt'
                     in add (map (export_rewrite ctxt ctxt'') pats) ctxt' end)))) comment

end