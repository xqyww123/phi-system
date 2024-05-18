signature PATTERN_REWRITE_GLOBAL = sig

type redex_residues = spattern * term list
type redex_residue = spattern * term

val rewrites : theory -> PLPR_Pattern.fixed_bounds -> bvs -> redex_residues -> term -> term list option
val rewrite  : theory -> PLPR_Pattern.fixed_bounds -> bvs -> redex_residue -> term -> term option

end

signature PATTERN_REWRITE = sig

type ML_rewr = Context.generic -> spattern -> term list option
datatype rewrite = By_Pattern of term list
                 | By_ML of ML_rewr
val rewrite_eq : rewrite * rewrite -> bool

type rewr = int * spattern * Position.T * rewrite

val add : rewr list -> Context.generic -> Context.generic
val remove : rewr -> Context.generic -> Context.generic
val translate : Context.generic -> term -> term list
val setup_attribute : binding -> string -> string
                  -> theory
                  -> ML_rewr option Unsynchronized.ref * theory

val list_rewrites : Context.generic -> rewr list

val print_rewrite  : Proof.context -> rewr -> Pretty.T
val print_rewrites : Context.generic -> unit

end

structure Pattern_Translation : PATTERN_REWRITE_GLOBAL = struct

type redex_residues = term * term list
type redex_residue = term * term

fun rewrites thy fixed_bounds bvs (pat,rets) term =
  let val s = PLPR_Pattern.smatch thy fixed_bounds bvs (pat, term) (Vartab.empty, Vartab.empty)
   in SOME (map (Envir.subst_term s) rets)
  end handle Pattern.MATCH => NONE

fun rewrite thy fixed_bounds bv_typs (pat,ret) term =
      Option.map hd (rewrites thy fixed_bounds bv_typs (pat,[ret]) term)

      

end

structure PLP_Reasoner_Pattern_Parse_Sender = Proof_Data (
  type T = (Context.generic -> term -> term list option)
  val init = K (K (K NONE))
)

functor Pattern_Translation (Config : sig
  val parse_pattern : Proof.context -> string -> term
  val check_pattern : Proof.context -> term list -> term list
  val multi_translation_err_msg : string
end) : PATTERN_REWRITE = struct

type ML_rewr = Context.generic -> term -> spattern list option
datatype rewrite = By_Pattern of term list | By_ML of ML_rewr

structure Store = Term_Pattern_Store (struct
    type T = rewrite
    fun eq (By_Pattern tms1, By_Pattern tms2) = eq_list (op aconv) (tms1, tms2)
      | eq (By_ML _, By_ML _ ) = true
      | eq _ = false
    fun export ctxt ctxt' (By_Pattern terms) =
          By_Pattern (Variable.export_terms ctxt ctxt' terms)
      | export _ _ (By_ML f) = By_ML f
  end)

type rewr = Store.entry

val add = Store.add
val remove = Store.remove
val list_rewrites = Store.list
val rewrite_eq = Store.Config.eq

local open Pretty in
fun print_rewrite ctxt (n,pat,pos, By_Pattern [dest]) =
      item([str "(", str (string_of_int n), str ") ", block [Syntax.pretty_term ctxt pat],
            str " \<Rightarrow> ", block [Syntax.pretty_term ctxt dest], str " "] @ here pos)
  | print_rewrite ctxt (n,pat,pos, By_Pattern dests) =
      item([str "(", str (string_of_int n), str ") ", block [Syntax.pretty_term ctxt pat],
            str " \<Rightarrow> ", block (map (fn d => item [Syntax.pretty_term ctxt d]) dests), str " "] @ here pos)
  | print_rewrite ctxt (n,pat,pos, By_ML _) =
      item([str "(", str (string_of_int n), str ") ", block [Syntax.pretty_term ctxt pat],
            str " \<Rightarrow> ML rewriter "] @ here pos)
fun print_rewrites ctxt = 
      writeln (chunks (map (print_rewrite (Context.proof_of ctxt)) (list_rewrites ctxt)))
end

fun do_rewrite ctxt term (n, pat0, _, By_Pattern ret0) =
      Option.map (pair n) (Pattern_Translation.rewrites (Context.theory_of ctxt) (K false) [] (pat0, ret0) term)
  | do_rewrite ctxt term (n, _, _, By_ML rewr) =
      Option.map (pair n) (rewr ctxt term)

fun rewr_clash ctxt (_,ret) (_,ret2) =
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

(*the term cannot contain loose bounded variables*)
fun gen_translate rewr ctxt =
  let val get = Store.get ctxt
   in fn term =>
       get [] term
    |> Seq.of_list
    |> Seq.map_filter (rewr ctxt term)
    |> Seq.pull
    |> (fn SOME ((n,ret), seq) => get_distinct_seq ctxt (n,ret) seq
         | NONE => [])
  end

val translate = gen_translate do_rewrite

(*fun parse_pats ctxt ((p1,p2),n) =
  let val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
      val (p1'::p2') = Config.check_pattern ctxt_p (Config.parse_pattern ctxt_p p1 ::
                                               map (Config.parse_pattern ctxt_p) p2)
   in (n,p1', By_Pattern p2')
  end*)

fun app2 f [] [] = ()
  | app2 f (h1::L1) (h2::L2) = (f (h1,h2); app2 f L1 L2)

(*
val pat2 =
   ((Scan.lift (Parse.position Args.internal_term --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) --
     Scan.repeat1 Args.internal_term --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (((p1,pos),p2),n) => (n,p1,pos, By_Pattern p2)))
|| ((Args.context -- Scan.lift (Parse.position (Parse.token Parse.embedded) --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
                  -- Scan.repeat1 (Parse.token Parse.embedded) --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (ctxt,(((tok_p1,pos),tok_p2),n)) =>
    let val p1 = Token.inner_syntax_of tok_p1
        val p2 = map (Token.inner_syntax_of) tok_p2
        val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
        val (p1'::p2') = Config.check_pattern ctxt_p (Config.parse_pattern ctxt_p p1 ::
                                                 map (Config.parse_pattern ctxt_p) p2)
        val _ = Token.assign (SOME (Token.Term p1')) tok_p1
        val _ = app2 (fn (tok,p') => Token.assign (SOME (Token.Term p')) tok) tok_p2 p2'
     in (n,p1',pos, By_Pattern p2')
     end))

val term_pattern = Scan.peek (fn generic => Parse.position (Args.named_term (
      let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of generic)
       in singleton (Config.check_pattern ctxt) o Config.parse_pattern ctxt end)))

val pat_ML = (Args.context -- term_pattern -- Scan.lift ((\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
                          |-- Parse.ML_source --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn ((ctxt,(p1',pos)),(src,n)) =>
    let val ctxt' = Context.Proof ctxt
            |> ML_Context.expression (Input.pos_of src)
              (ML_Lex.read "Theory.local_setup (PLP_Reasoner_Pattern_Parse_Sender.put ((" @
               ML_Lex.read_source src @
               ML_Lex.read ") : Context.generic -> term -> term list option))")
     in (n,p1',pos, By_ML (PLP_Reasoner_Pattern_Parse_Sender.get (Context.the_proof ctxt')))
     end)
*)

val cached_parser = Scan.repeat1 Args.internal_term >> By_Pattern
val T_parser = Scan.repeat1 (Parse.token Parse.embedded)

fun setup_attribute binding access_to_sender comment =
    Store.setup_decl_attr binding cached_parser T_parser
      (fn ctxt => fn (p1,emb) =>
          let val p2 = map (Token.inner_syntax_of) emb
              val (p1'::p2') = Config.check_pattern ctxt
                                    (Config.parse_pattern ctxt p1 ::
                                     map (Config.parse_pattern ctxt) p2)
           in (p1', By_Pattern p2')
          end) comment
 #> Store.setup_decl_ML_attr (Binding.suffix_name "_ML" binding)
                             access_to_sender
                             (fn ctxt => singleton (Config.check_pattern ctxt) o Config.parse_pattern ctxt)
                             (K By_ML)
                             comment
      
(*
      Attrib.setup binding
        (Args.context -- Parse.and_list' pat2 >> (fn (_,pats) =>
                Thm.declaration_attribute (K (fn ctxt' =>
                    add pats ctxt'
                    )))) comment
   #> Attrib.setup (Binding.suffix_name "_ML" binding)
        (Args.context -- Parse.and_list' pat_ML >> (fn (ctxt,pats) =>
                Thm.declaration_attribute (K (fn ctxt' =>
                    let val ctxt'' = Context.proof_of ctxt'
                     in add (map (export_rewrite ctxt ctxt'') pats) ctxt' end)))) comment
*)
end