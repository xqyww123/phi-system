signature PATTERN_REWRITE_GLOBAL = sig

type bv_typs = PLPR_Pattern.bv_typs

val mk_pattern : term -> term
val does_match_term : theory -> bv_typs -> term * term -> bool

type redex_residues = term * term list
type redex_residue = term * term

val rewrites : theory -> bv_typs -> redex_residues -> term -> term list option
val rewrite  : theory -> bv_typs -> redex_residue -> term -> term option

end

signature PATTERN_REWRITE = sig

datatype rewrite = By_Pattern of term list | By_ML of (Context.generic -> term -> term list option)
val rewrite_eq : rewrite * rewrite -> bool

type rewr = int * term * Position.T * rewrite

val add : rewr list -> Context.generic -> Context.generic
val remove : rewr -> Context.generic -> Context.generic
val translate : Context.generic -> term -> term list
val setup_attribute : binding -> string -> theory -> theory

val list_rewrites : Context.generic -> rewr list

val print_rewrite  : Proof.context -> rewr -> Pretty.T
val print_rewrites : Context.generic -> unit

end

structure Pattern_Translation : PATTERN_REWRITE_GLOBAL = struct

type bv_typs = PLPR_Pattern.bv_typs
type redex_residues = term * term list
type redex_residue = term * term

fun mk_pattern raw =
  map_aterms (fn Var ((s,i),T) =>
                    if i < 0
                    then raise TERM ("Pattern_Translation: the pattern contains negative schematic index", [raw])
                    else Var ((s, if String.isPrefix "var_" s orelse s = "var" then ~i - 1 else i),T)
               | X => X) raw

val chk_trick = Vartab.forall (fn ((_,i),(_,tm)) => i >= 0 orelse is_Var (Term.head_of (Envir.beta_eta_contract tm)))

fun match_term thy bv_typs pat_obj env =
  let val (tys,tms) = PLPR_Pattern.match thy bv_typs pat_obj env
   in if chk_trick tms then (tys,tms)
      else raise Pattern.MATCH
  end

fun does_match_term thy bv_typs pat_obj =
      (match_term thy bv_typs pat_obj (Vartab.empty, Vartab.empty) ; true)
      handle Pattern.MATCH => false

fun rewrites thy bv_typs (pat,rets) term =
  let val s = PLPR_Pattern.match thy bv_typs (pat, term) (Vartab.empty, Vartab.empty)
      in if chk_trick (snd s)
         then SOME (map (Envir.subst_term s) rets)
         else NONE
   end handle Pattern.MATCH => NONE

fun rewrite thy bv_typs (pat,ret) term = Option.map hd (rewrites thy bv_typs (pat,[ret]) term)

end

structure PLP_Reasoner_Pattern_Parse_Sender_Qiyuan_Xu = Proof_Data (
  type T = (Context.generic -> term -> term list option)
  val init = K (K (K NONE))
)

functor Pattern_Translation (Config : sig
  val parse_pattern : Proof.context -> string -> term
  val check_pattern : Proof.context -> term list -> term list
  val multi_translation_err_msg : string
end) : PATTERN_REWRITE = struct

datatype rewrite = By_Pattern of term list | By_ML of (Context.generic -> term -> term list option)
type rewr = int * term * Position.T * rewrite

fun rewrite_eq (By_Pattern tms1, By_Pattern tms2) = eq_list (op aconv) (tms1, tms2)
  | rewrite_eq (By_ML _, By_ML _ ) = true
  | rewrite_eq _ = false

fun pat_pat_eq ((p1,a1,o1,b1),(p2,a2,o2,b2)) =
      p1 = p2 andalso a1 aconv a2 andalso o1 = o2 andalso rewrite_eq (b1,b2)

fun export_rewrite ctxt ctxt' (n, tm, pos, By_Pattern terms)
      = (case Variable.export_terms ctxt ctxt' (tm::terms)
           of (tm'::terms') => (n, tm', pos, By_Pattern terms'))
  | export_rewrite ctxt ctxt' (n, tm, pos, By_ML f)
      = (n, singleton (Variable.export_terms ctxt ctxt') tm, pos, By_ML f)

structure Data = Generic_Data (
  type T = (int (*priority*) * term (*pattern P*) * Position.T * rewrite (*the default pattern X*)) Net.net
  (*It gives the default pattern P of an introduction rule whose conclusion matches some pattern P.
    Larger priority is more prior.*)
  val empty = Net.empty
  val merge = Net.merge pat_pat_eq
)

fun add pat_pats ctxt =
      Data.map (fold (fn (n,p1,pos,p2) =>
            let val p1' = Pattern_Translation.mk_pattern p1
             in Net.insert_term pat_pat_eq (p1',(n,p1',pos,p2))
            end
          ) pat_pats
        ) ctxt
      handle Net.INSERT => Exn.error ("Some pattern clashes with existing entries.")

fun remove (n,p1,pos,p2) =
      Data.map (Net.delete_term_safe pat_pat_eq (p1,(n,p1,pos,p2)))

fun list_rewrites ctxt = Net.content (Data.get ctxt)

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
      Option.map (pair n) (Pattern_Translation.rewrites (Context.theory_of ctxt) [] (pat0, ret0) term)
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
  let val data = Data.get ctxt
   in fn term => Net.match_term data term
    |> sort (fn ((n1,_,_,_),(n2,_,_,_)) => int_ord (n2,n1))
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
              (ML_Lex.read "Theory.local_setup (PLP_Reasoner_Pattern_Parse_Sender_Qiyuan_Xu.put ((" @
               ML_Lex.read_source src @
               ML_Lex.read ") : Context.generic -> term -> term list option))")
     in (n,p1',pos, By_ML (PLP_Reasoner_Pattern_Parse_Sender_Qiyuan_Xu.get (Context.the_proof ctxt')))
     end)

fun setup_attribute binding comment =
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

end