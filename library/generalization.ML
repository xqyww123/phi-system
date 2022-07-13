signature PHI_GENERALIZATION = sig

  val gen_pattern_match : (Proof.context -> 'a list -> string list * (string list * Proof.context))
        -> (Proof.context * string list -> 'b -> term)
        -> 'a list -> 'b -> Proof.context
        -> term -> string list * string list * (int * typ) Symtab.table * term * Proof.context

  datatype generic = ByPart of string list * string option
                   | ByPattern of ((binding * string option * mixfix) list * string) * string option
                   | None
  val generalize_cmd : generic -> Proof.context -> term -> term
  val syntax : Token.T list -> generic * Token.T list

end

structure Phi_Generalization : PHI_GENERALIZATION = struct

fun gen_pattern_match prep_vars prep_pattern
        raw_vars raw_pattern ctxt' term  =
  let
    val (origin_names, (vnames, ctxt)) = prep_vars ctxt' raw_vars
    val pattern = prep_pattern (ctxt,vnames) raw_pattern
    val (tyinst',tminst') =
            Pattern.first_order_match (Proof_Context.theory_of ctxt) (pattern,term)
                                      (Vartab.empty,Vartab.empty)
    fun filter x = fold (Vartab.delete_safe o rpair 0) vnames x
    val tyinst = filter tyinst'
    val tminst = filter tminst'
    val num = length vnames
    val pattern' = Envir.subst_term (tyinst,tminst) pattern
    fun update_vars n t tab =
          case Symtab.lookup tab n
                                  of SOME (_, t') =>
                                        if t = t' then tab
                                        else raise TYPE("pattern has different types", [t,t'], [])
                                   | NONE =>
                                      let val idx = find_index (fn n' => n' = n) vnames
                                       in if idx = ~1
                                          then tab
                                          else Symtab.update_new (n, (num - 1 - idx, t)) tab end
    val vars = fold_aterms (fn (Var ((n,0),t)) => update_vars n t
                             | (Free (n,t)) => update_vars n t
                             | _ => I
                           ) pattern' Symtab.empty
  in (origin_names, vnames, vars, pattern',ctxt)
  end


fun gen_generalize prep_vars prep_pattern prep_subj
        raw_vars raw_pattern subj ctxt' assn =
  let
    val (origin_names, vnames, vars, assn', ctxt) =
          gen_pattern_match prep_vars prep_pattern raw_vars raw_pattern ctxt' assn
    fun subst_var n x = case Symtab.lookup vars n
                of SOME (i,_) => Bound i
                 | NONE => x
  in assn'
       |> (fn x => case subj
                     of SOME s => Const (\<^const_name>\<open>Subjection\<close>, dummyT) $ x $ prep_subj ctxt s
                      | NONE => x)
       |> Term.map_aterms (fn (x as Var ((n,0),_)) => subst_var n x
                            | (x as Free (n,_)) => subst_var n x
                            | x => x)
       |> fold (fn v => fn b =>
            Const (\<^const_name>\<open>ExSet\<close>, dummyT) $ Abs (v, snd (the (Symtab.lookup vars v)), b)
          ) origin_names
  end

val generalize_by_pattern_cmd =
      gen_generalize (fn ctxt => fn vs =>
                          (map (Binding.name_of o #1) vs, Proof_Context.add_fixes_cmd vs ctxt))
                     (fn (ctxt,vnames) => Proof_Context.read_term_pattern ctxt
                                       #> map_aterms (
                                            fn (Free (n,t)) => if exists (fn n' => n' = n) vnames
                                                               then Var ((n,0), t)
                                                               else Free (n,t)
                                                      (*0 is ok because the name is fixed*)
                                             | x => x))
                     Syntax.read_term

fun generalize_by_parts_cmd raw_vars subj ctxt assn =
      gen_generalize (fn ctxt => Syntax.read_terms ctxt
                              #> map (fn (Free (x,_)) => x
                                       | t => raise TERM("pattern must be a free variable", [t]))
                              #> (fn vs => (vs, (vs, ctxt))))
                     (K (K assn)) Syntax.read_term
                     raw_vars () subj ctxt assn

datatype generic = ByPart of string list * string option
                 | ByPattern of ((binding * string option * mixfix) list * string) * string option
                 | None

fun generalize_cmd (ByPart (parts,subj)) = generalize_by_parts_cmd parts subj
  | generalize_cmd (ByPattern ((vars,pat),subj)) = generalize_by_pattern_cmd vars pat subj
  | generalize_cmd None = K I

local open Parse Scan in
val syntax =
     (\<^keyword>\<open>var\<close> |-- vars --| \<^keyword>\<open>in\<close> -- term -- option (\<^keyword>\<open>subj\<close> |-- term)) >> ByPattern
  || (\<^keyword>\<open>var\<close> |-- repeat term -- option (\<^keyword>\<open>subj\<close> |-- term)) >> ByPart
  || succeed None
end

end