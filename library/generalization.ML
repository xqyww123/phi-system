signature PHI_GENERALIZATION = sig

  val gen_pattern_match : (Proof.context -> 'a list -> string list * (string list * Proof.context))
        -> (Proof.context * string list -> 'b -> term)
        -> 'a list -> 'b -> Proof.context
        -> term -> string list * string list * (int * typ) Symtab.table * term * Proof.context

  datatype command = By_Quantifiers of string list * string option
                   | By_Pattern of ((binding * string option * mixfix) list * string) * string option
                   | Nop
  val generalize : command -> Proof.context -> term -> term
  val syntax : Token.T list -> command * Token.T list

end

structure Phi_Generalization : PHI_GENERALIZATION = struct

fun gen_pattern_match prep_vars prep_pattern
        raw_vars raw_pattern ctxt' term  =
  let
    val (origin_names, (vnames, ctxt)) = prep_vars ctxt' raw_vars
    val pattern = prep_pattern (ctxt,vnames) raw_pattern
  in
    if null origin_names
    then ([], [], Symtab.empty, pattern, ctxt)
    else
    let
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
  end


fun gen_generalize prep_vars prep_pattern prep_subj
        raw_vars raw_pattern subj ctxt' assn =
  let
    val (origin_names, _, vars, assn', ctxt) =
          gen_pattern_match prep_vars prep_pattern raw_vars raw_pattern ctxt' assn      
    fun subst_var lev n x = case Symtab.lookup vars n
                              of SOME (i,_) => Bound (lev + i)
                               | NONE => x
    fun abstract lev (tm as Var ((n,0),_)) = subst_var lev n tm
      | abstract lev (tm as Free (n,_)) = subst_var lev n tm
      | abstract lev (A $ B) = abstract lev A $ abstract lev B
      | abstract lev (Abs (name,ty,X)) = (Abs (name,ty, abstract (lev+1) X))
      | abstract j (Bound i) = if j <= i then Bound (i + length origin_names) else Bound i
      | abstract _ X = X
    fun generalize assn'' = assn''
           |> (fn x => case subj
                         of SOME s => Const (\<^const_name>\<open>Subjection\<close>, dummyT) $ x $ prep_subj ctxt s
                          | NONE => x)
           |> abstract 0
           |> fold (fn v => fn b =>
                Const (\<^const_name>\<open>ExSet\<close>, dummyT) $ Abs (v, snd (the (Symtab.lookup vars v)), b)
              ) origin_names
  in(case assn'
       of Abs (name, ty, X) => Abs (name, ty, generalize X)
        | X => generalize X)
     |> Syntax.check_term ctxt'
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

fun generalize_by_quantifiers_cmd raw_vars subj ctxt assn =
      gen_generalize (fn ctxt => Syntax.read_terms ctxt
                              #> map (fn (Free (x,_)) => x
                                       | t => raise TERM("pattern must be a free variable", [t]))
                              #> (fn vs => (vs, (vs, ctxt))))
                     (K (K assn)) Syntax.read_term
                     raw_vars () subj ctxt assn

datatype command = By_Quantifiers of string list * string option
                 | By_Pattern of ((binding * string option * mixfix) list * string) * string option
                 | Nop

fun generalize (By_Quantifiers (parts,subj)) = generalize_by_quantifiers_cmd parts subj
  | generalize (By_Pattern ((vars,pat),subj)) = generalize_by_pattern_cmd vars pat subj
  | generalize Nop = K I

local open Parse Scan in
val syntax =
     (\<^keyword>\<open>var\<close> |-- vars --| \<^keyword>\<open>in\<close> -- term -- option (\<^keyword>\<open>subj\<close> |-- term)) >> By_Pattern
  || (\<^keyword>\<open>var\<close> |-- repeat term -- option (\<^keyword>\<open>subj\<close> |-- term)) >> By_Quantifiers
  || (\<^keyword>\<open>subj\<close> |-- term) >> (fn subj => By_Quantifiers ([], SOME subj))
  || (term >> (fn t => By_Pattern (([],t),NONE)))
  || succeed Nop

(* Generalize an assertion by existentially quantifying vars and constraining with subj. *)

end

end