signature LOCAL_VALUE = sig
  val parse_var_add_tag : bool Config.T

  val mk_var_scope : Binding.binding list -> context_state -> context_state
  val dest_Var : term -> (string * (term * term)) option
end

structure Local_Value : LOCAL_VALUE = struct
open NuHelp PhiSyntax NuSys

fun dest_Var (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ (Const (\<^const_name>\<open>std.Var\<close>,_) $ _ $ name $ T))
      = SOME (Term.term_name name, (x,T))
  | dest_Var (Const (\<^const_name>\<open>std.Obj_Ele\<close>, _) $ x) = dest_Var x
  | dest_Var _ = NONE

fun local_value_export ctxt rule vars sequent =
  NuApply.MP ctxt (Drule.forall_intr_list vars sequent) rule

datatype operation = Set_Var of cterm | New_Var of Binding.binding

fun length_of_sets ret [] = ret
  | length_of_sets ret (Set_Var _ :: r) = length_of_sets (1+ret) r 
  | length_of_sets ret (New_Var _ :: r) = length_of_sets ret r

fun mk_var_scope names''' (ctxt,sequent) =
  let
    val blk_var as (Free (blk_name,_)) = current_block_var sequent
    val blk_name = Variable.revert_fixed ctxt blk_name
    val names = rev names'''
    val arity = length names
    val ex_vars = Thm.prop_of sequent
                  |> dest_CurrentConstruction |> #3
                  |> strip_separations
                  |> map_filter (dest_Var)
    fun check_name name =
          case Option.map (` (AList.defined (op =) ex_vars))
                  (Variable.lookup_fixed ctxt (Variable.check_name name))
            of SOME (true, iname) => Set_Var (Thm.cterm_of ctxt (Free (iname, \<^typ>\<open>varname\<close>)))
             | _ => New_Var name
    val oprs = map check_name names
    val num_sets = length_of_sets 0 oprs

    val init = Thm.trivial (Thm.var (("init",0),\<^ctyp>\<open>prop\<close>))
    val op_var_scope = Proof_Context.get_thm ctxt "local.__\<phi>op_var_scope__"
    val op_set_var   = Proof_Context.get_thm ctxt "local.__\<phi>op_set_var__"
    val op_var_scope0= Proof_Context.get_thm ctxt "local.__\<phi>op_var_scope__0"
    val op_var_scope' = init
          |> fold (fn v => fn th =>
                case v of Set_Var vterm =>
                            (Drule.infer_instantiate ctxt [(("var",0), vterm)] op_set_var) RS th
                        | New_Var _ => op_var_scope RS th) oprs
          |> (fn thm => op_var_scope0 RS thm)
    val (ctxt,sequent') = NuApply.apply [op_var_scope'] (ctxt,sequent)
                |> apsnd (
                      (fn th => @{thm Premise_True} RS th)
                   #> Thm.permute_prems 0 1
                   #> Goal.protect (num_sets + arity))
                |> Nu_Reasoner.reason
                |> (fn x => case x of SOME y => apsnd Goal.conclude y
                                    | _ => error (
    "Fail to assign variable(s). Typically, it is due to incorrect representation types."))

    val prem = Thm.cprem_of sequent' 1
    val (vnames,ctxt) =
          Proof_Context.add_fixes (oprs
                                   |> map_filter (fn x => case x of New_Var b => SOME b | _ => NONE)
                                   |> map (fn x => (x, SOME \<^typ>\<open>varname\<close>, NoSyn))) ctxt

    val vterms = map (fn name => Thm.cterm_of ctxt (Free (name, \<^typ>\<open>varname\<close>))) vnames
    val prem' = fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) vterms prem
    val (_,arg_phi,ret_phi,E) = dest_procedure_c prem'

    val ([], ctxt) =
      Proof_Context.add_assms (fn _ => fn [] => (local_value_export ctxt sequent' vterms, I)) [] ctxt

    val goal = NuToplevel.get_thesis ctxt
    val (trueprop, goal_term) = Thm.dest_comb goal
    val ((goal_F_arg,goal_ret), goal_E) = Thm.dest_comb goal_term |> apfst Thm.dest_comb
    fun left_most (Const (\<^const_name>\<open>times\<close>, _) $ A $ _) = left_most A
      | left_most X = X
    val ret_phi' = Thm.incr_indexes_cterm (Thm.maxidx_of_cterm goal) ret_phi
    val Var R = left_most (Thm.term_of ret_phi')
    val goal_ret' = Thm.instantiate_cterm (TVars.empty, Vars.make [(R,goal_ret)]) ret_phi'
    val goal' = Thm.apply trueprop (Thm.apply (Thm.apply goal_F_arg goal_ret') goal_E)
    val ctxt = NuToplevel.put_thesis goal' ctxt
  in
    start_proc blk_name arg_phi ctxt
  end


val parse_var_add_tag = Attrib.setup_config_bool \<^binding>\<open>\<phi>parse_var_add_tag\<close> (K false);

(* Syntax *)
val _ = Theory.setup (
let open Ast PhiSyntax
  fun strip_constrain (Const ("_constrain", _) $ x $ _) = strip_constrain x
    | strip_constrain (Const ("_type_constraint_", _) $ x) = strip_constrain x
    | strip_constrain x = x

  fun mk_GetVar ctxt name =
    let
      val value = Thm.prop_of (NuBasics.the_construction ctxt)
                  |> dest_CurrentConstruction |> #3
                  |> strip_separations
                  |> get_first (dest_Var #> Option.mapPartial (fn (name',(x,_)) =>
                                                        if name' = name then SOME x else NONE))
      fun tag v = if Config.get ctxt parse_var_add_tag orelse Config.get ctxt phi_synthesis_parsing
                  then Const (\<^const_name>\<open>Variable_of\<close>, dummyT) $ v $ Free (name, dummyT)
                  else v
    in case value of SOME v => tag v
                   | NONE => error ("No variable named "^quote name^" is found.")
    end

  fun has_get_var (Const (\<^const_name>\<open>get_var____\<phi>\<close>, _)) = true
    | has_get_var (A $ B) = has_get_var A orelse has_get_var B
    | has_get_var (Abs (_,_,X)) = has_get_var X
    | has_get_var _ = false
  fun map_get_var ctxt (Const (\<^const_name>\<open>get_var____\<phi>\<close>, _) $ X)
        = mk_GetVar ctxt (Term.term_name (strip_constrain X))
    | map_get_var ctxt (A $ B) = map_get_var ctxt A $ map_get_var ctxt B
    | map_get_var ctxt (Abs (name,ty,X)) = Abs (name,ty, map_get_var ctxt X)
    | map_get_var ctxt x = x
 in Context.theory_map (Syntax_Phases.term_check ~10 "\<phi>variable" (fn ctxt =>
      map (fn x => if has_get_var x then map_get_var ctxt x else x)))
end
)

end

