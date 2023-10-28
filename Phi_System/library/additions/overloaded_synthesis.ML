signature PHI_SYNTHESIS = sig
include PHI_SYNTHESIS

datatype ovld_signat = Signature of term list * term | Operator of term
val declare_overloaded_operator : ovld_signat -> Position.T
                               -> Phi_Reasoner.mode' * Reasoner_Group.group option
                               -> Context.generic -> Context.generic

end

structure Phi_Synthesis : PHI_SYNTHESIS = struct
open Phi_Synthesis

(*The maximal index must be 0!*)
fun overload_rule_of arity =
  case arity
    of 0 => @{thm overloaded_synthesis_nullary}
     | 1 => @{thm overloaded_synthesis_unary}
     | 2 => @{thm overloaded_synthesis_binary}
     | 3 => @{thm overloaded_synthesis_ternary}
     | _ => error "Arity greater than 3 is not supported yet."

datatype ovld_signat = Signature of term list * term | Operator of term

fun declare_overloaded_operator signat0 pos (mode, prio_group) ctxt0 =
  let val ctxt = Context.proof_of ctxt0

      fun default_signature operator0 =
        let val ctxt' = Proof_Context.augment operator0 ctxt
            val operator = singleton (Variable.export_terms ctxt' ctxt) operator0
            val arg_tys = binder_types (Term.fastype_of operator)
            val arity = length arg_tys
            val arg_names = Name.invent (Variable.names_of ctxt') "x" arity
            val phi_names = Name.invent (Variable.names_of ctxt') "T" arity
            val args = map2 (fn T => fn N => Var ((N,0),T)) arg_tys arg_names
            val phis = map2 (fn T => fn N => Var ((N,0), \<^typ>\<open>VAL \<phi>arg\<close> --> T --> \<^typ>\<open>assn\<close>))
                            arg_tys phi_names
            val arg_specs = map2 (fn x => fn T => Abs("", \<^typ>\<open>VAL \<phi>arg\<close>, Phi_Syntax.mk_phi_type (x, (T $ Bound 0))))
                                 args phis
            val y = list_comb (operator, args)
            val [y_phi_name] = Name.invent (Variable.names_of ctxt') "U" 1
            val y_phi = Var ((y_phi_name,0), \<^typ>\<open>VAL \<phi>arg\<close> --> Term.fastype_of y --> \<^typ>\<open>assn\<close>)
            val y_spec = Abs ("", \<^typ>\<open>VAL \<phi>arg\<close>, Phi_Syntax.mk_phi_type (y, (y_phi $ Bound 0)))
         in (arg_specs, y_spec)
        end

      val (args0, ret0) = case signat0 of Signature s => s
                                        | Operator f => default_signature f
      val (args, ret) = (map (Logic.incr_indexes ([],[],1)) args0,
                         Logic.incr_indexes ([],[],1) ret0)
      val arity = length args

      val rule = overload_rule_of arity
            |> Drule.infer_instantiate ctxt (
                  (("YY",0), Thm.cterm_of ctxt ret) ::
                  map_index (fn (i,tm) => (("S"^string_of_int (1+i), 0), Thm.cterm_of ctxt tm)) args)
      val _ = Phi_Reasoner.info_pretty ctxt 1 (fn () => Pretty.chunks [
                Pretty.str "Obtain the rule of overloaded synthesis:",
                Thm.pretty_thm ctxt rule
              ])

      val (dom_ty, rng_ty) = Term.dest_funT (Term.fastype_of ret)
      val ret_val_ty = Procedure_Syntax.dest_argT dom_ty
      val pattern1 = \<^pattern_prop>\<open>PROP Gen_Synthesis_Rule
                        (Trueprop (\<forall>vs::?'a. \<p>\<r>\<o>\<c> ?F vs \<lbrace> ?X vs \<longmapsto> \<lambda>ret::?'y \<phi>arg. ?YY ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E)) ?An ?Re\<close>
                  |> subst_vars ([(("'y",0), ret_val_ty)], [(("YY",0), ret)])
                  |> Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)
      val pattern2 = \<^pattern_prop>\<open>PROP Gen_Synthesis_Rule
                        (Trueprop (\<forall>vs::?'a. \<p>\<r>\<o>\<c> ?F vs \<lbrace> ?X vs \<longmapsto> \<lambda>ret::?'y \<phi>arg. ?YY ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E)) ?An ?Re\<close>
                  |> subst_vars ([(("'y",0), ret_val_ty)], [(("YY",0), ret)])
                  |> Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)

      val idx = maxidx_of_term ret + 1
      val no_val_ret =
            case Seq.chop 2 (Unify.hounifiers (Context.Proof ctxt, Envir.empty idx, [(ret, Abs("",dom_ty, Var(("X",0),rng_ty)))]))
              of ([(env, _)], _) => SOME (Envir.norm_term env (Var(("X",0),rng_ty)))
               | _ => NONE
      val synthesis_mode = Option.map (fn ret' =>
            Drule.infer_instantiate ctxt [(("A",0),Thm.cterm_of ctxt ret')] @{thm' synthesis_gen_mode_overloaded_I}
          ) no_val_ret

   in ctxt0
   |> Phi_Reasoner.add_rule pos mode prio_group ([],[]) NONE [rule]
   |> Phi_Reasoner.add_rule pos Phi_Reasoner.NORMAL_LOCAL_CUT' (SOME @{reasoner_group %\<phi>synthesis_gen_by_overloading})
                   ([(pattern1,NONE)],[]) NONE [@{thm make_overloaded_synthesis_rule}]
   |> Phi_Reasoner.add_rule pos Phi_Reasoner.NORMAL_LOCAL_CUT' (SOME @{reasoner_group %\<phi>synthesis_gen_by_overloading+10})
                   ([(pattern2,NONE)],[]) NONE [@{thm make_overloaded_synthesis_rule'}]
   |> is_some synthesis_mode ? (fn ctxt =>
      Phi_Reasoner.add_rule pos Phi_Reasoner.NORMAL_LOCAL_CUT' (SOME @{reasoner_group %synthesis_gen_mode_overridded})
                   ([],[]) NONE [the synthesis_mode] ctxt)
  end


(*
structure Overloaded = Generic_Data (
  type T = term Net.net
  val empty = Net.empty
  val merge = Net.merge (op aconv)
)

fun is_overloaded term ctxt =
  Net.match_term (Overloaded.get ctxt) term
    |> exists (fn X => ) *)

end