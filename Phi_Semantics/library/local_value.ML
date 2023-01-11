signature VARIABLE = sig

  val variable_is_typed : bool Config.T
  val dest_Var : term -> (string * (term * term)) option

end

structure Variable : VARIABLE = struct

val variable_is_typed = Config.declare_bool ("\<phi>variable_is_typed", \<^here>) (K false)

fun dest_Var (Const (\<^const_name>\<open>\<phi>Type\<close>, _)
                $ x
                $ (Const (\<^const_name>\<open>basic_fiction.\<phi>\<close>,_)
                    $ _
                    $ (Const (\<^const_name>\<open>\<phi>MapAt\<close>, _)
                        $ Free (name, \<^typ>\<open>varname\<close>)
                        $ (Const (\<^const_name>\<open>\<phi>Some\<close>, _) $ T))))
      = SOME (name, (x,T))
  | dest_Var _ = NONE

fun find_Var var (Const (\<^const_name>\<open>times\<close>, _) $ R $ X) =
     (case dest_Var X
        of SOME (name, xT) => if name = var then SOME xT else find_Var var R
         | NONE => find_Var var R)
  | find_Var var X =
      case dest_Var X
        of SOME (name, xT) => if name = var then SOME xT else NONE
         | NONE => NONE

fun variable_assigner b (ctxt,sequent) =
  let
  val existed = find_Var (Binding.name_of b) (Thm.concl_of sequent) |> is_some
  fun declare rule =
    let
    val pattern = case Thm.prop_of rule
                    of Const (\<^const_name>\<open>Pure.eq\<close>, (T1 as Type ("fun", [T,_]))) $ V1 $ _ =>
                        Const (\<^const_name>\<open>Pure.eq\<close>, T1)
                          $ V1 $ Var (("out", maxidx_of_term V1 + 1), T)
                     | _ => raise THM ("Bad rule.", 0, [rule])
     in Context.proof_map (Phi_Reasoner.add_intro_rule (Binding.pos_of b) 1000 ([pattern], []) rule)
    end
  in if existed
     then (@{thm "__set_var_rule__"}, ctxt, [], [declare])
     else let
          val rule = if Config.get ctxt variable_is_typed
                     then @{thm "__set_new_var_rule__"}
                     else @{thm "__set_new_var_noty_rule__"}
          val ([vname],ctxt) = Proof_Context.add_fixes [(b, SOME \<^typ>\<open>varname\<close>, NoSyn)] ctxt
          val ctxt = Value_Access.bind_local_vals
                        [(Binding.name_of b, Free (Binding.name_of b, @{typ varname}))] ctxt
          in (rule, ctxt, [Thm.cterm_of ctxt (Free (vname, @{typ varname}))], [declare])
          end
  end

val _ = Theory.setup (
            Value_Access.register_assigner ("var", \<^type_name>\<open>varname\<close>,
                "to assign to a new variable", variable_assigner))



end

