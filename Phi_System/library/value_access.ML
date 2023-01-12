signature PHI_VALUE = sig

val has_val : string (*external name*) -> Proof.context -> bool
val delete_val : string (*external name*) -> Proof.context -> Proof.context
val update_val : binding -> thm (*rule*) -> Proof.context -> Proof.context
      (*a rule in form \<open>(sem_value.dest (v <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)\<close>*)

end

structure Phi_Value : PHI_VALUE = struct

structure Values = Proof_Data (
  type T = thm Symtab.table
              (*rules in form \<open>(sem_value.dest (v <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)\<close>*)
  val init = K Symtab.empty
)

fun has_val xname ctxt = Symtab.defined (Values.get ctxt) xname

fun delete_val' pred xname ctxt =
  case Symtab.lookup (Values.get ctxt) xname
    of SOME rule => if pred rule
                    then ctxt
                    else Context.proof_map (Phi_Reasoner.del_intro_rule rule) ctxt
     | NONE => ctxt

val delete_val = delete_val' (K false)

fun pattern_of ctxt xname rule =
  let
    val iname = Variable.intern_fixed ctxt xname
    val i = 1 + Thm.maxidx_of rule
  in case Thm.prop_of rule
       of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>,
                                (T1 as Type ("fun", [_, Type ("fun", [T,_])])))
              $ (Const (\<^const_name>\<open>sem_value.dest\<close>, T2)
                              $ (Const (\<^const_name>\<open>Value_of\<close>, T3) $ V1 $ Free (vname, T4)))
              $ _)
             => if vname = iname
                then
                  \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, T1)
                    $ (Const (\<^const_name>\<open>sem_value.dest\<close>, T2)
                          $ (Const (\<^const_name>\<open>Value_of\<close>, T3) $ Var (("val", i), fastype_of V1)
                                                              $ Free (vname, T4)))
                    $ Var (("out", i), T))
                else raise THM ("Bad Rule", 0, [rule])
         | _ => raise THM ("Bad Rule", 0, [rule])
  end

fun valterm_of ctxt rule =
  case Thm.prop_of rule
    of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
          $ (Const (\<^const_name>\<open>sem_value.dest\<close>, _)
                       $ (Const (\<^const_name>\<open>Value_of\<close>, _) $ _ $ Free (vname, T)))
          $ _)
         => Free (Variable.revert_fixed ctxt vname, T)
     | _ => raise THM ("Bad Rule", 0, [rule])

fun update_val b rule ctxt = ctxt
     |> delete_val' (fn rule' => Thm.eq_thm_prop (rule',rule)) (Binding.name_of b)
     |> Values.map (Symtab.update ((Binding.name_of b), rule))
     |> Context.proof_map (Phi_Reasoner.add_intro_rule
                              (Binding.pos_of b) 1000
                              ([pattern_of ctxt (Binding.name_of b) rule],[])
                              rule)
     |> Generic_Variable_Access.bind_local_vals [(Binding.name_of b, valterm_of ctxt rule)]



fun value_assigner b (ctxt,_) =
  let
  val xname = Binding.name_of b
  val (vname, ctxt) = if has_val xname ctxt
                      then (Variable.intern_fixed ctxt xname, ctxt)
                      else Proof_Context.add_fixes [(b, SOME \<^typ>\<open>valname\<close>, NoSyn)] ctxt |> apfst hd
  val vterm = Thm.cterm_of ctxt (Free (vname, \<^typ>\<open>valname\<close>))
  val rule = @{thm "__set_value_rule__"}
        |> Thm.instantiate (TVars.empty, Vars.make [((("name",0), \<^typ>\<open>valname\<close>), vterm)])
  in (rule, ctxt, [], [update_val b]) end

val _ = Theory.setup (Generic_Variable_Access.register_assigner
          ("val", \<^type_name>\<open>valname\<close>, "to declare a new local value", value_assigner))

(*
if existed
     then (@{thm "__set_var_rule__"}, ctxt, [], [])
     else let
          val rule = if Config.get ctxt variable_is_typed
                     then @{thm "__set_new_var_rule__"}
                     else @{thm "__set_new_var_noty_rule__"}
          val ([vname],ctxt) = Proof_Context.add_fixes [(b, SOME \<^typ>\<open>varname\<close>, NoSyn)] ctxt
          val ctxt = Generic_Variable_Access.bind_local_vals
                        [(Binding.name_of b, Free (Binding.name_of b, @{typ varname}))] ctxt
          in (rule, ctxt, [Thm.cterm_of ctxt (Free (vname, @{typ varname}))], [declare])
          end *)

end