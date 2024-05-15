local

fun err_cg () =
  error "Guard \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> cannot be used check the consistency of contextual premises.\n\
        \The use of \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False\<close> is illegal."
fun chk_mode (Const(\<^const_name>\<open>MODE_GUARD\<close>, _)) = err_cg ()
  | chk_mode (Const(\<^const_name>\<open>NO_INST\<close>, _)) = err_cg ()
  | chk_mode _ = ()

val chk_condition_guard' =
  PLPR_Syntax.app_antecedents (fn bvs =>
      fn Const(\<^const_name>\<open>Premise\<close>, _) $ mode $ Const(\<^const_name>\<open>False\<close>, _) =>
          chk_mode mode
       | _ => ())

in

val _ = Theory.setup (Context.theory_map (
  Phi_Reasoner.add_pass (\<^prop>\<open>check (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False)\<close>, \<^pattern_prop>\<open>_\<close>, fn pos =>
      fn data as (rules,_,_,_,_) => (
          List.app (chk_condition_guard' [] o Thm.prop_of) rules
        ; data))
))

end