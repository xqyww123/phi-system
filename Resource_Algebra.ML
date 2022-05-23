(*  Title:      Resource_Algebra.ML
    Author:     Qiyuan Xu, 2022

    Mainly constrains valuetypes by @{locale project_inject_RA}.
    Part of the code is copyied and modified from 'HOL/Statespace/state_space.ML'
    written by Norbert Schirmer.
*)

signature RESOURCE_ALGEBRA = sig
  
end
structure Resource_Algebra : RESOURCE_ALGEBRA = struct

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>resource_space\<close>
  "define a resource locale involving given resources, see ????"
    (StateSpace.statespace_decl >> (fn ((args, name), (parents, comps)) =>
      Toplevel.theory (
        StateSpace.define_statespace_L @{locale project_inject_RA} (SOME @{sort unital_ra})
        NONE args name parents comps
      )));
end
