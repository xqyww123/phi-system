signature GOAL_DISPLAY = sig
include GOAL_DISPLAY

val pretty_a_goal  : Proof.context -> term -> Pretty.T
val pretty_a_goal' : Proof.context -> term list * term -> Pretty.T

end

structure Goal_Display: GOAL_DISPLAY = struct
open Goal_Display

fun pretty_a_goal' ctxt (prems, concl) =
  let open Pretty
   in chunks (
        keyword1 "goal: " :: indent 2 (Syntax.pretty_term ctxt concl) ::
        (if null prems then []
         else [keyword1 "premises: ",
           text_fold [indent 2 (chunks (map (fn prem => item [Syntax.pretty_term ctxt prem]) prems))]
        ])
     )
  end

fun pretty_a_goal ctxt state =
  let val (_, prems, concl) = Phi_Help.strip_meta_hhf state
   in pretty_a_goal' ctxt (prems, concl)
  end

end