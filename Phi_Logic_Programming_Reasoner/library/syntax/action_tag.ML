signature PLPR_SYNTAX = sig

  val dest_tags   :  term ->  term
  val dest_tags_c : cterm -> cterm

  val dest_action_of : string (*the leading constant name*) -> term -> term
  val dest_action_of' :  (term -> bool) -> term -> term * term
  val is_action_of : string (*the leading constant name*) -> term -> bool
  val is_action_of' : (term -> bool) -> term -> bool

  val find_tagged_premise': (term -> bool) -> thm -> (term * term) option
          (*scanning over every premises, compacted forms including \<and>, \<and>\<^sub>\<r>, \<longrightarrow>*)
  val find_tagged_premise : string -> thm -> (term * term) option

end

structure PLPR_Syntax : PLPR_SYNTAX = struct

fun dest_tags (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest_tags X
  | dest_tags (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) = dest_tags X
  | dest_tags (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ X) = dest_tags X
  | dest_tags X = X

fun dest_tags_c X = 
  case Thm.term_of X
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ _ => dest_tags_c (Thm.dest_arg X)
     | Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ _ => dest_tags_c (Thm.dest_arg1 X)
     | Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ _ => dest_tags_c (Thm.dest_arg X)
     | _ => X

fun is_action_of' P (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ _ $ A) = P A
  | is_action_of' P (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = is_action_of' P X
  | is_action_of' P (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ X) = is_action_of' P X
  | is_action_of' _ _ = false
fun is_action_of name = is_action_of' (fn tm => case Term.head_of tm of Const (N',_) => name = N'
                                        | _ => false)

fun dest_action_of' P (tm as (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ A))
      = if P A then (A, X) else raise TERM ("PLPR_Syntax.dest_action_of", [tm])
  | dest_action_of' P (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest_action_of' P X
  | dest_action_of' P (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ X) = dest_action_of' P X
  | dest_action_of' _ tm = raise TERM ("PLPR_Syntax.dest_action_of", [tm])

fun dest_action_of name =
      dest_action_of' (fn tm => case Term.head_of tm of Const (N',_) => name = N'
                        | _ => false) #> snd

fun find_tagged_premise' P =
  let fun find [] = NONE
        | find ((Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ A) :: R) =
            if P A then SOME (A, X) else find R
        | find (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X :: R) = find (X :: R)
        | find (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ X :: R) = find (X :: R)
        | find (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B :: R) = find (A :: B :: R)
        | find (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ A $ B :: R) = find (A :: B :: R)
        | find (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X :: R) = find (X :: R)
        | find (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X) :: R) = find (X :: R)
        | find (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, _, X) :: R) = find (X :: R)
        | find (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X :: R) = find (X :: R)
        | find (_ :: L) = find L
   in find o Thm.prems_of
  end

fun find_tagged_premise name =
      find_tagged_premise' (fn tm => case Term.head_of tm of Const (N',_) => name = N'
                             | _ => false)

end