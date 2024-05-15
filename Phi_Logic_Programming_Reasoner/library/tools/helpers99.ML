signature PLPR_SYNTAX = sig
include PLPR_SYNTAX

(*strips all controlling connectives*)
val fold_antecedents : (bvs -> term -> 'a -> 'a)
                    -> bvs -> term -> 'a -> 'a

val eixsts_antecedent : (term -> bool) -> term -> bool
val forall_antecedent : (term -> bool) -> term -> bool
val app_antecedents : (bvs -> term -> unit)
                    -> bvs -> term -> unit

end

structure PLPR_Syntax : PLPR_SYNTAX = struct
open PLPR_Syntax

fun fold_antecedents F =
  let fun fold bvtys (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ X $ Y) x = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (N, Ty, X)) x = fold ((N,Ty)::bvtys) X x
        | fold bvtys (Const(\<^const_name>\<open>pure_all_embed\<close>, _) $ Abs (N, Ty, X)) x = fold ((N,Ty)::bvtys) X x
        | fold bvtys (Const(\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ Abs (N, Ty, X)) x
            = fold ((N,Ty)::bvtys) X x
        | fold bvtys (Const(\<^const_name>\<open>\<r>Guard\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Ant_Seq\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>pure_prop_embed\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Do\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Do_embed\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Action_Tag\<close>, _) $ X $ _) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Meta_Tag\<close>, _) $ X $ _) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>NO_SIMP'\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>With_IN_Arg\<close>, _) $ X $ _) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>With_Pattern\<close>, _) $ X $ _) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Except_Pattern\<close>, _) $ X $ _) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>pure_imp_embed\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>pure_conj_embed\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>Branch\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>Branch_embed\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>HOL.disj\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>Orelse_shortcut\<close>, _) $ X $ Y) x
            = fold bvtys Y (fold bvtys X x)
        | fold bvtys (Const(\<^const_name>\<open>Try\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Attempt_Fallback\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys (Const(\<^const_name>\<open>Memoize\<close>, _) $ X) x = fold bvtys X x
        | fold bvtys X x = F bvtys X x
   in fold
  end

fun app_antecedents F bvs term =
  fold_antecedents (fn bvs => fn term => fn _ => F bvs term) bvs term ()

fun eixsts_antecedent P X = fold_antecedents (fn _ => fn X => fn b => b orelse P X) [] X false
fun forall_antecedent P X = fold_antecedents (fn _ => fn X => fn b => b andalso P X) [] X true

end