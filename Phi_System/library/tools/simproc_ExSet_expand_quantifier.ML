structure Phi_Help : PHI_HELP = struct
open Phi_Help

fun mk_exp' thy has_R arity =
  let val ctxt0 = Proof_Context.init_global thy
      val model_ty = TVar(("'c",0), \<^sort>\<open>type\<close>)
      val x_ty = TVar(("'x",0), \<^sort>\<open>type\<close>)
      val X = Var(("X",0), x_ty --> \<^Type>\<open>BI model_ty\<close>)
      val y_tys = List.tabulate (arity, fn i => TVar(("'a",i), \<^sort>\<open>type\<close>))
      val f = Var(("f",0), y_tys ---> x_ty)
      val R = Var(("R",0), y_tys ---> HOLogic.boolT)
      val x_eq_f_ys = (\<^Const>\<open>HOL.eq x_ty\<close> $ Bound arity
                          $ fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) y_tys f)
      val LHS = if has_R
                then \<^Const>\<open>HOL.conj\<close> $ x_eq_f_ys
                        $ (fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) y_tys R)
                else x_eq_f_ys
      val RHS = if has_R
                then fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) y_tys R
                else \<^Const>\<open>True\<close>

      val y_ty_names = map_index (apfst Name.bound) y_tys
      val goal =
            \<^Const>\<open>Pure.eq \<^Type>\<open>BI model_ty\<close>\<close>
              $ (\<^Const>\<open>ExBI x_ty model_ty\<close> $ Abs("x", x_ty,
                    \<^Const>\<open>Subjection model_ty\<close>
                        $ (X $ Bound 0)
                        $ (fold_rev (fn (N,T) => fn B => \<^Const>\<open>HOL.Ex T\<close> $ Abs (N, T, B)) y_ty_names LHS)
                     ))
              $ (fold_rev (fn (N,T) => fn B => \<^Const>\<open>ExBI T model_ty\<close> $ Abs(N, T, B)) y_ty_names
                  (\<^Const>\<open>Subjection model_ty\<close>
                      $ (X $ (fold_index (fn (i,_) => fn X => X $ Bound (arity - 1 - i)) y_tys f))
                      $ RHS))
       val goal' = Thm.cterm_of ctxt0 goal
                |> Goal.init
       val ((_, [goal'']), ctxt) = Variable.import true [goal'] ctxt0
       val tac = Local_Defs.unfold_tac ctxt @{thms BI_eq_iff ExBI_expn Subjection_expn atomize_eq}
                 THEN Blast.blast_tac ctxt 1
   in case Seq.pull (tac goal'')
        of NONE => error "Internal bug #1fa65324-1ec8-4708-859d-04bb31733ca8"
         | SOME (goal'3, _) =>
            Goal.conclude (singleton (Variable.export ctxt ctxt0) goal'3)
  end

val cache = List.tabulate (10, fn i => mk_exp' \<^theory> true (i+1) |> Thm.trim_context)
val cache_no_R = List.tabulate (10, fn i => mk_exp' \<^theory> false (i+1) |> Thm.trim_context )

fun mk_exp thy has_R arity =
  if arity > 10
  then mk_exp' thy has_R arity
  else List.nth ((if has_R then cache else cache_no_R), arity-1)

fun ExBI_expand_quantifier' ctxt ctm =
  let val thy = Proof_Context.theory_of ctxt
      val (_,tenv) = Pattern.match thy (\<^pattern>\<open>ExBI (\<lambda>x. _ \<s>\<u>\<b>\<j> ?X x)\<close>, Thm.term_of ctm)
                                       (Vartab.empty, Vartab.empty)
      val SOME (_, X) = Vartab.lookup tenv ("X",0)
      fun dest arity (Abs (_,_,X)) = dest arity X
        | dest arity (Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ X) = dest (arity+1) X
        | dest arity (Const(\<^const_name>\<open>conj\<close>, _)
                          $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound i $ _ )
                          $ _ )
            = if arity = 0 then NONE
              else if i = arity then SOME (mk_exp thy true arity) else NONE
        | dest arity (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ Bound i $ _ )
            = if arity = 0 then NONE
              else if i = arity then SOME (mk_exp thy false arity) else NONE
        | dest _ _ = NONE
   in dest 0 X
   |> Option.map (fn rule => Conv.rewr_conv rule ctm)
  end
  handle Pattern.MATCH => NONE


val _ = Theory.setup (Named_Target.theory_map (
          Simplifier.define_simproc \<^binding>\<open>ExBI_expand_quantifier\<close>
              {lhss = [\<^term>\<open>X x \<s>\<u>\<b>\<j> x. (\<exists>y. Y x y)\<close>], proc = K ExBI_expand_quantifier'}))

end