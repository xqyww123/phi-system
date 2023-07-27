chapter \<open>Reasoning Processes in IDE-CP - Part I\<close>

text \<open>The part includes some reasoning processes that can already be defined
  after the IDE-CP is ready.\<close>

theory IDE_CP_Reasoning2
  imports IDE_CP_Applications1
begin

section \<open>Small Reasoning Processes\<close>

text \<open>The section includes several processes handling values used in different scenarios.\<close>

subsection \<open>Removing Values\<close>

text \<open>Given an assertion X, antecedent \<^term>\<open>Remove_Values X X'\<close>
  returns X' where all free value assertions \<^term>\<open>x \<Ztypecolon> Val raw T\<close> filtered out, where \<^term>\<open>raw\<close>
  contains at least one free variable of \<^typ>\<open>'a \<phi>arg\<close>.

  It is typically used in exception. When a computation triggers an exception at state X,
    the state recorded in the exception is exactly X' where value assertions are filtered out.\<close>

declare [[\<phi>reason_default_pattern \<open>Remove_Values ?X _\<close> \<Rightarrow> \<open>Remove_Values ?X _\<close> (100)]]

(* lemma [\<phi>reason for \<open>Remove_Values ?ex ?var_X ?Z\<close>]:
  \<open>Remove_Values ex X X\<close>
  unfolding Remove_Values_def using transformation_refl . *)

lemma [\<phi>reason 1200]:
  \<open>(\<And>c. Remove_Values (T c) (T' c))
\<Longrightarrow> Remove_Values (ExSet T) (ExSet T')\<close>
  unfolding Remove_Values_def Transformation_def
  by simp blast

lemma [\<phi>reason 1200]:
  \<open>(\<And>c. Remove_Values (R * T c) (R' * T' c))
\<Longrightarrow> Remove_Values (R * ExSet T) (R' * ExSet T')\<close>
  unfolding Remove_Values_def Transformation_def
  by simp blast

lemma [\<phi>reason 1200]:
  \<open> Remove_Values T T'
\<Longrightarrow> Remove_Values (T \<s>\<u>\<b>\<j> P) (T' \<s>\<u>\<b>\<j> P)\<close>
  unfolding Remove_Values_def Transformation_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values (R * T) (R' * T')
\<Longrightarrow> Remove_Values (R * (T \<s>\<u>\<b>\<j> P)) (R' * (T' \<s>\<u>\<b>\<j> P))\<close>
  unfolding Remove_Values_def Transformation_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values (A * B) (A' * B')
\<Longrightarrow> Remove_Values (A * \<blangle> B \<brangle>) (A' * \<blangle> B' \<brangle>)\<close>
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values \<blangle> A \<brangle> \<blangle> A' \<brangle>\<close>
  by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values B B'
\<Longrightarrow> Remove_Values (A + B) (A' + B')\<close>
  unfolding Remove_Values_def Transformation_def
  by blast

lemma [\<phi>reason 1200]:
  \<open> Remove_Values R R'
\<Longrightarrow> Remove_Values (R * (x \<Ztypecolon> Val raw T)) R'\<close>
  unfolding Remove_Values_def Transformation_def by (simp add: Val_expn)

lemma [\<phi>reason 1200]:
  \<open>Remove_Values (x \<Ztypecolon> Val raw T) 1\<close>
  unfolding Remove_Values_def Transformation_def by (simp add: Val_expn)

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values (1 * A) A'\<close>
  unfolding Remove_Values_def Transformation_def by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values (A * 1) A'\<close>
  unfolding Remove_Values_def Transformation_def by simp

lemma [\<phi>reason 1200]:
  \<open>Remove_Values (A * 0) 0\<close>
  unfolding Remove_Values_def Transformation_def by simp

lemma [\<phi>reason 1100]:
  \<open> Remove_Values B B'
\<Longrightarrow> Remove_Values A A'
\<Longrightarrow> Remove_Values (A * B) (A' * B')\<close>
  unfolding Remove_Values_def Transformation_def by simp blast

lemma [\<phi>reason 1000]:
  \<open> Remove_Values A A\<close>
  unfolding Remove_Values_def
  by simp

(*
subsection \<open>Extract a Value\<close>

definition \<open>Extract_a_Value (S_in::assn) S_out val_out \<longleftrightarrow> (S_in \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S_out \<w>\<i>\<t>\<h> val_out)\<close>

text \<open>\<^prop>\<open>Extract_a_Value S_in S_out val_out\<close> removes the first (right-most) value from the
  input assertion \<open>S_in\<close> and gives the specification theorem of the removed value in \<open>val_out\<close>.

  The process is used during assigning a local value to a binding which
    enables user to access the value later.
  The specification theorem of the value is in form \<^prop>\<open>\<phi>arg.dest raw_val \<in> (x \<Ztypecolon> T)\<close>.
  The binding is bound with this theorem which is used when later loading this value back
    to the state sequent when user is accessing the value.
\<close>

lemma [\<phi>reason 1200 for \<open>Extract_a_Value (?R \<heavy_comma> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?T) ?R ?V\<close>]:
  \<open>Extract_a_Value (R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T) R (\<phi>arg.dest v \<in> (x \<Ztypecolon> T))\<close>
  unfolding Extract_a_Value_def Transformation_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1100]:
  \<open> Extract_a_Value R R' V
\<Longrightarrow> Extract_a_Value (R\<heavy_comma> X) (R'\<heavy_comma> X) V\<close>
  unfolding Extract_a_Value_def
  by (rule implies_right_prod)

lemma [\<phi>reason 1000]:
  \<open> ERROR TEXT(\<open>The assertion has no value.\<close>)
\<Longrightarrow> Extract_a_Value R R' V\<close>
  by blast

lemma apply_extract_a_value:
  \<open> \<c>\<u>\<r>\<r>\<e>\<n>\<t> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S
\<Longrightarrow> Extract_a_Value S S' V
\<Longrightarrow> (\<c>\<u>\<r>\<r>\<e>\<n>\<t> s [R] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> S') \<and> V\<close>
  unfolding Extract_a_Value_def
  using \<phi>apply_implication . *)








section \<open>\<exists>-free ToA Reasoning with Normalization\<close>

text \<open>The section and the next section present the main reasoning procedure for transformations of
  abstraction in the system. The section gives the part passing every element in the right hand side
  of a transformation goal, i.e., find the transformation of the target objects one by one, using
  the remained source objects of (the transformation of) the previous object as the source of the
  next transformation goal for the next object.

  The next section gives the other part that passes the left hand side, i.e., for a certain target
  object, search the source objects one by one to complete the transformation towards the target,
  using the remained unsolved target proportion of the previous search as the goal of
  the next search in the next source object.

  In the reasoning processes, we only consider logic connectives that have an interpretation of refinement.
  They include, \<open>\<or>, \<exists>, \<^emph>, \<and>\<close>. \<open>\<forall>\<close> is planned.
  \<open>\<not>\<close> and \<open>\<rightarrow>\<close> are depreciated, because we cannot interpret from them what is the exact refinement
  relation and the abstract object. \<open>@\<close> is only used in propositional constraints.

Priority Convention:

\<^item> 4000: Termination
\<^item> 3200: Very Safe Normalization
\<^item> 3150: Assigning Zeros
\<^item> 3000: Normalization
\<^item> 2800: Disjunction in source part
        Conjunction in target part
        Fix existentially quantified variables in source part
\<^item> 2600: Usual reasonings
\<^item> 2100: Padding void holes after the last item. Rules capturing the whole items including
        the last item in the \<open>\<^emph>\<close>-sequence should have priority higher than this.
\<^item> 2000: Step-by-step searching
\<^item> 1000 - 1999: Confident rules or shortcuts for specific \<phi>-types
\<^item> 800:  Disjunction in target part
\<^item> 50-54: Enters Structural Extraction. Elim-rules \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A'\<close> having a priority
         greater than 54, will be applied before Structural Extraction, and those less than 50,
        will only be applied in the backtrack of the Structural Extraction.
\<^item> 12: Instantiate existentially quantified variables in the target part
      Divergence for additive disjunction in the target part
\<close>


consts ToA_flag_deep :: bool


subsection \<open>Initialization\<close>

lemma [\<phi>reason 2100 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?P @action NToA' ?mode\<close>]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X @action NToA' mode\<close>
  unfolding Action_Tag_def using transformation_refl .

lemma [\<phi>reason 2100 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<s>\<u>\<b>\<j> True \<w>\<i>\<t>\<h> ?P @action NToA' ?mode\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action NToA' mode
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<s>\<u>\<b>\<j> True \<w>\<i>\<t>\<h> P @action NToA' mode\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 2020 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y @action NToA' _\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Any @action NToA' deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y @action NToA' deep\<close>
  unfolding Action_Tag_def
  by (simp add: transformation_weaken)

(*
lemma "_NToA_init_focus_":
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y' \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Simplify_def
  by simp

lemma "_NToA_init_by_focus_":
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Y' \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Simplify (assertion_simps undefined) R' R
\<Longrightarrow> Identity_Element\<^sub>I R' Q
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<and> Q\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def Simplify_def Identity_Element\<^sub>I_def
  by (simp; metis Transformation_def implies_right_prod mult_1_class.mult_1_left) *)

lemma "_NToA_init_":
  \<open> Simplify (assertion_simps SOURCE) X' X \<comment> \<open>TODO: move this into the bellow ML\<close>
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y' \<w>\<i>\<t>\<h> P
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Simplify_def Identity_Element\<^sub>I_def
  by simp

\<phi>reasoner_ML NToA_init 2000 (\<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?var_P @action NToA' _\<close>) = \<open>
fn (ctxt0,sequent0) => Seq.make (fn () =>
  let val sequent = @{thm' Action_Tag_I} RS sequent0
      val _ (*Trueprop*) $ ( _ (*Action_Tag*) $ (Const(\<^const_name>\<open>Transformation\<close>, _) $ _ $ Y $ _)
                                              $ (Const(\<^const_name>\<open>NToA'\<close>, _) $ deep))
         = Thm.major_prem_of sequent0

      val ctxt = PLPR_Env.push \<^const_name>\<open>ToA_flag_deep\<close> deep ctxt0

      fun mk_zero (v,ty) =
            ((v,ty), Thm.instantiate_cterm (TVars.make [((("'a",0),\<^sort>\<open>zero\<close>), Thm.ctyp_of ctxt ty)],
                                            Vars.empty)
                                           \<^schematic_cterm>\<open>0::?'a::zero\<close>)
      fun mk_one (v,ty) =
            ((v,ty), Thm.instantiate_cterm (TVars.make [((("'a",0),\<^sort>\<open>one\<close>), Thm.ctyp_of ctxt ty)],
                                            Vars.empty)
                                           \<^schematic_cterm>\<open>1::?'a::one\<close>)

      fun scan0 ret (Const (\<^const_name>\<open>plus\<close>, _) $ A $ B) = scan0 (scan0 ret A) B
        | scan0 ret (Const (@{const_name Subjection}, _) $ X) = scan0 ret X
        | scan0 ret (Const (@{const_name ExSet}, _) $ X) = scan0 ret X
        | scan0 ret (Abs (_,_,X)) = scan0 ret X
        | scan0 ret (Var v) = mk_zero v :: ret
        | scan0 ret _ = ret

      val zeros = scan0 [] Y
      val sequent1 = (case zeros of [] => sequent
                         | (_::zeros') => Thm.instantiate (TVars.empty, Vars.make zeros') sequent
                                       |> Simplifier.simplify (Phi_Programming_Simp_SS.equip ctxt))

      fun scan1 ret (Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _))
            = (true,[])
        | scan1 ret (Const (\<^const_name>\<open>times\<close>, _) $ A $ B) =
            scan1 (case B of Var v => mk_one v :: ret | _ => []) A
        | scan1 ret (Const (@{const_name Subjection}, _) $ X) = scan1 ret X
        | scan1 ret (Const (@{const_name ExSet}, _) $ X) = scan1 ret X
        | scan1 ret (Abs (_,_,X)) = scan1 ret X
        | scan1 ret (Var v) = (false, mk_one v :: ret)
        | scan1 _ _  = (false, [])

      val (X,Y,P) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent1)
      val (_, void_tails) = scan1 [] Y
      val sequent2 = (case void_tails of [] => sequent1 (*remove redundant void tails*)
                         | (_::voids') => Thm.instantiate (TVars.empty, Vars.make voids') sequent1)

   (* fun add_focus_tag' ctxt ctm =
        case Thm.term_of ctm
          of (Const (@{const_name Subjection}, _) $ _) => Conv.arg_conv (add_focus_tag' ctxt) ctm
           | (Const (@{const_name ExSet}, _) $ _) => Conv.arg_conv (add_focus_tag' ctxt) ctm
           | (Abs _) => Conv.abs_conv (add_focus_tag' o snd) ctxt ctm
           | (Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _)) =>
                Conv.all_conv ctm
           | (Const (\<^const_name>\<open>times\<close>, _) $ Var _ $ _) =>
                Conv.arg_conv (Conv.rewr_conv @{thm FOCUS_TAG_def[symmetric, folded atomize_eq]}) ctm
           | (Const (\<^const_name>\<open>times\<close>, _) $ _ $ _) =>
                Conv.fun_conv (Conv.arg_conv (add_focus_tag' ctxt)) ctm

      fun add_focus_tag ctxt =
        Phi_Conv.leading_antecedent_conv (Phi_Conv.hhf_concl_conv (fn ctxt =>
          Phi_Syntax.transformation_conv Conv.all_conv (add_focus_tag' ctxt) Conv.all_conv
        ) ctxt)

      val sequent3 = if null void_tails then sequent2
                     else Conv.fconv_rule (add_focus_tag ctxt) sequent2

      val is_unital = Sign.of_sort (Proof_Context.theory_of ctxt) (fastype_of Y, \<^sort>\<open>sep_magma_1\<close>)

      val rule = if already_has_focus
                 then @{thm "_NToA_init_focus_"}
                 else if null void_tails andalso is_unital
                 then @{thm "_NToA_init_by_focus_"}
                 else @{thm "_NToA_init_"}*)
   in SOME ((ctxt, @{thm "_NToA_init_"} RS sequent2), Seq.empty)
  end)
\<close>




subsection \<open>Special Process for Holes\<close>

lemma ToA_ex_intro:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U c \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet U \<w>\<i>\<t>\<h> P"
  for c :: 'b
  unfolding Transformation_def by (simp, metis)

lemma ToA_ex_intro':
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U c \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> ExSet U \<brangle> \<w>\<i>\<t>\<h> P"
  for c :: 'b
  unfolding Transformation_def by (simp, metis)

lemma NToA_finish': "X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 * \<blangle> X \<brangle>"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left FOCUS_TAG_def Action_Tag_def
  using transformation_refl by this+

ML \<open>
(* X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> P *)
fun NToA_to_wild_card ctxt thm =
  let val (vs, _, goal) = Phi_Help.leading_antecedent (Thm.prop_of thm)
      val N = length vs
      val (X,Y0,_) = Phi_Syntax.dest_transformation goal
      val Y = case Y0 of Const(\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ x) => x
                       | _ => Y0
      val \<^Type>\<open>set \<open>TY\<close>\<close> = Term.fastype_of Y
      val (Var V, args) = strip_comb Y
      val bnos = map (fn Bound i => i) args
      val N_bnos = length bnos
      val bads = subtract (op =) bnos (Term.loose_bnos X)
      val N_bads = length bads
      val insts' = List.tabulate (N, (fn i =>
            let val bi = find_index (fn k => k = i) bads
                val ci = find_index (fn k => k = i) bnos
             in if bi <> ~1
                then Bound (N_bads - 1 - bi)
                else if ci <> ~1
                then Bound (N_bads + N_bnos - 1 - ci)
                else Bound ~1
            end))
      val Y'1 = subst_bounds (insts', X)
      val Y'2 = fold (fn j => fn TM =>
                  let val (name,T) = List.nth (vs, N-1-j)
                   in \<^Const>\<open>ExSet \<open>T\<close> \<open>TY\<close>\<close> $ Abs (name, T, TM)
                  end) bads Y'1
      val Y'3 = fold (fn j => fn TM =>
                  let val (name,T) = List.nth (vs, N-1-j)
                   in Abs (name, T, TM)
                  end) bnos Y'2
      val thm' =
            if null bads then thm
            else Thm.instantiate (TVars.empty, Vars.make [(V, Thm.cterm_of ctxt Y'3)]) thm
      val tac = TRY (HEADGOAL (resolve0_tac @{thms Action_Tag_I}))
                THEN REPEAT_DETERM_N N_bads (HEADGOAL (resolve0_tac @{thms ToA_ex_intro ToA_ex_intro'}))
                THEN (HEADGOAL (resolve0_tac @{thms transformation_refl NToA_finish'}))
   in tac thm'
  end
\<close>

\<phi>reasoner_ML \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> P @action NToA\<close> 2015 (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _ @action NToA\<close>) = \<open>
  fn (ctxt,thm) => NToA_to_wild_card ctxt thm |> Seq.map (pair ctxt)
\<close>


subsection \<open>Termination\<close>

declare NToA_finish'[\<phi>reason 4000 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?X  \<brangle> \<w>\<i>\<t>\<h> _\<close>,
                     \<phi>reason 900  for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?X' \<brangle> \<w>\<i>\<t>\<h> _\<close>]

lemma [\<phi>reason 4000]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * \<blangle> 1 \<brangle>\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding FOCUS_TAG_def Action_Tag_def by simp

lemma [\<phi>reason 4000]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * \<blangle> any \<Ztypecolon> \<circle> \<brangle>\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding FOCUS_TAG_def Action_Tag_def by simp

\<phi>reasoner_ML \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> P @action NToA\<close> 4005 (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>
  fn (ctxt,thm) => NToA_to_wild_card ctxt thm |> Seq.map (pair ctxt)
\<close>


subsection \<open>Void Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 3200]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * 1 \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * (any \<Ztypecolon> \<circle>) \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right \<phi>None_itself_is_one .

lemma [\<phi>reason 3200]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X * 1 \<brangle> \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X * (any \<Ztypecolon> \<circle>) \<brangle> \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right \<phi>None_itself_is_one .

lemma [\<phi>reason 3200]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (any \<Ztypecolon> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P "
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right \<phi>None_itself_is_one .


subsection \<open>Subjection\<close>

lemma [\<phi>reason 3200]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow>
   (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> Pass_Embedded_Reasoning Q) \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Pass_Embedded_Reasoning_def by simp

lemma [\<phi>reason 3210]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> True \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Pass_Embedded_Reasoning_def by simp

lemma [\<phi>reason 3200]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P \<Longrightarrow>
   (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P \<Longrightarrow> Pass_Embedded_Reasoning Q) \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U \<s>\<u>\<b>\<j> Q \<brangle> \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Pass_Embedded_Reasoning_def by simp

lemma [\<phi>reason 3210]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U \<s>\<u>\<b>\<j> True \<brangle> \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Pass_Embedded_Reasoning_def by simp

lemma [\<phi>reason 3220]: (*THINK: add Q in P, is good or not?*)
  "(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P )
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason 3230]:
  "(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (R \<s>\<u>\<b>\<j> Q) * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason 3220]:
  \<open>(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> W * T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P )
\<Longrightarrow> W * (T \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason 3230]:
  "(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> W * T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> W * (T \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (R \<s>\<u>\<b>\<j> Q) * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast


subsection \<open>Existential\<close>

ML \<open>fun ToA_ex_intro_reasoning (ctxt,sequent) =
  let val (_, X'', _) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      fun parse (Const(\<^const_name>\<open>ExSet\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X) = (false, ty, X)
        | parse (Const(\<^const_name>\<open>times\<close>, _) $ _ $ (
                    Const(\<^const_name>\<open>FOCUS_TAG\<close>, _) $ (Const(\<^const_name>\<open>ExSet\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X)))
            = (true, ty, X)
        | parse X = parse (Envir.beta_eta_contract X)
      val (has_focus, ty, X) = parse X''
      fun ex_var_is_in_obj_only i (Abs(_,_,X)) = ex_var_is_in_obj_only (i+1) X
        | ex_var_is_in_obj_only i (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) = ex_var_is_in_obj_only i T
        | ex_var_is_in_obj_only i (Const(\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = ex_var_is_in_obj_only i X
        | ex_var_is_in_obj_only i (Bound j) = j <> i
        | ex_var_is_in_obj_only i (X $ Y) = ex_var_is_in_obj_only i X andalso ex_var_is_in_obj_only i Y
        | ex_var_is_in_obj_only i _ = true
      val rule0 = if has_focus
                  then if ex_var_is_in_obj_only ~1 X
                  then @{thm' ToA_ex_intro'[where c=\<open>id c\<close> for c]}
                  else @{thm' ToA_ex_intro'}
                  else if ex_var_is_in_obj_only ~1 X
                  then @{thm' ToA_ex_intro[where c=\<open>id c\<close> for c]}
                  else @{thm' ToA_ex_intro}
   in SOME ((ctxt, rule0 RS sequent), Seq.empty)
  end\<close>

\<phi>reasoner_ML ToA_ex_intro !10 (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet _ \<w>\<i>\<t>\<h> _\<close> | \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ExSet _ \<brangle> \<w>\<i>\<t>\<h> _\<close>)
  = \<open>fn stat => Seq.make (fn () => ToA_ex_intro_reasoning stat)\<close>

lemma [\<phi>reason 2800]:
  "(\<And>x.  T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason 2810]:
  "(\<And>x.  T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R x * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet R * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason 2800]:
  "(\<And>x.  W * T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> W * ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason 2810]:
  "(\<And>x.  W * T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R x * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> W * ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet R * \<blangle> U \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by simp fastforce



subsection \<open>Let Notation \& Prod Case\<close>

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U x \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Let x U \<w>\<i>\<t>\<h> P"
  unfolding Let_def .

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> U x \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> Let x U \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Let_def .

lemma [\<phi>reason 2610]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f (x,y) \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason 2610]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> f x y \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> case_prod f (x,y) \<brangle> \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<s>\<u>\<b>\<j> x y. xy = (x,y) \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f xy \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by (cases xy; simp)

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> f x y \<s>\<u>\<b>\<j> x y. xy = (x,y) \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> case_prod f xy \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by (cases xy; simp)



(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> VAL x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsection \<open>Zero\<close>

\<phi>reasoner_ML \<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close> 3100 (\<open>0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> | \<open>?var_A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>) =
\<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let fun collect L (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (_,_,X)) = collect L X
        | collect L (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = collect L X
        | collect L (Const (\<^const_name>\<open>times\<close>, _) $ A $ B) = collect (collect L A) B
        | collect L (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ X) = collect L X
        | collect L (Var (V, T)) = AList.update (op =) (V, Const (\<^const_name>\<open>zero_class.zero\<close>, T)) L
        | collect L (X $ _) = collect L X
        | collect L _ = L
      val (_,X,_) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      val sequent' = Drule.infer_instantiate ctxt
                        (collect [] X |> map (apsnd (Thm.cterm_of ctxt))) sequent
      val sequent'2 = (@{thm zero_implies_any} RS sequent')
                   |> Phi_Conv.rewrite_leading_antecedent ctxt @{thms zero_fun[folded atomize_eq]}
   in SOME ((ctxt, sequent'2), Seq.empty) end)
\<close>

lemma [\<phi>reason 3100]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X
\<Longrightarrow> R * 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X
\<Longrightarrow> 0 * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y + 0 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> 0 + Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X + 0 \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 + X \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X + 0 \<brangle> \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> 0 + X \<brangle> \<w>\<i>\<t>\<h> P\<close>
  by simp


subsection \<open>Divergence\<close>

subsubsection \<open>Conjunction\<close>

text \<open>Non-pure Additive Conjunction (excludes those are used in pure propositions), is rarely used under our
  refinement interpretation of BI assertions, because we can hardly imagine when and why an object
  has to be specified by two abstractions that cannot transform to each other (if they can,
  it is enough to use any one of them with a strong constraint over the abstraction, and transform it
  to the other when needed). We believe those abstractions if exist are specific enough to be preferably
  expressed by a specific \<phi>-type equipped with ad-hoc reasoning rules.

  To support additive conjunction, it brings enormous branches in the reasoning so affects the
  reasoning performance. Before applying the rules introduced previously, we can add the bellow
  rules which are also attempted subsequently in order and applied whenever possible.
  \<open>X \<longrightarrow> A \<Longrightarrow> X \<longrightarrow> B \<Longrightarrow> X \<longrightarrow> A \<and> B\<close> generates two subgoals.
  \<open>(A \<longrightarrow> Y) \<or> (B \<longrightarrow> Y) \<Longrightarrow> A \<and> B \<longrightarrow> Y\<close> branches the reasoning. Specially, when \<open>Y \<equiv> \<exists>x. P x\<close> is an
  existential quantification containing non-pure additive conjunction (e.g. \<open>P x \<equiv> C x \<and> D x\<close>),
  the priority of eliminating \<open>\<and>\<close> or instantiating \<open>\<exists>\<close> is significant.
  We attempt the both priorities by a search branch.
(*  If we instantiate first, the instantiation is forced to be identical in the two branches.
  If we eliminate \<open>\<and>\<close> first, the \<open>P\<close> can be too strong *)
  This rule is irreversible and we recall our hypothesis that \<phi>-types between the conjunction are
  considered disjoint, i.e., we only consider \<open>(x \<Ztypecolon> T) \<and> (y \<Ztypecolon> U) \<longrightarrow> Y\<close> when
  either \<open>x \<Ztypecolon> T \<longrightarrow> Y\<close> or \<open>y \<Ztypecolon> U \<longrightarrow> Y\<close>.
\<close>

lemma [\<phi>reason 2800]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P1
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P2
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<and>\<^sub>B\<^sub>I B \<w>\<i>\<t>\<h> P1 \<and> P2 \<close>
  unfolding Transformation_def
  by simp

lemma NToA_conj_src_A:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<and>\<^sub>B\<^sub>I B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def
  by simp blast

lemma NToA_conj_src_B:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<and>\<^sub>B\<^sub>I B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def
  by simp blast

\<phi>reasoner_ML NToA_conj_src !13  (\<open>_ \<and>\<^sub>B\<^sub>I _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let val tail = (case Thm.major_prem_of sequent
                    of _ (*Trueprop*) $ (_ (*Transformation*) $ _ $ (Const(\<^const_name>\<open>ExSet\<close>, _) $ X) $ _) =>
                            if Term.exists_Const (fn (\<^const_name>\<open>Additive_Conj\<close>, _) => true
                                                   | _ => false) X
                            then Seq.make (fn () => ToA_ex_intro_reasoning (ctxt,sequent))
                            else Seq.empty
                     | _ => Seq.empty)
   in SOME ((ctxt, @{thm' NToA_conj_src_A} RS sequent),
        Seq.make (fn () => SOME ((ctxt, @{thm' NToA_conj_src_B} RS sequent), tail)))
  end
  )\<close>


subsubsection \<open>Disjunction in Source\<close>

lemma [\<phi>reason 2800]:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A + B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (simp add: Transformation_def)

lemma [\<phi>reason 2800]:
  \<open> R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1
\<Longrightarrow> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P2
\<Longrightarrow> R * (A + B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (simp add: Transformation_def distrib_left) blast


lemma [\<phi>reason 2810]:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RB * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P1
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RA * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A + B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (RA + RB) * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (simp add: Transformation_def) meson

lemma [\<phi>reason 2810]:
  \<open> R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RB * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P1
\<Longrightarrow> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RA * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P2
\<Longrightarrow> R * (A + B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (RA + RB) * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (simp add: Transformation_def) blast


subsubsection \<open>Disjunction in Target\<close>

lemma NToA_disj_target_A:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<w>\<i>\<t>\<h> P\<close>
  unfolding plus_set_def
  by (metis implies_union(1) plus_set_def)

lemma NToA_disj_target_B:
  \<open>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<w>\<i>\<t>\<h> P\<close>
  by (simp add: Transformation_def)

declare [[\<phi>reason !12 NToA_disj_target_A NToA_disj_target_B for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A + ?B \<w>\<i>\<t>\<h> ?P\<close>]]

hide_fact NToA_disj_target_A NToA_disj_target_B

lemma NToA_disj_target_A':
  \<open>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> A \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> A + B \<brangle> \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Transformation_def
  by (simp add: distrib_left, blast)

lemma NToA_disj_target_B':
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> B \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> A + B \<brangle> \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Transformation_def
  by (simp add: distrib_left, blast)

declare [[\<phi>reason !12 NToA_disj_target_A' NToA_disj_target_B'
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?A + ?B \<brangle> \<w>\<i>\<t>\<h> _\<close>]]

hide_fact NToA_disj_target_A' NToA_disj_target_B'

subsubsection \<open>Conditional Branch\<close>

text \<open>The condition should be regarded as an output, and the reasoning process assigns which
the branch that it chooses to the output condition variable.\<close>

paragraph \<open>Normalization\<close>

lemma [\<phi>reason 2600]:
  \<open> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by (cases C; simp)

lemma [\<phi>reason 2600]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> If C A B \<w>\<i>\<t>\<h> P\<close>
  by (cases C; simp)


paragraph \<open>In Source\<close>

lemma NToA_cond_source_A[\<phi>reason 2601]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> (if True then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B[\<phi>reason 2601]:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> (if False then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)

declare [[\<phi>reason !12 NToA_cond_source_A NToA_cond_source_B
        for \<open>(if ?var_condition then ?A else ?B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P\<close>]]

hide_fact NToA_cond_source_A NToA_cond_source_B

lemma [\<phi>reason 2600 except \<open>(if ?var then _ else _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (if C then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P \<close>
  by (cases C; simp add: Premise_def)


lemma NToA_cond_source_A'[\<phi>reason 2601]:
  \<open> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (if True then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B'[\<phi>reason 2601]:
  \<open> R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (if False then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)

declare [[\<phi>reason !12 NToA_cond_source_A' NToA_cond_source_B'
        for \<open>?R * (if ?var_condition then ?A else ?B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P\<close>]]

hide_fact NToA_cond_source_A' NToA_cond_source_B'

lemma [\<phi>reason 2600 except \<open>_ * (if ?var then _ else _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P))
\<Longrightarrow> R * (if C then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P \<close>
  by (cases C; simp add: Premise_def)


paragraph \<open>in Target\<close>

lemma NToA_cond_target_A[\<phi>reason 2601]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if True then A else B) \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma NToA_cond_target_B[\<phi>reason 2601]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if False then A else B) \<w>\<i>\<t>\<h> P\<close>
  by simp

declare [[\<phi>reason !12 NToA_cond_target_A NToA_cond_target_B
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var_condition then ?A else ?B) \<w>\<i>\<t>\<h> ?P\<close> ]]

hide_fact NToA_cond_target_A NToA_cond_target_B

lemma [\<phi>reason 2600 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<w>\<i>\<t>\<h> P \<close>
  by (cases C; simp add: Premise_def)


lemma NToA_cond_target_A'[\<phi>reason 2601]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> A \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> if True then A else B \<brangle> \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma NToA_cond_target_B'[\<phi>reason 2601]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> B \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> if False then A else B \<brangle> \<w>\<i>\<t>\<h> P\<close>
  by simp

declare [[\<phi>reason !12 NToA_cond_target_B' NToA_cond_target_A'
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> if ?var_condition then ?A else ?B \<brangle> \<w>\<i>\<t>\<h> ?P\<close> ]]

hide_fact NToA_cond_target_A' NToA_cond_target_B'

lemma [\<phi>reason 2600 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<w>\<i>\<t>\<h> P \<close>
  by (cases C; simp add: Premise_def)



subsection \<open>Top\<close>

lemma [\<phi>reason 2600]:
  \<open>Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top>\<close>
  unfolding Transformation_def by blast

(*The following procedure only considers commutative semigroup*)
 
lemma [\<phi>reason 2605 if \<open>fn (ctxt,sequent) =>
          case Thm.major_prem_of sequent
            of _ (*Trueprop*) $ (_ (*transformation*) $ _ $ (_ (*times*) $ R $ _) $ _)
               => let fun chk (Const(\<^const_name>\<open>times\<close>, _) $ X $ Const(\<^const_name>\<open>top\<close>, _)) = chk X
                        | chk (Const(\<^const_name>\<open>top\<close>, _)) = false
                        | chk _ = true
                   in chk R
                  end\<close>]:
  \<open> Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top> * R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  for Any :: \<open>'a::sep_ab_semigroup BI\<close>
  by (simp add: mult.commute)

(*when we reach here, it means R all consists of \<top>, so that we can eliminate them one-by-one,
  until the last one which can be done by \<open>Any \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<top>\<close> directly.
  Again we assume and only consider commutative semigroup*)

lemma [\<phi>reason 2600]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  for A :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding Transformation_def
  by clarsimp blast

lemma [\<phi>reason 2595]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  for A :: \<open>'a::sep_algebra BI\<close>
  unfolding Transformation_def
  by clarsimp (metis mult_1_class.mult_1_right sep_magma_1_left)

lemma [\<phi>reason 0]:
  \<open> FAIL TEXT(\<open>Sorry, currently we do not support solving \<open>R * \<top>\<close> problems on non-monoidal-commutative group.\<close>)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<top> \<w>\<i>\<t>\<h> P\<close>
  unfolding Transformation_def
  by blast


subsection \<open>Step-by-Step Searching Procedure\<close>

(*
lemma [\<phi>reason 2100
 except \<open> ?H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> (?X1 * ?X2) \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA ?mode ?G\<close>
        \<open> ?H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> 1 \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA ?mode ?G\<close>
        \<open> ?H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> TAIL ?X \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA ?mode ?G\<close>
]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> 1 * X \<brangle> \<w>\<i>\<t>\<h> P @action reason_NToA mode G \<Longrightarrow>
    H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P @action reason_NToA mode G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left .


lemma [\<phi>reason 1050 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> ?Y \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA True ?G\<close>
   except \<open>(?X'::?'a::sep_magma_1 set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> ?Y' \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA True ?G\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P @action reason_NToA True G\<close>
  \<comment> \<open>If it doesn't have one, it cannot be reasoned by this procedure, so
      a fallback here handles it.\<close>
  unfolding FOCUS_TAG_def Action_Tag_def .*)

lemma [\<phi>reason 2030]:
  " Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 * \<blangle> R2 * \<blangle> X \<brangle> \<brangle> \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_left FOCUS_TAG_def .
(*
lemma [\<phi>reason 2020
   except \<open> ?Y1 * ?Y2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> ?P\<close>
          \<open> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> ?P\<close>
          \<open> TAIL ?H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> ?P\<close>
]:
  " 1 * Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left . *)

lemma [\<phi>reason 30 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  " R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R1 * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P1 \<Longrightarrow> R1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * X \<w>\<i>\<t>\<h> P1 \<and> P2"
  unfolding Action_Tag_def FOCUS_TAG_def Transformation_def split_paired_All Action_Tag_def Premise_def
  by clarsimp blast

lemma [\<phi>reason 2010]:
  " R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R1 * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (\<p>\<r>\<e>\<m>\<i>\<s>\<e> P1 \<Longrightarrow> R1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * \<blangle> R2 \<brangle> \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * \<blangle> R2 * X \<brangle> \<w>\<i>\<t>\<h> P1 \<and> P2"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Transformation_def split_paired_All Action_Tag_def Premise_def
  by clarsimp (metis sep_disj_multD2 sep_disj_multI2 sep_mult_assoc')
  

consts ToA_Annotation :: \<open>'a \<Rightarrow> 'a\<close>

(* lemma [\<phi>reason 25 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  " \<r>RECURSION_GUARD(ToA_Annotation X) (R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R1 * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P)
\<Longrightarrow> Identity_Element\<^sub>I R1
\<Longrightarrow> R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding FOCUS_TAG_def Transformation_def split_paired_All Identity_Element\<^sub>I_def \<r>Recursion_Guard_def
  by (metis mult_1_class.mult_1_left set_mult_expn) *)

(* lemma [\<phi>reason 1050 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> ?Y \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA True ?G\<close>
   except \<open>(?X'::?'a::sep_magma_1 set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> ?Y' \<brangle> \<w>\<i>\<t>\<h> ?P @action reason_NToA True ?G\<close>]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> \<blangle> Y \<brangle> \<w>\<i>\<t>\<h> P @action reason_NToA True G\<close>
  \<comment> \<open>If it isn't unital, it cannot be reasoned by this procedure, so
      a fallback here handles it.\<close>
  unfolding FOCUS_TAG_def Action_Tag_def . *)

subsection \<open>Confident Rules for Specific \<phi>-Types\<close>

subsubsection \<open>FOCUS_TAG\<close>

lemma [\<phi>reason 2000]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * \<blangle> \<blangle> X \<brangle> \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding FOCUS_TAG_def .

lemma [\<phi>reason 2000]:
  " R * Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * \<blangle> Y \<brangle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding FOCUS_TAG_def Transformation_def split_paired_All
  by simp


subsubsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-beta-eta-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1215 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<heavy_comma> \<blangle> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  "R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle>"
  unfolding FOCUS_TAG_def Transformation_def by blast

lemma [\<phi>reason 1210 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<heavy_comma> \<blangle> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<brangle> \<w>\<i>\<t>\<h> _\<close>
                    if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]:
  " y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def
  by (simp add: Val_expn times_list_def) metis

lemma [\<phi>reason 1200]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R'\<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding FOCUS_TAG_def split_paired_All
  by (metis implies_left_prod mult.assoc mult.commute)

lemma [\<phi>reason 1200 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?V \<brangle> \<w>\<i>\<t>\<h> _\<close>]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<heavy_comma> \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding FOCUS_TAG_def
  by (metis (no_types, opaque_lifting) implies_right_prod mult.assoc mult.commute)



subsection \<open>General Search\<close>

lemma [\<phi>reason default 12 except \<open> (_ :: ?'a :: sep_semigroup set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P"
  unfolding FOCUS_TAG_def Transformation_def
  by clarsimp blast


(*
lemma NToA_skip [\<phi>reason 65 for \<open> _ * _ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> ?X \<brangle> \<w>\<i>\<t>\<h> _\<close>
                            ]:
\<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' * H * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P"
  for H :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding FOCUS_TAG_def Transformation_def
  by clarsimp
     (smt (verit, best) sep_disj_commuteI sep_disj_multD1 sep_disj_multI1 sep_mult_assoc' sep_mult_commute)

lemma [\<phi>reason 60 for \<open> _ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> ?P\<close>
                  except \<open> _ * _ * _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ * \<blangle> _ \<brangle> \<w>\<i>\<t>\<h> ?P\<close>
                        ]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> H * R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> P"
  for H :: \<open>'a::sep_ab_semigroup BI\<close>
  unfolding FOCUS_TAG_def Transformation_def
  by (clarsimp, insert sep_disj_commute sep_mult_commute, blast)
*)  

(* lemma [\<phi>reason 1200
    on \<open>?R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<w>\<i>\<t>\<h> ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m @GOAL ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m @GOAL G
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<w>\<i>\<t>\<h> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V @GOAL G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>
*)

subsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  " R * T1 * T2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (T1 * T2) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * X1 * X2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * (X1 * X2) \<w>\<i>\<t>\<h> P"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding mult.assoc[symmetric] .


subsection \<open>Entry Point of Next Procedures\<close>

text \<open>The entry point of Structural Extraction is given in the section for SE.
      It covers all the form of \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T\<close> and \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T \<r>\<e>\<m>\<a>\<i>\<n>\<s> R\<close>\<close>

lemma [\<phi>reason 50]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P \<close>
  unfolding Identity_Element\<^sub>I_def .

lemma [\<phi>reason default 50]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<close>
  unfolding Identity_Element\<^sub>E_def .

(* subsection \<open>Structural Pairs\<close> (*depreciated*)

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def . *)


section \<open>Separation Extraction\<close>

text \<open>The canonical form is where all permission annotation are on leaves.
  It minimizes fragments. (TODO: move this)\<close>

consts \<A>SE :: \<open>action\<close>
       \<A>SEb :: \<open>action\<close> \<comment> \<open>Not for sep_magma_1 !\<close>

text \<open>\<^const>\<open>\<A>SEb\<close> is for boundary case: we reason the last element when the algebra doesn't
 have an identity element so that we cannot reduce it to the usual case by adding an identity element at the tail.
 The reasoning cannot assume the it always remains something and set that
 to the identity element if it actually doesn't remain anything.

The idea is to lift the non-unital algebra by adding an identity element. We use \<open>\<black_circle>\<close> for it.
Because substantially its reasoning has no identity element, we have to use
\<open>\<half_blkcirc>[Cw] W\<close> with a boolean flag \<open>Cw\<close> to rudimentarily check if the remainder is needed or not.
\<close>

subsubsection \<open>\<phi>Type Insertion into Unital Algebra\<close>

definition \<phi>None_freeobj :: \<open>('v::one, 'x) \<phi>\<close> ("\<circle>\<^sub>\<x>") where \<open>\<circle>\<^sub>\<x> = (\<lambda>x. 1)\<close>

lemma \<phi>None_freeobj_expn[\<phi>expns, simp]:
  \<open> p \<Turnstile> (x \<Ztypecolon> \<circle>\<^sub>\<x>) \<longleftrightarrow> p = 1\<close>
  unfolding \<phi>Type_def \<phi>None_freeobj_def
  by simp

lemma \<phi>Some_\<phi>None_freeobj:
  \<open> x \<Ztypecolon> \<black_circle> T \<^emph> \<circle>\<^sub>\<x> \<equiv> fst x \<Ztypecolon> \<black_circle> T\<close>
  unfolding atomize_eq BI_eq_iff
  by clarsimp

definition \<phi>Conditional_Opt_Ins :: \<open>bool \<Rightarrow> ('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<half_blkcirc>[_] _" [20,91] 90)
  where \<open>\<half_blkcirc>[C] T = (if C then \<black_circle> T else \<circle>\<^sub>\<x>)\<close>

lemma \<phi>Conditional_Opt_Ins_unfold:
  \<open> \<half_blkcirc>[C] T = (if C then \<black_circle> T else \<circle>\<^sub>\<x>) \<close>
  unfolding \<phi>Type_def \<phi>Conditional_Opt_Ins_def
  by clarsimp

lemma \<phi>Conditional_Opt_Ins_unfold_simp[simp]:
  \<open> \<half_blkcirc>[True] T \<equiv> \<black_circle> T \<close>
  \<open> \<half_blkcirc>[False] T \<equiv> \<circle>\<^sub>\<x> \<close>
  unfolding \<phi>Conditional_Opt_Ins_unfold
  by simp+

lemma \<phi>Conditional_Opt_Ins_expn[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> \<half_blkcirc>[C] T) \<longleftrightarrow> (if C then (\<exists>v. p = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T)) else p = None) \<close>
  unfolding \<phi>Conditional_Opt_Ins_unfold
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P x)
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[C] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> C \<longrightarrow> P x\<close>
  unfolding Action_Tag_def Inhabited_def
  by clarsimp blast



subsubsection \<open>Configuration\<close>

ML \<open>fun chk_SE_pattern ctxt tm =
  let fun chk_phityp (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ Var _ $ _) = true
        | chk_phityp (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ v $ _) =
              error ("In a rule of structural extraction, the abstract object of the source has to be a schematic variable\
                     \ but given\n" ^ Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt v)
      fun pattern (\<^Const>\<open>Trueprop\<close> $ X) = pattern X
        | pattern (\<^Const>\<open>Try\<close> $ _ $ X) = pattern X
        | pattern (\<^Const>\<open>Action_Tag\<close> $ X $ _) = pattern X
        | pattern (Const(\<^const_name>\<open>Transformation\<close>, _) $ A $ B $ _)
            = is_Var (Term.head_of B) orelse is_Var (Term.head_of A) orelse chk_phityp A
   in (pattern tm; NONE)
   handle Match => error ("Malform Structural Extraction rule: \n" ^
                          Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt tm)
  end\<close>

declare [[
  \<phi>reason_default_pattern_ML \<open> _ @action \<A>SE\<close>  \<Rightarrow> \<open>chk_SE_pattern\<close> (1000)
                         and \<open> _ @action \<A>SEb\<close> \<Rightarrow> \<open>chk_SE_pattern\<close> (1000),
  \<phi>reason_default_pattern
      \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close>   (105)
  and \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE \<close>   (100)
  and \<open> Try _ (_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE ) \<close> \<Rightarrow>
      \<open> Try _ (_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE ) \<close>   (105)
  and \<open> Try _ (_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE ) \<close> \<Rightarrow>
      \<open> Try _ (_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE ) \<close>   (100)

  and \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb \<close>   (105)
  and \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> _ @action \<A>SEb \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> _ @action \<A>SEb \<close>   (100)
  and \<open> Try _ (_ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb ) \<close> \<Rightarrow>
      \<open> Try _ (_ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb ) \<close>   (105)
  and \<open> Try _ (_ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> _ @action \<A>SEb ) \<close> \<Rightarrow>
      \<open> Try _ (_ \<Ztypecolon> \<black_circle> ?T \<^emph> \<half_blkcirc>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> \<half_blkcirc>[_] _ \<w>\<i>\<t>\<h> _ @action \<A>SEb ) \<close>   (100)

  and \<open> ?var_X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close> \<Rightarrow>
      \<open> ?var_X  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close>   (205)
  and \<open> ?var_X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE \<close> \<Rightarrow>
      \<open> ?var_X  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE \<close>   (200)
  and \<open> ?var_X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb \<close> \<Rightarrow>
      \<open> ?var_X  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb \<close>   (205)
  and \<open> ?var_X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SEb \<close> \<Rightarrow>
      \<open> ?var_X  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?U \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SEb \<close>   (200)

  and \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y' \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y  \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close>   (205)
  and \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y' \<w>\<i>\<t>\<h> _ @action \<A>SE \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y  \<w>\<i>\<t>\<h> _ @action \<A>SE \<close>   (200)
  and \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y' \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y  \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb \<close>   (205)
  and \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y' \<w>\<i>\<t>\<h> _ @action \<A>SEb \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y  \<w>\<i>\<t>\<h> _ @action \<A>SEb \<close>   (200)

  and \<open> ?XX @action \<A>SE \<close> \<Rightarrow>
      \<open> ERROR TEXT(\<open>Malformed Structural Extraction rule\<close> (?XX @action \<A>SE))\<close> (0)
  and \<open> ?XX @action \<A>SEb \<close> \<Rightarrow>
      \<open> ERROR TEXT(\<open>Malformed Structural Extraction rule\<close> (?XX @action \<A>SEb))\<close> (0)
]]

(*
declare [[\<phi>reason_default_pattern
      \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True\<close> \<Rightarrow> \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True\<close> (100)
  and \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE True\<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE True\<close>   (105)
  and \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True) \<close> \<Rightarrow> \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE True) \<close> (100)
  and \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE True) \<close> \<Rightarrow>
      \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE True) \<close>   (105)

  and \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> _ @action \<A>SE False\<close> \<Rightarrow> \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> _ @action \<A>SE False\<close> (100)
  and \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE False\<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE False\<close>   (105)
  and \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> _ @action \<A>SE False) \<close> \<Rightarrow> \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> _ @action \<A>SE False) \<close> (100)
  and \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE False) \<close> \<Rightarrow>
      \<open> Try _ (_ \<Ztypecolon> ?X \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?Y \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE False) \<close>   (105)

  and \<open> ?X @action \<A>SE True \<close> \<Rightarrow> \<open> ERROR TEXT(\<open>Bad Form: \<close> (?X @action \<A>SE True)) \<close> (1)
  and \<open> ?X @action \<A>SE False\<close> \<Rightarrow> \<open> ERROR TEXT(\<open>Bad Form: \<close> (?X @action \<A>SE True)) \<close> (1)
]]
*)

text \<open>Task of Structural Extract \<^prop>\<open>(x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y,r) \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P2 @action \<A>SE \<close>,
  given \<^term>\<open>x \<Ztypecolon> T\<close>, expecting \<^term>\<open>y \<Ztypecolon> U\<close>, the reasoner finds the further element \<^term>\<open>w \<Ztypecolon> W\<close>
  that needs to be extracted further and the remain \<^term>\<open>r \<Ztypecolon> R\<close> that remains from the extraction.
  \<^prop>\<open>x \<Ztypecolon> (Source \<^emph> Further_Task) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> (Target \<^emph> Remain) \<w>\<i>\<t>\<h> some_info\<close>.

  The original assertion was in a good form, but after the structural extraction, the form is destroyed.
  Many procedure application or ToA application just change the value (the abstract object) while
  the type structure is basically unchanged. If we can, after the application, recover the original
  form by some reverse transformation, it would be great.

  \<^term>\<open>Auto_Transform_Hint\<close> is for this.
  \<^prop>\<open> x \<Ztypecolon> (Source \<^emph> Further_Task) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> (Target \<^emph> Remain) \<w>\<i>\<t>\<h> (
        Auto_Transform_Hint (y' \<Ztypecolon> From_the_Target \<^emph> With_the_Remains)
                            (x' \<Ztypecolon> Recover_the_Source \<^emph> With_works_to_be_recovered_further) \<and> True
    ) @action \<A>SE \<close>
  The \<open>the_Target\<close> is a pattern having same constant and the rough structure with the \<open>Target\<close>.
  Many SE rules are equipped with a version with Auto_Transform_Hint. The rules maintains the patterns
  \<open>the_Target\<close> and \<open>the_Source\<close>, and later the system can pattern-match \<open>the_Target\<close> after
  the application to instantiate the original form \<open>the_Source\<close> and then recover it by a To-Transformation.

  The \<open>Auto_Transform_Hint\<close> only gives syntactic hint. The \<open>y'\<close> and \<open>x'\<close> are never used and can be any thing.
\<close>

paragraph \<open>Simplification Protect\<close>

(*definition \<open>\<A>SE_Simp_Protect x T W y U R P\<close> 

TODO!!!*)




subsection \<open>Termination\<close>
  
lemma [\<phi>reason 3010]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((), fst x) \<Ztypecolon> (\<circle> \<^emph> T) @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3011]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((), fst x) \<Ztypecolon> (\<circle> \<^emph> T) \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> \<circle> \<^emph> T) (x' \<Ztypecolon> T \<^emph> \<circle>) \<and> True) @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')


lemma [\<phi>reason 3000]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph> \<circle>) (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SE \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph> \<circle>) @action \<A>SE \<close>
  unfolding Action_Tag_def
  using transformation_refl .

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph> \<circle>) \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph> \<circle>) (x'' \<Ztypecolon> T' \<^emph> \<circle>) \<and> True) @action \<A>SE \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  using transformation_refl .


lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?T' \<w>\<i>\<t>\<h> _ @action \<A>SEb \<close>]:
  \<open> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SEb \<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEb \<close>]:
  \<open> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<and> True) @action \<A>SEb \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')



subsection \<open>Fall back\<close>

(*
Structural Extraction (SE) is free from backtrack because any \<phi>-type can have a (weakest)
rule that does nothing and just send the Y (the target) to the W (the further request).
Therefore, the fallback rules here are just those not configured with SE.
*)

lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> Try False (x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def Try_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

declare [[\<phi>trace_reasoning = 2]]

lemma [\<phi>reason default 2]:
  \<open> Try False (x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def Try_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')
 
lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 2]:
  \<open> x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

(*I don't think this rule is good

Okay, this rule is not good.
For a \<phi>-type T of sep-magma-1, if it can give a rule for ToA \<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> T\<close>, why not it
also provide the structural extraction?
Note it is sep-magma-1 after all meaning it has a notion of separation.

lemma [\<phi>reason default 3]: \<comment> \<open>Structural_Extract_fallback\<close>
  \<open> fst x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> T \<^emph> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, ()) \<Ztypecolon> U \<^emph> \<circle> \<w>\<i>\<t>\<h> P @action \<A>SE True\<close>
  for T :: \<open>('a::sep_magma_1,'b) \<phi>\<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')*)



subsection \<open>Stepwise of Separations\<close>
  
lemma Structural_Extract_\<phi>Prod_right:
  \<open> Try S1 ((fst a, fst (snd a)) \<Ztypecolon> A \<^emph> WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph> B \<w>\<i>\<t>\<h> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd b, snd (snd a)) \<Ztypecolon> B \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<^emph> C \<w>\<i>\<t>\<h> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> a \<Ztypecolon> A \<^emph> WY \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph> C \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SE \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
\<medium_left_bracket> premises Y and X
  apply_rule Y[THEN implies_left_prod, where R=\<open>snd (snd a) \<Ztypecolon> WX\<close>]
  apply_rule X[THEN implies_right_prod, where R=\<open>fst b \<Ztypecolon> Y\<close>]
\<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_right [(*THEN SE_clean_waste,*) \<phi>reason 1200]

lemma [(*THEN SE_clean_waste',*) \<phi>reason 1201]:
  \<open> Try S1 ((fst a, fst (snd a)) \<Ztypecolon> A \<^emph> WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph> B \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y' \<^emph> B') (x'1 \<Ztypecolon> A' \<^emph> WY') \<and> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd b, snd (snd a)) \<Ztypecolon> B \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<^emph> C \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> X' \<^emph> C') (x'2 \<Ztypecolon> B' \<^emph> WX') \<and> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> a \<Ztypecolon> A \<^emph> WY \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph> C \<w>\<i>\<t>\<h> 
      Auto_Transform_Hint (y'3 \<Ztypecolon> (Y' \<^emph> X') \<^emph> C') (x'3 \<Ztypecolon> A' \<^emph> WY' \<^emph> WX') \<and> P1 \<and> P2 @action \<A>SE \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and A' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_right .


lemma Structural_Extract_\<phi>Prod_left:
  \<open> Try S1 ((fst (fst x), fst w_ru) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<^emph> Rt \<w>\<i>\<t>\<h> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> U \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w_ru \<Ztypecolon> W \<^emph> Ru \<w>\<i>\<t>\<h> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y_rt, snd y_rt, snd w_ru) \<Ztypecolon> Y \<^emph> (Rt \<^emph> Ru) \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SE \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
  \<medium_left_bracket> premises T and U
    apply_rule U[THEN implies_right_prod, where R=\<open>fst (fst x) \<Ztypecolon> T\<close>]
    apply_rule T[THEN implies_left_prod, where R=\<open>snd w_ru \<Ztypecolon> Ru\<close>]
  \<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_left [(*THEN SE_clean_waste,*) \<phi>reason 1200]

lemma [(*THEN SE_clean_waste',*) \<phi>reason 1201]:
  \<open> Try S1 ((fst (fst x), fst w_ru) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<^emph> Rt \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y' \<^emph> Rt') (x'1 \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> U \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w_ru \<Ztypecolon> W \<^emph> Ru \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> W' \<^emph> Ru') (x'2 \<Ztypecolon> U' \<^emph> W2') \<and> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y_rt, snd y_rt, snd w_ru) \<Ztypecolon> Y \<^emph> (Rt \<^emph> Ru) \<w>\<i>\<t>\<h>
      Auto_Transform_Hint (y'3 \<Ztypecolon> Y' \<^emph> (Rt' \<^emph> Ru')) (x'3 \<Ztypecolon> (T' \<^emph> U') \<^emph> W2')
      \<and> P1 \<and> P2 @action \<A>SE \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and T' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_left .


paragraph \<open>Boundary\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma Structural_Extract_\<phi>Prod_right_b:
  \<open> Try S1 ((fst a, fst (snd a)) \<Ztypecolon> \<black_circle> A \<^emph> \<half_blkcirc>[Cy] WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cb] B \<w>\<i>\<t>\<h> P1 @action \<A>SEb )
\<Longrightarrow> Try S2 ((snd b, snd (snd a)) \<Ztypecolon> \<half_blkcirc>[Cb] B \<^emph> \<half_blkcirc>[Cx] WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> \<black_circle> X \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P2 @action \<A>SEb )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> a \<Ztypecolon> \<black_circle> A \<^emph> WY \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, c)) \<Ztypecolon> \<black_circle> (Y \<^emph> X) \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SEb \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
\<medium_left_bracket> premises Y and X
  apply_rule Y[THEN implies_left_prod, where R=\<open>snd (snd a) \<Ztypecolon> WX\<close>]
  apply_rule X[THEN implies_right_prod, where R=\<open>fst b \<Ztypecolon> Y\<close>]
\<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_right_b [(*THEN SE_clean_waste,*) \<phi>reason 1200]

lemma [(*THEN SE_clean_waste',*) \<phi>reason 1201]:
  \<open> Try S1 ((fst a, fst (snd a)) \<Ztypecolon> A \<^emph> WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph> B \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y' \<^emph> B') (x'1 \<Ztypecolon> A' \<^emph> WY') \<and> P1 @action \<A>SE True)
\<Longrightarrow> Try S2 ((snd b, snd (snd a)) \<Ztypecolon> B \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> X') (x'2 \<Ztypecolon> B' \<^emph> WX') \<and> P2 @action \<A>SE False)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> a \<Ztypecolon> A \<^emph> WY \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst b, c) \<Ztypecolon> (Y \<^emph> X) \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'3 \<Ztypecolon> Y' \<^emph> X') (x'3 \<Ztypecolon> A' \<^emph> WY' \<^emph> WX') \<and> P1 \<and> P2 @action \<A>SE False\<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and A' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_right_b .


lemma Structural_Extract_\<phi>Prod_left_b:
  \<open> Try S1 ((fst (fst x), w_ru) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<w>\<i>\<t>\<h> P1 @action \<A>SE False)
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> U \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w_ru \<Ztypecolon> W \<w>\<i>\<t>\<h> P2 @action \<A>SE False)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SE False\<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
  \<medium_left_bracket> premises T and U
    apply_rule U[THEN implies_right_prod, where R=\<open>fst (fst x) \<Ztypecolon> T\<close>]
    T
  \<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_left_b [(*THEN SE_clean_waste,*) \<phi>reason 1200]

lemma [(*THEN SE_clean_waste',*) \<phi>reason 1201]:
  \<open> Try S1 ((fst (fst x), w_ru) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y') (x'1 \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE False)
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> U \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w_ru \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> W') (x'2 \<Ztypecolon> U' \<^emph> W2') \<and> P2 @action \<A>SE False)
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y) (x'3 \<Ztypecolon> (T' \<^emph> U') \<^emph> W2') \<and> P1 \<and> P2 @action \<A>SE False \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and T' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_left_b .



subsection \<open>Entry Point\<close>

declare [[\<phi>trace_reasoning = 2]]

lemma enter_SE:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P1 @action \<A>SE True
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RR * \<blangle> w \<Ztypecolon> W \<brangle> \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RR * (snd y \<Ztypecolon> R) * \<blangle> fst y \<Ztypecolon> U \<brangle> \<w>\<i>\<t>\<h> P1 \<and> P2\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def FOCUS_TAG_def
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_prod, where R=\<open>x \<Ztypecolon> T\<close>]
    apply_rule T1[THEN implies_left_prod, where R=RR]
  \<medium_right_bracket> .

lemma [\<phi>reason 2000]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * \<blangle> X \<brangle> \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * \<blangle> X <changes-to> Y \<brangle> \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P\<close>
  \<comment> \<open>This is the entry point of Automatic_Rule !\<close>
  unfolding Changes_To_def .

lemma enter_SE_TH:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> U' \<^emph> R') (x'1 \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE True
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RR * \<blangle> w \<Ztypecolon> W \<brangle> \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> RR * (snd y \<Ztypecolon> R) * \<blangle> fst y \<Ztypecolon> U \<brangle> \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'3 \<Ztypecolon> U') (A' * (x'2 \<Ztypecolon> T'))  \<and> P1 \<and> P2\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SE .

ML \<open>
fun SE_entry_point (rules : thm * thm * thm * thm) sequent =
  let val (_, Y, P) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      fun obj_is_var (Const(\<^const_name>\<open>times\<close>, _) $ _ $ X) = obj_is_var X
        | obj_is_var (Const(\<^const_name>\<open>FOCUS_TAG\<close>, _) $ X) = obj_is_var X
        | obj_is_var (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _) = is_Var (Term.head_of x)
      val y_is_var = obj_is_var Y
      val has_auto_hint =
        case P of Const(\<^const_name>\<open>conj\<close>, _) $ (Const(\<^const_name>\<open>Auto_Transform_Hint\<close>, _) $ _ $ _) $ _ => true
                | _ => false
      val rule =
        if y_is_var
        then if has_auto_hint then #1 rules else #2 rules
        else if has_auto_hint then #3 rules else #4 rules
   in rule RS sequent
  end
\<close>

\<phi>reasoner_ML \<A>SE_Entry 50 (\<open>_ * (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (ctxt, sequent) =>
  Seq.make (fn () =>
    if Sign.of_sort (Proof_Context.theory_of ctxt)
                    (Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent), \<^sort>\<open>sep_semigroup\<close>)
    then SOME ((ctxt, SE_entry_point (@{thm' enter_SE_TH}, @{thm' enter_SE},
                                      @{thm' enter_SE_TH[THEN ToA_by_Equive_Class']},
                                      @{thm' enter_SE[THEN ToA_by_Equive_Class']}) sequent), Seq.empty)
    else (warning "The reasoner can barely do nothing for those even are not sep_semigroup" ;
          NONE))\<close>

lemma enter_SEc:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P1 @action \<A>SE True
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 \<and> P2 \<and> Q\<close>
  for A :: \<open>'a :: sep_magma_1 set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def
  \<medium_left_bracket> premises T and R and A
    apply_rule A[THEN implies_right_prod, where R=\<open>x \<Ztypecolon> T\<close>]
    T
    apply_rule R[THEN implies_right_prod, where R=\<open>fst y \<Ztypecolon> U\<close>]
  \<medium_right_bracket> .

lemma enter_SE_non_unital:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> R \<w>\<i>\<t>\<h> P1 @action \<A>SE True
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 \<and> P2 \<and> Q \<close>
  for A :: \<open>'a :: sep_magma set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def Premise_def

  unfolding Transformation_def
  by clarsimp fastforce
(*
  \<medium_left_bracket> premises T and R and A
    apply_rule A[THEN implies_right_prod, where R=\<open>x \<Ztypecolon> T\<close>]
    thm A[THEN implies_right_prod, where R=\<open>x \<Ztypecolon> T\<close>]
*)


lemma enter_SEb:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 @action \<A>SE False
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 \<and> P2\<close>
  unfolding Action_Tag_def \<phi>Prod_expn'
  by (smt (z3) implies_right_prod transformation_trans transformation_weaken)

lemma [\<phi>reason 2000]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X <changes-to> Y \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P\<close>
  \<comment> \<open>This is the entry point of Automatic_Rule !\<close>
  unfolding Changes_To_def .

lemma enter_SEb_TH:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> U') (x' \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE False
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (w' \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> U') (A' * (x'' \<Ztypecolon> T')) \<and> P1 \<and> P2\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEb .

\<phi>reasoner_ML \<A>SEb_Entry 50 (\<open>_ * (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (ctxt, sequent) =>
  Seq.make (fn () =>
    if Sign.of_sort (Proof_Context.theory_of ctxt)
                    (Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent), \<^sort>\<open>sep_magma\<close>)
    then SOME ((ctxt, SE_entry_point (@{thm' enter_SEb_TH}, @{thm' enter_SEb},
                                      @{thm' enter_SEb_TH[THEN ToA_by_Equive_Class]},
                                      @{thm' enter_SEb[THEN ToA_by_Equive_Class]}) sequent), Seq.empty)
    else (warning "The reasoner can barely do nothing for those even are not sep_magma" ;
          NONE))\<close>

hide_fact enter_SE enter_SE_TH enter_SEb enter_SEb_TH




section \<open>Programming Methods for Proving Specific Properties\<close>

subsection \<open>Functional\<close>

lemma Is_Functional_imp'':
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> Is_Functional S'
\<Longrightarrow> Is_Functional S\<close>
  unfolding Transformation_def Is_Functional_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (Trueprop (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> Embedded_Reasoning (Is_Functional S'))) M D R F
\<Longrightarrow> Friendly_Help TEXT(\<open>Hi! You are trying to show\<close> S \<open>is functional\<close>
      \<open>Now you entered the programming mode and you need to transform the specification to\<close>
      \<open>someone which is functional, so that we can verify your claim.\<close>)
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Is_Functional S)) M D R F\<close>
  unfolding \<phi>Programming_Method_def  ToA_Construction_def \<phi>SemType_def conjunction_imp
            Embedded_Reasoning_def
  by (rule Is_Functional_imp''[where S'=S']; simp)



end
