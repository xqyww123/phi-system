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
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values B B'
\<Longrightarrow> Remove_Values (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) (A' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B')\<close>
  unfolding REMAINS_def Remove_Values_def Transformation_def
  by (cases C; simp; blast)

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
  by (rule implies_right_frame)

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

  In the reasoning processes, we only consider logical connectives that have an interpretation of refinement.
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
\<^item> 1000 - 1999: Cut rules for specific \<phi>-types
\<^item> 900:  Step-by-step searching that splits elements in the target into each individual subgoals
        (the splitting of the source side is done by SE)
\<^item> 800:  Disjunction in target part
\<^item> 50-51: Enters Structural Extraction.
         Elim-rules \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A'\<close> having a priority greater than 52,
         will be applied before Structural Extraction, and those less than 50,
         will only be applied in the backtrack of the Structural Extraction.
         Enters \<open>Identity_Element\<^sub>I\<^sub>&\<^sub>E\<close>
\<^item> 45: Rules for non-semigroup algebras as there are no stepwise rules for them
\<^item> 12: Instantiate existentially quantified variables in the target part;
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
  by (simp; metis Transformation_def implies_right_frame mult_1_class.mult_1_left) *)

lemma "_NToA_init_":
  \<open> Simplify (assertion_simps SOURCE) X' X \<comment> \<open>TODO: move this into the ML below\<close>
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> X' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y' \<w>\<i>\<t>\<h> P
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def Simplify_def Identity_Element\<^sub>I_def
  by simp

\<phi>reasoner_ML NToA_init 2000 (\<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> ?var_P @action NToA' _\<close>) = \<open>
fn (_, (ctxt0,sequent0)) => Seq.make (fn () =>
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
                         | (_::zeros') =>
                                Thm.instantiate (TVars.empty, Vars.make zeros') sequent
                             |> Simplifier.simplify (Phi_Programming_Simp_SS.enhance (
                                                       Phi_Programming_Base_Simp_SS.equip ctxt)))

      fun scan1 ret (Const(\<^const_name>\<open>REMAINS\<close>, _) $ _ $ _ $ _) = (true,[])
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
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U c \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  for c :: 'b
  unfolding Transformation_def by (cases C; simp; metis)

(*lemma NToA_finish: \<comment>\<open>depreciated as all goes \<A>SEi\<close>
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Any] 1\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding REMAINS_def
  by simp*)

lemma NToA_finish':
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] \<top>\<close>
  unfolding REMAINS_def
  by simp

ML \<open>
(* (\<And>x. X x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> P) where ?Y is a variable.
   When X contains some quantified variables \<open>x\<close> that do not parameterize ?Y, the procedure
   existentially quantifies X, and assign \<open>\<exists>x. X x\<close> to ?Y.
 *)
fun NToA_to_wild_card ctxt thm0 =
  let val thm = perhaps (try (fn th => @{thm' Action_Tag_I} RS th)) thm0
      val (vs, _, goal) = Phi_Help.leading_antecedent (Thm.prop_of thm)
      val N = length vs
      val (X,Y0,_) = Phi_Syntax.dest_transformation goal
      val (refl, exintro, Y) =
            case Y0 of Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ C $ _ =>
                         if Term.is_Var (Term.head_of C)
                         then (@{thm' NToA_finish'}, @{thm' ToA_ex_intro'}, X)
                         else (@{thm' NToA_finish }, @{thm' ToA_ex_intro'}, X)
                     | _ => (@{thm' transformation_refl}, @{thm' ToA_ex_intro}, Y0)
      val (Var V, args) = strip_comb Y
      val bnos = map_filter (fn Bound i => SOME i | _ => NONE) args
      val bads = subtract (op =) bnos (Term.loose_bnos X)
   in if null bads
   then Phi_Reasoner.single_RS refl ctxt thm
   else let
      val N_bads = length bads
      val N_bnos = length bnos
      val (argTys, \<^Type>\<open>set \<open>TY\<close>\<close>) = Term.strip_type (snd V)
      val insts' = List.tabulate (N, fn i =>
            let val bi = find_index (fn k => k = i) bads
                val ci = find_index (fn k => k = i) bnos
             in if bi <> ~1
                then Bound (N_bads - 1 - bi)
                else if ci <> ~1
                then Bound (N_bads + N_bnos - 1 - ci)
                else Term.dummy (*not occur*)
            end)
      val Y'1 = subst_bounds (insts', X)
      val Y'2 = fold (fn j => fn TM =>
                  let val (name,T) = List.nth (vs, N-1-j)
                   in \<^Const>\<open>ExSet \<open>T\<close> \<open>TY\<close>\<close> $ Abs (name, T, TM)
                  end) bads Y'1
      val Y'3 = fold (fn (_, Bound j) => (fn TM =>
                            let val (name,T) = List.nth (vs, N-1-j)
                             in Abs (name, T, TM)
                            end)
                       | (ty, _) => (fn TM => Abs ("_", ty, TM))
                     ) (argTys ~~ args) Y'2
   in Thm.instantiate (TVars.empty, Vars.make [(V, Thm.cterm_of ctxt Y'3)]) thm
   |> funpow N_bads (fn th => exintro RS th)
   |> Phi_Reasoner.single_RS refl ctxt
   handle THM _ => Seq.empty
  end
  end
\<close>

\<phi>reasoner_ML \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<w>\<i>\<t>\<h> P @action NToA\<close> 2015 (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _ @action NToA\<close>) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (NToA_to_wild_card ctxt thm)
\<close>


subsection \<open>Termination\<close>

declare NToA_finish'[(*\<phi>reason 4001 for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X  \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>,*)
                     \<phi>reason 901  for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]
        (*NToA_finish [\<phi>reason 4000 for \<open>(?X::?'a::sep_magma_1 set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X  \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>,
                     \<phi>reason 900  for \<open>(?X::?'a::sep_magma_1 set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X' \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]*)

lemma [\<phi>reason 400]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

lemma [\<phi>reason 4000]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> any \<Ztypecolon> \<circle> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

lemma [\<phi>reason 4001]:
  \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> () \<Ztypecolon> \<circle> \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] X\<close>
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding REMAINS_def Action_Tag_def by simp

\<phi>reasoner_ML \<open>X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> P\<close> 4005 ( \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> |
                                                       \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?var_Y \<w>\<i>\<t>\<h> _\<close> ) = \<open>
  fn (_, (ctxt,thm)) => Seq.map (pair ctxt) (NToA_to_wild_card ctxt thm)
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
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  for X :: \<open>'a::sep_magma_1 BI\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * (any \<Ztypecolon> \<circle>) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
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
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> Q)
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Premise_def
  by simp

lemma [\<phi>reason 3210]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> True \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def by simp

lemma [\<phi>reason 3200]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> (P \<longrightarrow> Q)
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> Q \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def Premise_def
  by simp

lemma [\<phi>reason 3210]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<Longrightarrow>
    T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<s>\<u>\<b>\<j> True \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P "
  unfolding Transformation_def by simp

lemma [\<phi>reason 3220]: (*THINK: add Q in P, is good or not?*)
  "(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P )
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason 3230]:
  "(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason 3220]:
  \<open>(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> W * T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P )
\<Longrightarrow> W * (T \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P \<close>
  unfolding Transformation_def Premise_def by simp blast

lemma [\<phi>reason 3230]:
  "(\<p>\<r>\<e>\<m>\<i>\<s>\<e> Q \<Longrightarrow> W * T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P)
\<Longrightarrow> W * (T \<s>\<u>\<b>\<j> Q) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<s>\<u>\<b>\<j> Q \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def Premise_def by simp blast


subsection \<open>Existential\<close>

ML \<open>fun ToA_ex_intro_reasoning (ctxt,sequent) =
  let val (_, X'', _) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      fun parse (Const(\<^const_name>\<open>ExSet\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X) = (false, ty, X)
        | parse (Const(\<^const_name>\<open>REMAINS\<close>, _) $ (Const(\<^const_name>\<open>ExSet\<close>, \<^Type>\<open>fun \<^Type>\<open>fun ty _\<close> _\<close>) $ X) $ _ $ _)
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

\<phi>reasoner_ML ToA_ex_intro default ! 10 (\<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet _ \<w>\<i>\<t>\<h> _\<close> | \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ExSet _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>fn stat => Seq.make (fn () => ToA_ex_intro_reasoning (snd stat))\<close>

lemma [\<phi>reason 2800]:
  "(\<And>x.  T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason 2810]:
  "(\<And>x.  T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R x \<w>\<i>\<t>\<h> P)
\<Longrightarrow> ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] ExSet R \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def REMAINS_def by (cases C; simp; blast)

lemma [\<phi>reason 2800]:
  "(\<And>x.  W * T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> W * ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by simp fastforce

lemma [\<phi>reason 2810]:
  "(\<And>x.  W * T x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R x \<w>\<i>\<t>\<h> P)
\<Longrightarrow> W * ExSet T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] ExSet R \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by (cases C; simp; fastforce)



subsection \<open>Let Notation \& Prod Case\<close>

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U x \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Let x U \<w>\<i>\<t>\<h> P"
  unfolding Let_def .

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> U x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Let x U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  unfolding Let_def .

lemma [\<phi>reason 2610]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f (x,y) \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason 2610]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f (x,y) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<s>\<u>\<b>\<j> x y. xy = (x,y) \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f xy \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by (cases xy; simp)

lemma [\<phi>reason 2600]:
  " T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f x y \<s>\<u>\<b>\<j> x y. xy = (x,y) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_prod f xy \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def by (cases xy; cases C; simp)



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
\<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
  let fun collect' (Var (V, T)) L = AList.update (op =) (V, Const (\<^const_name>\<open>zero_class.zero\<close>, T)) L
        | collect' (X $ _) L = collect' X L
        | collect' _ L = L
      val collect = Phi_Syntax.fold_items_of_assertion collect'
      val (_,X,_) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      val sequent' = Drule.infer_instantiate ctxt
                        (collect X [] |> map (apsnd (Thm.cterm_of ctxt))) sequent
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
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X + 0 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 0 + X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
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
  reasoning performance. Before applying the rules introduced previously, we can add the following
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

(*diverges to 3 branches, left branch, right branch, and instantiating the Ex in the domain if any. *)
\<phi>reasoner_ML NToA_conj_src !13  (\<open>_ \<and>\<^sub>B\<^sub>I _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (_, (ctxt,sequent)) => Seq.make (fn () =>
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
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RB \<w>\<i>\<t>\<h> P1
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A + B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA + RB \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (cases C; simp add: Transformation_def; meson)

lemma [\<phi>reason 2810]:
  \<open> R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RB \<w>\<i>\<t>\<h> P1
\<Longrightarrow> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA \<w>\<i>\<t>\<h> P2
\<Longrightarrow> R * (A + B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] RA + RB \<w>\<i>\<t>\<h> P1 \<or> P2\<close>
  by (cases C; simp add: Transformation_def; blast)


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
  \<open>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow>  X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def
  by (cases C; simp add: distrib_left; blast)

lemma NToA_disj_target_B':
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A + B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def
  by (cases C; simp add: distrib_left; blast)

declare [[\<phi>reason !12 NToA_disj_target_A' NToA_disj_target_B'
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?A + ?B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]]

hide_fact NToA_disj_target_A' NToA_disj_target_B'

subsubsection \<open>Conditional Branch\<close>

paragraph \<open>Normalization\<close>

lemma [\<phi>reason 2600]:
  \<open> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P\<close>
  by (cases C; simp)

lemma [\<phi>reason 2600]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> If C (x \<Ztypecolon> A) (x \<Ztypecolon> B) \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> If C A B \<w>\<i>\<t>\<h> P\<close>
  by (cases C; simp)

paragraph \<open>Reduction for constant boolean condition\<close>

subparagraph \<open>Source\<close>

lemma NToA_cond_source_A[\<phi>reason 2610]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> (if True then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B[\<phi>reason 2610]:
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> (if False then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_A'[\<phi>reason 2610]:
  \<open> R * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (if True then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)

lemma NToA_cond_source_B'[\<phi>reason 2610]:
  \<open> R * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * (if False then A else B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P\<close>
  unfolding Action_Tag_def
  by (simp add: Transformation_def distrib_left)


subparagraph \<open>Target\<close>

lemma NToA_cond_target_A[\<phi>reason 2610]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if True then A else B) \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma NToA_cond_target_B[\<phi>reason 2610]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if False then A else B) \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma NToA_cond_target_A'[\<phi>reason 2610]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if True then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp

lemma NToA_cond_target_B'[\<phi>reason 2610]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if False then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P\<close>
  by simp


paragraph \<open>When the condition boolean is a variable\<close>

text \<open>The condition should be regarded as an output, and the reasoning process assigns which
the branch that it chooses to the output condition variable.\<close>

subparagraph \<open>Source\<close>

declare [[\<phi>reason !12 NToA_cond_source_A NToA_cond_source_B
        for \<open>(if ?var_condition then ?A else ?B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P\<close>]]

hide_fact NToA_cond_source_A NToA_cond_source_B

declare [[\<phi>reason !12 NToA_cond_source_A' NToA_cond_source_B'
        for \<open>?R * (if ?var_condition then ?A else ?B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?X \<w>\<i>\<t>\<h> ?P\<close>]]

hide_fact NToA_cond_source_A' NToA_cond_source_B'

subparagraph \<open>Target\<close>

declare [[\<phi>reason !12 NToA_cond_target_A NToA_cond_target_B
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var_condition then ?A else ?B) \<w>\<i>\<t>\<h> ?P\<close> ]]

hide_fact NToA_cond_target_A NToA_cond_target_B

declare [[\<phi>reason !12 NToA_cond_target_B' NToA_cond_target_A'
            for \<open>?X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var_condition then ?A else ?B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> ?P\<close> ]]

hide_fact NToA_cond_target_A' NToA_cond_target_B'



paragraph \<open>Case Split\<close>

subparagraph \<open>Source\<close>

lemma ToA_cond_branch_src_R:
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = (False, 0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = (False, 0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma ToA_cond_branch_src_R':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma ToA_cond_branch_src_WR:
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = (False, 0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = (False, 0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> W * If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma ToA_cond_branch_src_WR':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> W * If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

ML \<open>
fun reasoner_ToA_conditioned_subgoals_If ctxt'N (vars,Y,RHS) =
  let val (C, Ya, Yb) = Phi_Help.dest_triop_c \<^const_name>\<open>If\<close> RHS

      val Ya_s = map (fn ((N,i),ty) => Thm.var ((N,i+2), Thm.ctyp_of ctxt'N ty)) vars
      val Yb_s = map (fn ((N,i),ty) => Thm.var ((N,i+3), Thm.ctyp_of ctxt'N ty)) vars 
      val Y_s  = map2 (fn a => fn b =>
                   let val ty = Thm.typ_of_cterm a
                    in Thm.apply (Thm.apply (
                          Thm.apply (Thm.cterm_of ctxt'N \<^Const>\<open>If ty\<close>) C
                        ) (Thm.dest_fun a)
                        ) (Thm.dest_fun b)
                   end) Ya_s Yb_s
      val Ya' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Ya_s)) Y
      val Yb' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Yb_s)) Y
      fun mk_inst ctm Y =
        case Thm.term_of ctm
          of _ $ Free _ => mk_inst (Thm.dest_fun ctm) (Thm.lambda (Thm.dest_arg ctm) Y)
           | Var v => (v, Y)
           | _ => error "BUG: reasoner_ToA_conditioned_subgoals"
   in Vars.make (mk_inst Ya Ya' :: mk_inst Yb Yb' :: (vars ~~ Y_s))
  end
\<close>

lemma If_distrib_fx:
  \<open>(If C fa fb) (If C va vb) \<equiv> (If C (fa va) (fb vb))\<close>
  unfolding atomize_eq
  by (cases C; simp)
    
\<phi>reasoner_ML \<open>ML (If C A B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> 2000 (\<open>If _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_branch_src_R}, @{thm' ToA_cond_branch_src_R'},
          (\<^const_name>\<open>If\<close>, 3, @{thms' if_cancel[folded atomize_eq]}, @{thms' If_distrib_fx if_distrib}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>

\<phi>reasoner_ML \<open>ML (W * (If C A B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> 2000 (\<open>_ * If _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_branch_src_WR}, @{thm' ToA_cond_branch_src_WR'},
          (\<^const_name>\<open>If\<close>, 3, @{thms' if_cancel[folded atomize_eq]}, @{thms' If_distrib_fx if_distrib}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>


subparagraph \<open>Target\<close>

lemma [\<phi>reason 2600 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> P = False) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> Q = False) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma [\<phi>reason 2600 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = (False, 0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = (False, 0, False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)

lemma [\<phi>reason 2601 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if _ then _ else _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _ \<w>\<i>\<t>\<h> _\<close>
                    except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if ?var then _ else _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (if C then A else B) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Premise_def Orelse_shortcut_def)


subsubsection \<open>Type-embedding of Conditioned Remains\<close>



subsubsection \<open>Conditioned Remains\<close>

paragraph \<open>Reduction\<close>

subparagraph \<open>Source\<close>

lemma [\<phi>reason 2610]:
  " R * Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All
  by simp

lemma [\<phi>reason 2610 for \<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>
                        \<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close> ]:
  " Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All
  by simp

lemma [\<phi>reason 2610]:
  " A * (R * Y) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All
  by simp

lemma [\<phi>reason 2610]:
  " A * Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] R) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def split_paired_All
  by simp


subparagraph \<open>Target\<close>

lemma [\<phi>reason 2610]:
  " Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P"
  by simp

lemma [\<phi>reason 2610 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                        \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  " Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P
\<Longrightarrow> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[False] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> P"
  by simp


paragraph \<open>Case Split\<close>

subparagraph \<open>Source\<close>

lemma ToA_cond_remain_src_R:
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = (False,0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (B * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = (False,0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)

lemma ToA_cond_remain_src_R':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (B * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)

lemma ToA_cond_remain_src_WR:
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = (False,0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * (B * A) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = (False,0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)

lemma ToA_cond_remain_src_WR':
  \<open> Y \<equiv> If C Ya Yb
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * (B * A) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca] Ra \<w>\<i>\<t>\<h> P))
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,False)) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb] Rb \<w>\<i>\<t>\<h> Q))
\<Longrightarrow> W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C Ca Cb] If C Ra Rb \<w>\<i>\<t>\<h> If C P Q \<close>
  by (cases C; simp add: Orelse_shortcut_def Premise_def)


\<phi>reasoner_ML \<open>ML (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> 2000 (\<open>_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_remain_src_R}, @{thm' ToA_cond_remain_src_R'},
          (\<^const_name>\<open>If\<close>, 3, @{thms' if_cancel[folded atomize_eq]}, @{thms' If_distrib_fx if_distrib}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>

\<phi>reasoner_ML \<open>ML (W * (A \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] B) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> 2000 (\<open>_ * (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_cond_remain_src_WR}, @{thm' ToA_cond_remain_src_WR'},
          (\<^const_name>\<open>If\<close>, 3, @{thms' if_cancel[folded atomize_eq]}, @{thms' If_distrib_fx if_distrib}),
          reasoner_ToA_conditioned_subgoals_If, \<^context>) o snd\<close>

subparagraph \<open>Target\<close>

lemma [\<phi>reason 2600 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[CCa] RRa \<w>\<i>\<t>\<h> P)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[CCb] RRb \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[If C CCa CCb] If C RRa RRb \<w>\<i>\<t>\<h> If C P Q\<close>
  by (cases C; simp)

lemma [\<phi>reason 2601 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] _ \<w>\<i>\<t>\<h> _\<close>
                    except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[?var] _) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close> ]:
  \<open> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n>   C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R * Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RRa \<w>\<i>\<t>\<h> P)
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> C \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RRb \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] If C RRa RRb \<w>\<i>\<t>\<h> If C P Q\<close>
  by (cases C; simp)


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
  unfolding Transformation_def FAIL_def
  by blast


subsection \<open>Step-by-Step Searching Procedure\<close>

lemma [\<phi>reason no explorative backtrack ! 900]:
  " R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R1 \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<Longrightarrow> R1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * X \<w>\<i>\<t>\<h> P1 \<and> P2"
  unfolding Action_Tag_def REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def
  by clarsimp blast

lemma [\<phi>reason no explorative backtrack ! 900]:
  " R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R1 \<w>\<i>\<t>\<h> P1
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<Longrightarrow> R1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P2)
\<Longrightarrow> R  \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R2 * X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R' \<w>\<i>\<t>\<h> P1 \<and> P2"
  for R :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def REMAINS_def Transformation_def split_paired_All Action_Tag_def Premise_def
  by (cases C; clarsimp; metis sep_disj_multD2 sep_disj_multI2 sep_mult_assoc')

lemma [\<phi>reason default ! 45 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ :: ?'a :: sep_semigroup set) \<w>\<i>\<t>\<h> _\<close>]:
  \<comment> \<open>must be lower than the entry point of Separation Extraction\<close>
  \<open> B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X * Y \<w>\<i>\<t>\<h> P \<and> Q \<close>
  unfolding Transformation_def
  by clarsimp blast

lemma [\<phi>reason default ! 45 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (_ :: ?'a :: sep_semigroup set) \<w>\<i>\<t>\<h> _\<close>]:
  \<comment> \<open>must be lower than the entry point of Separation Extraction\<close>
  " (C,P) = (True, P1 \<and> P2) \<and> (B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P1) \<and> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> P1 \<longrightarrow> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> P2)) \<or>\<^sub>c\<^sub>u\<^sub>t
    C = False \<and> (A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)
\<Longrightarrow> A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P"
  unfolding Orelse_shortcut_def Transformation_def REMAINS_def Premise_def
  by clarsimp blast



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

subsection \<open>For Specific \<phi>-Types\<close>

subsubsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-beta-eta-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1215 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  "R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R"
  unfolding REMAINS_def Transformation_def by simp

lemma [\<phi>reason 1210 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>
                    if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]:
  " y \<Ztypecolon> U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v] U \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P"
  unfolding Transformation_def
  by (simp add: Val_expn times_list_def) metis

lemma [\<phi>reason 1200]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R'\<heavy_comma> X \<w>\<i>\<t>\<h> P"
  unfolding REMAINS_def split_paired_All
  by (simp; metis implies_left_frame mult.assoc mult.commute)

lemma [\<phi>reason 1200 except \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?V \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>]:
  " R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<w>\<i>\<t>\<h> P
\<Longrightarrow> R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R' \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<w>\<i>\<t>\<h> P"
  unfolding REMAINS_def
  by (metis (no_types, opaque_lifting) implies_right_frame mult.assoc mult.commute)



subsection \<open>General Search\<close>

lemma [\<phi>reason default 12 except \<open> (_ :: ?'a :: sep_semigroup set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  " H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> P
\<Longrightarrow> R * H \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] R \<w>\<i>\<t>\<h> P"
  unfolding REMAINS_def Transformation_def
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

lemma [\<phi>reason default ! 50]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P \<close>
  unfolding Identity_Element\<^sub>I_def .

lemma [\<phi>reason default ! 51 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<circle> \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> () \<Ztypecolon> \<circle> \<w>\<i>\<t>\<h> P \<close>
  unfolding Identity_Element\<^sub>I_def
  by simp

lemma [\<phi>reason default ! 50]:
  \<open> Identity_Element\<^sub>I X P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> \<circle> \<w>\<i>\<t>\<h> P \<close>
  unfolding Identity_Element\<^sub>I_def
  by simp

lemma [\<phi>reason default ! 50]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<close>
  unfolding Identity_Element\<^sub>E_def .

lemma [\<phi>reason default ! 51 for \<open>_ \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> () \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<close>
  unfolding Identity_Element\<^sub>E_def
  by simp

lemma [\<phi>reason default ! 50]:
  \<open> Identity_Element\<^sub>E X
\<Longrightarrow> x \<Ztypecolon> \<circle> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<close>
  unfolding Identity_Element\<^sub>E_def
  by simp

lemma [\<phi>reason 2000]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X <changes-to> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R2 \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P\<close>
  \<comment> \<open>This is the entry point of Auto_Transform_Hint !\<close>
  unfolding Changes_To_def .

lemma [\<phi>reason 2000]:
  \<open> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P
\<Longrightarrow> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> X <changes-to> Y \<w>\<i>\<t>\<h> Auto_Transform_Hint (y \<Ztypecolon> Y) Ret \<and> P\<close>
  \<comment> \<open>This is the entry point of Automatic_Rule !\<close>
  unfolding Changes_To_def .


(* subsection \<open>Structural Pairs\<close> (*depreciated*)

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def . *)

subsection \<open>Miscellaneous\<close>

subsubsection \<open>Case-split of Sum\<close>

paragraph \<open>Reduction\<close>

subparagraph \<open>Target\<close>

lemma [\<phi>reason 2020]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A x \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inl x) \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 2020]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inl x) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 2020]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B x \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inr x) \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 2020]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B (Inr x) \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

subparagraph \<open>Source\<close>

declare [[\<phi>trace_reasoning = 1]]

lemma [\<phi>reason 2020]:
  \<open> A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> case_sum A B (Inl x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 2020]:
  \<open> B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> case_sum A B (Inr x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 2020]:
  \<open> W * A x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> W * case_sum A B (Inl x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 2020]:
  \<open> W * B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> W * case_sum A B (Inr x) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp


paragraph \<open>Case Split\<close>

subparagraph \<open>Target\<close>

lemma [\<phi>reason 2000]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A a \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B b \<w>\<i>\<t>\<h> Q b)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp)

lemma [\<phi>reason 2011]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def)

lemma [\<phi>reason 2010]:
  \<open> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> A a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Ra a \<w>\<i>\<t>\<h> P a)
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> B b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] Rb b \<w>\<i>\<t>\<h> Q b)
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> case_sum A B x \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def)

subparagraph \<open>Source\<close>

lemma ToA_case_sum_src_R:
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = ((\<lambda>_. False),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = ((\<lambda>_. False),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

lemma ToA_case_sum_src_R':
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

lemma ToA_case_sum_src_WR:
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ca,Ra,P) = ((\<lambda>_. False),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Cb,Rb,Q) = ((\<lambda>_. False),0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> W * case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

lemma ToA_case_sum_src_WR':
  \<open> Y \<equiv> case_sum Ya Yb x
\<Longrightarrow> (\<And>a. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inl a \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Ra,P) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * A a \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Ya a \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Ca a] Ra a \<w>\<i>\<t>\<h> P a))
\<Longrightarrow> (\<And>b. \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> x = Inr b \<Longrightarrow> ((\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> False) \<and> (Rb,Q) = (0,(\<lambda>_. False))) \<or>\<^sub>c\<^sub>u\<^sub>t (W * B b \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Yb b \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Cb b] Rb b \<w>\<i>\<t>\<h> Q b))
\<Longrightarrow> W * case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<r>\<e>\<m>\<a>\<i>\<n>\<s>[case_sum Ca Cb x] case_sum Ra Rb x \<w>\<i>\<t>\<h> case_sum P Q x \<close>
  by (cases x; simp add: Simplify_def Premise_def Orelse_shortcut_def)

lemma case_sum_degenerate:
  \<open>(case_sum (\<lambda>_. a) (\<lambda>_. a) x) \<equiv> a\<close>
  unfolding atomize_eq
  by (cases x; simp) 

lemma sum_case_distrib_fx:
  \<open>(case_sum fa fb x) (case_sum va vb x) \<equiv> (case_sum (\<lambda>x. fa x (va x)) (\<lambda>x. fb x (vb x)) x)\<close>
  unfolding atomize_eq
  by (cases x; simp)

ML \<open>
(*instantiates variables vs to \<open>case_sum va vb x\<close> for each*)
fun reasoner_ToA_conditioned_subgoals_sum ctxt'N (vars,Y,RHS) =
  let val (Ya, Yb, x) = Phi_Help.dest_triop_c \<^const_name>\<open>case_sum\<close> RHS
      val \<^Type>\<open>sum ta tb\<close> = Thm.typ_of_cterm x
      val ([Na,Nb], ctxt'N) = Variable.variant_fixes ["xa","xb"] ctxt'N
      val xa = Thm.cterm_of ctxt'N (Free (Na, ta))
      val xb = Thm.cterm_of ctxt'N (Free (Nb, tb))

      val Ya_s = map (fn ((N,i),ty) => Thm.apply (Thm.var ((N,i+2), Thm.ctyp_of ctxt'N (ta --> ty))) xa) vars
      val Yb_s = map (fn ((N,i),ty) => Thm.apply (Thm.var ((N,i+3), Thm.ctyp_of ctxt'N (tb --> ty))) xb) vars 
      val Y_s  = map2 (fn a => fn b =>
                   let val ty = Thm.typ_of_cterm a
                    in Thm.apply (Thm.apply (Thm.apply (
                            Thm.cterm_of ctxt'N \<^Const>\<open>case_sum ta ty tb\<close>) (Thm.dest_fun a)
                        ) (Thm.dest_fun b)) x
                   end) Ya_s Yb_s
      val Ya' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Ya_s)) Y
             |> Thm.lambda xa
      val Yb' = Thm.instantiate_cterm (TVars.empty, Vars.make (vars ~~ Yb_s)) Y
             |> Thm.lambda xb
      fun mk_inst ctm Y =
        case Thm.term_of ctm
          of _ $ Free _ => mk_inst (Thm.dest_fun ctm) (Thm.lambda (Thm.dest_arg ctm) Y)
           | Var v => (v, Y)
           | _ => error "BUG: reasoner_ToA_conditioned_subgoals"
   in Vars.make (mk_inst Ya Ya' :: mk_inst Yb Yb' :: (vars ~~ Y_s))
  end
\<close>

\<phi>reasoner_ML \<open>ML (case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> 2000 (\<open>case_sum _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_case_sum_src_R}, @{thm' ToA_case_sum_src_R'},
          (\<^const_name>\<open>case_sum\<close>, 3, @{thms' case_sum_degenerate}, @{thms' sum_case_distrib_fx sum.case_distrib}),
          reasoner_ToA_conditioned_subgoals_sum, \<^context>) o snd\<close>

\<phi>reasoner_ML \<open>ML (W * case_sum A B x \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P)\<close> 2000 (\<open>_ * case_sum _ _ _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>)
  = \<open>Phi_Reasoners.reasoner_ToA_conditioned_subgoals
         (@{thm' ToA_case_sum_src_WR}, @{thm' ToA_case_sum_src_WR'},
          (\<^const_name>\<open>case_sum\<close>, 3, @{thms' case_sum_degenerate}, @{thms' sum_case_distrib_fx sum.case_distrib}),
          reasoner_ToA_conditioned_subgoals_sum, \<^context>) o snd\<close>



section \<open>Separation Extraction\<close>

text \<open>Extract a \<phi>-type assertion with potential remainders from a \<open>*\<close>-sequence of \<phi>-types.
  Extracting a \<phi>-type assertion (with potential remainders) from a \<phi>-type assertion, is not
  its job, but the usual transformation reasoning (the one having no tags) of the source \<phi>-type.
\<close>

text \<open>The canonical form is where all permission annotation are on leaves.
  It minimizes fragments. (TODO: move this)\<close>

text \<open>Log:
The assumption of identity element is bad. Consider a transformation functor whose container algebra
is unital but element algebra is not. The container goes to \<A>SE and leads us to apply \<A>SE on the
elements also, but that is wrong. We cannot assume the element algebra is also unital.
So then, instead of splitting the case of unitral elements or not, why not from the very beginning
we only assume non-unital algebra and use \<A>SEi only?
\<close>

consts (*\<A>SE  :: action  \<comment> \<open>Monoidal\<close>*)
       (*\<A>SEi :: action \<comment> \<open>Non-unital semigroup\<close>*)
       (*\<A>SEa :: action \<comment> \<open>Non-Associative\<close>*)
       \<A>SE_internal :: action \<comment> \<open>internal rules used in \<A>SE reasoning\<close>

text \<open>\<A>SEi is for algebras having no identity element.
  The reasoning cannot assume the it always remains something and set that
  to the identity element if it actually doesn't remain anything.
  It causes the reasoning essentially changed because we need to use a conditional boolean flag
  \<open>\<half_blkcirc>[Cw] W\<close> to case-analysis if the remainder is produced or not.

  \<open>\<A>SEa\<close> is for the algebras that are not even associative. The separation extraction is totally
  degenerated to one-to-one transformation of each separated cells.

  We use the two actions because they are essentially three different reasoning procedures.
  Their forms of goal are different.

\<comment> \<open>\<A>SE : \<^prop>\<open>x \<Ztypecolon> Source \<^emph> Further_Work \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> Target \<^emph> Remain \<w>\<i>\<t>\<h> some @action \<A>SE\<close>\<close>
\<^item> \<A>SEi: \<open>x \<Ztypecolon> \<black_circle> Source \<^emph> \<half_blkcirc>[Cw] Further \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> \<black_circle> Target \<^emph> \<half_blkcirc>[Cr] Remain \<w>\<i>\<t>\<h> some @action \<A>SEi\<close>
    \<open>\<black_circle>\<close> inserts it into a unital algebra.
(*\<A>SEa: \<^prop>\<open>x \<Ztypecolon> Source \<^emph> Further \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> f(x) \<Ztypecolon> Target \<w>\<i>\<t>\<h> some @action \<A>SEa\<close>
    It doesn't has the remain part because it cannot has because it is non-associative.
    It must has some unsolved further work because it is separation extraction, of form
      \<^prop>\<open>A * B \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>, not the simple transformation of form \<^prop>\<open>x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U\<close>.
      To consume \<open>A\<close>, the transformation of \<open>B\<close> to \<open>y \<Ztypecolon> U\<close> must remain some further work.*)

    Note non-associativity also implies non-commutativity, as in our formalization there is no
    algebra that is non-associative but commutative.
\<close>


subsubsection \<open>\<phi>Type Insertion into Unital Algebra\<close>

text \<open>\<^term>\<open>T \<^emph>[C] R\<close> is identical to \<open>\<black_circle> T \<^emph> \<half_blkcirc>[C] R\<close> to certain degree but however cannot replace it
as \<open>\<half_blkcirc>\<close> is convenient to specify elementwise existence, and makes the rule \<open>Structural_Extract_\<phi>Prod_right_i\<close>
easy. 

  \<open> Try S1 ((fst a, wy) \<Ztypecolon> \<black_circle> A \<^emph> \<half_blkcirc>[Cy] WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cb] B \<w>\<i>\<t>\<h> P1 @action \<A>SEi )
\<Longrightarrow> Try S2 ((snd b, wx) \<Ztypecolon> \<half_blkcirc>[Cb] B \<^emph> \<half_blkcirc>[Cx] WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> \<black_circle> X \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P2 @action \<A>SEi )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> (snd a \<Ztypecolon> \<half_blkcirc>[Cw] W) = ((wy, wx) \<Ztypecolon> \<half_blkcirc>[Cy] WY \<^emph> \<half_blkcirc>[Cx] WX) @action \<A>SE_internal
\<Longrightarrow> a \<Ztypecolon> \<black_circle> A \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> \<black_circle> (Y \<^emph> X) \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SEi \<close>

By \<open>\<half_blkcirc>\<close>, we can easily merge the two remainders of the transformation two-side. However, using \<open>T \<^emph>[C] U\<close>
is not as easy as this.
Nonetheless, \<open>T \<^emph>[C] R\<close> is suitable for the one-to-one transformation with remainders.
\<close>

definition \<phi>None_freeobj :: \<open>('v::one, 'x) \<phi>\<close> ("\<circle>\<^sub>\<x>") where \<open>\<circle>\<^sub>\<x> = (\<lambda>x. 1)\<close>

lemma \<phi>None_freeobj_expn[\<phi>expns, simp]:
  \<open> (x \<Ztypecolon> \<circle>\<^sub>\<x>) = 1\<close>
  unfolding \<phi>Type_def \<phi>None_freeobj_def
  by simp

lemma \<phi>Some_\<phi>None_freeobj:
  \<open> x \<Ztypecolon> \<black_circle> T \<^emph> \<circle>\<^sub>\<x> \<equiv> fst x \<Ztypecolon> \<black_circle> T\<close>
  \<open> y \<Ztypecolon> \<circle>\<^sub>\<x> \<^emph> \<black_circle> T \<equiv> snd y \<Ztypecolon> \<black_circle> T\<close>
  \<open> x \<Ztypecolon> \<circle>\<^sub>\<x> \<^emph> (\<circle>\<^sub>\<x> :: ('v::sep_magma_1, 'x) \<phi>) \<equiv> 1\<close>
  unfolding atomize_eq BI_eq_iff
  by ((rule \<phi>Type_eqI)?; clarsimp)+

definition \<phi>Cond_Unital_Ins :: \<open>bool \<Rightarrow> ('v, 'x) \<phi> \<Rightarrow> ('v option, 'x) \<phi>\<close> ("\<half_blkcirc>[_] _" [20,91] 90)
  \<comment> \<open>Conditional Unital Insertion\<close>
  where \<open>\<half_blkcirc>[C] T = (if C then \<black_circle> T else \<circle>\<^sub>\<x>)\<close>

lemma \<phi>Cond_Unital_Ins_unfold:
  \<open> \<half_blkcirc>[C] T = (if C then \<black_circle> T else \<circle>\<^sub>\<x>) \<close>
  unfolding \<phi>Type_def \<phi>Cond_Unital_Ins_def
  by clarsimp

lemma \<phi>Cond_Unital_Ins_unfold_simp[simp]:
  \<open> \<half_blkcirc>[True] T \<equiv> \<black_circle> T \<close>
  \<open> \<half_blkcirc>[False] T \<equiv> \<circle>\<^sub>\<x> \<close>
  unfolding \<phi>Cond_Unital_Ins_unfold
  by simp+

lemma \<phi>Cond_Unital_Ins_expn[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> \<half_blkcirc>[C] T) \<longleftrightarrow> (if C then (\<exists>v. p = Some v \<and> v \<Turnstile> (x \<Ztypecolon> T)) else p = None) \<close>
  unfolding \<phi>Cond_Unital_Ins_unfold
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> (\<And>x. x \<Ztypecolon> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> P x)
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[C] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> C \<longrightarrow> P x\<close>
  unfolding Action_Tag_def Inhabited_def
  by clarsimp blast

lemma [\<phi>reason 1000]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> C = False
\<Longrightarrow> Identity_Element\<^sub>I (any \<Ztypecolon> \<half_blkcirc>[C] T) True \<close>
  unfolding Identity_Element\<^sub>I_def Transformation_def Premise_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> C = False
\<Longrightarrow> Identity_Element\<^sub>E (x \<Ztypecolon> \<half_blkcirc>[C] T) \<close>
  unfolding Identity_Element\<^sub>E_def Transformation_def Premise_def
  by clarsimp

lemma [\<phi>reason 1000]:
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> Cx = Cy
\<Longrightarrow> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cy \<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P)
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[Cx] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[Cy] U \<w>\<i>\<t>\<h> Cy \<longrightarrow> P\<close>
  unfolding Premise_def Transformation_def
  by clarsimp


(*subsubsection \<open>Bi-conditioned Separation\<close>

definition biCond_\<phi>Prod :: \<open> ('v,'x) \<phi> \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('v,'y) \<phi> \<Rightarrow> ('v::sep_magma,'x \<times> 'y) \<phi> \<close> ("_ [_]\<^emph>[_] _" [71,40,40,70] 70)
    \<comment> \<open>\<phi>Type embedding of conditional remainder\<close>
  where \<open>(T [Ca]\<^emph>[Cb] U) \<equiv> if Ca then T \<^emph>[Cb] U else if Cb then (\<lambda>x. snd x \<Ztypecolon> U) else \<top>\<close>

lemma biCond_\<phi>Prod_expn:
  \<open> (x \<Ztypecolon> T [C']\<^emph>[C] U) = (if C' then (x \<Ztypecolon> T \<^emph>[C] U) else if C then (snd x \<Ztypecolon> U) else \<top>) \<close>
  unfolding biCond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

lemma biCond_\<phi>Prod_expn'[simp, \<phi>expns]:
  \<open> p \<Turnstile> (x \<Ztypecolon> T [Ca]\<^emph>[C] U) = (if Ca then p \<Turnstile> (x \<Ztypecolon> T \<^emph>[C] U) else if C then p \<Turnstile> (snd x \<Ztypecolon> U) else True) \<close>
  unfolding biCond_\<phi>Prod_def \<phi>Type_def
  by clarsimp

lemma biCond_\<phi>Prod_expn_const[simp]:
  \<open> T [True]\<^emph>[C] U \<equiv> T \<^emph>[C] U \<close>
  \<open> x \<Ztypecolon> T [False]\<^emph>[True] U \<equiv> snd x \<Ztypecolon> U \<close>
  \<open> x \<Ztypecolon> T [False]\<^emph>[False] U \<equiv> \<top> \<close>
  unfolding biCond_\<phi>Prod_def \<phi>Type_def
  by clarsimp+*)

lemma Cond_\<phi>Prod_expn_\<phi>Some:
  \<open>\<black_circle> (T \<^emph>[C] U) \<equiv> \<black_circle> T \<^emph> \<half_blkcirc>[C] U\<close>
  unfolding atomize_eq
  by (rule \<phi>Type_eqI; cases C; clarsimp; force)

lemma cond_prod_transformation_rewr:
  \<open> x \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U' \<w>\<i>\<t>\<h> P \<equiv> x \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> \<black_circle> U' \<w>\<i>\<t>\<h> P\<close>
  \<open> x' \<Ztypecolon> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[C] R \<w>\<i>\<t>\<h> P \<equiv> x' \<Ztypecolon> \<black_circle> T' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[C] R \<w>\<i>\<t>\<h> P\<close>
  unfolding atomize_eq
  by (cases C; clarsimp simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj \<phi>Some_transformation_strip)+

(*
lemma biCond_\<phi>Prod_expn_\<phi>Some:
  \<open>\<black_circle> (T [Ca]\<^emph>[C] U) \<equiv> \<half_blkcirc>[Ca] T \<^emph> \<half_blkcirc>[C] U\<close>
  unfolding atomize_eq
  apply (rule \<phi>Type_eqI; cases C; cases Ca; clarsimp)
  apply force
*)

subsubsection \<open>Auxiliary Rules\<close>

declare [[\<phi>reason_default_pattern
      \<open>(_ \<Ztypecolon> \<half_blkcirc>[_] _) = ((_,_) \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) @action \<A>SE_internal\<close> \<Rightarrow>
      \<open>(_ \<Ztypecolon> \<half_blkcirc>[_] _) = (_ \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) @action \<A>SE_internal\<close>   (100)
  and \<open>(_ \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) = (_ \<Ztypecolon> \<half_blkcirc>[_] _) @action \<A>SE_internal\<close> \<Rightarrow>
      \<open>(_ \<Ztypecolon> \<half_blkcirc>[?Ca] _ \<^emph> \<half_blkcirc>[?Cb] _) = (_ \<Ztypecolon> \<half_blkcirc>[_] _) @action \<A>SE_internal\<close>   (100)
  and \<open>_ = (if ?flag then _ else _) @action \<A>SE_internal \<close> \<Rightarrow>
      \<open>_ = (if ?flag then _ else _) @action \<A>SE_internal \<close>   (100)
(*  and \<open>?flag \<longrightarrow> _ @action \<A>SE_internal\<close> \<Rightarrow>
      \<open>?flag \<longrightarrow> _ @action \<A>SE_internal\<close>   (100)*)
  and \<open>?X @action \<A>SE_internal\<close> \<Rightarrow>
      \<open>ERROR TEXT(\<open>Malformed \<A>SE_internal rule\<close> (?X @action \<A>SE_internal))\<close> (0)
]]

text \<open>Information is always given from left to right below.
      They accept argument from LHS and assign the result to RHS\<close>

lemma [\<phi>reason 1000]: \<comment> \<open>contracts two sides respectively\<close>
  \<open>(x \<Ztypecolon> \<half_blkcirc>[True] (A \<^emph> B)) = ((fst x, snd x) \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[True] B) @action \<A>SE_internal\<close>
  \<open>(a \<Ztypecolon> \<half_blkcirc>[True] A) = ((a, undefined) \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[False] B) @action \<A>SE_internal\<close>
  \<open>(b \<Ztypecolon> \<half_blkcirc>[True] B) = ((undefined, b) \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[True] B) @action \<A>SE_internal\<close>
  \<open>(c \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) = ((undefined, undefined) \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[False] B) @action \<A>SE_internal\<close>
  unfolding Action_Tag_def BI_eq_iff
  by (clarsimp; force)+

lemma [\<phi>reason 1000]:
  \<open> (x \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[True] B) = (x \<Ztypecolon> \<half_blkcirc>[True] (A \<^emph> B)) @action \<A>SE_internal \<close>
  \<open> (x \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[False] B) = (fst x \<Ztypecolon> \<half_blkcirc>[True] A) @action \<A>SE_internal \<close>
  \<open> (x \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[True] B) = (snd x \<Ztypecolon> \<half_blkcirc>[True] B) @action \<A>SE_internal \<close>
  \<open> (x \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[False] B) = (undefined \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SE_internal \<close>
  unfolding Action_Tag_def BI_eq_iff
  by (clarsimp; force)+

lemma [\<phi>reason 1010]:
  \<open> ((x,y) \<Ztypecolon> \<half_blkcirc>[True] A \<^emph> \<half_blkcirc>[False] B) = (x \<Ztypecolon> \<half_blkcirc>[True] A) @action \<A>SE_internal \<close>
  \<open> ((x,y) \<Ztypecolon> \<half_blkcirc>[False] A \<^emph> \<half_blkcirc>[True] B) = (y \<Ztypecolon> \<half_blkcirc>[True] B) @action \<A>SE_internal \<close>
  unfolding Action_Tag_def BI_eq_iff
  by (clarsimp; force)+

lemma [\<phi>reason 1000]:
  \<open> A = (if True then A else B) @action \<A>SE_internal \<close>
  unfolding Action_Tag_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> B = (if False then A else B) @action \<A>SE_internal \<close>
  unfolding Action_Tag_def
  by simp


subsubsection \<open>Configuration\<close>
(*
ML \<open>fun chk_SE_pattern ctxt tm =
  let fun chk_phityp (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ Var _ $ _) = true
        | chk_phityp (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ v $ _) =
              error ("In a rule of structural extraction, the abstract object of the source has to be a schematic variable\
                     \ but given\n" ^ Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt v)
      fun pattern (\<^Const>\<open>Trueprop\<close> $ X) = pattern X
        | pattern (\<^Const>\<open>Attempt_Fallback\<close> $ _ $ X) = pattern X
        | pattern (\<^Const>\<open>Action_Tag\<close> $ X $ _) = pattern X
        | pattern (Const(\<^const_name>\<open>Transformation\<close>, _) $ A $ B $ _)
            = is_Var (Term.head_of B) orelse is_Var (Term.head_of A) orelse chk_phityp A
   in (pattern tm; NONE)
   handle Match => error ("Malform Structural Extraction rule: \n" ^
                          Context.cases Syntax.string_of_term_global Syntax.string_of_term ctxt tm)
  end\<close>
*)

(* TODO!
declare [[ (*TODO!*)
  (*\<phi>reason_default_pattern_ML \<open> _ @action \<A>SEi\<close> \<Rightarrow> \<open>chk_SE_pattern\<close> (1000),*)
  \<phi>reason_default_pattern
      \<open> _ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) \<close> \<Rightarrow>
      \<open> _ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) \<close>   (105)
  and \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) ) \<close> \<Rightarrow>
      \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) ) \<close>   (105)
  and \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _ ) \<close> \<Rightarrow>
      \<open> Attempt_Fallback (_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?U \<^emph>[_] _ \<w>\<i>\<t>\<h> _ ) \<close>   (100)

(*
  and \<open> ?XX @action \<A>SEi \<close> \<Rightarrow>
      \<open> ERROR TEXT(\<open>Malformed Separation Extraction rule\<close> (?XX @action \<A>SEi))\<close> (0)*)
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

paragraph \<open>\<open>T \<longrightarrow> \<circle>\<close>\<close>

(* preserved for documenting
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
*)

paragraph \<open>\<open>\<circle> \<longrightarrow> T\<close>\<close>

(* preserved for documenting
subparagraph \<open>Monoidal\<close>

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

lemma [\<phi>reason 3010]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> @action \<A>SE) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3011]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, ()) \<Ztypecolon> T \<^emph> \<circle> \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph> \<circle>) (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SE) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')
*)

(*
subparagraph \<open>Non-unital semigroup\<close>

lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (U \<^emph>[False] \<top>\<^sub>\<phi>) @action \<A>SEi \<close>
  unfolding Action_Tag_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (U \<^emph>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> U' \<^emph>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> T' [False]\<^emph>[True] U') \<and> True) @action \<A>SEi \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3010 for \<open> Attempt_Fallback (_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (U \<^emph>[False] \<top>\<^sub>\<phi>) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3011 for \<open> Attempt_Fallback (_ \<Ztypecolon> (_ [False]\<^emph>[_] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph>[_] _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (T [False]\<^emph>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> ( U \<^emph>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
                     (Auto_Transform_Hint (y' \<Ztypecolon> U' \<^emph>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> T' [False]\<^emph>[True] U') \<and> True) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)
*)


(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> _ @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SEi \<close>
  unfolding Action_Tag_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U') \<and> True) @action \<A>SEi \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3010 for \<open> Attempt_Fallback (_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> _ @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)

lemma [\<phi>reason 3011 for \<open> Attempt_Fallback (_ \<Ztypecolon> (\<half_blkcirc>[False] _ \<^emph> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (\<black_circle> _ \<^emph> _) \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi) \<close>]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, undefined) \<Ztypecolon> (\<black_circle> U \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
                     (Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> \<half_blkcirc>[False] \<top>\<^sub>\<phi> \<^emph> \<half_blkcirc>[True] U') \<and> True) @action \<A>SEi) \<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def Attempt_Fallback_def
  by (simp add: \<phi>Some_\<phi>None_freeobj)
*)

(*subparagraph \<open>Non-associative\<close>

lemma [\<phi>reason 3000]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T @action \<A>SEa \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001]:
  \<open> x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T') (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SEa \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3010]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T @action \<A>SEa) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close>
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3011]:
  \<open> Attempt_Fallback (x \<Ztypecolon> (\<circle> \<^emph> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> snd x \<Ztypecolon> T \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T') (x' \<Ztypecolon> (\<circle> \<^emph> T')) \<and> True) @action \<A>SEa) \<close>
  for T :: \<open>('c::sep_magma_1, 'a) \<phi>\<close> and T' :: \<open>('c'::sep_magma_1, 'a') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: \<phi>Prod_expn')
*)

paragraph \<open>\<open>T \<longrightarrow> T\<close>\<close>

(* preserved for documenting
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SE \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph> \<circle>) @action \<A>SE \<close>
  unfolding Action_Tag_def
  using transformation_refl .

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SE \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (T \<^emph> \<circle>) \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph> \<circle>) (x'' \<Ztypecolon> T' \<^emph> \<circle>) \<and> True) @action \<A>SE \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding Action_Tag_def
  using transformation_refl .
*)

lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph>[_] _ \<w>\<i>\<t>\<h> _ \<close>]:
  \<open> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<^emph>[_] _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) \<close>]:
  \<open> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> T' \<^emph>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> T' \<^emph>[False] \<top>\<^sub>\<phi>) \<and> True) \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?T' \<^emph> _ \<w>\<i>\<t>\<h> _ @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) @action \<A>SEi \<close>
  unfolding Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> \<black_circle> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<black_circle> ?T' \<^emph> _ \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEi \<close>]:
  \<open> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> (\<black_circle> T \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<w>\<i>\<t>\<h>
          (Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) (x' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[False] \<top>\<^sub>\<phi>) \<and> True) @action \<A>SEi \<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Action_Tag_def
  by (cases x; simp add: \<phi>Prod_expn')
*)

(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> _ @action \<A>SEa \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst x \<Ztypecolon> T @action \<A>SEa \<close>
  for T :: \<open>'b \<Rightarrow> 'a :: sep_magma_1 set\<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp

lemma [\<phi>reason 3001 for \<open>_ \<Ztypecolon> ?T \<^emph> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> ?T' \<w>\<i>\<t>\<h> (Auto_Transform_Hint _ _ \<and> _) @action \<A>SEa \<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<circle>) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst x \<Ztypecolon> T \<w>\<i>\<t>\<h> (Auto_Transform_Hint (y' \<Ztypecolon> T') (x'' \<Ztypecolon> T' \<^emph> \<circle>) \<and> True) @action \<A>SEa \<close>
  for T :: \<open>'b \<Rightarrow> 'a :: sep_magma_1 set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Action_Tag_def Transformation_def
  by clarsimp
*)

subsection \<open>Normalization\<close>

subsubsection \<open>Non-Unital Algebra\<close>

(*convention: \<A>SEi reasoning can send upward the Cw/Cr*)

(*
lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[True] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[Cw] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cw
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[True] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 3000 for \<open>_ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[False] _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[Cw] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> Cw
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> \<half_blkcirc>[False] W) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 3000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[True] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[Cr] R) \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> Cr
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[True] R) \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp

lemma [\<phi>reason 3000 for \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> (_ \<^emph> \<half_blkcirc>[False] _) \<w>\<i>\<t>\<h> _ @action \<A>SEi\<close>]:
  \<open> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[Cr] R) \<w>\<i>\<t>\<h> P @action \<A>SEi
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> \<not> Cr
\<Longrightarrow> x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> (U \<^emph> \<half_blkcirc>[False] R) \<w>\<i>\<t>\<h> P @action \<A>SEi \<close>
  unfolding Premise_def by simp
*)

text \<open>TODO: depreciate??? I am not sure\<close>
(*
lemma [\<phi>reason 1000]:
  \<open> x \<Ztypecolon> \<black_circle> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[True] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> 1 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> x \<Ztypecolon> \<half_blkcirc>[False] T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (x \<Ztypecolon> \<half_blkcirc>[True] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> A * (x \<Ztypecolon> \<half_blkcirc>[False] T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> Y \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[True] U \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[False] U \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[True] U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> 1 \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P
\<Longrightarrow> X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<half_blkcirc>[False] U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<close>
  by simp
*)

subsection \<open>Fall back\<close>

(*
Structural Extraction (SE) is free from backtrack because any \<phi>-type can have a (weakest)
rule that does nothing and just send the Y (the target) to the W (the further request).
Therefore, the fallback rules here are just those not configured with SE.
*)

subsubsection \<open>Monoidal\<close>

(* preserved for documenting
lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 2 for \<open>Attempt_Fallback ((_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _ @action \<A>SE)\<close>]:
  \<open> Attempt_Fallback ((x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 3]:
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 4 for \<open>Attempt_Fallback ((_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> Auto_Transform_Hint _ _ \<and> _ @action \<A>SE)\<close>]:
  \<open> Attempt_Fallback ((x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (simp add: mult.commute \<phi>Prod_expn')
 
lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 2 for \<open>(_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _ @action \<A>SE\<close>]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> (x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 3]:
  \<open> x \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 4 for \<open>(_,_) \<Ztypecolon> _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> Auto_Transform_Hint _ _ \<and> _ @action \<A>SE\<close>]:
  \<open> (x,y) \<Ztypecolon> X \<^emph> Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y, x) \<Ztypecolon> Y \<^emph> X \<w>\<i>\<t>\<h> Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True @action \<A>SE \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (simp add: mult.commute \<phi>Prod_expn')
*)

subsubsection \<open>Non-unital Semigroup\<close>

lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> x \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph>[True] X \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

text \<open>The commutative requirement is not strong, as there is no fallback for non-commutative algebras at all!\<close>

lemma [\<phi>reason default 1]: \<comment> \<open>Structural_Extract_fail\<close>
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph>[True] X) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close>
  unfolding \<phi>None_itself_is_one Action_Tag_def Attempt_Fallback_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 2]:
  \<open> x \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph>[True] X \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

lemma [\<phi>reason default 2]:
  \<open> Attempt_Fallback (x \<Ztypecolon> X \<^emph>[True] Y \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (snd x, fst x) \<Ztypecolon> Y \<^emph>[True] X \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y' \<Ztypecolon> Y' \<^emph> X') (x' \<Ztypecolon> X' \<^emph> Y') \<and> True) \<close>
  for X :: \<open>('a::sep_ab_semigroup,'b) \<phi>\<close> and X' :: \<open>('a'::sep_ab_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22) Attempt_Fallback_def
  unfolding \<phi>None_itself_is_one Action_Tag_def
  by (cases x; simp add: mult.commute \<phi>Prod_expn')

subsubsection \<open>Non-associative\<close>

text \<open>Non-associative algebras have no fallback on this\<close>



subsection \<open>Trim Waste\<close>

definition \<open>\<A>SE_trim\<^sub>I y R y' R' Q \<equiv> \<forall>U. y \<Ztypecolon> U \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> Q\<close>
definition \<open>\<A>SE_trim\<^sub>E x W x' W' \<equiv> \<forall>T. x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph> W\<close>
definition \<open>\<A>SE_trim\<^sub>I_TH y R y' R' Q (R'\<^sub>H :: 'b2 \<Rightarrow> 'c2 set) (R\<^sub>H :: 'd2 \<Rightarrow> 'c2 set) \<equiv> \<forall>U. y \<Ztypecolon> U \<^emph> R \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> Q\<close>
definition \<open>\<A>SE_trim\<^sub>E_TH x W x' W' (W\<^sub>H :: 'b2 \<Rightarrow> 'c2 set) (W'\<^sub>H :: 'd2 \<Rightarrow> 'c2 set) \<equiv> \<forall>T. x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> x \<Ztypecolon> T \<^emph> W\<close>

declare [[ \<phi>reason_default_pattern
      \<open> \<A>SE_trim\<^sub>E _ ?W _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>E _ ?W _ _ \<close>   (100)
  and \<open> \<A>SE_trim\<^sub>I ?y ?R _ _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>I ?y ?R _ _ _ \<close>   (100)
  and \<open> \<A>SE_trim\<^sub>E_TH _ ?W _ _ _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>E_TH _ ?W _ _ _ _ \<close>   (110)
  and \<open> \<A>SE_trim\<^sub>I_TH ?y ?R _ _ _ _ _ \<close> \<Rightarrow> \<open> \<A>SE_trim\<^sub>I_TH ?y ?R _ _ _ _ _ \<close>   (110)
]]

(* preserved for documenting
lemma \<A>SE_clean_waste:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P @action \<A>SE
\<Longrightarrow> \<A>SE_trim\<^sub>I y R y' R' Q
\<Longrightarrow> \<A>SE_trim\<^sub>E x W x' W'
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> P \<and> Q @action \<A>SE\<close>
  unfolding Action_Tag_def Transformation_def \<A>SE_trim\<^sub>I_def \<A>SE_trim\<^sub>E_def
  by blast

lemma \<A>SE_clean_waste_TH:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> U\<^sub>H \<^emph> R\<^sub>H) (x'1 \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P @action \<A>SE
\<Longrightarrow> \<A>SE_trim\<^sub>I_TH y R y' R' Q R'\<^sub>H R\<^sub>H
\<Longrightarrow> \<A>SE_trim\<^sub>E_TH x W x' W' W'\<^sub>H W\<^sub>H
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph> R' \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'4 \<Ztypecolon> U\<^sub>H \<^emph> R'\<^sub>H) (x'4 \<Ztypecolon> T\<^sub>H \<^emph> W'\<^sub>H) \<and> P \<and> Q @action \<A>SE\<close>
  unfolding Action_Tag_def Auto_Transform_Hint_def HOL.simp_thms(22) Transformation_def
            \<A>SE_trim\<^sub>I_TH_def \<A>SE_trim\<^sub>E_TH_def
  by blast
*)

(*\<A>SEi doesn't need trim.  not now... when we also use \<A>SEi for monoidal algebra*)

(*
lemma \<A>SEa_clean_waste:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>SEa
\<Longrightarrow> \<A>SE_trim\<^sub>E x W x' W'
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P @action \<A>SEa\<close>
  unfolding Action_Tag_def Transformation_def \<A>SE_trim\<^sub>E_def
  by blast

lemma \<A>SEa_clean_waste_TH:
  \<open> x \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y\<^sub>H \<Ztypecolon> U\<^sub>H) (x\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W\<^sub>H) \<and> P @action \<A>SEa
\<Longrightarrow> \<A>SE_trim\<^sub>E_TH x W x' W' W'\<^sub>H W\<^sub>H
\<Longrightarrow> x' \<Ztypecolon> T \<^emph> W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y\<^sub>H \<Ztypecolon> U\<^sub>H) (x'\<^sub>H \<Ztypecolon> T\<^sub>H \<^emph> W'\<^sub>H) \<and> P @action \<A>SEa\<close>
  unfolding Action_Tag_def Transformation_def Auto_Transform_Hint_def HOL.simp_thms(22) \<A>SE_trim\<^sub>E_TH_def
  by blast
*)

lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>I y R y R True \<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I (x,y) \<circle> (x, ()) \<circle> True \<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I (x,(r,())) (R \<^emph> \<circle>) (x,r) R True\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I (x,((),r)) (\<circle> \<^emph> R) (x,r) R True\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>I_TH y R y R True R\<^sub>H R\<^sub>H \<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def Auto_Transform_Hint_def HOL.simp_thms(22)
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I_TH (x,y) \<circle> (x, ()) \<circle> True \<circle> \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I_TH (x,(r,())) (R \<^emph> \<circle>) (x,r) R True (\<circle> \<^emph> R\<^sub>H) R\<^sub>H\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>I_TH (x,(r,())) (R \<^emph> \<circle>) (x,r) R True (R\<^sub>H \<^emph> \<circle>) R\<^sub>H\<close>
  for R :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>I_TH_def
  by (simp add: \<phi>Prod_expn')


lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>E x W x W \<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E (x,()) \<circle> (x,()) \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E (fst xw,(snd xw,())) (W \<^emph> \<circle>) xw W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E (x,(w,())) (W \<^emph> \<circle>) (x,w) W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E (fst xw,((), snd xw)) (\<circle> \<^emph> W) xw W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E (x,((),w)) (\<circle> \<^emph> W) (x,w) W \<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_def
  by (simp add: \<phi>Prod_expn')


lemma [\<phi>reason default 1]:
  \<open> \<A>SE_trim\<^sub>E_TH x W x W W\<^sub>H W\<^sub>H \<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def Auto_Transform_Hint_def HOL.simp_thms(22)
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E_TH (x,()) \<circle> (x,()) \<circle> \<circle> \<circle> \<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def Auto_Transform_Hint_def HOL.simp_thms(22)
  by simp

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E_TH (fst xw,((), snd xw)) (\<circle> \<^emph> W) xw W W\<^sub>H (\<circle> \<^emph> W\<^sub>H)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E_TH (x,((),w)) (\<circle> \<^emph> W) (x,w) W W\<^sub>H (\<circle> \<^emph> W\<^sub>H)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1000]:
  \<open> \<A>SE_trim\<^sub>E_TH (fst xw,(snd xw,())) (W \<^emph> \<circle>) xw W W\<^sub>H (W\<^sub>H \<^emph> \<circle>)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (cases xw; simp add: \<phi>Prod_expn')

lemma [\<phi>reason 1010]:
  \<open> \<A>SE_trim\<^sub>E_TH (x,(w,())) (W \<^emph> \<circle>) (x,w) W W\<^sub>H (W\<^sub>H \<^emph> \<circle>)\<close>
  for W :: \<open>'b \<Rightarrow> 'c::sep_magma_1 set\<close>
  unfolding \<A>SE_trim\<^sub>E_TH_def
  by (simp add: \<phi>Prod_expn')



subsection \<open>Stepwise of Product Separations\<close>

(* preserved for documenting
paragraph \<open>Monoidal\<close>

declare [[\<phi>trace_reasoning = 2]]

lemma Structural_Extract_\<phi>Prod_right:
  \<open> Try S1 ((fst a, fst (snd a)) \<Ztypecolon> A \<^emph> WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph> B \<w>\<i>\<t>\<h> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd b, snd (snd a)) \<Ztypecolon> B \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<^emph> C \<w>\<i>\<t>\<h> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> a \<Ztypecolon> A \<^emph> WY \<^emph> WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph> C \<w>\<i>\<t>\<h> (P1 \<and> P2) @action \<A>SE \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
\<medium_left_bracket> premises Y and X
  apply_rule Y[THEN implies_left_frame, where R=\<open>snd (snd a) \<Ztypecolon> WX\<close>]
  apply_rule X[THEN implies_right_frame, where R=\<open>fst b \<Ztypecolon> Y\<close>]
\<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_right [THEN \<A>SE_clean_waste, \<phi>reason 1200]

lemma [THEN \<A>SE_clean_waste_TH, \<phi>reason 1201]:
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
    apply_rule U[THEN implies_right_frame, where R=\<open>fst (fst x) \<Ztypecolon> T\<close>]
    apply_rule T[THEN implies_left_frame, where R=\<open>snd w_ru \<Ztypecolon> Ru\<close>]
  \<medium_right_bracket> .

declare Structural_Extract_\<phi>Prod_left [THEN \<A>SE_clean_waste, \<phi>reason 1200]

lemma [THEN \<A>SE_clean_waste_TH, \<phi>reason 1201]:
  \<open> Try S1 ((fst (fst x), fst w_ru) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y_rt \<Ztypecolon> Y \<^emph> Rt \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'1 \<Ztypecolon> Y' \<^emph> Rt') (x'1 \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE )
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> U \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w_ru \<Ztypecolon> W \<^emph> Ru \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> W' \<^emph> Ru') (x'2 \<Ztypecolon> U' \<^emph> W2') \<and> P2 @action \<A>SE )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph> W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst y_rt, snd y_rt, snd w_ru) \<Ztypecolon> Y \<^emph> (Rt \<^emph> Ru) \<w>\<i>\<t>\<h>
      Auto_Transform_Hint (y'3 \<Ztypecolon> Y' \<^emph> (Rt' \<^emph> Ru')) (x'3 \<Ztypecolon> (T' \<^emph> U') \<^emph> W2')
      \<and> P1 \<and> P2 @action \<A>SE \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and T' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_left .
*)

paragraph \<open>Non-Unital\<close>

lemma Structural_Extract_\<phi>Prod_right_i[\<phi>reason 1200]:
  \<open> Try S1 ((fst a, wy) \<Ztypecolon> A \<^emph>[Cy] WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<^emph>[Cb] B \<w>\<i>\<t>\<h> P1)
\<Longrightarrow> Try S2 (if Cb then ((snd b, wx) \<Ztypecolon> B \<^emph>[Cx] WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> X \<^emph>[Cr] R \<w>\<i>\<t>\<h> P2)
                  else (Cx, Cr, WX, wx, P2) = (True, False, X, fst c, True) )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> (snd a \<Ztypecolon> \<half_blkcirc>[Cw] W) = ((wy, wx) \<Ztypecolon> \<half_blkcirc>[Cy] WY \<^emph> \<half_blkcirc>[Cx] WX) @action \<A>SE_internal
\<Longrightarrow> a \<Ztypecolon> A \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> (Y \<^emph> X) \<^emph>[Cr] R \<w>\<i>\<t>\<h> (P1 \<and> P2) \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
  apply (cases Cb; simp add: cond_prod_transformation_rewr;
         clarsimp simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises Y and X and _ and _
    apply_rule Y[THEN implies_left_frame, where R=\<open>wx \<Ztypecolon> \<half_blkcirc>[Cx] WX\<close>]
    apply_rule X[THEN implies_right_frame, where R=\<open>fst b \<Ztypecolon> \<black_circle> Y\<close>]
  \<medium_right_bracket>
  \<medium_left_bracket> premises Y
    Y
  \<medium_right_bracket> .

(* TODO!
lemma [\<phi>reason 1201]:
  \<open> Try S1 ((fst a, wy) \<Ztypecolon> \<black_circle> A \<^emph> \<half_blkcirc>[Cy] WY \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cb] B \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> Y' \<^emph> \<half_blkcirc>[Cb] B') (x'1 \<Ztypecolon> \<black_circle> A' \<^emph> \<half_blkcirc>[Cy] WY') \<and> P1 @action \<A>SEi )
\<Longrightarrow> Try S2 ((snd b, wx) \<Ztypecolon> \<half_blkcirc>[Cb] B \<^emph> \<half_blkcirc>[Cx] WX \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> c \<Ztypecolon> \<black_circle> X \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'2 \<Ztypecolon> \<black_circle> X' \<^emph> \<half_blkcirc>[Cr] R') (x'2 \<Ztypecolon> \<half_blkcirc>[Cb] B' \<^emph> \<half_blkcirc>[Cx] WX') \<and> P2 @action \<A>SEi )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> (snd a \<Ztypecolon> \<half_blkcirc>[Cw] W) = ((wy, wx) \<Ztypecolon> \<half_blkcirc>[Cy] WY \<^emph> \<half_blkcirc>[Cx] WX) @action \<A>SE_internal
\<Longrightarrow> a \<Ztypecolon> \<black_circle> A \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((fst b, fst c), snd c) \<Ztypecolon> \<black_circle> (Y \<^emph> X) \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'3 \<Ztypecolon> \<black_circle> (Y' \<^emph> X') \<^emph> \<half_blkcirc>[Cr] R') (x'3 \<Ztypecolon> \<black_circle> A' \<^emph> \<half_blkcirc>[Cw] W') \<and> P1 \<and> P2 @action \<A>SEi \<close>
  for A :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and A' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_right_i .*)

lemma Structural_Extract_\<phi>Prod_left_i [\<phi>reason 1200]:
  \<open> Try S1 ((fst (fst x), fst wr) \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yr \<Ztypecolon> Y \<^emph>[Cra] Rt \<w>\<i>\<t>\<h> P1)
\<Longrightarrow> Try S2 (if Cw then ((snd (fst x), snd x) \<Ztypecolon> U \<^emph>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> wr \<Ztypecolon> W \<^emph>[Crb] Ru \<w>\<i>\<t>\<h> P2)
                  else (Cw2, Crb, Ru, wr, P2) = (False, True, U, (undefined, snd (fst x)), True))
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> ((snd yr, snd wr) \<Ztypecolon> \<half_blkcirc>[Cra] Rt \<^emph> \<half_blkcirc>[Crb] Ru) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>SE_internal
\<Longrightarrow> x \<Ztypecolon> (T \<^emph> U) \<^emph>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst yr, r) \<Ztypecolon> Y \<^emph>[Cr] R \<w>\<i>\<t>\<h> P1 \<and> P2 \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close>
  unfolding Action_Tag_def Try_def
  apply (cases Cw; simp add: cond_prod_transformation_rewr;
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some)
  \<medium_left_bracket> premises T and U and _ and S
    apply_rule U[THEN implies_right_frame, where R=\<open>fst (fst x) \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T[THEN implies_left_frame, where R=\<open>snd wr \<Ztypecolon> \<half_blkcirc>[Crb] Ru\<close>]
    fold mult.assoc
    unfold S
  \<medium_right_bracket>
  \<medium_left_bracket> premises Y and _ and _ and S
    Y
    apply_rule S[THEN eq_right_frame]
  \<medium_right_bracket> .

(* TODO
lemma [\<phi>reason 1201]:
  \<open> Try S1 ((fst (fst x), fst wr) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> yr \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cra] Rt \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> Y' \<^emph> \<half_blkcirc>[Cra] Rt') (x'1 \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[Cw] W') \<and> P1 @action \<A>SEi )
\<Longrightarrow> Try S2 ((snd (fst x), snd x) \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> wr \<Ztypecolon> \<half_blkcirc>[Cw] W \<^emph> \<half_blkcirc>[Crb] Ru \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'2 \<Ztypecolon> \<half_blkcirc>[Cw] W' \<^emph> \<half_blkcirc>[Crb] Ru') (x'2 \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[Cw2] W2') \<and> P2 @action \<A>SEi )
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> S1 \<or> S2
\<Longrightarrow> ((snd yr, snd wr) \<Ztypecolon> \<half_blkcirc>[Cra] Rt \<^emph> \<half_blkcirc>[Crb] Ru) = (r \<Ztypecolon> \<half_blkcirc>[Cr] R) @action \<A>SE_internal
\<Longrightarrow> x \<Ztypecolon> \<black_circle> (T \<^emph> U) \<^emph> \<half_blkcirc>[Cw2] W2 \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (fst yr, r) \<Ztypecolon> \<black_circle> Y \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> Y' \<^emph> \<half_blkcirc>[Cr] R') (x'3 \<Ztypecolon> \<black_circle> (T' \<^emph> U') \<^emph> \<half_blkcirc>[Cw2] W2') \<and> P1 \<and> P2 @action \<A>SEi \<close>
  for T :: \<open>('a::sep_semigroup,'b) \<phi>\<close> and T' :: \<open>('a'::sep_semigroup,'b') \<phi>\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using Structural_Extract_\<phi>Prod_left_i .
*)

paragraph \<open>Non-Associative\<close>

lemma Structural_Extract_\<phi>Prod_a[\<phi>reason 1190 except \<open>(_ :: ?'a::sep_semigroup set) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _\<close>]:
  \<open> fst a \<Ztypecolon> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> b \<Ztypecolon> Y \<w>\<i>\<t>\<h> P
\<Longrightarrow> a \<Ztypecolon> A \<^emph>[True] X \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> ((b, snd a), undefined) \<Ztypecolon> (Y \<^emph> X) \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def Transformation_def
  by clarsimp blast

(*TODO: TH*)


subsection \<open>Entry Point\<close>

(* preserved for documenting
lemma enter_SE:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P1 @action \<A>SE
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR \<w>\<i>\<t>\<h> P2 \<comment> \<open>Here, we force the reasoning entering a mode where
                                    it always yields a remainder. We can do so as \<A>SE reasoning
                                    assumes unital algebra.\<close>
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR * (snd y \<Ztypecolon> R) \<w>\<i>\<t>\<h> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def REMAINS_simp
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    apply_rule T1[THEN implies_left_frame, where R=RR]
  \<medium_right_bracket> .

lemma enter_SE_TH:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> U' \<^emph> R') (x'1 \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'2 \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[True] RR * (snd y \<Ztypecolon> R) \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'3 \<Ztypecolon> U') (A' * (x'3 \<Ztypecolon> T')) \<and> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SE .
*)

lemma enter_SEi:
  \<open> (x,w) \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P1
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h> P2) else (P2, Crr) = (True, False)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Action_Tag_def REMAINS_def Simplify_def
  apply (cases Cw; cases Cr; cases Crr;
         simp add: \<phi>Some_\<phi>Prod \<phi>Some_transformation_strip \<phi>Some_\<phi>None_freeobj \<phi>Prod_expn')
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    apply_rule T1[THEN implies_left_frame, where R=RR]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    apply_rule T1
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    apply_rule T1[THEN implies_left_frame, where R=RR]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    apply_rule T1
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1
    apply_rule T1[THEN implies_left_frame, where R=A]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1
    apply_rule T1[THEN implies_left_frame, where R=A]
  \<medium_right_bracket> .

lemma enter_SEi_TH:
  \<open> (x,w) \<Ztypecolon> T \<^emph>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'1 \<Ztypecolon> U' \<^emph>[Cr] R') (x'1 \<Ztypecolon> T' \<^emph>[Cw] W') \<and> P1
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h>
                    Auto_Transform_Hint (y'2 \<Ztypecolon> W') A' \<and> P2)
          else (P2, Crr) = (True, False)
\<Longrightarrow> if Cw then ATH = (A' * (x'3 \<Ztypecolon> T')) else ATH = (x'3 \<Ztypecolon> T')
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'3 \<Ztypecolon> U) ATH \<and> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup BI\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEi .

(* no need
lemma enter_SEi_\<phi>Some:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P1 @action \<A>SEi
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h> P2) else (P2, Crr) = (True, False)
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> \<black_circle> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> \<black_circle> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> \<black_circle> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup option BI\<close>
  unfolding Action_Tag_def REMAINS_def Simplify_def
  apply (cases Cw; cases Cr; cases Crr;
         simp add: \<phi>Some_\<phi>None_freeobj \<phi>Prod_expn')
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1[THEN implies_left_frame, where R=RR]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1[THEN implies_left_frame, where R=RR]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1 and T2
    apply_rule T2[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> \<black_circle> T\<close>]
    apply_rule T1
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1
    apply_rule T1[THEN implies_left_frame, where R=A]
  \<medium_right_bracket>
  \<medium_left_bracket> premises T1
    apply_rule T1[THEN implies_left_frame, where R=A]
  \<medium_right_bracket> .

lemma enter_SEi_\<phi>Some_TH:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[Cw] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'1 \<Ztypecolon> \<black_circle> U' \<^emph> \<half_blkcirc>[Cr] R') (x'1 \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[Cw] W') \<and> P1 @action \<A>SEi
\<Longrightarrow> if Cw then (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<r>\<e>\<m>\<a>\<i>\<n>\<s>[Crr] RR \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> \<black_circle> W') A' \<and> P2)
          else (P2, Crr) = (True, False)
\<Longrightarrow> if Cw then ATH = (A' * (x'3 \<Ztypecolon> \<black_circle> T')) else ATH = (x'3 \<Ztypecolon> \<black_circle> T')
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y>[assertion_simps undefined]
        (C, R3) : (Cr \<or> Crr \<or> \<not> Cw,
                   if Crr then if Cr then RR * (snd y \<Ztypecolon> \<black_circle> R) else RR
                   else if Cw then if Cr then (snd y \<Ztypecolon> \<black_circle> R) else \<top>
                   else if Cr then A * (snd y \<Ztypecolon> \<black_circle> R) else A)
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R3 \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'3 \<Ztypecolon> \<black_circle> U) ATH \<and> P2 \<and> P1\<close>
  for A :: \<open>'a::sep_semigroup option BI\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEi_\<phi>Some .
*)

lemma enter_SEa:
  \<open> C = True \<and>\<^sub>\<r> (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> P) \<and>\<^sub>\<r> (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> Q) \<or>\<^sub>c\<^sub>u\<^sub>t 
    (C, y) = (False, fst y') \<and>\<^sub>\<r>
    ((x, w) \<Ztypecolon> T \<^emph>[True] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h> P) \<and>\<^sub>\<r>
    (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Q)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h> P \<and> Q \<close>
  unfolding Action_Tag_def Orelse_shortcut_def Ant_Seq_def
  by (cases C; simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj \<phi>Some_transformation_strip;
      clarsimp simp add: Transformation_def; blast)

lemma enter_SEa_TH:
  \<open> (C, ATH) = (True, x'2 \<Ztypecolon> T') \<and>\<^sub>\<r>
    (x \<Ztypecolon> T \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> U') (x'2 \<Ztypecolon> T') \<and> P) \<and>\<^sub>\<r>
    (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> R \<w>\<i>\<t>\<h> Q)
    \<or>\<^sub>c\<^sub>u\<^sub>t
    (C, ATH, y) = (False, A' * (x'2) \<Ztypecolon> T', fst y') \<and>\<^sub>\<r>
    ((x, w) \<Ztypecolon> T \<^emph>[True] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y' \<Ztypecolon> U \<^emph>[False] \<top>\<^sub>\<phi> \<w>\<i>\<t>\<h>
          Auto_Transform_Hint (y'1 \<Ztypecolon> U' \<^emph>[False] \<top>\<^sub>\<phi>) (x'1 \<Ztypecolon> T' \<^emph>[True] W') \<and> P) \<and>\<^sub>\<r>
    (A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (y'2 \<Ztypecolon> W') A' \<and> Q)
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<r>\<e>\<m>\<a>\<i>\<n>\<s>[C] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y'2 \<Ztypecolon> U') ATH \<and> P \<and> Q \<close>
  unfolding Action_Tag_def Orelse_shortcut_def Ant_Seq_def Auto_Transform_Hint_def
  by (cases C; simp add: \<phi>Some_\<phi>Prod \<phi>Some_\<phi>None_freeobj \<phi>Some_transformation_strip;
      clarsimp simp add: Transformation_def; blast)

(* preserved for documenting
lemma enter_SEb:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h> P1 @action \<A>SE
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 \<and> P2 \<and> Q\<close>
  for A :: \<open>'a :: sep_magma_1 set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def
  \<medium_left_bracket> premises T and R and A
    apply_rule A[THEN implies_right_frame, where R=\<open>x \<Ztypecolon> T\<close>]
    T
    apply_rule R[THEN implies_right_frame, where R=\<open>fst y \<Ztypecolon> U\<close>]
  \<medium_right_bracket> .

lemma enter_SEb_TH:
  \<open> (x,w) \<Ztypecolon> T \<^emph> W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph> R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> U') (x' \<Ztypecolon> T' \<^emph> W') \<and> P1 @action \<A>SE
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> R) Q
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (w' \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P1 \<and> P2 \<and> Q\<close>
  for A :: \<open>'a :: sep_magma_1 set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEb .
*)

lemma enter_SEbi:
  \<open> (x, w) \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h> P1
\<Longrightarrow> if Cr then Identity_Element\<^sub>I (snd y \<Ztypecolon> \<black_circle> R) Q else Q = True
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def Premise_def
            Transformation_def
  by (cases C; cases Cr; clarsimp; blast)

lemma enter_SEbi_TH:
  \<open> (x, w) \<Ztypecolon> T \<^emph>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> U') (x' \<Ztypecolon> T' \<^emph>[C] W') \<and> P1
\<Longrightarrow> if Cr then Identity_Element\<^sub>I (snd y \<Ztypecolon> \<black_circle> R) Q else Q = True
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (w' \<Ztypecolon> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> U \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> U') (A' * (x'' \<Ztypecolon> T')) \<and> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEbi .

(* no need
lemma enter_SEbi_\<phi>Some:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h> P1 @action \<A>SEi
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> \<half_blkcirc>[Cr] R) Q
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<w>\<i>\<t>\<h> P2
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma option set\<close>
  unfolding Action_Tag_def \<phi>Prod_expn' Identity_Element\<^sub>I_def Premise_def
            Transformation_def
  by clarsimp fastforce

lemma enter_SEbi_\<phi>Some_TH:
  \<open> (x, w) \<Ztypecolon> \<black_circle> T \<^emph> \<half_blkcirc>[C] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> \<black_circle> U \<^emph> \<half_blkcirc>[Cr] R \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U') (x' \<Ztypecolon> \<black_circle> T' \<^emph> \<half_blkcirc>[C] W') \<and> P1 @action \<A>SEi
\<Longrightarrow> Identity_Element\<^sub>I (snd y \<Ztypecolon> \<half_blkcirc>[Cr] R) Q
\<Longrightarrow> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> C
\<Longrightarrow> A \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> w \<Ztypecolon> \<black_circle> W \<w>\<i>\<t>\<h> Auto_Transform_Hint (w' \<Ztypecolon> \<black_circle> W') A' \<and> P2
\<Longrightarrow> A * (x \<Ztypecolon> \<black_circle> T) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> fst y \<Ztypecolon> \<black_circle> U \<w>\<i>\<t>\<h>
        Auto_Transform_Hint (y' \<Ztypecolon> \<black_circle> U') (A' * (x'' \<Ztypecolon> \<black_circle> T')) \<and> P2 \<and> Q \<and> P1 \<close>
  for A :: \<open>'a :: sep_magma option set\<close>
  unfolding Auto_Transform_Hint_def HOL.simp_thms(22)
  using enter_SEbi_\<phi>Some .
*)

ML \<open>
fun SE_entry_point rules thy sequent =
  let val (X, Y, P) = Phi_Syntax.dest_transformation (Thm.major_prem_of sequent)
      val ty = Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent)
      val rules = (if Sign.of_sort thy (ty, \<^sort>\<open>sep_semigroup\<close>) then #1 else #2) rules
                  (*there is no support for commutative non-semigroup in the system*)
      fun obj_is_var (Const(\<^const_name>\<open>times\<close>, _) $ _ $ X) = obj_is_var X
        | obj_is_var (Const(\<^const_name>\<open>REMAINS\<close>, _) $ X $ _ $ _) = obj_is_var X
        | obj_is_var (Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ _) = is_Var (Term.head_of x)
      val rules = (if obj_is_var Y then fst else snd) rules
      val has_auto_hint =
        case P of Const(\<^const_name>\<open>conj\<close>, _) $ (Const(\<^const_name>\<open>Auto_Transform_Hint\<close>, _) $ _ $ _) $ _ => true
                | _ => false
      val rule = (if has_auto_hint then snd else fst) rules
   in rule RS sequent
  end

val SE_entry_point_normal = SE_entry_point (
      ((@{thm' enter_SEi}, @{thm' enter_SEi_TH}),
           (@{thm' enter_SEi[THEN ToA_by_Equiv_Class']}, @{thm' enter_SEi_TH[THEN ToA_by_Equiv_Class']})),
      ((@{thm' enter_SEa}, @{thm' enter_SEa_TH}),
           (@{thm' enter_SEa[THEN ToA_by_Equiv_Class']}, @{thm' enter_SEa_TH[THEN ToA_by_Equiv_Class']})))

val SE_entry_point_b = SE_entry_point (
      ((@{thm' enter_SEbi}, @{thm' enter_SEbi_TH}),
           (@{thm' enter_SEbi[THEN ToA_by_Equiv_Class]}, @{thm' enter_SEbi_TH[THEN ToA_by_Equiv_Class]})),
      ((@{thm' enter_SEbi}, @{thm' enter_SEbi_TH}),
           (@{thm' enter_SEbi[THEN ToA_by_Equiv_Class]}, @{thm' enter_SEbi_TH[THEN ToA_by_Equiv_Class]})))
\<close>
 
\<phi>reasoner_ML \<A>SE_Entry 50 (\<open>_ * (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<r>\<e>\<m>\<a>\<i>\<n>\<s>[_] _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (_, (ctxt, sequent)) =>
  Seq.make (fn () =>
    if Sign.of_sort (Proof_Context.theory_of ctxt)
                    (Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent), \<^sort>\<open>sep_magma\<close>)
    then SOME ((ctxt, SE_entry_point_normal (Proof_Context.theory_of ctxt) sequent), Seq.empty)
    else (warning "The reasoner can barely do nothing for those even are not sep_magma" ;
          NONE))\<close>

\<phi>reasoner_ML \<A>SEb_Entry 50 (\<open>_ * (_ \<Ztypecolon> _) \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> _ \<w>\<i>\<t>\<h> _\<close>) = \<open>fn (_, (ctxt, sequent)) =>
  Seq.make (fn () =>
    if Sign.of_sort (Proof_Context.theory_of ctxt)
                    (Phi_Syntax.dest_transformation_typ (Thm.major_prem_of sequent), \<^sort>\<open>sep_magma\<close>)
    then SOME ((ctxt, SE_entry_point_b (Proof_Context.theory_of ctxt) sequent), Seq.empty)
    else (warning "The reasoner can barely do nothing for those even are not sep_magma" ;
          NONE))\<close>

(* TODO:
hide_fact enter_SEb enter_SEb_TH*)


section \<open>Programming Methods for Proving Specific Properties\<close>

subsection \<open>Functional\<close>

lemma Is_Functional_imp'':
  \<open> S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<w>\<i>\<t>\<h> Is_Functional S'
\<Longrightarrow> Is_Functional S\<close>
  unfolding Transformation_def Is_Functional_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (Trueprop (S \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> S' \<s>\<u>\<b>\<j>-\<r>\<e>\<a>\<s>\<o>\<n>\<i>\<n>\<g> Is_Functional S')) M D R F
\<Longrightarrow> Friendly_Help TEXT(\<open>Hi! You are trying to show\<close> S \<open>is functional\<close>
      \<open>Now you entered the programming mode and you need to transform the specification to\<close>
      \<open>someone which is functional, so that we can verify your claim.\<close>)
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (Is_Functional S)) M D R F\<close>
  unfolding \<phi>Programming_Method_def  ToA_Construction_def \<phi>SemType_def conjunction_imp
            Subjec_Reasoning_def
  by (rule Is_Functional_imp''[where S'=S']; simp)



end
