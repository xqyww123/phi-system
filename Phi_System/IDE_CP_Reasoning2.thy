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
  unfolding Remove_Values_def using implies_refl . *)

lemma [\<phi>reason 1200]:
  \<open>(\<And>c. Remove_Values (T c) (T' c))
\<Longrightarrow> Remove_Values (ExSet T) (ExSet T')\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200]:
  \<open>(\<And>c. Remove_Values (R * T c) (R' * T' c))
\<Longrightarrow> Remove_Values (R * ExSet T) (R' * ExSet T')\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1200]:
  \<open> Remove_Values T T'
\<Longrightarrow> Remove_Values (T \<s>\<u>\<b>\<j> P) (T' \<s>\<u>\<b>\<j> P)\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns)

lemma [\<phi>reason 1200]:
  \<open> Remove_Values (R * T) (R' * T')
\<Longrightarrow> Remove_Values (R * (T \<s>\<u>\<b>\<j> P)) (R' * (T' \<s>\<u>\<b>\<j> P))\<close>
  unfolding Remove_Values_def Imply_def
  by (simp add: \<phi>expns)

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
  unfolding Remove_Values_def Imply_def
  by blast

lemma [\<phi>reason 1200]:
  \<open> Remove_Values R R'
\<Longrightarrow> Remove_Values (R * (x \<Ztypecolon> Val raw T)) R'\<close>
  unfolding Remove_Values_def Imply_def by (simp add: Val_expn Subjection_expn)

lemma [\<phi>reason 1200]:
  \<open>Remove_Values (x \<Ztypecolon> Val raw T) 1\<close>
  unfolding Remove_Values_def Imply_def by (simp add: Val_expn Subjection_expn)

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values (1 * A) A'\<close>
  unfolding Remove_Values_def Imply_def by simp

lemma [\<phi>reason 1200]:
  \<open> Remove_Values A A'
\<Longrightarrow> Remove_Values (A * 1) A'\<close>
  unfolding Remove_Values_def Imply_def by simp

lemma [\<phi>reason 1200]:
  \<open>Remove_Values (A * 0) 0\<close>
  unfolding Remove_Values_def Imply_def by simp

lemma [\<phi>reason 1100]:
  \<open> Remove_Values B B'
\<Longrightarrow> Remove_Values A A'
\<Longrightarrow> Remove_Values (A * B) (A' * B')\<close>
  unfolding Remove_Values_def Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 1000]:
  \<open> Remove_Values A A\<close>
  unfolding Remove_Values_def
  by simp


subsection \<open>Rewrite into \<phi>-Type\<close>

definition Rewrite_into_\<phi>Type :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close>
  where \<open>Rewrite_into_\<phi>Type IN OUT \<longleftrightarrow> IN = OUT\<close>

declare [[\<phi>reason_default_pattern \<open>Rewrite_into_\<phi>Type ?X _\<close> \<Rightarrow> \<open>Rewrite_into_\<phi>Type ?X _\<close> (100)]]

lemma [\<phi>reason 3000]:
  \<open>Rewrite_into_\<phi>Type (x \<Ztypecolon> T) (x \<Ztypecolon> T)\<close>
  unfolding Rewrite_into_\<phi>Type_def ..


(*
subsection \<open>Extract a Value\<close>

definition \<open>Extract_a_Value (S_in::assn) S_out val_out \<longleftrightarrow> (S_in \<i>\<m>\<p>\<l>\<i>\<e>\<s> S_out \<a>\<n>\<d> val_out)\<close>

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
  unfolding Extract_a_Value_def Imply_def
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


subsection \<open>Cleaning to 1\<close>

definition Is_Stateless :: \<open>'a::one set \<Rightarrow> bool\<close> where \<open>Is_Stateless S \<longleftrightarrow> (S \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1)\<close>

subsubsection \<open>Termination\<close>

lemma [\<phi>reason 3000]:
  \<open>Is_Stateless 0\<close>
  unfolding Is_Stateless_def by simp

lemma [\<phi>reason 3000]:
  \<open>Is_Stateless 1\<close>
  unfolding Is_Stateless_def by simp

subsubsection \<open>Logic Connectives\<close>

lemma [\<phi>reason 1200]:
  \<open> Is_Stateless A
\<Longrightarrow> Is_Stateless B
\<Longrightarrow> Is_Stateless (A + B)\<close>
  unfolding Is_Stateless_def
  using \<phi>CASE_IMP by force

lemma [\<phi>reason 1200]:
  \<open>(\<And>x. Is_Stateless (A x))
\<Longrightarrow> Is_Stateless (ExSet A)\<close>
  unfolding Is_Stateless_def
  by (metis ExSet_expn Imply_def)

lemma [\<phi>reason 1200]:
  \<open> Is_Stateless A
\<Longrightarrow> Is_Stateless (A \<s>\<u>\<b>\<j> P)\<close>
  unfolding Is_Stateless_def Imply_def
  by (simp add: Subjection_expn)

subsubsection \<open>General Reasoning by Algebraic Properties\<close>

lemma Is_Stateless_general_rule:
  \<open> Is_Stateless (x \<Ztypecolon> T)
\<Longrightarrow> Semi_Unit_Functor F
\<Longrightarrow> Is_Stateless (x \<Ztypecolon> F T)\<close>
  unfolding Semi_Unit_Functor_def Is_Stateless_def Unit_Homo_def
  by clarsimp

\<phi>reasoner_ML "Is_Stateless_general_rule" 50 (\<open>Is_Stateless (_ \<Ztypecolon> _)\<close>) = \<open>
fn (ctxt,sequent) => Seq.make (fn () =>
  let val _ (*Trueprop*) $ (_ (*Is_Stateless*) $ ( _ (*\<phi>Type*) $ _ $ T)) = Thm.major_prem_of sequent
   in case Phi_Functor_Detect.detect 1 ctxt T
        of SOME [Ft,Tt] => let
            val rule = Drule.infer_instantiate ctxt
                          [(("F",0), Thm.cterm_of ctxt Ft), (("T",0), Thm.cterm_of ctxt Tt)]
                          @{thm "Is_Stateless_general_rule"}
             in SOME ((ctxt, rule RS sequent), Seq.empty) end
         | _ => NONE
  end)
\<close>

lemma [\<phi>reason 1200]:
  \<open> Unit_Homo T
\<Longrightarrow> Is_Stateless (1 \<Ztypecolon> T)\<close>
  unfolding Unit_Homo_def Is_Stateless_def \<r>Guard_def Premise_def
  by clarsimp

lemma [\<phi>reason 1200]:
  \<open> Unit_Homo T
\<Longrightarrow> Is_Stateless (() \<Ztypecolon> T)\<close>
  unfolding Unit_Homo_def Is_Stateless_def \<r>Guard_def Premise_def
  by clarsimp


subsubsection \<open>Structural Node\<close>

lemma [\<phi>reason 1200]:
  \<open> Is_Stateless A
\<Longrightarrow> Is_Stateless B
\<Longrightarrow> Is_Stateless (A * B)\<close>
  for A :: \<open>'a::sep_magma_1 set\<close>
  unfolding Is_Stateless_def Imply_def
  apply (simp add: \<phi>expns)
  using mult_1_class.mult_1_left by blast

lemma [\<phi>reason 1200]:
  \<open> Is_Stateless X
\<Longrightarrow> Is_Stateless (TECHNICAL X)\<close>
  unfolding Technical_def .


section \<open>Transformation of State Abstraction (ToSA)\<close>

text \<open>This is a reasoning procedure for transformations of abstraction of the whole computation
  state, which we name \<^emph>\<open>Transformation of State Abstraction (ToSA)\<close>.
  Specifications must be given in MTF.
  The procedure can recognize items specifying identical objects and
    invoke the reasoning for transforming the object from the source abstraction to the target
    abstraction.\<close>

text \<open>Priority Convention:
\<^item> 4000: Termination
\<^item> 3200: Very Safe Normalization
\<^item> 3150: Assigning Zeros
\<^item> 3000: Normalization
\<^item> 2800: Disjunction in source part; Default normalization in source part
\<^item> 2600: Disjunction in target part; Default normalization in target part
        Divergence happens here!
        Existentially quantified variables are fixed here!
\<^item> 2100: Padding void holes after the last item. Rules capturing the whole items including
        the last item in the \<open>\<^emph>\<close>-sequence should have priority higher than this.
\<^item> 2000: Step-by-step searching
\<^item> \<le> 1999: Rules for searching specific object like value, variable, etc.
\<^item> 800:  Disjunction in target part
\<^item> \<le> 80: Rules for general searching. This feature is disabled in view shift
          because most of the global-state-level components are configured
          with properly search rules so the general search is not required.
\<close>


consts ToA_flag_deep :: bool


subsection \<open>Initialization\<close>

lemma [\<phi>reason 2100 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?P @action ToSA' ?mode\<close>]:
  \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> X @action ToSA' mode\<close>
  unfolding Action_Tag_def using implies_refl .

lemma [\<phi>reason 2100 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<s>\<u>\<b>\<j> True \<a>\<n>\<d> ?P @action ToSA' ?mode\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P @action ToSA' mode
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<s>\<u>\<b>\<j> True \<a>\<n>\<d> P @action ToSA' mode\<close>
  unfolding Action_Tag_def by simp

lemma [\<phi>reason 2020 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y @action ToSA' _\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> Any @action ToSA' deep
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y @action ToSA' deep\<close>
  unfolding Action_Tag_def
  by (simp add: implies_weaken)

lemma "_ToSA_init_focus_": (*[\<phi>reason 2010 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> ?var_P @action ToSA' _\<close>]:*)
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> \<r>CALL X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> Y' \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> Y \<brangle> \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def Simplify_def \<r>Call_def
  by simp

lemma "_ToSA_init_by_focus_": (*[\<phi>reason 2005 for \<open>(?X::?'a::sep_magma_1 set) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?var_P @action ToSA' _\<close>]:*)
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> \<r>CALL X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> Y' \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Simplify (assertion_simps undefined) R' R
\<Longrightarrow> Is_Stateless R'
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding Action_Tag_def Simplify_def \<r>Call_def Is_Stateless_def
  apply simp
  by (metis Imply_def implies_right_prod mult_1_class.mult_1_left)

lemma "_ToSA_init_": (*[\<phi>reason 2000 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?var_P @action ToSA' _\<close>]:*)
  \<open> Simplify (assertion_simps SOURCE) X' X
\<Longrightarrow> Simplify (assertion_simps TARGET) Y' Y
\<Longrightarrow> \<r>CALL X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y' \<a>\<n>\<d> P
\<Longrightarrow> Pop_Envir_Var ToA_flag_deep
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def Simplify_def \<r>Call_def Is_Stateless_def
  by simp

\<phi>reasoner_ML ToSA_init 2000 (\<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> ?var_P @action ToSA' _\<close>) = \<open>
fn (ctxt0,sequent0) => Seq.make (fn () =>
  let val sequent = @{thm Action_Tag_I} RS sequent0
      val _ (*Action_Tag*) $ (_ (*Trueprop*) $ (Const(\<^const_name>\<open>Imply\<close>, _) $ _ $ Y $ _))
                           $ (Const(\<^const_name>\<open>ToSA'\<close>, _) $ deep)
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
                                       |> Simplifier.simplify (Phi_Programming_Safe_Simp_SS.equip ctxt))

      fun scan1 ret (Const (\<^const_name>\<open>times\<close>, _) $ _ $ (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ _))
            = (true,[])
        | scan1 ret (Const (\<^const_name>\<open>times\<close>, _) $ A $ B) =
            scan1 (case B of Var v => mk_one v :: ret | _ => []) A
        | scan1 ret (Const (@{const_name Subjection}, _) $ X) = scan1 ret X
        | scan1 ret (Const (@{const_name ExSet}, _) $ X) = scan1 ret X
        | scan1 ret (Abs (_,_,X)) = scan1 ret X
        | scan1 ret (Var v) = (false, mk_one v :: ret)
        | scan1 _ _  = (false, [])

      val (X,Y,P) = Phi_Syntax.dest_implication (Thm.major_prem_of sequent1)
      val (already_has_focus, void_tails) = scan1 [] Y
      val sequent2 = (case void_tails of [] => sequent1
                         | (_::voids') => Thm.instantiate (TVars.empty, Vars.make voids') sequent1)

      fun add_focus_tag' ctxt ctm =
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
        Phi_Helper_Conv.leading_antecedent_conv (Phi_Helper_Conv.hhf_concl_conv (fn ctxt =>
          Phi_Syntax.implication_conv Conv.all_conv (add_focus_tag' ctxt) Conv.all_conv
        ) ctxt)

      val sequent3 = if null void_tails then sequent2
                     else Conv.fconv_rule (add_focus_tag ctxt) sequent2

      val is_unital = Sign.of_sort (Proof_Context.theory_of ctxt) (fastype_of Y, \<^sort>\<open>sep_magma_1\<close>)

      val rule = if already_has_focus
                 then @{thm "_ToSA_init_focus_"}
                 else if null void_tails andalso is_unital
                 then @{thm "_ToSA_init_by_focus_"}
                 else @{thm "_ToSA_init_"}
   in SOME ((ctxt, rule RS sequent3), Seq.empty)
  end)
\<close>




subsection \<open>Special Process for Holes\<close>

lemma ToA_ex_intro:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U c \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ExSet U \<a>\<n>\<d> P"
  unfolding Imply_def by (simp add: \<phi>expns, metis)

lemma ToA_ex_intro':
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> U c \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> ExSet U \<brangle> \<a>\<n>\<d> P"
  unfolding Imply_def by (simp add: \<phi>expns, metis)

lemma ToSA_finish': "X \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 * \<blangle> X \<brangle>"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left FOCUS_TAG_def Action_Tag_def
  using implies_refl by this+

ML \<open>
(* X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> P *)
fun ToSA_to_wild_card ctxt thm =
  let val (vs, _, goal) = Phi_Help.leading_antecedent (Thm.prop_of thm)
      val N = length vs
      val (X,Y0,_) = Phi_Syntax.dest_implication goal
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
                THEN (HEADGOAL (resolve0_tac @{thms implies_refl ToSA_finish'}))
   in tac thm'
  end
\<close>

\<phi>reasoner_ML \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<a>\<n>\<d> P @action ToSA\<close> 2015 (\<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?var_Y \<a>\<n>\<d> _ @action ToSA\<close>) = \<open>
  fn (ctxt,thm) => ToSA_to_wild_card ctxt thm |> Seq.map (pair ctxt)
\<close>


subsection \<open>Termination\<close>

declare ToSA_finish'[\<phi>reason 4000 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> ?X  \<brangle> \<a>\<n>\<d> ?P\<close>,
                     \<phi>reason 900  for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> ?X' \<brangle> \<a>\<n>\<d> ?P\<close>]

lemma [\<phi>reason 4000]:
  \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * \<blangle> 1 \<brangle>\<close>
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding FOCUS_TAG_def Action_Tag_def by simp

\<phi>reasoner_ML \<open>X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<a>\<n>\<d> P @action ToSA\<close> 4005 (\<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?var_Y \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<a>\<n>\<d> _\<close>) = \<open>
  fn (ctxt,thm) => ToSA_to_wild_card ctxt thm |> Seq.map (pair ctxt)
\<close>


subsection \<open>Void Holes\<close> \<comment> \<open>eliminate 1 holes generated during the reasoning \<close>

lemma [\<phi>reason 3200]:
  " H \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> H \<i>\<m>\<p>\<l>\<i>\<e>\<s> X * 1 \<a>\<n>\<d> P "
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  " H \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> H \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X * 1 \<brangle> \<a>\<n>\<d> P"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_right .

lemma [\<phi>reason 3200]:
  " R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> R * 1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P "
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_right .


subsection \<open>Subjection\<close>

lemma [\<phi>reason 3200]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P \<Longrightarrow>
   (P \<Longrightarrow> Pass_Embedded_Reasoning Q) \<Longrightarrow>
    T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<s>\<u>\<b>\<j> Q \<a>\<n>\<d> P "
  unfolding Imply_def Pass_Embedded_Reasoning_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3210]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P \<Longrightarrow>
    T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<s>\<u>\<b>\<j> True \<a>\<n>\<d> P "
  unfolding Imply_def Pass_Embedded_Reasoning_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3200]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> U \<brangle> \<a>\<n>\<d> P \<Longrightarrow>
   (P \<Longrightarrow> Pass_Embedded_Reasoning Q) \<Longrightarrow>
    T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> U \<s>\<u>\<b>\<j> Q \<brangle> \<a>\<n>\<d> P "
  unfolding Imply_def Pass_Embedded_Reasoning_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3210]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> U \<brangle> \<a>\<n>\<d> P \<Longrightarrow>
    T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> U \<s>\<u>\<b>\<j> True \<brangle> \<a>\<n>\<d> P "
  unfolding Imply_def Pass_Embedded_Reasoning_def by (simp add: \<phi>expns)

lemma [\<phi>reason 3200]: (*TODO: add Q in P*)
  "(Q \<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P )
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P"
  unfolding Imply_def by (simp add: \<phi>expns) blast

lemma [\<phi>reason 3210]:
  "(Q \<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> U \<brangle> \<a>\<n>\<d> P)
\<Longrightarrow> T \<s>\<u>\<b>\<j> Q \<i>\<m>\<p>\<l>\<i>\<e>\<s> (R \<s>\<u>\<b>\<j> Q) * \<blangle> U \<brangle> \<a>\<n>\<d> P"
  unfolding Imply_def by (simp add: \<phi>expns) blast


subsection \<open>Existential\<close>

declare ToA_ex_intro [\<phi>reason 2600]
declare ToA_ex_intro'[\<phi>reason 2600]

lemma [\<phi>reason 2800]:
  "(\<And>x.  T x \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P)
\<Longrightarrow> ExSet T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U \<a>\<n>\<d> P"
  unfolding Imply_def by (simp add: \<phi>expns) fastforce

lemma [\<phi>reason 2810]:
  "(\<And>x.  T x \<i>\<m>\<p>\<l>\<i>\<e>\<s> R x * \<blangle> U \<brangle> \<a>\<n>\<d> P)
\<Longrightarrow> ExSet T \<i>\<m>\<p>\<l>\<i>\<e>\<s> ExSet R * \<blangle> U \<brangle> \<a>\<n>\<d> P"
  unfolding Imply_def by (simp add: \<phi>expns) fastforce

subsection \<open>Let Notation \& Prod Case\<close>

lemma [\<phi>reason 2600]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> U x \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> Let x U \<a>\<n>\<d> P"
  unfolding Let_def .

lemma [\<phi>reason 2600]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> U x \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> Let x U \<brangle> \<a>\<n>\<d> P"
  unfolding Let_def .

lemma [\<phi>reason 2610]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f x y \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> case_prod f (x,y) \<a>\<n>\<d> P"
  by simp

lemma [\<phi>reason 2610]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> f x y \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> case_prod f (x,y) \<brangle> \<a>\<n>\<d> P"
  by simp

lemma [\<phi>reason 2600]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> f x y \<s>\<u>\<b>\<j> x y. xy = (x,y) \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> case_prod f xy \<a>\<n>\<d> P"
  unfolding Imply_def by (cases xy; simp add: \<phi>expns)

lemma [\<phi>reason 2600]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> f x y \<s>\<u>\<b>\<j> x y. xy = (x,y) \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> case_prod f xy \<brangle> \<a>\<n>\<d> P"
  unfolding Imply_def by (cases xy; simp add: \<phi>expns)

(* subsubsection \<open>Tailling\<close> \<comment> \<open>\<close>

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<a>\<n>\<d> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> VAL x \<Ztypecolon> X \<brangle> \<a>\<n>\<d> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l H\<^sub>m \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .

lemma [\<phi>intro 1100]: \<comment> \<open>tail the step\<close>
  "H \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 \<heavy_comma> \<blangle> x \<Ztypecolon> X \<brangle> \<a>\<n>\<d> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l 1 \<heavy_comma> \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> \<Longrightarrow>
  H \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> x \<Ztypecolon> X \<brangle> \<a>\<n>\<d> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l \<blangle> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> H\<^sub>m \<brangle> "
  unfolding Separation_emptyL Separation_emptyR .
*)

subsection \<open>Zero\<close>

\<phi>reasoner_ML \<open>0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X\<close> 3100 (\<open>0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _\<close> | \<open>?var_A \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<a>\<n>\<d> _\<close>) =
\<open>fn (ctxt,sequent) => Seq.make (fn () =>
  let fun collect L (Const (\<^const_name>\<open>ExSet\<close>, _) $ Abs (_,_,X)) = collect L X
        | collect L (Const (\<^const_name>\<open>Subjection\<close>, _) $ X $ _) = collect L X
        | collect L (Const (\<^const_name>\<open>times\<close>, _) $ A $ B) = collect (collect L A) B
        | collect L (Const (\<^const_name>\<open>FOCUS_TAG\<close>, _) $ X) = collect L X
        | collect L (Var (V, T)) = AList.update (op =) (V, Const (\<^const_name>\<open>zero_class.zero\<close>, T)) L
        | collect L (X $ _) = collect L X
        | collect L _ = L
      val (_,X,_) = Phi_Syntax.dest_implication (Thm.major_prem_of sequent)
      val sequent' = Drule.infer_instantiate ctxt
                        (collect [] X |> map (apsnd (Thm.cterm_of ctxt))) sequent
      val sequent'2 = (@{thm zero_implies_any} RS sequent')
                   |> Phi_Helper_Conv.rewrite_leading_antecedent ctxt @{thms zero_fun[folded atomize_eq]}
   in SOME ((ctxt, sequent'2), Seq.empty) end)
\<close>

lemma [\<phi>reason 3100]:
  \<open> 0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X
\<Longrightarrow> R * 0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> 0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X
\<Longrightarrow> 0 * R \<i>\<m>\<p>\<l>\<i>\<e>\<s> X\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> Y + 0 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> 0 + Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> X + 0 \<a>\<n>\<d> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> 0 + X \<a>\<n>\<d> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X + 0 \<brangle> \<a>\<n>\<d> P\<close>
  by simp

lemma [\<phi>reason 3100]:
  \<open> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> 0 + X \<brangle> \<a>\<n>\<d> P\<close>
  by simp


subsection \<open>Divergence\<close>

subsubsection \<open>Disjunction in Source\<close>

lemma [\<phi>reason 2800]:
  \<open> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P1
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P2
\<Longrightarrow> A + B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P1 \<or> P2\<close>
  by (simp add: Imply_def)

lemma [\<phi>reason 2800]:
  \<open> R * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P1
\<Longrightarrow> R * A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P2
\<Longrightarrow> R * (A + B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P1 \<or> P2\<close>
  apply (simp add: Imply_def distrib_left)
  by (metis plus_set_in_iff set_mult_expn)

lemma [\<phi>reason 2810]:
  \<open> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> RB * \<blangle> X \<brangle> \<a>\<n>\<d> P1
\<Longrightarrow> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> RA * \<blangle> X \<brangle> \<a>\<n>\<d> P2
\<Longrightarrow> A + B \<i>\<m>\<p>\<l>\<i>\<e>\<s> (RA + RB) * \<blangle> X \<brangle> \<a>\<n>\<d> P1 \<or> P2\<close>
  apply (simp add: Imply_def)
  by (metis plus_set_in_iff subset_iff times_set_subset(2))

lemma [\<phi>reason 2810]:
  \<open> R * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> RB * \<blangle> X \<brangle> \<a>\<n>\<d> P1
\<Longrightarrow> R * A \<i>\<m>\<p>\<l>\<i>\<e>\<s> RA * \<blangle> X \<brangle> \<a>\<n>\<d> P2
\<Longrightarrow> R * (A + B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> (RA + RB) * \<blangle> X \<brangle> \<a>\<n>\<d> P1 \<or> P2\<close>
  apply (simp add: Imply_def)
  by (smt (z3) plus_set_in_iff set_mult_expn)


subsubsection \<open>Disjunction in Target\<close>

lemma ToSA_disj_target_A:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A + B \<a>\<n>\<d> P\<close>
  unfolding plus_set_def
  by (metis implies_union(1) plus_set_def)

lemma ToSA_disj_target_B:
  \<open>  X \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P
\<Longrightarrow>  X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A + B \<a>\<n>\<d> P\<close>
  unfolding plus_set_def
  by (simp add: Imply_def)

declare [[\<phi>reason 2600 ToSA_disj_target_A ToSA_disj_target_B for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?A + ?B \<a>\<n>\<d> ?P\<close>]]

hide_fact ToSA_disj_target_A ToSA_disj_target_B

lemma ToSA_disj_target_A':
  \<open>  X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> A \<brangle> \<a>\<n>\<d> P
\<Longrightarrow>  X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> A + B \<brangle> \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def
  apply (simp add: distrib_left)
  by (metis plus_set_in_iff set_mult_expn)

lemma ToSA_disj_target_B':
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> B \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> A + B \<brangle> \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def
  apply (simp add: distrib_left)
  by (metis plus_set_in_iff set_mult_expn)

declare [[\<phi>reason 2600 ToSA_disj_target_A' ToSA_disj_target_B'
            for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> ?A + ?B \<brangle> \<a>\<n>\<d> _\<close>]]

hide_fact ToSA_disj_target_A' ToSA_disj_target_B'

subsubsection \<open>Conditional Branch in Source\<close>

text \<open>The condition should be regarded as an output, and the reasoning process assigns which
the branch that it chooses to the output condition variable.\<close>

lemma ToSA_cond_source_A:
  \<open> A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> (if True then A else B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def
  by (simp add: Imply_def distrib_left)

lemma ToSA_cond_source_B:
  \<open> B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> (if False then A else B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def
  by (simp add: Imply_def distrib_left)

declare [[\<phi>reason 2600 ToSA_cond_source_A ToSA_cond_source_B
        for \<open>(if ?condition then ?A else ?B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X \<a>\<n>\<d> ?P\<close>]]

hide_fact ToSA_cond_source_A ToSA_cond_source_B

lemma ToSA_cond_source_A':
  \<open> R * A \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> R * (if True then A else B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def
  by (simp add: Imply_def distrib_left)

lemma ToSA_cond_source_B':
  \<open> R * B \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> R * (if False then A else B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P\<close>
  unfolding Action_Tag_def
  by (simp add: Imply_def distrib_left)

declare [[\<phi>reason 2600 ToSA_cond_source_A' ToSA_cond_source_B'
        for \<open>?R * (if ?condition then ?A else ?B) \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?X \<a>\<n>\<d> ?P\<close>]]

hide_fact ToSA_cond_source_A' ToSA_cond_source_B'


subsubsection \<open>Conditional Branch in Target\<close>

lemma ToSA_cond_target_A:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> A \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (if True then A else B) \<a>\<n>\<d> P\<close>
  by simp

lemma ToSA_cond_target_B:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> B \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (if False then A else B) \<a>\<n>\<d> P\<close>
  by simp

declare [[\<phi>reason 2600 ToSA_cond_target_A ToSA_cond_target_B
            for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> (if ?condition then ?A else ?B) \<a>\<n>\<d> ?P\<close> ]]

hide_fact ToSA_cond_target_A ToSA_cond_target_B

lemma ToSA_cond_target_A':
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> A \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> if True then A else B \<brangle> \<a>\<n>\<d> P\<close>
  by simp

lemma ToSA_cond_target_B':
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> B \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> if False then A else B \<brangle> \<a>\<n>\<d> P\<close>
  by simp

declare [[\<phi>reason 2600 ToSA_cond_target_B' ToSA_cond_target_A'
            for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> if ?condition then ?A else ?B \<brangle> \<a>\<n>\<d> ?P\<close> ]]

hide_fact ToSA_cond_target_A' ToSA_cond_target_B'

subsection \<open>Step-by-Step Searching Procedure\<close>

(*
lemma [\<phi>reason 2100
 except \<open> ?H \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> (?X1 * ?X2) \<brangle> \<a>\<n>\<d> ?P @action reason_ToSA ?mode ?G\<close>
        \<open> ?H \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> 1 \<brangle> \<a>\<n>\<d> ?P @action reason_ToSA ?mode ?G\<close>
        \<open> ?H \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> TAIL ?X \<brangle> \<a>\<n>\<d> ?P @action reason_ToSA ?mode ?G\<close>
]:
  " H \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> 1 * X \<brangle> \<a>\<n>\<d> P @action reason_ToSA mode G \<Longrightarrow>
    H \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> X \<brangle> \<a>\<n>\<d> P @action reason_ToSA mode G"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left .


lemma [\<phi>reason 1050 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> ?Y \<brangle> \<a>\<n>\<d> ?P @action reason_ToSA True ?G\<close>
   except \<open>(?X'::?'a::sep_magma_1 set) \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> ?Y' \<brangle> \<a>\<n>\<d> ?P @action reason_ToSA True ?G\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> Y \<brangle> \<a>\<n>\<d> P @action reason_ToSA True G\<close>
  \<comment> \<open>If it doesn't have one, it cannot be reasoned by this procedure, so
      a fallback here handles it.\<close>
  unfolding FOCUS_TAG_def Action_Tag_def .*)

lemma [\<phi>reason 2030]:
  " Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 * \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> 1 * \<blangle> R2 * \<blangle> X \<brangle> \<brangle> \<a>\<n>\<d> P"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left FOCUS_TAG_def .

lemma [\<phi>reason 2020
   except \<open> ?Y1 * ?Y2 \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> ?P\<close>
          \<open> 1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> ?P\<close>
          \<open> TAIL ?H \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> ?P\<close>
]:
  " 1 * Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle> \<a>\<n>\<d> P"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding mult_1_left .

lemma [\<phi>reason 30 except \<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> _\<close>]:
  " R  \<i>\<m>\<p>\<l>\<i>\<e>\<s> R1 * \<blangle> X \<brangle> \<a>\<n>\<d> P1
\<Longrightarrow> (P1 \<Longrightarrow> R1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 \<a>\<n>\<d> P2)
\<Longrightarrow> R  \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 * X \<a>\<n>\<d> P1 \<and> P2"
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All Action_Tag_def
  by (metis set_mult_expn)

lemma [\<phi>reason 2010]:
  " R  \<i>\<m>\<p>\<l>\<i>\<e>\<s> R1 * \<blangle> X \<brangle> \<a>\<n>\<d> P1
\<Longrightarrow> (P1 \<Longrightarrow> R1 \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' * \<blangle> R2 \<brangle> \<a>\<n>\<d> P2)
\<Longrightarrow> R  \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' * \<blangle> R2 * X \<brangle> \<a>\<n>\<d> P1 \<and> P2"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding Action_Tag_def FOCUS_TAG_def Imply_def split_paired_All Action_Tag_def
  by (metis (no_types, lifting) mult.assoc set_mult_expn)

consts ToA_Annotation :: \<open>'a \<Rightarrow> 'a\<close>

(* lemma [\<phi>reason 25 except \<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> _\<close>]:
  " \<r>RECURSION_GUARD(ToA_Annotation X) (R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R1 * \<blangle> X \<brangle> \<a>\<n>\<d> P)
\<Longrightarrow> Is_Stateless R1
\<Longrightarrow> R  \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P"
  for X :: \<open>'a::sep_magma_1 set\<close>
  unfolding FOCUS_TAG_def Imply_def split_paired_All Is_Stateless_def \<r>Recursion_Guard_def
  by (metis mult_1_class.mult_1_left set_mult_expn) *)

(* lemma [\<phi>reason 1050 for \<open>?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> ?Y \<brangle> \<a>\<n>\<d> ?P @action reason_ToSA True ?G\<close>
   except \<open>(?X'::?'a::sep_magma_1 set) \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> ?Y' \<brangle> \<a>\<n>\<d> ?P @action reason_ToSA True ?G\<close>]:
  \<open> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> Y \<a>\<n>\<d> P
\<Longrightarrow> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> \<blangle> Y \<brangle> \<a>\<n>\<d> P @action reason_ToSA True G\<close>
  \<comment> \<open>If it isn't unital, it cannot be reasoned by this procedure, so
      a fallback here handles it.\<close>
  unfolding FOCUS_TAG_def Action_Tag_def . *)


subsection \<open>Annotations\<close>

lemma [\<phi>reason 2000]:
  " R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 * \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 * \<blangle> \<blangle> X \<brangle> \<brangle> \<a>\<n>\<d> P"
  unfolding FOCUS_TAG_def .

lemma [\<phi>reason 2000]:
  " R * Y \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> R * \<blangle> Y \<brangle> \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P"
  unfolding FOCUS_TAG_def Imply_def split_paired_All
  by (simp add: \<phi>expns)

lemma [\<phi>reason 2000]:
  \<open> R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 * \<blangle> X \<brangle> \<a>\<n>\<d> Reverse_Transformation RP RX \<and> P
\<Longrightarrow> R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R2 * \<blangle> SMORPH X \<brangle> \<a>\<n>\<d> Reverse_Transformation RP RX \<and> P\<close>
  \<comment> \<open>This is the entry point of Reverse_Transformation !\<close>
  unfolding SMorphism_def .


subsection \<open>Value\<close>

text \<open>The rules require the same values are alpha-beta-eta-conversible. \<close>
text \<open>Priority shouldn't exceed 2000.\<close>

lemma [\<phi>reason 1215 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<heavy_comma> \<blangle> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<brangle> \<a>\<n>\<d> _\<close>]:
  "R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R \<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle>"
  unfolding FOCUS_TAG_def Imply_def by blast

lemma [\<phi>reason 1210 for \<open>_ \<heavy_comma> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<heavy_comma> \<blangle> _ \<Ztypecolon> \<v>\<a>\<l>[_] _ \<brangle> \<a>\<n>\<d> _\<close>
                    if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]:
  " y \<Ztypecolon> U \<i>\<m>\<p>\<l>\<i>\<e>\<s> x \<Ztypecolon> T \<a>\<n>\<d> P
\<Longrightarrow> R \<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l>[v] U \<i>\<m>\<p>\<l>\<i>\<e>\<s> R \<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle> \<a>\<n>\<d> P"
  unfolding Imply_def by (simp add: \<phi>expns times_list_def) metis

lemma [\<phi>reason 1200]:
  " R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R'\<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> R \<heavy_comma> X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R'\<heavy_comma> X\<heavy_comma> \<blangle> x \<Ztypecolon> \<v>\<a>\<l>[v] T \<brangle> \<a>\<n>\<d> P"
  unfolding FOCUS_TAG_def split_paired_All
  by (metis implies_left_prod mult.assoc mult.commute)

lemma [\<phi>reason 1200 except \<open>_ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ \<heavy_comma> \<blangle> ?x \<Ztypecolon> \<v>\<a>\<l>[?v] ?V \<brangle> \<a>\<n>\<d> _\<close>]:
  " R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' \<heavy_comma> \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> R \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' \<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l>[v] V \<heavy_comma> \<blangle> X \<brangle> \<a>\<n>\<d> P"
  unfolding FOCUS_TAG_def
  by (metis (no_types, opaque_lifting) implies_right_prod mult.assoc mult.commute)


subsection \<open>General Search\<close>

lemma [\<phi>reason 800 for \<open> _ * ?X \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> ?X''' \<brangle> \<a>\<n>\<d> _\<close>]:
  " R * X \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle>"
  by simp

text \<open>A very weak, one-to-one search.\<close>

lemma [\<phi>reason 70 if \<open>PLPR_Env.boolean_flag \<^const_name>\<open>ToA_flag_deep\<close> true o fst\<close>]: \<comment> \<open>attempts the immediate cell\<close>
  " H \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> R * H \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle> \<a>\<n>\<d> P"
  for H :: \<open>'a::sep_semigroup set\<close>
  unfolding FOCUS_TAG_def Imply_def
  by (metis (no_types, lifting) mult.assoc set_mult_expn)

lemma ToSA_skip [\<phi>reason 65 for \<open> _ * _ * _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> ?X \<brangle> \<a>\<n>\<d> _\<close>
                            ]:
\<comment> \<open>or attempts the next cell, if still not succeeded\<close>
  " R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' * \<blangle> X \<brangle> \<a>\<n>\<d> P
\<Longrightarrow> R * H \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' * H * \<blangle> X \<brangle> \<a>\<n>\<d> P"
  for H :: \<open>'a::sep_ab_semigroup set\<close>
  unfolding FOCUS_TAG_def Imply_def
  by (smt (verit, del_insts) mult.assoc mult.commute set_mult_expn)

lemma [\<phi>reason 60 for \<open> _ * _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> ?P\<close>
                  except \<open> _ * _ * _ \<i>\<m>\<p>\<l>\<i>\<e>\<s> _ * \<blangle> _ \<brangle> \<a>\<n>\<d> ?P\<close>
                        ]:
  " H \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> H * R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * \<blangle> X \<brangle> \<a>\<n>\<d> P"
  for H :: \<open>'a::sep_ab_semigroup set\<close>
  unfolding FOCUS_TAG_def Imply_def
  by (metis mult.commute set_mult_expn)

(* lemma [\<phi>reason 1200
    on \<open>?R \<i>\<m>\<p>\<l>\<i>\<e>\<s> ?R' \<heavy_comma> \<blangle> OBJ ?a \<Zinj> ?x \<Ztypecolon> ?X \<brangle> \<a>\<n>\<d> ?P \<^bold>d\<^bold>u\<^bold>a\<^bold>l ?R'\<^sub>m \<heavy_comma> VAL ?V \<heavy_comma> \<blangle> OBJ ?a\<^sub>m \<Zinj> ?x\<^sub>m \<Ztypecolon> ?X\<^sub>m \<brangle> \<longmapsto> ?R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L ?G\<close>
  ]: \<comment> \<open>OR search the later cells, if hasn't succeeded.\<close>
  " R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<a>\<n>\<d> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G
\<Longrightarrow> R \<i>\<m>\<p>\<l>\<i>\<e>\<s> R' \<heavy_comma> \<blangle> OBJ a \<Zinj> x \<Ztypecolon> X \<brangle> \<a>\<n>\<d> P \<^bold>d\<^bold>u\<^bold>a\<^bold>l R'\<^sub>m \<heavy_comma> VAL V \<heavy_comma> \<blangle> OBJ a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m \<brangle> \<longmapsto> R\<^sub>m \<heavy_comma> VAL V \<^bold>@\<^bold>G\<^bold>O\<^bold>A\<^bold>L G"
  unfolding FOCUS_TAG_def Subty_Target2_def Separation_assoc[symmetric]
    Separation_comm(2)[of "VAL V" "\<tort_lbrace>a\<^sub>m \<Zinj> x\<^sub>m \<Ztypecolon> X\<^sub>m\<tort_rbrace>"]
  unfolding Separation_assoc
  by (rule cast_dual_intro_frame_R[where M = 1, unfolded Separation_empty])

text \<open>step cases when the reasoner faces an object argument \<^term>\<open>OBJ a \<Zinj> x \<Ztypecolon> T\<close>\<close>
*)

subsection \<open>Plainize\<close>

lemma [\<phi>reason 2000]:
  " R * T1 * T2 \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P
\<Longrightarrow> R * (T1 * T2) \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<a>\<n>\<d> P"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding mult.assoc[symmetric] .

lemma [\<phi>reason 2000]:
  " T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * X1 * X2 \<a>\<n>\<d> P
\<Longrightarrow> T \<i>\<m>\<p>\<l>\<i>\<e>\<s> R * (X1 * X2) \<a>\<n>\<d> P"
  for R :: \<open>'a::sep_semigroup set\<close>
  unfolding mult.assoc[symmetric] .



(* subsection \<open>Structural Pairs\<close> (*depreciated*)

definition StructuralTag ("<Structural> _" [10] 9) where "StructuralTag \<equiv> Trueprop"
lemma StructuralTag_I: "P \<Longrightarrow> <Structural> P" unfolding StructuralTag_def . *)


section \<open>Programming Methods\<close>

subsection \<open>Functional\<close>

lemma is_functional_imp'':
  \<open> S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> is_functional S'
\<Longrightarrow> is_functional S\<close>
  unfolding Imply_def is_functional_def
  by blast

lemma [\<phi>reason 1000]:
  \<open> PROP \<phi>Programming_Method (Trueprop (S \<i>\<m>\<p>\<l>\<i>\<e>\<s> S' \<a>\<n>\<d> Embedded_Reasoning (is_functional S'))) M D R F
\<Longrightarrow> Friendly_Help TEXT(\<open>Hi! You are trying to show\<close> S \<open>is functional\<close>
      \<open>Now you entered the programming mode and you need to transform the specification to\<close>
      \<open>someone which is functional, so that we can verify your claim.\<close>)
\<Longrightarrow> PROP \<phi>Programming_Method (Trueprop (is_functional S)) M D R F\<close>
  unfolding \<phi>Programming_Method_def  ToA_Construction_def \<phi>SemType_def conjunction_imp
            Embedded_Reasoning_def
  by (rule is_functional_imp''[where S'=S']; simp)



end
