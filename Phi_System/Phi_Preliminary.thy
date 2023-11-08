chapter \<open>Theoretical Foundations\<close>

section \<open>Preliminary\<close>

theory Phi_Preliminary
  imports Main "Phi_Algebras.Algebras"
          Phi_Logic_Programming_Reasoner.PLPR
          Phi_Logic_Programming_Reasoner.PLPR_error_msg
  keywords "optional_translations" :: thy_decl
       and "\<phi>adhoc_overloading" "\<phi>no_adhoc_overloading" :: thy_decl
  abbrevs "<implies>" = "\<i>\<m>\<p>\<l>\<i>\<e>\<s>"
      and "<suffices>" = "\<s>\<u>\<f>\<f>\<i>\<c>\<e>\<s>"
begin

declare [[ML_debugger, ML_exception_debugger, ML_print_depth=100]]

subsection \<open>Named Theorems\<close>

ML \<open>structure Phi_Expansions = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>expns\<close>
  val comment = "Semantics Expansions, used to expand assertions semantically."
  val attribute = NONE
  val post_merging = I
)\<close>

declare set_mult_expn[\<phi>expns] Premise_def[\<phi>expns]

ML \<open>
structure Phi_Programming_Simp_SS = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>programming_simps\<close>
  val comment = "Simplification rules used in the deductive programming, including the \<phi>programming_base_simps."
  val attribute = NONE
  val post_merging = I
)
\<comment> \<open>A trick: if a \<phi>programming_simp rule is also declared in the system simpset, just declare it
    by \<phi>programming_base_simps, and it can improve the performance.\<close>

structure Phi_Programming_Base_Simp_SS = Simpset (
  val initial_ss = Simpset_Configure.Minimal_SS
  val binding = SOME \<^binding>\<open>\<phi>programming_base_simps\<close>
  val comment = "Simplification rules used only in low level automation"
  val attribute = NONE
  val post_merging = I
)
\<close>


setup \<open>Context.theory_map (Phi_Programming_Base_Simp_SS.map (fn ctxt =>
  ctxt addsimprocs [\<^simproc>\<open>NO_MATCH\<close>, \<^simproc>\<open>defined_All\<close>, \<^simproc>\<open>defined_Ex\<close>]))\<close>



subsection \<open>Error Mechanism\<close>

ML_file \<open>library/tools/error.ML\<close>


subsection \<open>Helper ML\<close>

ML_file \<open>library/tools/Phi_Help.ML\<close>
ML_file \<open>library/tools/lift_type_sort.ML\<close>
ML_file \<open>library/syntax/helps.ML\<close>
ML_file \<open>library/system/Phi_Envir0.ML\<close>
ML_file \<open>library/system/Phi_ID.ML\<close>
ML_file \<open>library/tools/Hasher.ML\<close>
ML_file \<open>library/tools/cache_file.ML\<close>


(*
A JSON lib. Maybe one day in the cache file we will use JSON (or better some K-V data base)
instead of XML. I'm thinking of the performance of the XML, particularly we have a lot of
`<` and `>` symbols. Need some tests.

ML_file \<open>contrib/sml-json/json.sig\<close>
ML_file \<open>contrib/sml-setmap/map/MONO_MAP.sig\<close>
ML_file \<open>contrib/sml-setmap/map/OrderMapImpl.sml\<close>
ML_file \<open>contrib/sml-setmap/map/OrderMap.sml\<close>
ML_file \<open>contrib/sml-setmap/map/StringMap.sml\<close>
ML_file \<open>contrib/sml-json/json.sml\<close> *)

subsection \<open>Helper Methods\<close>

method_setup subgoal' = \<open>
     Scan.lift (Scan.option (\<^keyword>\<open>premises\<close> |-- Parse.binding))
  -- Scan.lift (Scan.option (\<^keyword>\<open>for\<close> |-- Parse.and_list (Scan.repeat1 Parse.binding) >> flat))
  -- Scan.lift (Parse.token Parse.embedded) >>
 (fn ((prem_b, fixes), text_tok) => fn ctxt => fn rules =>
  let fun FOCUS tac ctxt i st =
        if Thm.nprems_of st < i then Seq.empty
        else let val (args as {context = ctxt', params, asms, prems, ...}, st') =
                    (if is_some prem_b then Subgoal.focus else Subgoal.focus_params_fixed) ctxt i fixes st
                 val ctxt' = case prem_b of SOME b =>
                                    Proof_Context.note_thms "" ((b,[]), map (fn th => ([th],[])) prems) ctxt'
                                      |> snd
                                | _ => ctxt'
              in Seq.lifts (Subgoal.retrofit ctxt' ctxt params asms i) (tac ctxt' st') st
             end
   in Context_Tactic.CONTEXT_TACTIC (HEADGOAL (FOCUS (fn ctxt =>
      let val (text, src) = Method.read_closure_input ctxt (Token.input_of text_tok)
       in Context_Tactic.NO_CONTEXT_TACTIC ctxt (Method.evaluate_runtime text ctxt rules)
      end) ctxt))
  end)
\<close>


subsection \<open>Helper Lemmas\<close>

lemma imp_implication: "(P \<longrightarrow> Q \<Longrightarrow> PROP R) \<equiv> ((P \<Longrightarrow> Q) \<Longrightarrow> PROP R)" by rule simp+

lemma case_sum_collapse[simp]:
  \<open>case_sum Inl Inr = (\<lambda>x. x)\<close>
  unfolding fun_eq_iff
  by (clarsimp simp add: split_sum_all)

lemma snd_o_Pair_eq_id[simp]:
  \<open> snd \<circ> Pair c = (\<lambda>x. x) \<close>
  unfolding fun_eq_iff
  by simp

lemma apfst_id'[simp]:
  \<open>apfst (\<lambda>x. x) = (\<lambda>x. x)\<close>
  by (simp add: fun_eq_iff)


ML_file \<open>library/tools/help_lemmas.ML\<close>

subsection \<open>Helper Attributes \& Tactics\<close>

attribute_setup rotated = \<open>Scan.lift (Scan.optional Parse.int 1 -- Scan.optional Parse.int 0) >>
  (fn (k,j) => Thm.rule_attribute [] (fn _ => Thm.permute_prems j k))\<close>
  \<open>Enhanced version of the Pure.rotated\<close>

attribute_setup TRY_THEN = \<open>(Scan.lift (Scan.optional (Args.bracks Parse.nat) 1) -- Attrib.thm
      >> (fn (i, B) => Thm.rule_attribute [B] (fn _ => fn A => A RSN (i, B) handle THM _ => A)))
    \<close> "resolution with rule, and do nothing if fail"

ML \<open>
val phi_system_ML_attribute_locker_do_not_override = Mutex.mutex ()
val phi_system_ML_attribute_sender_do_not_override : (morphism -> Thm.attribute) option Unsynchronized.ref =
      Unsynchronized.ref NONE
fun phi_system_read_ML_attribute generic src =
  let val _ = Mutex.lock phi_system_ML_attribute_locker_do_not_override
      val _ =   ML_Context.expression (Input.pos_of src)
              ( ML_Lex.read "phi_system_ML_attribute_sender_do_not_override := SOME (("
              @ ML_Lex.read_source src
              @ ML_Lex.read ") : morphism -> Thm.attribute)") generic
            handle err => (
              Mutex.unlock phi_system_ML_attribute_locker_do_not_override;
              raise err)
      val attr = the (@{print} (!phi_system_ML_attribute_sender_do_not_override))
      val _ = Mutex.unlock phi_system_ML_attribute_locker_do_not_override;
  in attr
  end
val phi_system_ML_attribute_parser = (
   Scan.lift Args.internal_attribute
|| Scan.peek (fn ctxt => Parse.token Parse.ML_source >>
    Token.evaluate Token.Attribute (fn tok => 
let val src = Token.input_of tok
in Morphism.entity (phi_system_read_ML_attribute ctxt src)
end )))
\<close>

attribute_setup ML_attribute = \<open>
  phi_system_ML_attribute_parser >> Morphism.form\<close>
  \<open>Use ML directly in an attribute without defining a new attribute if you just
  want to use it here specifically\<close>


subsection \<open>Helper Objects\<close>

subsubsection \<open>Embedding Function into Relation\<close>

definition embedded_func :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool\<close>
  where \<open>embedded_func f P = (\<lambda>x y. y = f x \<and> P x)\<close>

lemma embedded_func_red[iff]:
  \<open> embedded_func f P x y \<longleftrightarrow> y = f x \<and> P x \<close>
  unfolding embedded_func_def
  by simp

subsubsection \<open>Big Number\<close>

text \<open>A tag to suppress unnecessary expanding of big numbers like \<open>2^256\<close>
  (*depreciated! use \<open>declare power_numeral[simp del]\<close> instead!*)\<close>

definition \<open>Big x = x\<close>

lemma [iff]:
  \<open>(2::nat) ^ Big 8  = 256\<close>
  \<open>(2::nat) ^ Big 16 = 65536\<close>
  \<open>(2::nat) ^ Big 32 = 4294967296\<close>
  by (simp add: Big_def)+

lemma [iff]:
  \<open> numeral x < (2::'a) ^ Big n \<longleftrightarrow> numeral x < (2::'a::{numeral,power,ord}) ^ n\<close>
  \<open> 1 < (2::'a) ^ Big n \<longleftrightarrow> 1 < (2::'a::{numeral,power,ord}) ^ n\<close>
  \<open> 0 < (2::'b) ^ Big n \<longleftrightarrow> 0 < (2::'b::{numeral,power,ord,zero}) ^ n\<close>
  \<open> n < 16 \<Longrightarrow> Big n = n \<close>
  unfolding Big_def by simp+

subsubsection \<open>Product\<close>


text \<open>An algorithm of normalizing tuple operations.

Primitive operations:

\<^item> rotL : left rotation
\<^item> rotR : right rotation
\<^item> prod.swap
\<^item> fst, snd
\<^item> apfst, apsnd, map_prod

Composite operations are only combined from the primitive operations and functional composition.
\<open>case_prod\<close> is not allowed (because it mixes operations together and cannot be separated any more,
cause certain operations that could be reduced e.g. \<open>map (apfst f) o zip_list \<equiv> zip_list o apfst f\<close>
cannot be reduced any more).

We apply the following normalization strategy to hope two equivalent sequences of the operations can
be normalized to an identical form.

\<^item> apfst, apsnd, map_prod are aggregated together, and split to each projection when need.
  They are swapped over prod.swap, rotations, down to the left most.
  The reason is, projectors (fst, snd) are always given at the left side, so we hope when the projectors
  meet the apfst, apsnd, map_prod first, their reduction can eliminate irrelevant mappings as early
  as possible.
\<^item> swap, rotation are reduced if possible, i.e. the following 6 rules
    (S for swap, L for L-rotate, R for R-rotate, A B for A o B, rewrites from LHS to RHS)
    L S L S = S R
    S L S L = R S
    S R S = L S L
    R S R = S L S
    L R = id, R L = id

Key facts why this normalization can work are,
1. Below, we only need to consider operations \<open>h = apfst f | apsnd g\<close>, and we split \<open>map_prod f g\<close>
   to \<open>apfst f o apsnd g\<close> and consider them separately.
   Note any \<open>h\<close> can swap over \<open>S\<close>.
2. any operation \<open>h\<close> that can swap over LHS in any of the equation above, can also swap over the RHS
   and result in an identical form.
3. S L S h L, if h can swap over the right L, h can also swap over the left \<open>S L S\<close>
   Similarly for the other rewrites.
4. L S h L, if h can swap over the right L to \<open>h'\<close>, \<open>h'\<close> can also swap over \<open>S R S\<close> from right,
   and results in the identical form with \<open>h\<close> swapping over \<open>L S\<close> from right
It means, swapping any \<open>h\<close> in any order towards the left end, doesn't break the normalization-ability.
The order doesn't matter.

So, any \<open>apfst, apsnd, map_prod\<close> can be swapped to the left most end, if it can.

Now, the sequence only remains \<open>S, L, R\<close>, ... the proof is to be completed

idk, maybe we lost some assumption, like, requiring the first projection of the tuple is always
single-element or a pair but no more nested level.

I am not sure if the normaliza is complete but is terminating.
\<close>

named_theorems prod_opr_norm \<open>normalizations of product operations\<close>

notation map_prod (infixr "\<otimes>\<^sub>f" 56)

(*if C\<^sub>R\<^sub>1 then *)
setup \<open>Sign.mandatory_path "prod"\<close>

definition rotL :: \<open>'a \<times> 'b \<times> 'c \<Rightarrow> ('a \<times> 'b) \<times> 'c\<close>
  where \<open>rotL x = ((fst x, fst (snd x)), snd (snd x))\<close>

definition rotR :: \<open>('a \<times> 'b) \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c\<close>
  where \<open>rotR x = (fst (fst x), snd (fst x), snd x)\<close>

lemma rot[simp]:
  \<open>prod.rotL (a,b,c) = ((a,b),c)\<close>
  \<open>prod.rotR ((a,b),c) = (a,b,c)\<close>
  unfolding prod.rotL_def prod.rotR_def
  by simp_all

lemma rot_rot[simp]:
  \<open>prod.rotL (prod.rotR x) = x\<close>
  \<open>prod.rotR (prod.rotL y) = y\<close>
  unfolding prod.rotL_def prod.rotR_def
  by simp_all

lemma rot_rot_comp[simp]:
  \<open> prod.rotL o prod.rotR = id \<close>
  \<open> prod.rotR o prod.rotL = id \<close>
  unfolding fun_eq_iff
  by simp_all

lemma rot_rot_comp'[simp]:
  \<open> x o prod.rotL o prod.rotR = x \<close>
  \<open> y o prod.rotR o prod.rotL = y \<close>
  unfolding fun_eq_iff
  by simp_all

lemma rot_prj[simp]:
  \<open>fst (fst (prod.rotL x)) = fst x\<close>
  \<open>snd (fst (prod.rotL x)) = fst (snd x)\<close>
  \<open>snd (prod.rotL x) = snd (snd x)\<close>
  \<open>fst (prod.rotL (a, bc)) = (a, fst bc) \<close>
  \<open>snd (snd (prod.rotR y)) = snd y\<close>
  \<open>fst (snd (prod.rotR y)) = snd (fst y)\<close>
  \<open>fst (prod.rotR y) = fst (fst y)\<close>
  \<open>snd (prod.rotR (ab, c)) = (snd ab, c)\<close>
  unfolding prod.rotL_def prod.rotR_def
  by simp_all

lemma rot_prj_comp[simp]:
  \<open>fst o fst o prod.rotL = fst\<close>
  \<open>snd o fst o prod.rotL = fst o snd\<close>
  \<open>snd o prod.rotL = snd o snd\<close>
  \<open>snd o snd o prod.rotR = snd\<close>
  \<open>fst o snd o prod.rotR = snd o fst\<close>
  \<open>fst o prod.rotR = fst o fst\<close>
  unfolding prod.rotL_def prod.rotR_def fun_eq_iff
  by simp_all



lemma ap_rotate[prod_opr_norm]:
  \<open>prod.rotL (apfst f y) = apfst (apfst f) (prod.rotL y)\<close>
  \<open>prod.rotL (apsnd (apfst f) y\<^sub>2) = apfst (apsnd f) (prod.rotL y\<^sub>2)\<close>
  \<open>prod.rotL (apsnd (apsnd f) y\<^sub>3) = apsnd f (prod.rotL y\<^sub>3)\<close>
  \<open>prod.rotR (apfst (apfst f) x) = apfst f (prod.rotR x)\<close>
  \<open>prod.rotR (apsnd f x\<^sub>2) = apsnd (apsnd f) (prod.rotR x\<^sub>2)\<close>
  \<open>prod.rotR (apfst (apsnd f) x\<^sub>3) = apsnd (apfst f) (prod.rotR x\<^sub>3)\<close>
  unfolding prod.rotL_def prod.rotR_def
  by simp_all

lemma ap_rotate_comp[prod_opr_norm]:
  \<open>prod.rotL o apfst f = apfst (apfst f) o prod.rotL\<close>
  \<open>prod.rotL o apsnd (apfst f) = apfst (apsnd f) o prod.rotL\<close>
  \<open>prod.rotL o apsnd (apsnd f) = apsnd f o prod.rotL\<close>
  \<open>prod.rotR o apfst (apfst f) = apfst f o prod.rotR\<close>
  \<open>prod.rotR o apsnd f = apsnd (apsnd f) o prod.rotR\<close>
  \<open>prod.rotR o apfst (apsnd f) = apsnd (apfst f) o prod.rotR\<close>
  unfolding fun_eq_iff
  by (simp_all add: prod.ap_rotate)

lemma ap_rotate_comp'[prod_opr_norm]:
  \<open>x\<^sub>1 o prod.rotL o apfst f = x\<^sub>1 o apfst (apfst f) o prod.rotL\<close>
  \<open>x\<^sub>2 o prod.rotL o apsnd (apfst f) = x\<^sub>2 o apfst (apsnd f) o prod.rotL\<close>
  \<open>x\<^sub>3 o prod.rotL o apsnd (apsnd f) = x\<^sub>3 o apsnd f o prod.rotL\<close>
  \<open>x\<^sub>4 o prod.rotR o apfst (apfst f) = x\<^sub>4 o apfst f o prod.rotR\<close>
  \<open>x\<^sub>5 o prod.rotR o apsnd f = x\<^sub>5 o apsnd (apsnd f) o prod.rotR\<close>
  \<open>x\<^sub>6 o prod.rotR o apfst (apsnd f) = x\<^sub>6 o apsnd (apfst f) o prod.rotR\<close>
  unfolding fun_eq_iff
  by (simp_all add: prod.ap_rotate)


lemma rotate_eq_simp[simp]:
  \<open>((a,b),c) = prod.rotL x \<longleftrightarrow> (a,b,c) = x\<close>
  \<open>(a,b,c) = prod.rotR y \<longleftrightarrow> ((a,b),c) = y\<close>
  unfolding prod.rotL_def prod.rotR_def
  by (clarsimp; rule; clarsimp)+

lemma rotate_eq_ap_simp[simp]:
  \<open>(x, prod.rotL y) = apsnd prod.rotL z \<longleftrightarrow> (x, y) = z\<close>
  by (cases z; cases y; clarsimp)

lemma swap_proj_comp[simp]:
  \<open>fst o prod.swap = snd\<close>
  \<open>snd o prod.swap = fst\<close>
  unfolding fun_eq_iff
  by simp_all

lemma swap_proj_comp'[simp]:
  \<open>x o fst o prod.swap = x o snd\<close>
  \<open>y o snd o prod.swap = y o fst\<close>
  unfolding fun_eq_iff
  by simp_all

lemma swap_ap[prod_opr_norm]:
  \<open>prod.swap (apfst f x) = apsnd f (prod.swap x)\<close>
  \<open>prod.swap (apsnd g x) = apfst g (prod.swap x)\<close>
  by (cases x; simp)+

lemma swap_ap_comp[prod_opr_norm]:
  \<open>prod.swap o apfst f = apsnd f o prod.swap\<close>
  \<open>prod.swap o apsnd g = apfst g o prod.swap\<close>
  unfolding fun_eq_iff
  by (simp_all add: prod.swap_ap)

lemma swap_ap_comp'[prod_opr_norm]:
  \<open>x\<^sub>1 o prod.swap o apfst f = x\<^sub>1 o apsnd f o prod.swap\<close>
  \<open>x\<^sub>2 o prod.swap o apsnd g = x\<^sub>2 o apfst g o prod.swap\<close>
  unfolding fun_eq_iff
  by (simp_all add: prod.swap_ap)

lemma prj_rot_apS_rot[prod_opr_norm]:
  \<open>fst (prod.rotL (apsnd prod.swap (prod.rotR x))) = apfst fst x\<close>
  \<open>snd (prod.rotR (apfst prod.swap (prod.rotL y))) = apsnd snd y\<close>
  by ((cases x; clarsimp),
      (cases y; clarsimp))

lemma prj_rot_apS_rot_comp[prod_opr_norm]:
  \<open>fst \<circ> prod.rotL \<circ> apsnd prod.swap \<circ> prod.rotR = apfst fst\<close>
  \<open>snd \<circ> prod.rotR \<circ> apfst prod.swap \<circ> prod.rotL = apsnd snd\<close>
  unfolding fun_eq_iff
  by simp_all

lemma prj_rot_apS_rot_comp'[prod_opr_norm]:
  \<open>x o fst \<circ> prod.rotL \<circ> apsnd prod.swap \<circ> prod.rotR = x o apfst fst\<close>
  \<open>y o snd \<circ> prod.rotR \<circ> apfst prod.swap \<circ> prod.rotL = y o apsnd snd\<close>
  unfolding fun_eq_iff
  by simp_all

lemma ap_ap[prod_opr_norm]:
  \<open>apfst f (apfst g x) = apfst (f o g) x\<close>
  \<open>apsnd f (apsnd g y) = apsnd (f o g) y\<close>
  by ((cases x; simp), (cases y; simp))

lemma ap_ap_comp[prod_opr_norm]:
  \<open>apfst f o apfst g = apfst (f o g)\<close>
  \<open>apsnd f o apsnd g = apsnd (f o g)\<close>
  unfolding fun_eq_iff
  by simp_all

lemma ap_ap_comp'[prod_opr_norm]:
  \<open>a o apfst f o apfst g = a o apfst (f o g)\<close>
  \<open>b o apsnd f o apsnd g = b o apsnd (f o g)\<close>
  unfolding fun_eq_iff
  by simp_all

setup \<open>Sign.parent_path\<close>

lemma rotate_map_prod[prod_opr_norm]:
  \<open>prod.rotL (map_prod g\<^sub>1 (map_prod g\<^sub>2 g\<^sub>3) x) = map_prod (map_prod g\<^sub>1 g\<^sub>2) g\<^sub>3 (prod.rotL x)\<close>
  \<open>prod.rotR (map_prod (map_prod f\<^sub>1 f\<^sub>2) f\<^sub>3 y) = map_prod f\<^sub>1 (map_prod f\<^sub>2 f\<^sub>3) (prod.rotR y)\<close>
  unfolding prod.rotR_def prod.rotL_def
  by simp_all

lemma rotate_map_prod_comp[prod_opr_norm]:
  \<open>prod.rotL o (g\<^sub>1 \<otimes>\<^sub>f g\<^sub>2 \<otimes>\<^sub>f g\<^sub>3) = ((g\<^sub>1 \<otimes>\<^sub>f g\<^sub>2) \<otimes>\<^sub>f g\<^sub>3) o prod.rotL\<close>
  \<open>prod.rotR o ((f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2) \<otimes>\<^sub>f f\<^sub>3) = (f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2 \<otimes>\<^sub>f f\<^sub>3) o prod.rotR\<close>
  unfolding prod.rotR_def prod.rotL_def fun_eq_iff
  by simp_all

lemma rotate_map_prod_comp'[prod_opr_norm]:
  \<open>g o prod.rotL o (g\<^sub>1 \<otimes>\<^sub>f g\<^sub>2 \<otimes>\<^sub>f g\<^sub>3) = g o ((g\<^sub>1 \<otimes>\<^sub>f g\<^sub>2) \<otimes>\<^sub>f g\<^sub>3) o prod.rotL\<close>
  \<open>f o prod.rotR o ((f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2) \<otimes>\<^sub>f f\<^sub>3) = f o (f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2 \<otimes>\<^sub>f f\<^sub>3) o prod.rotR\<close>
  unfolding prod.rotR_def prod.rotL_def fun_eq_iff
  by simp_all

lemma swap_map_prod[prod_opr_norm]:
  \<open>prod.swap ((f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2) x) = (f\<^sub>2 \<otimes>\<^sub>f f\<^sub>1) (prod.swap x)\<close>
  by (cases x; simp)+

lemma swap_map_prod_comp[prod_opr_norm]:
  \<open>prod.swap o (f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2) = (f\<^sub>2 \<otimes>\<^sub>f f\<^sub>1) o prod.swap\<close>
  unfolding fun_eq_iff
  by clarsimp

lemma swap_map_prod_comp'[prod_opr_norm]:
  \<open>g o prod.swap o (f\<^sub>1 \<otimes>\<^sub>f f\<^sub>2) = g o (f\<^sub>2 \<otimes>\<^sub>f f\<^sub>1) o prod.swap\<close>
  unfolding fun_eq_iff
  by clarsimp


lemma map_prod_eq_apfst_apsnd:
  \<open>map_prod f g = apfst f o apsnd g\<close>
  unfolding fun_eq_iff
  by clarsimp

lemma map_prod_eq_apsnd_apfst:
  \<open>map_prod f g = apsnd g o apfst f\<close>
  unfolding fun_eq_iff
  by clarsimp



lemma map_prod_ap_simp[prod_opr_norm]:
  \<open>map_prod f g (apsnd h x) = map_prod f (g o h) x\<close>
  \<open>apsnd h' (map_prod f g x') = map_prod f (h' o g) x'\<close>
  \<open>map_prod f g (apfst l y) = map_prod (f o l) g y\<close>
  \<open>apfst l' (map_prod f g y') = map_prod (l' o f) g y'\<close>
  by ((cases x; clarsimp),
      (cases x'; clarsimp),
      (cases y; clarsimp),
      (cases y'; clarsimp))

declare map_prod.compositionality[prod_opr_norm]
        map_prod.comp [prod_opr_norm]

lemma map_prod_comp'[prod_opr_norm]:
  \<open>x o f \<otimes>\<^sub>f g \<circ> h \<otimes>\<^sub>f i = x o (f \<circ> h) \<otimes>\<^sub>f (g \<circ> i)\<close>
  unfolding fun_eq_iff
  by clarsimp

lemma map_prod_ap_simp_comp[simp]:
  \<open> (f \<otimes>\<^sub>f g) o apsnd h = (f \<otimes>\<^sub>f (g \<circ> h)) \<close>
  \<open> apsnd h' o (f \<otimes>\<^sub>f g) = f \<otimes>\<^sub>f (h' \<circ> g) \<close>
  \<open> (f \<otimes>\<^sub>f g) o apfst l = (f \<circ> l) \<otimes>\<^sub>f g \<close>
  \<open> apfst l' o (f \<otimes>\<^sub>f g) = (l' \<circ> f) \<otimes>\<^sub>f g \<close>
  by (simp_all add: fun_eq_iff)

lemma map_prod_ap_simp_comp'[simp]:
  \<open> x\<^sub>1 o (f \<otimes>\<^sub>f g) o apsnd h = x\<^sub>1 o (f \<otimes>\<^sub>f (g \<circ> h)) \<close>
  \<open> x\<^sub>2 o apsnd h' o (f \<otimes>\<^sub>f g) = x\<^sub>2 o f \<otimes>\<^sub>f (h' \<circ> g) \<close>
  \<open> x\<^sub>3 o (f \<otimes>\<^sub>f g) o apfst l = x\<^sub>3 o (f \<circ> l) \<otimes>\<^sub>f g \<close>
  \<open> x\<^sub>4 o apfst l' o (f \<otimes>\<^sub>f g) = x\<^sub>4 o (l' \<circ> f) \<otimes>\<^sub>f g \<close>
  by (simp_all add: fun_eq_iff)

lemma swap_comp_swap'[simp]:
  \<open>x o prod.swap \<circ> prod.swap = x\<close>
  unfolding fun_eq_iff
  by simp



subsection \<open>Helper Conversion\<close>

definition \<open>PURE_TOP \<equiv> (\<And>P::prop. PROP P \<Longrightarrow> PROP P)\<close>

lemma PURE_TOP_I[\<phi>reason 1000]: \<open>PROP PURE_TOP\<close> unfolding PURE_TOP_def .

lemma PURE_TOP_imp:
  \<open>(PROP PURE_TOP \<Longrightarrow> PROP P) \<equiv> PROP P\<close> (is \<open>PROP ?LHS \<equiv> PROP ?RHS\<close>)
proof
  assume \<open>PROP ?LHS\<close>
  from this[OF PURE_TOP_I] show \<open>PROP ?RHS\<close> .
next
  assume \<open>PROP ?RHS\<close>
  then show \<open>PROP ?LHS\<close> .
qed

ML_file \<open>library/syntax/helper_conv.ML\<close>

subsection \<open>Helper Simplification\<close>

simproc_setup Funcomp_Lambda (\<open>f o g\<close>) = \<open>fn _ => fn ctxt => fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Fun.comp\<close>, _) $ Abs _ $ _ =>
        SOME (Conv.rewr_conv @{thm' comp_def[folded atomize_eq]} ctm)
     | Const(\<^const_name>\<open>Fun.comp\<close>, _) $ _ $ Abs _ =>
        SOME (Conv.rewr_conv @{thm' comp_def[folded atomize_eq]} ctm)
     | _ => NONE
\<close>

subsection \<open>Helper Isar Commands\<close>

declare [[ML_debugger=false, ML_exception_debugger=false]]

ML_file \<open>library/tools/optional_translation.ML\<close>
ML_file \<open>library/tools/adhoc_overloading.ML\<close>

declare [[ML_debugger, ML_exception_debugger]]


subsection \<open>The Friendly Character\<close>

ML_file \<open>library/tools/the_friendly_character.ML\<close>

definition Friendly_Help :: \<open>text \<Rightarrow> bool\<close> where [iff]: \<open>Friendly_Help _ \<longleftrightarrow> True\<close>

lemma Friendly_Help_I[intro!]: \<open>Friendly_Help ANY\<close> unfolding Friendly_Help_def ..
lemma Friendly_Help_E[elim!]: \<open>Friendly_Help ANY \<Longrightarrow> C \<Longrightarrow> C\<close> .

(*TODO: move this to \<phi>lang_parser so that the help is displayed only when the IDECP ends at that*)

\<phi>reasoner_ML Friendly_Help 1000 (\<open>Friendly_Help _\<close>) = \<open>fn (_, (ctxt,sequent)) =>
 (if Config.get ctxt Phi_The_Friendly_Character.enable
  then let
        val _ $ (_ $ text) = Thm.major_prem_of sequent
        val pretty = Text_Encoding.decode_text_pretty ctxt text
       in Phi_The_Friendly_Character.info ctxt (fn _ => pretty) end
  else ();
  Seq.single (ctxt, @{thm Friendly_Help_I} RS sequent)
 )
\<close>

subsection \<open>General Reasoning Rules\<close>

declare refl[\<phi>reason 1000]

subsubsection \<open>pred_option\<close>

lemma [\<phi>reason 1000]:
  \<open> P x
\<Longrightarrow> pred_option P (Some x)\<close>
  by simp

lemma [\<phi>reason 1000]:
  \<open> pred_option P None\<close>
  by simp

subsection \<open>Some very Early Reasoning\<close>



(*

declare (* disjE[\<phi>inhabitance_rule] *) (*I don't like divergence!*)
        conjE[\<phi>inhabitance_rule]
        set_mult_inhabited[\<phi>inhabitance_rule]
        set_plus_inhabited[\<phi>inhabitance_rule]

lemma [\<phi>inhabitance_rule, elim!]:
  \<open>Inhabited 1 \<Longrightarrow> C \<Longrightarrow> C\<close> .*)

(*TODO:
lemma Membership_E_Inhabitance:
  \<open>x \<in> S \<Longrightarrow> (Inhabited S \<Longrightarrow> C) \<Longrightarrow> C\<close>
  unfolding Inhabited_def by blast*)



subsubsection \<open>Supplementary of Meta-Ball\<close>

lemma [\<phi>reason %meta_ball]:
  \<open> (Q \<Longrightarrow> (\<And>x \<in> S. PROP P x))
\<Longrightarrow> (\<And>x \<in> S \<s>\<u>\<b>\<j> Q. PROP P x)\<close>
  unfolding meta_Ball_def Premise_def Subjection_expn_set
  by (clarsimp simp add: atomize_conj[symmetric] conjunction_imp norm_hhf_eq)

lemma [\<phi>reason %meta_ball]:
  \<open> (Q \<Longrightarrow> \<forall>x \<in> S. P x)
\<Longrightarrow> (\<forall>x \<in> S \<s>\<u>\<b>\<j> Q. P x)\<close>
  unfolding Ball_def Subjection_expn_set
  by simp




subsection \<open>Very Early Mechanism\<close>

\<phi>reasoner_group local = (10000, [10000,10000])
  \<open>local reasoning rules given from the hypothese of a programming context\<close>

subsubsection \<open>Default Attributes in Programming\<close>

text \<open>Registry of default attributes of antecedents in the deductive programming.\<close>

ML_file \<open>library/system/premise_attribute.ML\<close>

paragraph \<open>Configuring Existing Antecedents\<close>

declare [[
  \<phi>premise_attribute? [\<phi>declare] for \<open>PROP _\<close>,
  \<phi>premise_attribute? [\<phi>reason? %local] for \<open>Is_Literal _\<close>,

  \<phi>premise_attribute_ML \<open>fn _ => Thm.declaration_attribute (fn thm => fn ctxt =>
    let val term_A = case Thm.prop_of thm
                       of _ $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ A $ _ ) => A
                        | _ $ (Const(\<^const_name>\<open>Simplify\<close>, _) $ _ $ A $ _ ) => A
        val cterm_A = Context.cases Thm.global_cterm_of Thm.cterm_of ctxt term_A
        val rule = \<^instantiate>\<open>cterm_A and 'a=\<open>Thm.ctyp_of_cterm cterm_A\<close> in
                                  lemma \<open>Is_Literal (cterm_A::'a)\<close> by (simp add: Is_Literal_def)\<close>
     in Phi_Reasoner.add_rule Position.none Phi_Reasoner.NORMAL_LOCAL_CUT' (SOME @{reasoner_group %is_literal})
            ([(Thm.concl_of rule, NONE)], []) NONE [rule] ctxt
    end
    handle MATCH => ctxt
  )\<close> for \<open>Simplify \<phi>mode_literal _ _\<close>
]]


subsection \<open>Convention of Syntax Priority\<close>


text \<open>
\<^item> 10: Labelled, Programming_CurrentConstruction, View_Shift_CurrentConstruction
      PendingConstruction, ToA_Construction, Argument tag
\<^item> 12: View_Shift, Transformation
\<^item> 13: Remains
\<^item> 14: ExSet
\<^item> 15: Comma, Subjection
\<^item> 16: Struct Tag, SYNTHESIS
\<^item> 18: Assertion_Matches
\<^item> 20: \<phi>-type colon
\<close>


(*TODO: Move this*)
end
