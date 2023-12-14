theory PhiSem_Aggregate_Tuple
  imports PhiSem_Aggregate_Base
  abbrevs "<tup>" = "\<t>\<u>\<p>"
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype tuple_ty =
  tup     :: \<open>'self list\<close>

debt_axiomatization T_tup :: \<open>TY list type_entry\<close>
  where tuple_ty_ax: \<open>tuple_ty TY_CONS_OF T_tup\<close>

interpretation tuple_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_tup using tuple_ty_ax .

(*TODO: intergrate automatic hidding into the automation command*)
hide_fact tuple_ty_ax

definition \<open>semty_tup \<equiv> tup.mk\<close>

paragraph \<open>Syntax\<close>

abbreviation semty_tup_empty ("\<t>\<u>\<p> {}")
  where \<open>semty_tup_empty \<equiv> semty_tup []\<close>

notation semty_tup_empty ("tup{}")
     and semty_tup_empty ("T{}")
     and semty_tup_empty ("\<t>\<u>\<p> { }")

syntax "\<phi>_tuple_" :: \<open>logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_")

       "_semty_tup" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("tup{_}" [50] 999)
       "_semty_tup" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("T{_}" [50] 999)
       "_semty_tup" :: \<open>\<phi>_tuple_args_ \<Rightarrow> logic\<close> ("\<t>\<u>\<p> {_}" [50] 999)

parse_translation \<open>[
  (\<^syntax_const>\<open>_semty_tup\<close>, fn ctxt => fn [args] =>
    \<^Const>\<open>semty_tup\<close> $
    fold_rev (fn (Const(\<^syntax_const>\<open>\<phi>_tuple_\<close>, _) $ T) => (fn X => \<^Const>\<open>list.Cons \<^Type>\<open>TY\<close>\<close> $ T $ X)
               | _ => error "Bad Syntax")
             (strip_phi_tuple_args args) \<^Const>\<open>list.Nil \<^Type>\<open>TY\<close>\<close>)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>semty_tup\<close>, fn ctxt => fn [args] =>
  let fun strip_list (Const(\<^const_syntax>\<open>list.Cons\<close>, _) $ T $ L)
            = T :: strip_list L
        | strip_list (Const(\<^const_syntax>\<open>list.Nil\<close>, _)) = []
      fun assemble [T] =
            Const(\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $ (Const(\<^syntax_const>\<open>\<phi>_tuple_\<close>, dummyT) $ T)
        | assemble (T::L) =
            Const(\<^syntax_const>\<open>_\<phi>tuple_args\<close>, dummyT)
              $ (Const(\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $ (Const(\<^syntax_const>\<open>\<phi>_tuple_\<close>, dummyT) $ T))
              $ (assemble L)
      fun assemble' [] = Const(\<^const_syntax>\<open>semty_tup_empty\<close>, dummyT)
        | assemble' L = Const(\<^syntax_const>\<open>_semty_tup\<close>, dummyT) $ assemble L
   in assemble' (strip_list args)
  end)
]\<close>

(*
  "_semty_tup_arg0 (_semty_tup_arg s x)" <= "CONST list.Cons (_MK_SYMBOL_ s) x CONST fmempty"
  "_semty_tup_arg0 (_semty_tup_arg s x)" == "CONST list.Cons s x CONST fmempty"
  "_semty_tup_args (_semty_tup_arg s x) r" <= "CONST fmupd (_MK_SYMBOL_ s) x r"
  "_semty_tup_args (_semty_tup_arg s x) r" == "CONST fmupd s x r"
*)



subsubsection \<open>Value\<close>

virtual_datatype tuple_val =
  V_tup     :: \<open>'self list\<close>

debt_axiomatization V_tup :: \<open>VAL list value_entry\<close>
  where tuple_val_ax: \<open>tuple_val VAL_CONS_OF V_tup\<close>

interpretation tuple_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_tup
  using tuple_val_ax .

hide_fact tuple_val_ax

subsection \<open>Semantics\<close>

debt_axiomatization
        WT_tup[simp]: \<open>Well_Type (semty_tup ts)  = { V_tup.mk vs       |vs. list_all2 (\<lambda> t v. v \<in> Well_Type t) ts vs }\<close>
  and   zero_tup[simp]: \<open>Zero (semty_tup Ts)     = map_option V_tup.mk (those (map Zero Ts))\<close>
  and   V_tup_sep_disj_R[simp]: \<open>V_tup.mk l1 ## vl2 \<longleftrightarrow> (\<exists>l2. vl2 = V_tup.mk l2)\<close>
  and   V_tup_sep_disj_L[simp]: \<open>vl1 ## V_tup.mk l2 \<longleftrightarrow> (\<exists>l1. vl1 = V_tup.mk l1)\<close>
  and   V_tup_mult    : \<open>V_tup.mk l1 * V_tup.mk l2 = V_tup.mk (l2 @ l1)\<close>
  and   idx_step_type_tup [eval_aggregate_path] : \<open>i < length tys \<Longrightarrow> idx_step_type (AgIdx_N i) (semty_tup tys) = tys!i \<close>
  and   valid_idx_step_tup[eval_aggregate_path] : \<open>valid_idx_step (semty_tup tys) j \<longleftrightarrow> j \<in> {AgIdx_N i | i. i < length tys}\<close>
  and   idx_step_value_tup[eval_aggregate_path] : \<open>idx_step_value (AgIdx_N i) (V_tup.mk vs) = vs!i\<close>
  and   idx_step_mod_value_tup : \<open>idx_step_mod_value (AgIdx_N i) f (V_tup.mk vs) = V_tup.mk (vs[i := f (vs!i)])\<close>

lemma V_tup_mult_cons:
  \<open>NO_MATCH vs ([]::VAL list) \<Longrightarrow> V_tup.mk (v#vs) = V_tup.mk vs * V_tup.mk [v]\<close>
  using V_tup_mult by simp

lemma list_all_replicate:
  \<open>list_all P (replicate n x) \<longleftrightarrow> n = 0 \<or> P x\<close>
  by (induct n; simp; blast)

primrec semantic_tuple_constructor
  where \<open>semantic_tuple_constructor [] = V_tup.mk []\<close>
      | \<open>semantic_tuple_constructor (v#R) =
            V_tup.mk (v # V_tup.dest (semantic_tuple_constructor R))\<close>

(* lemma Valid_Type_\<tau>Tuple[simp]:
  \<open>Valid_Type (semty_tup Ts) \<longleftrightarrow> list_all Valid_Type Ts\<close>
  unfolding Inhabited_def
  by (simp; induct Ts; simp add: list_all2_Cons1) *)

section \<open>\<phi>Type\<close>

subsection \<open>Empty Tuple\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Empty_Tuple :: \<open>(VAL, unit) \<phi>\<close>
  where \<open>x \<Ztypecolon> Empty_Tuple \<equiv> V_tup.mk [] \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality
       and \<open>\<phi>SemType (x \<Ztypecolon> Empty_Tuple) (semty_tup [])\<close>
       and \<open>Semantic_Zero_Val (semty_tup []) Empty_Tuple ()\<close>
       and \<open>Is_Aggregate Empty_Tuple\<close>

\<phi>adhoc_overloading \<phi>_Empty_Tuple_sugar Empty_Tuple

subsection \<open>Field\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Tuple_Field :: "(VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>"
  where \<open>Tuple_Field T \<equiv> (\<lambda>v. V_tup.mk [v]) \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Functionality
       and \<open>\<phi>SemType (x \<Ztypecolon> T) TY
        \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> Tuple_Field T) (semty_tup [TY])\<close>
       and \<open>Semantic_Zero_Val TY T x
        \<Longrightarrow> Semantic_Zero_Val (semty_tup [TY]) (Tuple_Field T) x \<close>
       and \<open>Is_Aggregate (Tuple_Field T)\<close>

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_tuple_ X))" \<rightleftharpoons> "CONST Tuple_Field X"

lemma Empty_Tuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> Empty_Tuple \<^emph> \<lbrace> T \<rbrace>) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  \<open>((a,()) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> Empty_Tuple) = (a \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding BI_eq_iff
  by ((clarsimp; rule; clarsimp simp add: V_tup_mult),
      (metis V_tup_mult append_Nil),
      (clarsimp; rule; clarsimp simp add: V_tup_mult),
      metis V_tup_mult append.right_neutral)

lemma Tuple_Field_zeros [\<phi>reason %semantic_zero_val_cut]:
  \<open> Semantic_Zero_Val ty T x
\<Longrightarrow> Semantic_Zero_Val (semty_tup tys) Ts xs
\<Longrightarrow> Semantic_Zero_Val (semty_tup (ty#tys)) (\<lbrace> T \<rbrace> \<^emph> Ts) (x,xs) \<close>
  unfolding Semantic_Zero_Val_def
  by (clarsimp simp add: V_tup_mult_cons image_iff, insert V_tup_sep_disj_L, blast)

declare [[\<phi>trace_reasoning = 1]]

lemma Tuple_Field_semtys[\<phi>reason %\<phi>sem_type_cut]:
  \<open> \<phi>SemType (fst x_xs \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (snd x_xs \<Ztypecolon> Ts) (semty_tup TYs)
\<Longrightarrow> \<phi>SemType (x_xs \<Ztypecolon> (\<lbrace> T \<rbrace> \<^emph> Ts)) (semty_tup (TY#TYs))\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp, metis V_tup_mult append.left_neutral append_Cons list.rel_inject(2))


section \<open>Reasoning\<close>

subsection \<open>Show validity of an index for a type\<close>

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> is_valid_step_idx_of (AgIdx_N 0) (semty_tup (Ty # Tys)) Ty \<close>
  unfolding is_valid_step_idx_of_def Premise_def
  by (simp add: valid_idx_step_tup idx_step_type_tup)

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> is_valid_step_idx_of (AgIdx_N i) (semty_tup Tys) RET
\<Longrightarrow> is_valid_step_idx_of (AgIdx_N (Suc i)) (semty_tup (Ty # Tys)) RET \<close>
  unfolding is_valid_step_idx_of_def Premise_def
  by (simp add: valid_idx_step_tup idx_step_type_tup)


subsection \<open>Aggregate Access\<close>

lemma idx_step_value_V_tup_suc:
  \<open>idx_step_value (AgIdx_N (Suc i)) (V_tup.mk (va # vs)) = idx_step_value (AgIdx_N i) (V_tup.mk vs)\<close>
  by (simp add: idx_step_value_tup)

lemma idx_step_mod_value_V_tup_suc:
  \<open>idx_step_mod_value (AgIdx_N (Suc i)) g (V_tup.mk (va # vs)) = idx_step_mod_value (AgIdx_N i) g (V_tup.mk vs) * V_tup.mk [va]\<close>
  by (metis NO_MATCH_I V_tup_mult_cons idx_step_mod_value_tup list_update_code(3) nth_Cons_Suc)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter (AgIdx_N i # idx) X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N (Suc i) # idx) (\<lbrace> T \<rbrace> \<^emph> X) Y (f o snd)\<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_value_V_tup_suc)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter idx X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N 0 # idx) \<lbrace> X \<rbrace> Y f \<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Getter idx X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_N 0 # idx) (\<lbrace> X \<rbrace> \<^emph> R) Y (f o fst) \<close>
  unfolding \<phi>Aggregate_Getter_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper (AgIdx_N i # idx) X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N (Suc i) # idx) (\<lbrace> T \<rbrace> \<^emph> X) (\<lbrace> T \<rbrace> \<^emph> X') Y Y' (apsnd o f) \<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_mod_value_V_tup_suc,
      metis V_tup_sep_disj_R idx_step_mod_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N 0 # idx) \<lbrace> X \<rbrace> \<lbrace> X' \<rbrace> Y Y' f \<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_mod_value_tup)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_N 0 # idx) (\<lbrace> X \<rbrace> \<^emph> R) (\<lbrace> X' \<rbrace> \<^emph> R) Y Y' (apfst o f) \<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: V_tup_mult idx_step_mod_value_tup,
      metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L)


lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Constructor_Synth semantic_tuple_constructor (() \<Ztypecolon> \<circle>) (semty_tup []) (() \<Ztypecolon> \<lbrace> \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def
  by clarsimp

lemma [\<phi>reason %aggregate_access+20]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth semantic_tuple_constructor (x \<Ztypecolon> List_Item T) (semty_tup [TY]) (x \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def \<phi>SemType_def
  by (clarsimp; blast)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth semantic_tuple_constructor
        (xs \<Ztypecolon> Ts) (semty_tup Tys) (r \<Ztypecolon> Tr)
\<Longrightarrow> \<phi>Aggregate_Constructor_Synth semantic_tuple_constructor
        ((x,xs) \<Ztypecolon> List_Item T \<^emph> Ts) (semty_tup (TY # Tys)) ((x, r) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> Tr)\<close>
  unfolding \<phi>Aggregate_Constructor_Synth_def \<phi>SemType_def
  by (clarsimp simp: V_tup_mult_cons times_list_def,
      metis NO_MATCH_def V_tup.dest_mk V_tup_mult_cons V_tup_sep_disj_L list.rel_intros(2))

lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Constructor semantic_tuple_constructor [] (semty_tup []) (() \<Ztypecolon> \<lbrace> \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_tuple_constructor_def
  by clarsimp

lemma [\<phi>reason %aggregate_access+20]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor semantic_tuple_constructor [v] (semty_tup [TY]) (x \<Ztypecolon> \<lbrace> T \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_tuple_constructor_def \<phi>SemType_def
  by (cases v; clarsimp; blast)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor semantic_tuple_constructor vR (semty_tup Tys) (r \<Ztypecolon> Tr)
\<Longrightarrow> \<phi>Aggregate_Constructor semantic_tuple_constructor (v # vR) (semty_tup (TY # Tys)) ((x, r) \<Ztypecolon> \<lbrace> T \<rbrace> \<^emph> Tr)\<close>
  unfolding \<phi>Aggregate_Constructor_def \<phi>SemType_def
  by (cases v; clarsimp; metis NO_MATCH_def V_tup_mult_cons V_tup_sep_disj_L)

setup \<open>Context.theory_map (
  Generic_Element_Access.Agg_Constructors.add 0 (fn (kind, args, (ctxt,sequent)) =>
    if kind = "" andalso forall (fn ((NONE,_),[_]) => true | _ => false) args
    then let val args' = map (fn (_,[rule]) => Phi_Local_Value.get_raw_val_in_rule rule) args
          in SOME (ctxt, \<^cterm>\<open>semantic_tuple_constructor\<close>, args')
         end
    else NONE
))\<close>

subsection \<open>Synthesis\<close>

\<phi>reasoner_group \<phi>synthesis_ag_T = (%\<phi>synthesis_ag, [%\<phi>synthesis_ag, %\<phi>synthesis_ag]) in \<phi>synthesis_ag
  \<open>for tuple\<close>

declare synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> T \<rbrace> \<^emph> U\<close> for T U,
         \<phi>reason %\<phi>synthesis_ag_T
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. ?x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> ?T \<rbrace> \<^emph> ?U \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>]

        synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> T \<rbrace>\<close> for T,
         \<phi>reason %\<phi>synthesis_ag_T
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. ?x \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> ?T \<rbrace> \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>]

        synthesis_construct_aggregate_\<phi>app
        [where T=\<open>\<lbrace> \<rbrace>\<close>,
         \<phi>reason %\<phi>synthesis_ag_T
             for \<open>\<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>\<r>\<e>\<t>. () \<Ztypecolon> \<v>\<a>\<l>[\<r>\<e>\<t>] \<lbrace> \<rbrace> \<r>\<e>\<m>\<a>\<i>\<n>\<s> _ \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> _ @action synthesis\<close>]



end