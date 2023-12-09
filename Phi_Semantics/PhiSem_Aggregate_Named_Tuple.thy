theory PhiSem_Aggregate_Named_Tuple
  imports PhiSem_Aggregate_Base
  abbrevs "<struct>" = "\<s>\<t>\<r>\<u>\<c>\<t>"
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

subsubsection \<open>Type\<close>

virtual_datatype named_tuple_ty =
  named_tup     :: \<open>(symbol, 'self) fmap\<close>

debt_axiomatization T_named_tup :: \<open>(symbol, TY) fmap type_entry\<close>
  where named_tuple_ty_ax: \<open>named_tuple_ty TY_CONS_OF T_named_tup\<close>

interpretation named_tuple_ty TY_CONS_OF \<open>TYPE(TY_N)\<close> \<open>TYPE(TY)\<close> T_named_tup
  using named_tuple_ty_ax .

(*TODO: intergrate automatic hidding into the automation command*)
hide_fact named_tuple_ty_ax

definition \<open>semty_ntup \<equiv> named_tup.mk\<close>

paragraph \<open>Syntax\<close>

abbreviation "semty_ntup_empty" ("\<s>\<t>\<r>\<u>\<c>\<t> {}")
  where \<open>semty_ntup_empty \<equiv> semty_ntup fmempty\<close>

notation semty_ntup_empty ("struct{}")
     and semty_ntup_empty ("S{}")
     and semty_ntup_empty ("\<s>\<t>\<r>\<u>\<c>\<t> { }")

nonterminal semty_ntup_args and semty_ntup_arg

syntax "semty_ntup_arg" :: \<open>\<phi>_symbol_ \<Rightarrow> logic \<Rightarrow> semty_ntup_arg\<close> ("_: _")
       "semty_ntup_arg0" :: \<open>semty_ntup_arg \<Rightarrow> semty_ntup_args\<close> ("_")
       "semty_ntup_args" :: \<open>semty_ntup_arg \<Rightarrow> semty_ntup_args \<Rightarrow> semty_ntup_args\<close> ("_, _")

       "_semty_ntup" :: \<open>semty_ntup_args \<Rightarrow> logic\<close> ("struct{_}" [50] 999)
       "_semty_ntup" :: \<open>semty_ntup_args \<Rightarrow> logic\<close> ("S{_}" [50] 999)
       "_semty_ntup" :: \<open>semty_ntup_args \<Rightarrow> logic\<close> ("\<s>\<t>\<r>\<u>\<c>\<t> {_}" [50] 999)

parse_translation \<open>[
  (\<^syntax_const>\<open>_semty_ntup\<close>, fn ctxt => fn [args] =>
    let fun strip_args (Const(\<^syntax_const>\<open>semty_ntup_args\<close>, _) $ x $ L)
              = x :: strip_args L
          | strip_args (Const(\<^syntax_const>\<open>semty_ntup_arg0\<close>, _) $ x) = [x]
          | strip_args _ = error "Bad Syntax"
     in \<^Const>\<open>semty_ntup\<close> $
        fold_rev (fn (Const(\<^syntax_const>\<open>semty_ntup_arg\<close>, _) $ s $ T) => (fn X =>
                        \<^Const>\<open>fmupd \<^Type>\<open>symbol\<close> \<^Type>\<open>TY\<close>\<close> $ s $ T $ X)
                   | X => error "Bad Syntax")
                 (strip_args args) \<^Const>\<open>fmempty \<^Type>\<open>symbol\<close> \<^Type>\<open>TY\<close>\<close>
    end)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>semty_ntup\<close>, fn ctxt => fn [args] =>
  let fun strip_fmupd (Const(\<^const_syntax>\<open>fmupd\<close>, _) $ s $ v $ L)
            = (s,v) :: strip_fmupd L
        | strip_fmupd (Const(\<^const_syntax>\<open>fmempty\<close>, _)) = []
      fun pass_sym (Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ X) = Phi_Tool_Symbol.print X
        | pass_sym X = X
      fun assemble [(s,v)] =
            Const(\<^syntax_const>\<open>semty_ntup_arg0\<close>, dummyT) $ (Const(\<^syntax_const>\<open>semty_ntup_arg\<close>, dummyT) $ pass_sym s $ v)
        | assemble ((s,v)::L) =
            Const(\<^syntax_const>\<open>semty_ntup_args\<close>, dummyT)
              $ (Const(\<^syntax_const>\<open>semty_ntup_arg\<close>, dummyT) $ pass_sym s $ v)
              $ (assemble L)
      fun assemble' [] = Const(\<^const_syntax>\<open>semty_ntup_empty\<close>, dummyT)
        | assemble' L = Const(\<^syntax_const>\<open>_semty_ntup\<close>, dummyT) $ assemble L
   in assemble' (strip_fmupd args)
  end)
]\<close>

(*examples:

term \<open>\<s>\<t>\<r>\<u>\<c>\<t> {a: A, b: B}\<close>


*)

subsubsection \<open>Value\<close>

virtual_datatype named_tuple_val =
  V_named_tup   :: \<open>(symbol, 'self) fmap\<close>

debt_axiomatization V_named_tup :: \<open>(symbol, VAL) fmap value_entry\<close>
  where named_tuple_val_ax: \<open>named_tuple_val VAL_CONS_OF V_named_tup\<close>

interpretation named_tuple_val VAL_CONS_OF \<open>TYPE(VAL_N)\<close> \<open>TYPE(VAL)\<close> V_named_tup
  using named_tuple_val_ax .

hide_fact named_tuple_val_ax

(* abbreviation \<open>struct \<equiv> named_tup.mk\<close> *)

(*TODO: syntax*)
(* term \<open>struct {name: asd, nam2: TT}\<close> *)


subsection \<open>Semantics\<close>

debt_axiomatization
        WT_named_tup[simp]:
            \<open>Well_Type (semty_ntup Ts)  = { V_named_tup.mk vs |vs. fmrel (\<lambda> t v. v \<in> Well_Type t) Ts vs }\<close>
  and   zero_named_tup[simp]:
            \<open>Zero (semty_ntup Ts) = (if fmpred (\<lambda>_ t. Zero t \<noteq> None) Ts
                                     then Some (V_named_tup.mk (fmmap (the o Zero) Ts))
                                     else None)\<close>
  and   V_named_tup_sep_disj_R:
            \<open>V_named_tup.mk f1 ## vf2 \<Longrightarrow> (\<exists>f2. vf2 = V_named_tup.mk f2)\<close>
  and   V_named_tup_sep_disj_L:
            \<open>vf1 ## V_named_tup.mk f2 \<Longrightarrow> (\<exists>f1. vf1 = V_named_tup.mk f1)\<close>
  and   V_named_tup_sep_disj:
            \<open>V_named_tup.mk f1 ## V_named_tup.mk f2 \<longleftrightarrow> (fmdom f1 |\<inter>| fmdom f2 = {||})\<close>
  and   V_named_tup_mult:
            \<open>V_named_tup.mk f1 * V_named_tup.mk f2 = V_named_tup.mk (f1 ++\<^sub>f f2)\<close>
  and   idx_step_type_tup [eval_aggregate_path]:
            \<open>s |\<in>| fmdom Ts \<Longrightarrow> idx_step_type (AgIdx_S s) (semty_ntup Ts) = the (fmlookup Ts s)\<close>
  and   valid_idx_step_named_tup[eval_aggregate_path]:
            \<open>valid_idx_step (semty_ntup Ts) j \<longleftrightarrow> j \<in> {AgIdx_S s | s. s |\<in>| fmdom Ts }\<close>
  and   idx_step_value_named_tup[eval_aggregate_path]:
            \<open>idx_step_value (AgIdx_S s) (V_named_tup.mk vs) = the (fmlookup vs s)\<close>
  and   idx_step_mod_value_named_tup:
            \<open>idx_step_mod_value (AgIdx_S s) f (V_named_tup.mk vs) = V_named_tup.mk (fmupd s (f (the (fmlookup vs s))) vs)\<close>

lemma V_named_tup_mult_cons:
  \<open> NO_MATCH fmempty y
\<Longrightarrow> V_named_tup.mk y * V_named_tup.mk (fmupd s x fmempty) = V_named_tup.mk (fmupd s x y)\<close>
  by (simp add: V_named_tup_mult)

lemma idx_step_mod_value_named_tupl_cons:
  \<open> s \<noteq> s'
\<Longrightarrow> idx_step_mod_value (AgIdx_S s') f (V_named_tup.mk (fmupd s v vs))
      = idx_step_mod_value (AgIdx_S s') f (V_named_tup.mk vs) * V_named_tup.mk (fmupd s v fmempty)\<close>
  unfolding idx_step_mod_value_named_tup
  by (simp add: V_named_tup_mult_cons fmupd_reorder_neq)

lemma idx_step_mod_value_named_tupl_cons':
  \<open> NO_MATCH fmempty vs
\<Longrightarrow> idx_step_mod_value (AgIdx_S s) f (V_named_tup.mk (fmupd s v vs))
      = V_named_tup.mk vs * idx_step_mod_value (AgIdx_S s) f (V_named_tup.mk (fmupd s v fmempty)) \<close>
  unfolding idx_step_mod_value_named_tup
  by (simp add: V_named_tup_mult_cons fmupd_reorder_neq)

primrec semantic_named_tuple_constructor
  where \<open>semantic_named_tuple_constructor syms [] = V_named_tup.mk fmempty\<close>
      | \<open>semantic_named_tuple_constructor syms (v#R) =
            V_named_tup.mk (fmupd (hd syms) (\<phi>arg.dest v)
                (V_named_tup.dest (semantic_named_tuple_constructor (tl syms) R)))\<close>


section \<open>\<phi>Type\<close>

subsection \<open>Empty Tuple\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Empty_Named_Tuple :: \<open>(VAL, unit) \<phi>\<close>
  where \<open>x \<Ztypecolon> Empty_Named_Tuple \<equiv> V_named_tup.mk fmempty \<Ztypecolon> Itself\<close>
  deriving Basic
       and Functionality
       and \<open>\<phi>SemType (x \<Ztypecolon> Empty_Named_Tuple) (semty_ntup fmempty)\<close>
       and \<open>Semantic_Zero_Val (semty_ntup fmempty) Empty_Named_Tuple ()\<close>
       and \<open>Is_Aggregate Empty_Named_Tuple\<close>

\<phi>adhoc_overloading \<phi>_Empty_Tuple_sugar Empty_Named_Tuple


subsection \<open>Field\<close>

\<phi>type_def Named_Tuple_Field :: "symbol \<Rightarrow> (VAL, 'a) \<phi> \<Rightarrow> (VAL, 'a) \<phi>"
  where \<open>Named_Tuple_Field s T \<equiv> (\<lambda>v. V_named_tup.mk (fmupd s v fmempty)) \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Functionality
       and \<open>Is_Aggregate (Named_Tuple_Field s T)\<close>

subsubsection \<open>Syntax\<close>

syntax "\<phi>_named_tuple_" :: \<open>\<phi>_symbol_ \<Rightarrow> logic \<Rightarrow> \<phi>_tuple_arg_\<close> ("_: _")

translations
  "_\<phi>Tuple (_\<phi>tuple_arg (\<phi>_named_tuple_ s X))" => "\<phi>_named_tuple_ s X"

parse_translation \<open>[
  (\<^syntax_const>\<open>\<phi>_named_tuple_\<close>, fn ctxt => fn [sym,T] =>
      Const(\<^const_name>\<open>Named_Tuple_Field\<close>, dummyT)
          $ sym
          $ T)
]\<close>

print_translation \<open>[
  (\<^const_syntax>\<open>Named_Tuple_Field\<close>, fn ctxt => fn [sym,T] =>
      Const (\<^syntax_const>\<open>_\<phi>Tuple\<close>, dummyT) $
        (Const (\<^syntax_const>\<open>_\<phi>tuple_arg\<close>, dummyT) $
           (Const (\<^syntax_const>\<open>\<phi>_named_tuple_\<close>, dummyT)
              $ (case sym of Const(\<^const_syntax>\<open>mk_symbol\<close>, _) $ id => Phi_Tool_Symbol.print id
                           | _ => sym)
              $ T)))
]\<close>

subsubsection \<open>Properties\<close>

let_\<phi>type Named_Tuple_Field
  deriving \<open> \<phi>SemType (x \<Ztypecolon> T) TY
         \<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>) (semty_ntup (fmupd s TY fmempty))\<close>
       and \<open> Semantic_Zero_Val ty T x
         \<Longrightarrow> Semantic_Zero_Val (semty_ntup (fmupd s ty fmempty)) \<lbrace> SYMBOL_VAR(s): T \<rbrace> x \<close>

lemma Empty_Tuple_reduce[simp]:
  \<open>(((),a) \<Ztypecolon> Empty_Named_Tuple \<^emph> \<lbrace> SYMBOL_VAR(s): T \<rbrace>) = (a \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>)\<close>
  \<open>((a,()) \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> Empty_Named_Tuple) = (a \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>)\<close>
  unfolding BI_eq_iff
  by ((clarsimp; rule; clarsimp simp add: V_named_tup_mult V_named_tup_sep_disj),
      blast,
      metis V_named_tup_mult V_named_tup_sep_disj fmadd_empty(2) fmdom'_restrict_fset_precise fmdom_empty fmrestrict_fset_null,
      (clarsimp; rule; clarsimp simp add: V_named_tup_mult V_named_tup_sep_disj),
      blast,
      metis V_named_tup_mult V_named_tup_sep_disj fmadd_empty(1) fmdom'_restrict_fset_precise fmdom_empty fmrestrict_fset_empty)

lemma Tuple_Field_zeros [\<phi>reason %semantic_zero_val_cut]:
  \<open> s |\<notin>| fmdom tys
\<Longrightarrow> Semantic_Zero_Val ty T x
\<Longrightarrow> Semantic_Zero_Val (semty_ntup tys) Ts xs
\<Longrightarrow> Semantic_Zero_Val (semty_ntup (fmupd s ty tys)) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> Ts) (x,xs) \<close>
  unfolding Semantic_Zero_Val_def
  apply (clarsimp; cases \<open>fmpred (\<lambda>_ t. \<exists>y. Zero t = Some y) tys\<close>;
     auto simp add: inj_image_mem_iff fmmap_fmupd
     V_named_tup_mult_cons[where s=s and y=\<open>fmmap (the \<circ> Zero) tys\<close>, symmetric])
  subgoal for x'
    by (rule exI[where x=\<open>V_named_tup.mk (fmmap (the \<circ> Zero) tys)\<close>],
        rule exI[where x=\<open>V_named_tup.mk (fmupd s x' fmempty)\<close>],
        auto simp add: V_named_tup_sep_disj) .

lemma Tuple_Field_semty[\<phi>reason %\<phi>sem_type_cut]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>) (semty_ntup (fmupd s TY fmempty)) \<close>
  unfolding \<phi>SemType_def subset_iff
  by clarsimp blast

lemma Tuple_Field_semtys[\<phi>reason %\<phi>sem_type_cut]:
  \<open> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>SemType (xs \<Ztypecolon> Ts) (semty_ntup TYs)
\<Longrightarrow> \<phi>SemType ((x,xs) \<Ztypecolon> (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> Ts)) (semty_ntup (fmupd s TY TYs))\<close>
  unfolding \<phi>SemType_def subset_iff
  by (clarsimp; metis V_named_tup_mult fmadd_empty(2) fmadd_fmupd fmrel_upd)


section \<open>Reasoning\<close>

subsection \<open>Semantics Related\<close>

lemma [\<phi>reason %chk_sem_ele_idx+20]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s = s'
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s') (semty_ntup (fmupd s TY Tys)) TY \<close>
  unfolding \<r>Guard_def Premise_def is_valid_step_idx_of_def
  by (clarsimp simp add: valid_idx_step_named_tup idx_step_type_tup)

lemma [\<phi>reason %chk_sem_ele_idx]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s \<noteq> s'
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s') (semty_ntup Tys) RET
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s') (semty_ntup (fmupd s TY Tys)) RET \<close>
  unfolding \<r>Guard_def Premise_def is_valid_step_idx_of_def
  by (clarsimp simp add: valid_idx_step_named_tup idx_step_type_tup)

lemma [\<phi>reason %chk_sem_ele_idx+20]:
  \<open> FAIL TEXT(s \<open>is not a field of the named tuple\<close>)
\<Longrightarrow> is_valid_step_idx_of (AgIdx_S s) (semty_ntup fmempty) RET \<close>
  unfolding \<r>Guard_def Premise_def FAIL_def
  by blast


subsection \<open>General\<close>

lemma [\<phi>reason 2000]:
  \<open> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s \<noteq> s'
\<Longrightarrow> s |\<notin>| fmdom R
\<Longrightarrow> s |\<notin>| fmdom (fmupd s' v R)\<close>
  for s :: symbol
  unfolding Premise_def
  by simp

lemma [\<phi>reason 1200]:
  \<open> s |\<notin>| fmdom fmempty \<close>
  by simp

subsection \<open>Index\<close>

lemma [\<phi>reason %aggregate_access]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' \<noteq> s
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) X Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X) Y (f o snd)\<close>
  unfolding \<phi>Aggregate_Getter_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp, metis V_named_tup_mult V_named_tup_sep_disj_L fmadd_empty(2) fmadd_fmupd fmupd_lookup idx_step_value_named_tup)

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> \<phi>Aggregate_Getter idx T Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X) Y (f o fst)\<close>
  unfolding \<phi>Aggregate_Getter_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp, metis V_named_tup_mult V_named_tup_sep_disj_L fmadd_fmupd fmupd_lookup idx_step_value_named_tup option.sel)

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> \<phi>Aggregate_Getter idx T Y f
\<Longrightarrow> \<phi>Aggregate_Getter (AgIdx_S s' # idx) \<lbrace> SYMBOL_VAR(s): T \<rbrace> Y f\<close>
  unfolding \<phi>Aggregate_Getter_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def
  by (clarsimp, metis fmupd_lookup idx_step_value_named_tup option.sel)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' \<noteq> s
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X) (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> X') Y Y' (apsnd o f)\<close>
  unfolding \<phi>Aggregate_Mapper_def \<r>Guard_def Premise_def \<phi>Type_Mapping_def
  apply clarsimp
  subgoal premises prems for g g' a b c' v' proof -
    obtain c'f where c'f: \<open>c' = V_named_tup.mk c'f\<close> using V_named_tup_sep_disj_L[OF \<open>c' ## _\<close>] by blast
    show ?thesis
      by (insert prems, simp add: c'f V_named_tup_mult_cons idx_step_mod_value_named_tupl_cons,
          rule exI[where x=\<open>idx_step_mod_value (AgIdx_S s') (index_mod_value idx g) (V_named_tup.mk c'f)\<close>],
          rule exI[where x=\<open>V_named_tup.mk (fmupd s v' fmempty)\<close>],
          simp add: V_named_tup_sep_disj, rule,
          blast,
          simp add: idx_step_mod_value_named_tup V_named_tup_sep_disj)
  qed .

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) (\<lbrace> SYMBOL_VAR(s): X \<rbrace> \<^emph> R) (\<lbrace> SYMBOL_VAR(s): X' \<rbrace> \<^emph> R) Y Y' (apfst o f)\<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  apply clarsimp
  subgoal premises prems for g g' a b c' v' proof -
    obtain c'f where c'f: \<open>c' = V_named_tup.mk c'f\<close> using V_named_tup_sep_disj_L[OF \<open>c' ## _\<close>] by blast
    show ?thesis
      by (insert prems, simp add: c'f V_named_tup_mult_cons idx_step_mod_value_named_tupl_cons' \<r>Guard_def Premise_def,
          metis V_named_tup_sep_disj fmdom_fmupd fmupd_idem fmupd_lookup idx_step_mod_value_named_tup option.sel)
  qed .

lemma [\<phi>reason %aggregate_access+1]:
  \<open> \<g>\<u>\<a>\<r>\<d> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> s' = s
\<Longrightarrow> \<phi>Aggregate_Mapper idx X X' Y Y' f
\<Longrightarrow> \<phi>Aggregate_Mapper (AgIdx_S s' # idx) \<lbrace> SYMBOL_VAR(s): X \<rbrace> \<lbrace> SYMBOL_VAR(s): X' \<rbrace> Y Y' f\<close>
  unfolding \<phi>Aggregate_Mapper_def \<phi>Type_Mapping_def
  by (clarsimp simp add: \<r>Guard_def Premise_def, metis fmupd_idem fmupd_lookup idx_step_mod_value_named_tup option.sel)

lemma [\<phi>reason %aggregate_access]:
  \<open>\<phi>Aggregate_Constructor (semantic_named_tuple_constructor []) [] (semty_ntup fmempty) (() \<Ztypecolon> \<lbrace> \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_named_tuple_constructor_def \<phi>Type_Mapping_def
  by clarsimp

lemma [\<phi>reason %aggregate_access+20]:
  \<open> \<phi>arg.dest v \<in> (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_named_tuple_constructor [s]) [v]
          (semty_ntup (fmupd s TY fmempty)) (x \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace>)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_named_tuple_constructor_def \<phi>SemType_def
  by (clarsimp, metis Satisfaction_def fmempty_transfer fmrel_upd)

lemma [\<phi>reason %aggregate_access]:
  \<open> \<phi>arg.dest v \<Turnstile> (x \<Ztypecolon> T)
\<Longrightarrow> \<phi>SemType (x \<Ztypecolon> T) TY
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_named_tuple_constructor sR) vR (semty_ntup TyR) (r \<Ztypecolon> R)
\<Longrightarrow> s |\<notin>| fmdom TyR
\<Longrightarrow> \<phi>Aggregate_Constructor (semantic_named_tuple_constructor (s # sR)) (v # vR)
          (semty_ntup (fmupd s TY TyR)) ((x, r) \<Ztypecolon> \<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> R)\<close>
  unfolding \<phi>Aggregate_Constructor_def semantic_named_tuple_constructor_def \<phi>SemType_def
  apply (clarsimp simp: V_named_tup_mult_cons[symmetric]; rule)
  subgoal for vs
    by (rule exI[where x=\<open>V_named_tup.mk vs\<close>], rule exI[where x=\<open>V_named_tup.mk (fmupd s (\<phi>arg.dest v) fmempty)\<close>],
        simp add: V_named_tup_sep_disj , insert fmrel_fmdom_eq, blast)
  using V_named_tup_mult by auto
  
setup \<open>Context.theory_map (
  Generic_Element_Access.Agg_Constructors.add 0 (fn (kind, args, (ctxt,sequent)) =>
    if kind = "" andalso forall (fn ((SOME _, _),[_]) => true | _ => false) args
    then let val args' = map (fn (_,[rule]) => Phi_Local_Value.get_raw_val_in_rule rule) args
             val symbols = map (fn ((SOME s, _),_) => Phi_Tool_Symbol.mk_symbol s) args
                        |> HOLogic.mk_list \<^typ>\<open>symbol\<close>
             val ctor = Thm.cterm_of ctxt \<^Const>\<open>semantic_named_tuple_constructor for symbols\<close>
          in SOME (ctxt, ctor, args')
         end
    else NONE
))\<close>

subsection \<open>Auxiliary\<close>

subsubsection \<open>Is_Named_Tuple\<close>

definition Is_Named_Tuple :: \<open>(VAL, 'x) \<phi> \<Rightarrow> symbol fset \<Rightarrow> bool\<close>
  where \<open>Is_Named_Tuple T Fields = (\<forall>x c. c \<Turnstile> (x \<Ztypecolon> T) \<longrightarrow> (\<exists>vf. c = V_named_tup.mk vf \<and> fmdom vf = Fields))\<close>

\<phi>reasoner_group Is_Named_Tuple = (1000, [1000,1200]) for \<open>Is_Named_Tuple T Fields\<close>
  \<open>chekcs whether \<open>T\<close> is a named tuple\<close>

declare [[
  \<phi>reason_default_pattern \<open>Is_Named_Tuple ?T _\<close> \<Rightarrow> \<open>Is_Named_Tuple ?T _\<close> (100),
  \<phi>default_reasoner_group \<open>Is_Named_Tuple _ _\<close> : %Is_Named_Tuple (100)
]]

lemma Is_Named_Tuple_sing[\<phi>reason add]:
  \<open>Is_Named_Tuple \<lbrace> SYMBOL_VAR(s): T \<rbrace> {|s|}\<close>
  unfolding Is_Named_Tuple_def
  by clarsimp

lemma Is_Named_Tuple_comp[\<phi>reason add]:
  \<open> Is_Named_Tuple U S
\<Longrightarrow> Is_Named_Tuple (\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> U) (finsert s S) \<close>
  unfolding Is_Named_Tuple_def
  by (clarsimp, metis NO_MATCH_def V_named_tup_mult_cons fmdom_fmupd)


end