theory PhiSem_Mem_C
  imports PhiSem_Mem_Pointer
  abbrevs "<mem>" = "\<m>\<e>\<m>"
      and "<mem-blk>" = "\<m>\<e>\<m>-\<b>\<l>\<k>"
      and "<slice>" = "\<s>\<l>\<i>\<c>\<e>"
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

(* For technical reasons, the memory resource is installed in \<^file>\<open>PhiSem_Mem_Pointer.thy\<close> *)

(*
definition Valid_Mem :: "('TY,'VAL) R_mem set"
  where "Valid_Mem = { Fine h |h. finite (dom h)
                                \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` Well_Type (segidx.layout seg))}"

lemma Valid_Mem_1[simp]: \<open>1 \<in> Valid_Mem\<close>
  unfolding Valid_Mem_def one_fun_def one_fine_def by simp
*)


subsection \<open>Fiction\<close>

declare [[\<phi>trace_reasoning = 0]]

type_synonym mem_fic = \<open>aggregate_path \<Rightarrow> VAL discrete share option\<close> \<comment> \<open>fiction of a single memory object\<close>

fiction_space aggregate_mem =
  aggregate_mem :: \<open>RES.aggregate_mem.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>blk. \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (memblk.layout blk)))\<close>
     (perm_aggregate_mem_fiction RES.aggregate_mem memblk.layout)
  by (standard; simp)


section \<open>Basic \<phi>Types for Semantic Models\<close>


(* subsubsection \<open>Slice Pointer\<close>

text \<open>A limitation of TypPtr is that it cannot point to the end of an array,
  because there is no object exists at the end. To address this, we provide slice pointer which
  can range over a piece of the array including the end.\<close>

definition SlicePtr :: "TY \<Rightarrow> (VAL, logaddr \<times> nat \<times> nat) \<phi>"
  where "SlicePtr TY = (\<lambda>(base,i,len).
    if valid_logaddr base \<and> base \<noteq> 0 \<and> (\<exists>N. logaddr_type base = array N TY \<and> len \<le> N)
        \<and> 0 < MemObj_Size TY \<and> i \<le> len
    then { V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY)) }
    else {})"

lemma SlicePtr_expn[\<phi>expns]:
  \<open>v \<in> ((base, i, len) \<Ztypecolon> SlicePtr TY) \<longleftrightarrow>
      valid_logaddr base \<and> base \<noteq> 0
      \<and> (\<exists>N. logaddr_type base = \<tau>Array N TY \<and> len \<le> N)
      \<and> 0 < MemObj_Size TY \<and> i \<le> len
      \<and> v = V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY))\<close>
  unfolding SlicePtr_def \<phi>Type_def by simp blast

lemma SlicePtr_inhabited[\<phi>reason_elim!,elim!]:
  \<open>Inhabited ((base, i, len) \<Ztypecolon> SlicePtr TY)
\<Longrightarrow> (\<And>N. valid_logaddr base \<Longrightarrow> base \<noteq> 0 \<Longrightarrow> logaddr_type base = \<tau>Array N TY \<Longrightarrow> len \<le> N
          \<Longrightarrow> 0 < MemObj_Size TY \<Longrightarrow> i \<le> len \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def SlicePtr_expn by simp blast

lemma SlicePtr_eqcmp[\<phi>reason on \<open>\<phi>Equal (SlicePtr ?TY) ?c ?eq\<close>]:
    "\<phi>Equal (SlicePtr TY) (\<lambda>x y. fst x = fst y) (\<lambda>(_,i1,_) (_,i2,_). i1 = i2)"
  unfolding \<phi>Equal_def
  apply (clarsimp simp add: \<phi>expns word_of_nat_eq_iff take_bit_nat_def simp del: of_nat_mult)
  subgoal premises for addr i1 n1 i2 N n2 proof -
    note logaddr_storable_in_mem[OF \<open>valid_logaddr addr\<close> \<open>addr \<noteq> 0\<close>,
            unfolded \<open>logaddr_type addr = \<tau>Array N TY\<close>, unfolded memobj_size_arr]
    then have \<open>i1 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
          and \<open>i2 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
      by (meson \<open>i1 \<le> n1\<close> \<open>n1 \<le> N\<close> \<open>i2 \<le> n2\<close> \<open>n2 \<le> N\<close> dual_order.strict_trans2 mult_le_mono1)+
    then show ?thesis
      using \<open>0 < MemObj_Size TY\<close> by fastforce 
  qed
  done

lemma SlicePtr_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> SlicePtr ?TY) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> SlicePtr TY) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (cases x, simp add: \<phi>expns valid_logaddr_def)

*)



subsection \<open>Coercion from Value Spec to Mem Spec\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Mem_Coercion :: \<open>(VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> _" [81] 80)
  where \<open>Mem_Coercion T \<equiv> (o) (to_share o map_option discrete) o Map_of_Val \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Commutativity_Deriver

definition Guided_Mem_Coercion :: \<open>TY \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[_] _" [50,81] 80)
  where \<open>\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T \<equiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T\<close>

(* \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 Mem_Coercion Mem_Coercion Mem_Coercion (\<^emph>) (\<^emph>) T U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close> *)


subsection \<open>Memory Object\<close>

declare [[\<phi>trace_reasoning = 1]]

\<phi>type_def MemBlk :: \<open>memblk \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<m>\<e>\<m>-\<b>\<l>\<k>[_]")
  where \<open>MemBlk blk T \<equiv> FIC.aggregate_mem.\<phi> (blk \<^bold>\<rightarrow> T)\<close>
  deriving Sep_Functor_1

abbreviation Mem :: \<open>logaddr \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<m>\<e>\<m>[_]")
  where \<open>\<m>\<e>\<m>[addr] T \<equiv> \<m>\<e>\<m>-\<b>\<l>\<k>[memaddr.blk addr] (memaddr.index addr \<^bold>\<rightarrow>\<^sub>@ T)\<close>


section \<open>Instructions & Their Specifications\<close>

proc op_load_mem:
  input  \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] (n \<odiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<close>
  requires \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and    \<open>parse_eleidx_input_least1 TY input_index sem_idx idx pidx reject\<close>
    and    \<open>\<phi>Aggregate_Getter idx T U f\<close>
    and    \<open>report_unprocessed_element_index reject\<close>
  output \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] (n \<odiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)\<heavy_comma> f x \<Ztypecolon> \<v>\<a>\<l> U\<close>
  unfolding Guided_Mem_Coercion_def
  including \<phi>sem_type_sat_EIF
\<medium_left_bracket>
  to \<open>OPEN _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v
  apply_rule FIC.aggregate_mem.getter_rule[where u_idx=v and n=n and blk=\<open>memaddr.blk addr\<close> and idx=\<open>memaddr.index addr\<close>]
  \<open>x \<Ztypecolon> MAKE (\<m>\<e>\<m>[addr] (n \<odiv> MAKE (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)))\<close>

  semantic_assert \<open>index_value (memaddr.index addr) (discrete.dest (\<phi>arg.dest \<v>0)) \<in> Well_Type TY\<close>
  semantic_return \<open>index_value (memaddr.index addr) (discrete.dest (\<phi>arg.dest \<v>0)) \<Turnstile> (x \<Ztypecolon> T)\<close>

  apply_rule op_get_aggregate[where input_index=input_index and sem_idx=sem_idx and spec_idx=idx
                                and pidx=pidx and reject=reject]
\<medium_right_bracket> .

proc op_store_mem:
  input  \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U'\<close>
  requires \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
    and    \<open>\<phi>SemType (y \<Ztypecolon> U') TY\<^sub>U\<close>
    and    \<open>parse_eleidx_input_least1 TY input_index sem_idx idx pidx reject\<close>
    and    \<open>is_valid_index_of idx TY TY\<^sub>U\<close>
    and    \<open>\<phi>Aggregate_Mapper idx T T' U U' f\<close>
    and    \<open>report_unprocessed_element_index reject\<close>
  output \<open>f (\<lambda>_. y) x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T')\<close>
  unfolding Guided_Mem_Coercion_def
  including \<phi>sem_type_sat_EIF
\<medium_left_bracket>
  to \<open>OPEN _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  apply_rule FIC.aggregate_mem.getter_rule[where u_idx=v and n=1 and blk=\<open>memaddr.blk addr\<close> and idx=\<open>memaddr.index addr\<close>]

  semantic_assert \<open>index_value (memaddr.index addr) (discrete.dest (\<phi>arg.dest \<v>0)) \<in> Well_Type TY\<close>
  semantic_return \<open>index_value (memaddr.index addr) (discrete.dest (\<phi>arg.dest \<v>0)) \<Turnstile> (x \<Ztypecolon> T)\<close>
  $y
  apply_rule "_op_set_aggregate_"[where TY=TY and TY\<^sub>U=TY\<^sub>U and TY\<^sub>U'=TY\<^sub>U and sem_idx=sem_idx and idx=idx
                                    and pidx=pidx and reject=reject and input_index=input_index]

  semantic_local_value_nochk 

  apply_rule FIC.aggregate_mem.setter_rule[where u_idx=v and idx=\<open>memaddr.index addr\<close>
                                    and v=\<open>\<phi>arg.dest \<v>2\<close> and blk=\<open>memaddr.blk addr\<close>]

  \<open>f (\<lambda>_. y) x \<Ztypecolon> MAKE (\<m>\<e>\<m>[addr] (MAKE (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T')))\<close>

\<medium_right_bracket> .

text \<open>A simplification in the semantics is, we only consider allocation with zero initialization
  (i.e., \<open>calloc\<close> but not \<open>malloc\<close>), which frees us from modelling uninitialized memory state so
  simplifies the system a lot. We can do so because we aim to provide a certified language
  over a subset of C semantics. The absence of non-initialized allocation does not affect the functionality
  but only little performance which we believe worthy against the simplification in reasoning. \<close>

declare [[\<phi>trace_reasoning=2]]

proc op_allocate_mem_1:
  input \<open>Void\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>z \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY \<s>\<u>\<b>\<j> addr. memaddr.index addr = 0\<close>
  unfolding Guided_Mem_Coercion_def
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=TY and v=\<open>the (Zero TY)\<close>]

  \<open>z \<Ztypecolon> MAKE (\<m>\<e>\<m>[memaddr blk 0] (MAKE (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)))\<close>
  
  semantic_return \<open>V_pointer.mk (memaddr (\<phi>arg.dest \<v>1) 0) \<Turnstile> (memaddr blk 0 \<Ztypecolon> Ptr TY)\<close>

\<medium_right_bracket> .
 
proc op_free_mem:
  input \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<close>
  requires \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  premises \<open>memaddr.index addr = 0\<close>
  output \<open>Void\<close>
  unfolding Guided_Mem_Coercion_def
  including \<phi>sem_type_sat_EIF
\<medium_left_bracket>
  to \<open>OPEN _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  apply_rule FIC.aggregate_mem.deallocate_rule[where v=v and blk=\<open>memaddr.blk addr\<close>]

\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 0]]
  
\<phi>type_def Mem_Slice :: \<open>logaddr \<Rightarrow> nat len_intvl \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close>
  where \<open>l \<Ztypecolon> Mem_Slice addr iv T \<equiv> l \<Ztypecolon> \<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv (\<lambda>j. \<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T) \<s>\<u>\<b>\<j> length l = len_intvl.len iv\<close>
    \<comment> \<open>Length is still required because it determines the domain of the \<phi>-type so guides the reasoning\<close>
  deriving Sep_Functor_1
       and Semimodule_NonAssoc
       and \<open>Abstract_Domain T P
        \<Longrightarrow> Abstract_Domain (Mem_Slice addr iv T) (\<lambda>x. length x = len_intvl.len iv \<and> list_all P x) \<close>
       and \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (Mem_Slice addr iv T) (list_all2 eq) \<close>
       and \<open>Identity_Elements\<^sub>I T T\<^sub>D T\<^sub>P
        \<Longrightarrow> Identity_Elements\<^sub>I (Mem_Slice addr iv T) (list_all T\<^sub>D) (\<lambda>x. length x = len_intvl.len iv \<and> list_all T\<^sub>P x) \<close>
       and \<open>Identity_Elements\<^sub>E T T\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E (Mem_Slice addr iv T) (\<lambda>x. length x = len_intvl.len iv \<and> list_all T\<^sub>D x) \<close>
       and Transformation_Functor
       and \<open>Separation_Homo\<^sub>I (Mem_Slice addr iv) (Mem_Slice addr iv) (Mem_Slice addr iv) T U UNIV zip' \<close>
       and Separation_Homo
       and \<open>Semimodule_One\<^sub>I (\<lambda>iv. Mem_Slice addr iv T) (\<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T) \<lbrakk>j:1\<rwpar> (\<lambda>_. True) (\<lambda>x. [x]) (\<lambda>_. True)\<close>
       and \<open>Semimodule_One\<^sub>E (\<lambda>iv. Mem_Slice addr iv T) (\<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T) \<lbrakk>j:1\<rwpar> (\<lambda>l. length l = 1) hd (\<lambda>_. True)\<close>

term \<open>\<big_ast>\<^sub>\<lbrakk>\<^sub>:\<^sub>\<rbrakk>\<^sup>\<phi> iv (\<lambda>j. f j \<^bold>\<rightarrow>\<^sub>@ T)\<close>

thm \<phi>Mul_Quant_Tree.wrap_module_src
thm \<phi>Mul_Quant_Tree.separation_extraction
thm \<phi>Mul_Quant_Tree.Separation_Homo\<^sub>I_Cond
thm \<phi>Mul_Quant_Tree.Separation_Homo\<^sub>E_Cond

thm \<phi>Mul_Quant_Tree.wrap_module_src


lemma
  \<open> \<g>\<u>\<a>\<r>\<d> (\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> y' ! (i - len_intvl.start iv) = fst y \<and> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv \<longrightarrow>
              ((fst x, w) \<Ztypecolon> ks \<^bold>\<rightarrow>\<^sub>@ T \<^emph>[C\<^sub>W] W \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y \<Ztypecolon> U \<^emph>[C\<^sub>R] R \<w>\<i>\<t>\<h> P))
       \<and>\<^sub>\<r> \<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> len_intvl.start iv \<le> i \<and> i < len_intvl.start iv + len_intvl.len iv
\<Longrightarrow> \<p>\<r>\<e>\<m>\<i>\<s>\<e> length y' = len_intvl.len iv \<and> y' ! (i - len_intvl.start iv) = fst y
\<Longrightarrow> \<s>\<i>\<m>\<p>\<l>\<i>\<f>\<y> (j, len, j', len') : (len_intvl.start iv, i - len_intvl.start iv,
                                 i + 1, len_intvl.start iv + len_intvl.len iv - i - 1)
\<Longrightarrow> ((snd x) \<Ztypecolon> \<half_blkcirc>[C\<^sub>W'] W') = (
        (w, take len y', drop (len+1) y') \<Ztypecolon> \<half_blkcirc>[C\<^sub>W] W \<^emph> \<half_blkcirc>[True] (\<phi>Mul_Quant_Tree f \<lbrakk>j:len\<rwpar> U) \<^emph> \<half_blkcirc>[True] (\<phi>Mul_Quant_Tree f \<lbrakk>j':len'\<rwpar> U)) @action \<A>merge
\<Longrightarrow> x \<Ztypecolon> (f i # ks) \<^bold>\<rightarrow>\<^sub>@ T \<^emph>[C\<^sub>W'] f i \<^bold>\<rightarrow>\<^sub># W' \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> (y', snd y) \<Ztypecolon> \<phi>Mul_Quant_Tree f iv U \<^emph>[C\<^sub>R] f i \<^bold>\<rightarrow>\<^sub># R \<w>\<i>\<t>\<h> P \<close>
  unfolding Action_Tag_def \<r>Guard_def Ant_Seq_imp
  (*apply (simp add: cond_prod_transformation_rewr,
         simp add: \<phi>Prod_expn'' \<phi>Prod_expn' \<phi>Some_\<phi>Prod[symmetric] Cond_\<phi>Prod_expn_\<phi>Some) *)
  \<medium_left_bracket> premises Tr and _ and _ and _ and []
    note [[\<phi>trace_reasoning = 2]]
    ;;
      thm Tr
      thm apply_Separation_Homo\<^sub>I_Cond[OF \<phi>MapAt_L.Separation_Homo\<^sub>I_Cond]
    ;; apply_rule apply_Separation_Homo\<^sub>I_Cond[OF \<phi>MapAt_L.Separation_Homo\<^sub>I_Cond]
    thm \<phi>MapAt_L.Separation_Homo\<^sub>I_Cond
    ;; apply_rule apply_Semimodule_SAssoc\<^sub>E[OF \<phi>MapAt_L.Semimodule_Scalar_Assoc\<^sub>E, where s=\<open>[f i]\<close> and t=\<open>ks\<close>,
            unfolded times_list_def append_Cons append_Nil]

      thm Tr
      thm 
      thm \<phi>MapAt_L.scalar_transformation
      thm \<phi>MapAt_L.scalar_transformation[OF Tr]

      thm \<phi>MapAt_L.Semimodule_Scalar_Assoc\<^sub>E
      thm apply_Semimodule_SAssoc\<^sub>E[OF \<phi>MapAt_L.Semimodule_Scalar_Assoc\<^sub>E, where s=\<open>[f i]\<close> and t=\<open>ks\<close>,
            unfolded times_list_def append_Cons append_Nil]

      thm times_list_def






term \<open>Semimodule_One\<^sub>E (\<lambda>iv. \<phi>Mul_Quant_Tree f iv T) (f j \<^bold>\<rightarrow>\<^sub># T) \<lbrakk>j:1\<rwpar> (\<lambda>l. length l = 1) hd (\<lambda>_. True)\<close>

term \<open>Identity_Elements\<^sub>E T T\<^sub>D
        \<Longrightarrow> Identity_Elements\<^sub>E (\<phi>Mul_Quant_Tree f iv T) (\<lambda>x. length x = len_intvl.len iv \<and> list_all T\<^sub>D x) \<close>


term \<open>Identity_Elements\<^sub>I T T\<^sub>D T\<^sub>P
        \<Longrightarrow> Identity_Elements\<^sub>I (\<phi>Mul_Quant_Tree f iv T) (list_all T\<^sub>D) (\<lambda>x. length x = len_intvl.len iv \<and> list_all T\<^sub>P x) \<close>

term \<open>Object_Equiv T eq
        \<Longrightarrow> Object_Equiv (\<phi>Mul_Quant_Tree f iv T) (list_all2 eq) \<close>







consts Mem_Slice_synt :: \<open>logaddr \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a list) \<phi>\<close> ("\<s>\<l>\<i>\<c>\<e>[_ : _ : _]")

translations "\<s>\<l>\<i>\<c>\<e>[addr : start : len]" == "CONST Mem_Slice addr \<lbrakk>start : len\<rwpar>"

thm Mem_Slice.wrap_module_src


lemma
  \<open>hd (drop (j - start) (take (Suc (j - start)) y)) = y ! (j - start)\<close>
  apply simp


ML \<open>@{term \<open>\<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T\<close>}\<close>

lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[addr : start : len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet>\<^sub>a j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[addr : j + 1 : start + len - j - 1] T\<heavy_comma>
             take (j - start) y \<Ztypecolon> \<s>\<l>\<i>\<c>\<e>[addr : start : j - start] T\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by (insert \<phi>, auto_sledgehammer)

  term \<open>snd ((prod.swap \<circ> (\<lambda>x. (drop (len_intvl.len \<lbrakk>start : j - start\<rwpar>) x, take (len_intvl.len \<lbrakk>start : j - start\<rwpar>) x))) (fst (y, undefined)))\<close>

lemma
  \<open>\<close>

term \<open> \<phi>Aggregate_Getter idx T U f
   \<Longrightarrow> (x \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) = (r \<Ztypecolon> R) * (f x \<Ztypecolon> idx \<^bold>\<rightarrow>\<^sub>@ \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U)\<close>


end