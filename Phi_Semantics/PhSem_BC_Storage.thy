theory PhSem_BC_Storage
  imports PhSem_MoV PhSm_Addr
  abbrevs "<storage>" = "\<s>\<t>\<o>\<r>\<a>\<g>\<e>"
begin

section \<open>Semantics\<close>

type_synonym contract = block

setup \<open>Sign.mandatory_path "RES"\<close>

type_synonym storage = \<open>contract \<rightharpoonup> VAL discrete\<close>

setup \<open>Sign.parent_path\<close>

resource_space storage =
  storage :: \<open>{h::RES.storage. finite (dom h) \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` discrete ` Well_Type (block.layout seg))}\<close>
  (MoV_res \<open>id :: VAL \<Rightarrow> VAL\<close> \<open>block.layout\<close>)
  by (standard; simp)

type_synonym contract_state = \<open>aggregate_path \<Rightarrow> VAL discrete share option\<close>

fiction_space storage =
  storage :: \<open>RES.storage.basic_fiction \<Zcomp>
              \<F>_pointwise (\<lambda>blk.
                  \<F>_functional (MovI.Rep_of_Val_ins (block.layout blk)) (MovI.Rep_of_Val_ins_dom (block.layout blk)) \<Zcomp>
                  \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (block.layout blk)))\<close>
     (perm_MoV_fiction RES.storage \<open>id :: VAL \<Rightarrow> VAL\<close> block.layout Null)
  by (standard, auto simp add: MovI.Rep_of_Val_ins_def BI_eq_iff)

\<phi>type_def Storage :: \<open>contract \<Rightarrow> (contract_state,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<s>\<t>\<o>\<r>\<a>\<g>\<e>[_]")
  where \<open>x \<Ztypecolon> Storage contract T \<equiv> x \<Ztypecolon> FIC.storage.\<phi> (contract \<^bold>\<rightarrow> T) \<s>\<u>\<b>\<j> contract \<noteq> Null\<close>
  deriving Sep_Functor_1

text \<open>\<s>\<t>\<o>\<r>\<a>\<g>\<e>\<close>

end