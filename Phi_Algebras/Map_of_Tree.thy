theory Map_of_Tree
  imports Main Algebras
begin

section \<open>Map Representation of a Tree\<close>

text \<open>This section presents a representation of tree using the mapping from path to value,
    of type \<^typ>\<open>'key list \<Rightarrow> 'val\<close>.
  It implements the hierarchical algebra and supports for permission algebra.

  Basic operations include `push_map` and `pull_map` which put a sub-tree onto certain location
    and fetch a sub-tree at certain location respectively.

  In this representation, the indexes near the root locate at the left side of the list, e.g.,
  \<open>[a,b,c] \<^enum>\<^sub>m D\<close> characterizes tree \<open>Root \<rightarrow> a \<rightarrow> b \<rightarrow> c \<rightarrow> D\<close>.
\<close>

(* subsection \<open>Preliminary\<close>

primrec subtract_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where \<open>subtract_prefix l' (h#l) =
      (case l' of h' # l'' \<Rightarrow> if h = h' then subtract_prefix l'' l else undefined
                | [] \<Rightarrow> undefined)\<close>
  | \<open>subtract_prefix l [] = l\<close>

lemma subtract_prefix[simp]:
  \<open>subtract_prefix (ha#la) (hb#lb) = (if ha = hb then subtract_prefix la lb else undefined)\<close>
  \<open>subtract_prefix l [] = l\<close>
  by simp_all

declare subtract_prefix.simps[simp del]

lemma subtract_prefix_app[simp]:
  \<open>subtract_prefix (xs @ zs) xs = zs\<close>
  by (induct xs; simp)

lemma prefix_subtract_prefix[simp]:
  \<open> prefix xs ys
\<Longrightarrow> xs @ (subtract_prefix ys xs) = ys \<close>
  unfolding prefix_def by clarsimp

"HOL-Library.Sublist" *)

subsection \<open>Push a map to a location\<close>

definition push_map :: \<open>'a list \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> ('a list \<Rightarrow> 'b::one)\<close> (infixr "\<^enum>\<^sub>m" 75)
  where \<open>push_map idx f = (\<lambda>x. if take (length idx) x = idx then f (drop (length idx) x) else 1 )\<close>

lemma push_map_unit[simp]:
  \<open>push_map ia (1(ib := x)) = 1(ia@ib := x)\<close>
  unfolding push_map_def
  by (simp add: fun_eq_iff, metis append_eq_conv_conj)

lemma push_map_push_map:
  \<open>push_map ia (push_map ib f) = push_map (ia@ib) f\<close>
  unfolding push_map_def fun_eq_iff
  by (smt (verit, ccfv_threshold) add.commute append_eq_append_conv append_eq_conv_conj drop_drop length_append take_add take_drop)

lemma push_map_distrib_mult:
  \<open>push_map idx f * push_map idx g = push_map idx (f * g)\<close>
  for f :: \<open>'a list \<Rightarrow> 'b::monoid_mult\<close>
  unfolding push_map_def fun_eq_iff times_fun_def by simp

lemma push_map_distrib_map_add:
  \<open>push_map idx (f ++ g) = push_map idx f ++ push_map idx g\<close>
  unfolding push_map_def fun_eq_iff map_add_def by simp

lemma push_map_sep_disj[simp]:
  \<open>push_map idx a ## push_map idx b \<longleftrightarrow> a ## b\<close>
  for a :: \<open>'k list \<Rightarrow> 'v::sep_magma_1\<close>
  unfolding sep_disj_fun_def push_map_def apply simp
  by (metis append_eq_conv_conj)

lemma push_map_distrib_sep_mult:
  \<open> f ## g
\<Longrightarrow> push_map idx f * push_map idx g = push_map idx (f * g)\<close>
  for f :: \<open>'a list \<Rightarrow> 'b::sep_monoid\<close>
  unfolding push_map_def fun_eq_iff times_fun_def by simp


lemma push_map_eq_1[simp]:
  \<open>push_map idx f = 1 \<longleftrightarrow> f = 1\<close>
  unfolding push_map_def fun_eq_iff by simp (metis append_eq_conv_conj)

lemma push_map_1[simp]:
  \<open>push_map idx 1 = 1\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_mult_nil[simp]:
  \<open>push_map [] f = f\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma share_push_map:
  \<open>share n (push_map idx f) = push_map idx (share n f)\<close>
  for f :: \<open>'a list \<Rightarrow> 'b :: share_one\<close>
  unfolding push_map_def fun_eq_iff share_fun_def by simp

lemma (in homo_one) push_map_homo:
  \<open>\<phi> o (push_map idx f) = push_map idx (\<phi> o f)\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_to_share:
  \<open>push_map idx (to_share o f) = to_share o (push_map idx f)\<close>
  unfolding push_map_def fun_eq_iff by simp

lemma push_map_dom_eq[simp]:
  \<open>dom (push_map idx f) = dom (push_map idx g) \<longleftrightarrow> dom f = dom g\<close>
  unfolding dom_def fun_eq_iff push_map_def set_eq_iff apply simp
  by (metis (full_types) append_eq_conv_conj)


subsection \<open>Pull a map at a location\<close>

definition pull_map :: \<open>'a list \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> ('a list \<Rightarrow> 'b)\<close>
  where \<open>pull_map idx f = (\<lambda>x. f (idx@x))\<close>

lemma pull_map_unit[simp]:
  \<open>pull_map ia (1((ia@ib) := x)) = 1(ib := x)\<close>
  unfolding pull_map_def by (simp add: fun_eq_iff)

lemma pull_push_map[simp]:
  \<open>pull_map idx (push_map idx f) = f\<close>
  unfolding pull_map_def push_map_def fun_eq_iff by simp

lemma push_pull_map:
  \<open>push_map idx (pull_map idx f) \<subseteq>\<^sub>m f\<close>
  unfolding pull_map_def push_map_def map_le_def dom_def
  by simp (metis append_take_drop_id)

lemma pull_map_1[simp]:
  \<open>pull_map idx 1 = 1\<close> 
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_0[simp]:
  \<open>pull_map idx 0 = 0\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_nil[simp]:
  \<open>pull_map [] f = f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_pull_map[simp]:
  \<open>pull_map a (pull_map b f) = pull_map (b@a) f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_cons:
  \<open>pull_map a (pull_map [b] f) = pull_map (b#a) f\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_funcomp:
  \<open>\<phi> 1 = 1 \<Longrightarrow> \<phi> o (pull_map idx f) = pull_map idx (\<phi> o f)\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_homo_mult:
  \<open>pull_map idx (f * g) = pull_map idx f * pull_map idx g\<close>
  unfolding pull_map_def fun_eq_iff
  by (simp add: times_fun)

lemma pull_map_to_share:
  \<open>pull_map idx (to_share o f) = to_share o (pull_map idx f)\<close>
  unfolding pull_map_def fun_eq_iff by simp

lemma pull_map_share:
  \<open>pull_map idx (share n f) = share n (pull_map idx f)\<close>
  unfolding pull_map_def fun_eq_iff share_fun_def by simp

lemma pull_map_sep_disj[simp]:
  \<open>f ## g \<Longrightarrow> pull_map idx f ## pull_map idx g\<close>
  unfolding pull_map_def sep_disj_fun_def by simp


subsection \<open>Helpers\<close>

subsubsection \<open>For Trees of Numeric Path\<close>

definition nnode :: \<open>(nat list \<Rightarrow> 'b) list \<Rightarrow> nat list \<Rightarrow> 'b::one\<close>
  \<comment> \<open>A tree node of children L\<close>
  where \<open>nnode L = (\<lambda>idx. case idx of i#idx' \<Rightarrow> (if i < length L then (L!i) idx' else 1) | _ \<Rightarrow> 1)\<close>

lemma share_nnode:
  \<open>share n (nnode L) = nnode (map (share n) L)\<close>
  for L :: \<open>(nat list \<Rightarrow> 'a::share_one) list\<close>
  unfolding nnode_def fun_eq_iff by (simp add: share_fun_def split: list.split)

lemma pull_map_node:
  \<open>pull_map (i#idx) (nnode L) = (if i < length L then pull_map idx (L!i) else 1)\<close>
  unfolding nnode_def pull_map_def fun_eq_iff by simp


(*
TODO

subsubsection \<open>Extract & Contract from higher-order function\<close>

definition contract_map :: \<open>('k \<Rightarrow> 'k list \<Rightarrow> ('v::one)) \<Rightarrow> 'k list \<Rightarrow> 'v\<close>
  where \<open>contract_map f = (\<lambda>ks. case ks of [] \<Rightarrow> 1 | h#r \<Rightarrow> f h r)\<close>

definition extract_map :: \<open>('k list \<Rightarrow> ('v::one)) \<Rightarrow> 'k \<Rightarrow> 'k list \<Rightarrow> 'v\<close>
  where \<open>extract_map f = (\<lambda>h r. f (h#r))\<close>


lemma
  \<open>extract_map (contract_map f) = f\<close>
  unfolding extract_map_def contract_map_def fun_eq_iff
  by (clarsimp)

lemma
  \<open>extract_map f h = pull_map [h] f\<close>
  unfolding pull_map_def extract_map_def fun_eq_iff
  by (clarsimp; case_tac x; clarsimp)
*)

end