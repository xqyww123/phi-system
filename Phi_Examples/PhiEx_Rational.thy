theory PhiEx_Rational
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

declare [[recording_timing_of_semantic_operation = true,
         \<phi>LPR_collect_statistics derivation start]]

\<phi>type_def \<phi>Rational :: \<open>(VAL, rat) \<phi>\<close> ("\<rat>")
  where \<open>x \<Ztypecolon> \<phi>Rational \<equiv> (n,d) \<Ztypecolon> \<lbrace> num: \<int>, den: \<int> \<rbrace> \<s>\<u>\<b>\<j> n d. of_int n / of_int d = x \<and> d \<noteq> 0\<close>
  deriving Abstract_Domain\<^sub>L (*Basic
       and \<open>Object_Equiv \<rat> (=)\<close>*)


declare [[\<phi>LPR_collect_statistics derivation stop,
          \<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics,
          \<phi>async_proof = true]]

proc rat_add:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 + q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 to \<open>OPEN _ _\<close> ;;
  val q2 \<leftarrow> $q2 to \<open>OPEN _ _\<close> ;;
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> den + $q2 \<tribullet> num * $q1 \<tribullet> den,
    den: $q1 \<tribullet> den * $q2 \<tribullet> den \<rbrace>
  \<open>MAKE _ \<rat>\<close>
\<medium_right_bracket> .

proc rat_sub:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 - q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 to \<open>OPEN _ _\<close> ;;
  val q2 \<leftarrow> $q2 to \<open>OPEN _ _\<close> ;;
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> den - $q2 \<tribullet> num * $q1 \<tribullet> den,
    den: $q1 \<tribullet> den * $q2 \<tribullet> den \<rbrace>
  \<open>MAKE _ \<rat>\<close>
\<medium_right_bracket> .

proc rat_mul:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  output \<open>q1 * q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 to \<open>OPEN _ _\<close> ;;
  val q2 \<leftarrow> $q2 to \<open>OPEN _ _\<close> ;;
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> num,
    den: $q1 \<tribullet> den * $q2 \<tribullet> den \<rbrace>
  \<open>MAKE _ \<rat>\<close>
\<medium_right_bracket> .

proc rat_div:
  input \<open>q1 \<Ztypecolon> \<v>\<a>\<l> \<rat> \<heavy_comma> q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
  premises \<open>q2 \<noteq> 0\<close>
  output \<open>q1 / q2 \<Ztypecolon> \<v>\<a>\<l> \<rat>\<close>
\<medium_left_bracket>  
  val q1 \<leftarrow> $q1 to \<open>OPEN _ _\<close> ;;
  val q2 \<leftarrow> $q2 to \<open>OPEN _ _\<close> ;;
  \<lbrace> num: $q1 \<tribullet> num * $q2 \<tribullet> den,
    den: $q1 \<tribullet> den * $q2 \<tribullet> num \<rbrace>
  \<open>MAKE _ \<rat>\<close>
\<medium_right_bracket> .

ML \<open>length (rev (Phi_Syntax.semantic_operations (Thm.prop_of @{thm' rat_div_def})))\<close>

declare [[\<phi>LPR_collect_statistics program stop,
          collecting_subgoal_statistics = false,
          \<phi>async_proof,
          recording_timing_of_semantic_operation = false]]

end