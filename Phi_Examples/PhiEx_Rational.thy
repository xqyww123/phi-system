theory PhiEx_Rational
  imports Phi_Semantics.PhiSem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
begin

\<phi>reasoner_group \<phi>Rational = (100,[0,9999]) \<open>derived reasoning rules of Linked_Lst\<close>

declare [[recording_timing_of_semantic_operation = true,
         \<phi>LPR_collect_statistics derivation start,
         collect_reasoner_statistics \<phi>Rational start]]

\<phi>type_def \<phi>Rational :: \<open>(VAL, rat) \<phi>\<close> ("\<rat>")
  where \<open>x \<Ztypecolon> \<phi>Rational \<equiv> (n,d) \<Ztypecolon> \<lbrace> num: \<int>, den: \<int> \<rbrace> \<s>\<u>\<b>\<j> n d. of_int n / of_int d = x \<and> d \<noteq> 0\<close>
  deriving Basic
       and \<open>Object_Equiv \<rat> (=)\<close>

ML \<open>Phi_Reasoner.clear_utilization_statistics_of_group \<^theory> (the (snd @{reasoner_group %\<phi>Rational})) "derivation"\<close>

declare [[collect_reasoner_statistics \<phi>Rational stop,
          \<phi>LPR_collect_statistics derivation stop,
          \<phi>LPR_collect_statistics program start,
          collecting_subgoal_statistics,
          \<phi>async_proof = true]]

ML \<open>PLPR_Statistics.reset_utilization_statistics_all ()\<close>


ML \<open>fun report_utilization statistic_groups reasoner_groups =
  let open Pretty
      val statistics = Phi_Reasoner.utilization_of_groups_in_all_theories
          (Context.Theory \<^theory>) (map (the o snd) reasoner_groups) statistic_groups
        |> filter (fn (_, i) => i > 0)
   in (length statistics, Integer.sum (map snd statistics))
  end
\<close>

ML \<open>report_utilization ["program"] [@{reasoner_group %Field}, @{reasoner_group %Array},
        @{reasoner_group %\<phi>MapAt}, @{reasoner_group %\<phi>MapAt_L}, @{reasoner_group %\<phi>Some},
        @{reasoner_group %Mem_Coercion}, @{reasoner_group %\<phi>Share},
        @{reasoner_group %Resource_Space},
        @{reasoner_group %Var}, @{reasoner_group %MemBlk},
        @{reasoner_group %\<phi>Mul_Quant_Tree},
        @{reasoner_group %\<phi>Rational} ] \<close>


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


ML \<open>fun report_utilization statistic_groups reasoner_groups =
  let open Pretty
      val statistics = Phi_Reasoner.utilization_of_groups_in_all_theories
          (Context.Theory \<^theory>) (map (the o snd) reasoner_groups) statistic_groups
        |> filter (fn (_, i) => i > 0)
   in (length statistics, Integer.sum (map snd statistics))
  end
\<close>

ML \<open>report_utilization ["program"] [@{reasoner_group %Field}, @{reasoner_group %Array},
        @{reasoner_group %\<phi>MapAt}, @{reasoner_group %\<phi>MapAt_L}, @{reasoner_group %\<phi>Some},
        @{reasoner_group %Mem_Coercion}, @{reasoner_group %\<phi>Share},
        @{reasoner_group %Resource_Space},
        @{reasoner_group %Var}, @{reasoner_group %MemBlk},
        @{reasoner_group %\<phi>Mul_Quant_Tree},
        @{reasoner_group %\<phi>Rational} ] \<close>


end