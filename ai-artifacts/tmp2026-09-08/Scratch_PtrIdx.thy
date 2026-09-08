theory Scratch_PtrIdx
  imports Phi_Semantics.PhiSem_C
begin

text \<open>Experiment: can a slice pointer be indexed with a negative literal?
  Round 1 showed: in the \<phi>-language \<open>-\<close> is only infix and prefix negation \<open>~\<close> has no
  overload on \<open>\<nat>(\<int'>)\<close> (the type a bare literal gets); and a negative literal of type
  \<open>\<int>(\<int'>)\<close> cannot be synthesised because the width of \<open>int_t\<close> is abstract, so its two's
  complement \<open>2 ^ LENGTH(int_t) - 1\<close> is not a literal.  This round uses a concrete width.\<close>

proc control_add_positive:
  input  \<open>i \<Ztypecolon> \<val> \<slice>-\<ptr>[addr:LEN] \<int'>\<heavy_comma>
          l \<Ztypecolon> \<mem>[addr] \<slice>[i+1,1] \<nat>(\<int'>)\<close>
  premises \<open>i + 2 \<le> LEN\<close>
  output \<open>l \<Ztypecolon> \<mem>[addr] \<slice>[i+1,1] \<nat>(\<int'>)\<heavy_comma>
          l ! 0 \<Ztypecolon> \<val> \<nat>(\<int'>)\<close>
\<medium_left_bracket>
  *(i + 1)
\<medium_right_bracket> .

proc control_bracket_positive:
  input  \<open>i \<Ztypecolon> \<val> \<slice>-\<ptr>[addr:LEN] \<int'>\<heavy_comma>
          l \<Ztypecolon> \<mem>[addr] \<slice>[i+1,1] \<nat>(\<int'>)\<close>
  premises \<open>i + 2 \<le> LEN\<close>
  output \<open>l \<Ztypecolon> \<mem>[addr] \<slice>[i+1,1] \<nat>(\<int'>)\<heavy_comma>
          l ! 0 \<Ztypecolon> \<val> \<nat>(\<int'>)\<close>
\<medium_left_bracket>
  i[1]
\<medium_right_bracket> .

proc test_add_negative_int32:
  input  \<open>i \<Ztypecolon> \<val> \<slice>-\<ptr>[addr:LEN] \<int'>\<heavy_comma>
          l \<Ztypecolon> \<mem>[addr] \<slice>[i-1,1] \<nat>(\<int'>)\<close>
  premises \<open>1 \<le> i\<close> and \<open>i \<le> LEN\<close>
  output \<open>l \<Ztypecolon> \<mem>[addr] \<slice>[i-1,1] \<nat>(\<int'>)\<heavy_comma>
          l ! 0 \<Ztypecolon> \<val> \<nat>(\<int'>)\<close>
\<medium_left_bracket>
  *(i + \<open>-1 \<Ztypecolon> \<int>(32)\<close>)
\<medium_right_bracket> .

proc test_bracket_negative_int32:
  input  \<open>i \<Ztypecolon> \<val> \<slice>-\<ptr>[addr:LEN] \<int'>\<heavy_comma>
          l \<Ztypecolon> \<mem>[addr] \<slice>[i-1,1] \<nat>(\<int'>)\<close>
  premises \<open>1 \<le> i\<close> and \<open>i \<le> LEN\<close>
  output \<open>l \<Ztypecolon> \<mem>[addr] \<slice>[i-1,1] \<nat>(\<int'>)\<heavy_comma>
          l ! 0 \<Ztypecolon> \<val> \<nat>(\<int'>)\<close>
\<medium_left_bracket>
  i[\<open>-1 \<Ztypecolon> \<int>(32)\<close>]
\<medium_right_bracket> .

end
