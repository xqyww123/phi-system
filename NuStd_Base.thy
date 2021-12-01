theory NuStd_Base
  imports  NuInstructions
begin

\<nu>overloads split pop

declare Separation_assoc[simp]

proc split_array[\<nu>overload split]: \<open>ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> l \<tycolon> Array T\<close>
  \<longmapsto> \<open>ptr ||+ n \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> take n l \<tycolon> Array T \<heavy_asterisk> (ptr ||+ n) \<R_arr_tail> drop n l \<tycolon> Array T\<close>
  premises [used]: "n \<le> length l"
  \<bullet> + split_cast n
  finish

proc pop_array[\<nu>overload pop]: \<open>ptr \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> l \<tycolon> Array T\<close>
  \<longmapsto> \<open>ptr ||+ 1 \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p (ptr ||+ 1) \<R_arr_tail> tl l \<tycolon> Array T \<heavy_asterisk> ptr \<R_arr_tail> hd l \<tycolon> Ref T \<close>
  premises A: "l \<noteq> []"
  have [used]: "1 \<le> length l" by (meson Premise_def length_0_conv less_one not_le A)
  \<bullet> \<open>1 \<tycolon> \<nat>[size_t]\<close> +


end