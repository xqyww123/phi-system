theory NuStd_Base
  imports  NuInstructions
begin

\<nu>overloads split

declare Separation_assoc[simp]

proc split_array[\<nu>overload split]: \<open>ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> l \<tycolon> Array T\<close>
  \<longmapsto> \<open>ptr ||+ n \<tycolon> Pointer\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p ptr \<R_arr_tail> take n l \<tycolon> Array T \<heavy_asterisk> (ptr ||+ n) \<R_arr_tail> drop n l \<tycolon> Array T\<close>
  premises [used]: "n < length l"
  \<bullet> + cast_heap split_cast n
  finish


end