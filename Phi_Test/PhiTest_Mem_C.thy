theory PhiTest_Mem_C
  imports Phi_Semantics.PhiSem_Mem_C
          Phi_Semantics.PhiSem_Int_ArbiPrec
          Phi_Semantics.PhiSem_Mem_C_Ag_NT
          Phi_Semantics.PhiSem_Mem_C_Ag_Ar
          Phi_Semantics.PhiSem_Mem_C_Ar_AI
begin

declare One_nat_def[simp del]

declare [[\<phi>reasoning_step_limit = 70]]

proc test_mem1:
  input \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr \<a>\<i>\<n>\<t>\<close>
  output \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket>
    $addr ! (*BUG!*)
  \<medium_right_bracket> .
 
proc test_mem1':
  input \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<a>\<i>\<n>\<t>\<close>
  output \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  \<medium_left_bracket>
    * $addr
  \<medium_right_bracket> .

proc test_mem2:
  input \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr \<a>\<i>\<n>\<t>\<close>
  output \<open>2 \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<close>
  \<medium_left_bracket>
    $addr := \<open>2 \<Ztypecolon> \<nat>\<close>
  \<medium_right_bracket> .

proc test_ptr3:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>})\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>addr \<tribullet> c \<Ztypecolon> \<v>\<a>\<l> TypedPtr \<a>\<i>\<n>\<t>\<close>
\<medium_left_bracket>
  &addr.c
\<medium_right_bracket> .



declare [[\<phi>reasoning_step_limit = 170]]


proc test_mem3:
  input \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  output \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  addr.b
\<medium_right_bracket> .

proc test_mem4:
  input \<open>(x,(y,z)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> z \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  addr.d.e
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 2]]

proc test_mem4a:
  input \<open>(x,(y,z)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> (y, z) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> b: \<nat>, e: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d
\<medium_right_bracket> .


proc test_mem5:
  input \<open>(x,(y,z,f)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z,f)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<nat>\<rbrace> \<rbrace>\<heavy_comma> f \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  addr.d.f
\<medium_right_bracket> .

proc test_mem6:
  input \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<s>\<t>\<r>\<u>\<c>\<t> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}}\<close>
  output \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<rbrace> \<rbrace>\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  addr.d.f.j
\<medium_right_bracket> .

declare [[\<phi>reasoning_step_limit = 275]]


proc test_mem6a:
  input \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<s>\<t>\<r>\<u>\<c>\<t> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}})\<close>
  output \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<rbrace> \<rbrace>\<heavy_comma>
          (y, z, g, h, i, j) \<Ztypecolon> \<v>\<a>\<l> \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d
\<medium_right_bracket> .



proc test_mem6b:
  input \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<s>\<t>\<r>\<u>\<c>\<t> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}}\<close>
  output \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<rbrace> \<rbrace>\<heavy_comma>
          (g, h, i, j) \<Ztypecolon> \<v>\<a>\<l>[\<v>1] \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d.f
\<medium_right_bracket> .

declare [[\<phi>reasoning_step_limit = 140]]

proc test_mem7:
  input  \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  output \<open>(x,2) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr.b := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 1]]

proc test_mem8:
  input  \<open>(x,(y,z)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,2)) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d.e := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

declare [[\<phi>reasoning_step_limit = 180]]

lemmas ttt = synthesis_construct_aggregate_\<phi>app [where T=\<open>\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> U\<close> for s T U]

        synthesis_construct_aggregate_\<phi>app [where T=\<open>\<lbrace> \<rbrace>\<close>]

        synthesis_construct_aggregate_\<phi>app [where T=\<open>\<lbrace> SYMBOL_VAR(s): T \<rbrace>\<close> for s T]

(*
proc test_mem8a:
  input  \<open>(x,y,z) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,2,3) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<close>
  \<medium_left_bracket> 
    $addr \<tribullet> d := \<open>(2,3) \<Ztypecolon> \<lbrace> b: \<nat>, e: \<nat>\<rbrace>\<close>
  \<medium_right_bracket> .
*)


proc test_mem9:
  input  \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<s>\<t>\<r>\<u>\<c>\<t> {c: \<a>\<i>\<n>\<t>, d: \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<s>\<t>\<r>\<u>\<c>\<t> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}}\<close>
  output \<open>(x,(y,z,(g,h,i,2))) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d.f.j := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .


proc test_mem10:
  input  \<open>Void\<close>
  output \<open>2 \<Ztypecolon> \<m>\<e>\<m>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr \<a>\<i>\<n>\<t> \<s>\<u>\<b>\<j> addr. \<top>\<close>
\<medium_left_bracket>
  calloc1 \<nat> \<rightarrow> val addr\<semicolon>
  addr := \<open>2 \<Ztypecolon> \<nat>\<close> \<semicolon>  
  addr
\<medium_right_bracket> .

proc test_mem11:
  input  \<open>Void\<close>
  output \<open>(4,2) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})
          \<s>\<u>\<b>\<j> addr. address_to_base addr\<close>
\<medium_left_bracket>
  calloc1 \<open>\<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close> \<rightarrow> val addr
  addr.b := \<open>4 \<Ztypecolon> \<nat>\<close> ;
  addr.c := \<open>2 \<Ztypecolon> \<nat>\<close> ;
  addr
\<medium_right_bracket> .

proc test_mem12:
  input  \<open>(x,y) \<Ztypecolon> \<m>\<e>\<m>[addr] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})\<close>
  premises \<open>address_to_base addr\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  mfree (addr)
\<medium_right_bracket> .

proc test_mem13:
  input  \<open>xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<a>\<r>\<r>\<a>\<y>[3] \<a>\<i>\<n>\<t>)\<close>
  output \<open>xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<nat>\<heavy_comma> xs ! Suc 0 \<Ztypecolon> \<v>\<a>\<l>[\<v>1] \<nat>\<close>
\<medium_left_bracket>
  addr[1]
\<medium_right_bracket> .


proc test_mem14:
  input  \<open>xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<nat>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<a>\<r>\<r>\<a>\<y>[3] \<a>\<i>\<n>\<t>)\<close>
  output \<open>xs[1 := 2] \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<nat>\<close>
\<medium_left_bracket>
  addr[1] := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .


proc test_mem15:
  input  \<open>xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> TypedPtr (\<a>\<r>\<r>\<a>\<y>[3] \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})\<close>
  output \<open>xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[0, 3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> snd (xs ! 2) \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  addr[2].c \<rightarrow> val t \<semicolon>
  t
\<medium_right_bracket> .


proc test_mem16:
  input  \<open>xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<a>\<r>\<r>\<a>\<y>[3] \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>}\<close>
  output \<open>list_upd_map 2 (id \<otimes>\<^sub>f (\<lambda>x. 3)) xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[0, 3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr[2].c := \<open>3 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

proc test_mem17:
  input  \<open>[(1,2),(3,4),(5,6)] \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<close>
  premises \<open>\<t>\<y>\<p>\<e>\<o>\<f> addr = \<a>\<r>\<r>\<a>\<y>[3] \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>}\<close>
  output \<open>[(1,2),(3,4),(5,42)] \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr[2].c := \<open>42 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

proc test_mem18:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr\<heavy_comma> i \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma> j \<Ztypecolon> \<v>\<a>\<l> \<nat>\<heavy_comma>
          [[1,2],[3,4]] \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,n] \<s>\<l>\<i>\<c>\<e>[j,m] \<nat>\<close>
  premises \<open>i + n \<le> N \<and> j + m \<le> M \<and> \<t>\<y>\<p>\<e>\<o>\<f> addr = \<a>\<r>\<r>\<a>\<y>[N] \<a>\<r>\<r>\<a>\<y>[M] \<a>\<i>\<n>\<t>\<close>
  output \<open>[[1,2],[3,4]] \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,n] \<s>\<l>\<i>\<c>\<e>[j,m] \<nat>\<heavy_comma> 3 \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  addr[i + 1, j]
\<medium_right_bracket> .

proc test_mem19:
  input  \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,n] \<nat>\<heavy_comma>
          j \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:N] \<a>\<i>\<n>\<t>\<close>
  premises \<open>i \<le> j \<and> j < i + n \<and> i + n \<le> N\<close>
  output \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[i,n] \<nat>\<heavy_comma> x ! (j-i) \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
\<medium_left_bracket>
  j !
\<medium_right_bracket> .

proc test_mem20:
  input  \<open>j \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:n] \<a>\<i>\<n>\<t>\<heavy_comma> k \<Ztypecolon> \<v>\<a>\<l> \<nat>\<close>
  premises \<open>j + k \<le> n\<close>
  output \<open>j+k \<Ztypecolon> \<v>\<a>\<l> \<s>\<l>\<i>\<c>\<e>\<bbbP>\<t>\<r>[addr:n] \<a>\<i>\<n>\<t>\<close>
\<medium_left_bracket>
  j + k
\<medium_right_bracket> .


(*FIXME!
proc test_mem15:
  input  \<open>xs \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> \<bbbP>\<t>\<r> (\<a>\<r>\<r>\<a>\<y>[3] \<s>\<t>\<r>\<u>\<c>\<t> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})\<close>
  output \<open>yyy \<Ztypecolon> \<m>\<e>\<m>[addr] \<bbbA>\<r>\<r>\<a>\<y>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  $addr \<tribullet> 2
*)









lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T\<heavy_comma>
             take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket>
  \<medium_right_bracket> certified by auto_sledgehammer .






lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T\<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .


lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T \<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .

lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len]  T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T \<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T \<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T \<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .

lemma
  \<open> \<p>\<r>\<e>\<m>\<i>\<s>\<e> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T
    \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> take (j - start) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, j - start] T \<heavy_comma>
              y ! (j - start) \<Ztypecolon> \<m>\<e>\<m>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T \<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[j + 1, start + len - j - 1] T \<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by auto_sledgehammer .



end