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
  input \<open>x \<Ztypecolon> \<mem>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr \<a>\<i>\<n>\<t>\<close>
  output \<open>x \<Ztypecolon> \<mem>[addr] \<nat>\<heavy_comma> x \<Ztypecolon> \<val> \<nat>\<close>
  \<medium_left_bracket>
    $addr ! (*BUG!*)
  \<medium_right_bracket> .
 
proc test_mem1':
  input \<open>x \<Ztypecolon> \<mem>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<a>\<i>\<n>\<t>\<close>
  output \<open>x \<Ztypecolon> \<mem>[addr] \<nat>\<heavy_comma> x \<Ztypecolon> \<val> \<nat>\<close>
  \<medium_left_bracket>
    * $addr
  \<medium_right_bracket> .

proc test_mem2:
  input \<open>x \<Ztypecolon> \<mem>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr \<a>\<i>\<n>\<t>\<close>
  output \<open>2 \<Ztypecolon> \<mem>[addr] \<nat>\<close>
  \<medium_left_bracket>
    $addr := \<open>2 \<Ztypecolon> \<nat>\<close>
  \<medium_right_bracket> .

proc test_ptr3:
  input \<open>addr \<Ztypecolon> \<val> TypedPtr (\<struct> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>})\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>addr \<tribullet> c \<Ztypecolon> \<val> TypedPtr \<a>\<i>\<n>\<t>\<close>
\<medium_left_bracket>
  &addr.c
\<medium_right_bracket> .



declare [[\<phi>reasoning_step_limit = 170]]


proc test_mem3:
  input \<open>(x,y) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  output \<open>(x,y) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> y \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  addr.b
\<medium_right_bracket> .

proc test_mem4:
  input \<open>(x,(y,z)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> z \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  addr.d.e
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 2]]

proc test_mem4a:
  input \<open>(x,(y,z)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> (y, z) \<Ztypecolon> \<val> \<lbrace> b: \<nat>, e: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d
\<medium_right_bracket> .


proc test_mem5:
  input \<open>(x,(y,z,f)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,z,f)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<nat>\<rbrace> \<rbrace>\<heavy_comma> f \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  addr.d.f
\<medium_right_bracket> .

proc test_mem6:
  input \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<struct> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}}\<close>
  output \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<rbrace> \<rbrace>\<heavy_comma> j \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  addr.d.f.j
\<medium_right_bracket> .

declare [[\<phi>reasoning_step_limit = 275]]


proc test_mem6a:
  input \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<val> TypedPtr (\<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<struct> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}})\<close>
  output \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<rbrace> \<rbrace>\<heavy_comma>
          (y, z, g, h, i, j) \<Ztypecolon> \<val> \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d
\<medium_right_bracket> .



proc test_mem6b:
  input \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
         addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<struct> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}}\<close>
  output \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<rbrace> \<rbrace>\<heavy_comma>
          (g, h, i, j) \<Ztypecolon> \<val>[\<v>1] \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d.f
\<medium_right_bracket> .

declare [[\<phi>reasoning_step_limit = 140]]

proc test_mem7:
  input  \<open>(x,y) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, b: \<a>\<i>\<n>\<t>}\<close>
  output \<open>(x,2) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, b: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr.b := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 1]]

proc test_mem8:
  input  \<open>(x,(y,z)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,(y,2)) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d.e := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

declare [[\<phi>reasoning_step_limit = 180]]

lemmas ttt = synthesis_construct_aggregate_\<phi>app [where T=\<open>\<lbrace> SYMBOL_VAR(s): T \<rbrace> \<^emph> U\<close> for s T U]

        synthesis_construct_aggregate_\<phi>app [where T=\<open>\<lbrace> \<rbrace>\<close>]

        synthesis_construct_aggregate_\<phi>app [where T=\<open>\<lbrace> SYMBOL_VAR(s): T \<rbrace>\<close> for s T]

(*
proc test_mem8a:
  input  \<open>(x,y,z) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> \<Ptr> \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>}}\<close>
  output \<open>(x,2,3) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>\<rbrace> \<rbrace>\<close>
  \<medium_left_bracket> 
    $addr \<tribullet> d := \<open>(2,3) \<Ztypecolon> \<lbrace> b: \<nat>, e: \<nat>\<rbrace>\<close>
  \<medium_right_bracket> .
*)


proc test_mem9:
  input  \<open>(x,(y,z,(g,h,i,j))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<heavy_comma>
          addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<struct> {c: \<a>\<i>\<n>\<t>, d: \<struct> {b: \<a>\<i>\<n>\<t>, e: \<a>\<i>\<n>\<t>, f: \<struct> {g: \<a>\<i>\<n>\<t>, h: \<a>\<i>\<n>\<t>, i: \<a>\<i>\<n>\<t>, j: \<a>\<i>\<n>\<t>}}}\<close>
  output \<open>(x,(y,z,(g,h,i,2))) \<Ztypecolon> \<mem>[addr] \<lbrace> c: \<nat>, d: \<lbrace> b: \<nat>, e: \<nat>, f: \<lbrace> g: \<nat>, h: \<nat>, i: \<nat>, j: \<nat> \<rbrace> \<rbrace> \<rbrace>\<close>
\<medium_left_bracket>
  addr.d.f.j := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .


proc test_mem10:
  input  \<open>Void\<close>
  output \<open>2 \<Ztypecolon> \<mem>[addr] \<nat>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr \<a>\<i>\<n>\<t> \<subj> addr. \<top>\<close>
\<medium_left_bracket>
  calloc1 \<nat> \<rightarrow> val addr\<semicolon>
  addr := \<open>2 \<Ztypecolon> \<nat>\<close> \<semicolon>  
  addr
\<medium_right_bracket> .

proc test_mem11:
  input  \<open>Void\<close>
  output \<open>(4,2) \<Ztypecolon> \<mem>[addr] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr (\<struct> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})
          \<subj> addr. address_to_base addr\<close>
\<medium_left_bracket>
  calloc1 \<open>\<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close> \<rightarrow> val addr
  addr.b := \<open>4 \<Ztypecolon> \<nat>\<close> ;
  addr.c := \<open>2 \<Ztypecolon> \<nat>\<close> ;
  addr
\<medium_right_bracket> .

proc test_mem12:
  input  \<open>(x,y) \<Ztypecolon> \<mem>[addr] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr (\<struct> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})\<close>
  premises \<open>address_to_base addr\<close>
  output \<open>Void\<close>
\<medium_left_bracket>
  mfree (addr)
\<medium_right_bracket> .

proc test_mem13:
  input  \<open>xs \<Ztypecolon> \<mem>[addr] \<Array>[3] \<nat>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr (\<array>[3] \<a>\<i>\<n>\<t>)\<close>
  output \<open>xs \<Ztypecolon> \<mem>[addr] \<Array>[3] \<nat>\<heavy_comma> xs ! Suc 0 \<Ztypecolon> \<val>[\<v>1] \<nat>\<close>
\<medium_left_bracket>
  addr[1]
\<medium_right_bracket> .


proc test_mem14:
  input  \<open>xs \<Ztypecolon> \<mem>[addr] \<Array>[3] \<nat>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr (\<array>[3] \<a>\<i>\<n>\<t>)\<close>
  output \<open>xs[1 := 2] \<Ztypecolon> \<mem>[addr] \<Array>[3] \<nat>\<close>
\<medium_left_bracket>
  addr[1] := \<open>2 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .


proc test_mem15:
  input  \<open>xs \<Ztypecolon> \<mem>[addr] \<Array>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> TypedPtr (\<array>[3] \<struct> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})\<close>
  output \<open>xs \<Ztypecolon> \<mem>[addr] \<slice>[0, 3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> snd (xs ! 2) \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  addr[2].c \<rightarrow> val t \<semicolon>
  t
\<medium_right_bracket> .


proc test_mem16:
  input  \<open>xs \<Ztypecolon> \<mem>[addr] \<Array>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<array>[3] \<struct> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>}\<close>
  output \<open>list_upd_map 2 (id \<otimes>\<^sub>f (\<lambda>x. 3)) xs \<Ztypecolon> \<mem>[addr] \<slice>[0, 3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr[2].c := \<open>3 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

proc test_mem17:
  input  \<open>[(1,2),(3,4),(5,6)] \<Ztypecolon> \<mem>[addr] \<Array>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> Ptr\<close>
  premises \<open>\<typeof> addr = \<array>[3] \<struct> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>}\<close>
  output \<open>[(1,2),(3,4),(5,42)] \<Ztypecolon> \<mem>[addr] \<Array>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  addr[2].c := \<open>42 \<Ztypecolon> \<nat>\<close>
\<medium_right_bracket> .

proc test_mem18:
  input  \<open>addr \<Ztypecolon> \<val> Ptr\<heavy_comma> i \<Ztypecolon> \<val> \<nat>\<heavy_comma> j \<Ztypecolon> \<val> \<nat>\<heavy_comma>
          [[1,2],[3,4]] \<Ztypecolon> \<mem>[addr] \<slice>[i,n] \<slice>[j,m] \<nat>\<close>
  premises \<open>i + n \<le> N \<and> j + m \<le> M \<and> \<typeof> addr = \<array>[N] \<array>[M] \<a>\<i>\<n>\<t>\<close>
  output \<open>[[1,2],[3,4]] \<Ztypecolon> \<mem>[addr] \<slice>[i,n] \<slice>[j,m] \<nat>\<heavy_comma> 3 \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  addr[i + 1, j]
\<medium_right_bracket> .

proc test_mem19:
  input  \<open>x \<Ztypecolon> \<mem>[addr] \<slice>[i,n] \<nat>\<heavy_comma>
          j \<Ztypecolon> \<val> \<slice>-\<ptr>[addr:N] \<a>\<i>\<n>\<t>\<close>
  premises \<open>i \<le> j \<and> j < i + n \<and> i + n \<le> N\<close>
  output \<open>x \<Ztypecolon> \<mem>[addr] \<slice>[i,n] \<nat>\<heavy_comma> x ! (j-i) \<Ztypecolon> \<val> \<nat>\<close>
\<medium_left_bracket>
  j !
\<medium_right_bracket> .

proc test_mem20:
  input  \<open>j \<Ztypecolon> \<val> \<slice>-\<ptr>[addr:n] \<a>\<i>\<n>\<t>\<heavy_comma> k \<Ztypecolon> \<val> \<nat>\<close>
  premises \<open>j + k \<le> n\<close>
  output \<open>j+k \<Ztypecolon> \<val> \<slice>-\<ptr>[addr:n] \<a>\<i>\<n>\<t>\<close>
\<medium_left_bracket>
  j + k
\<medium_right_bracket> .


(*FIXME!
proc test_mem15:
  input  \<open>xs \<Ztypecolon> \<mem>[addr] \<Array>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<heavy_comma> addr \<Ztypecolon> \<val> \<Ptr> (\<array>[3] \<struct> {b: \<a>\<i>\<n>\<t>, c: \<a>\<i>\<n>\<t>})\<close>
  output \<open>yyy \<Ztypecolon> \<mem>[addr] \<Array>[3] \<lbrace> b: \<nat>, c: \<nat> \<rbrace>\<close>
\<medium_left_bracket>
  $addr \<tribullet> 2
*)









lemma
  \<open> \<premise> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<mem>[addr] \<slice>[start, len] T
    \<transforms> y ! (j - start) \<Ztypecolon> \<mem>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<mem>[addr] \<slice>[j + 1, start + len - j - 1] T\<heavy_comma>
             take (j - start) y \<Ztypecolon> \<mem>[addr] \<slice>[start, j - start] T\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket>
  \<medium_right_bracket> certified by hammer_or_aoa .






lemma
  \<open> \<premise> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<mem>[addr] \<slice>[start, len] T
    \<transforms> drop (j - start + 1) y \<Ztypecolon> \<mem>[addr] \<slice>[j + 1, start + len - j - 1] T\<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<mem>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             take (j - start) y \<Ztypecolon> \<mem>[addr] \<slice>[start, j - start] T\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket>
  \<medium_right_bracket> certified by hammer_or_aoa .


lemma
  \<open> \<premise> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<mem>[addr] \<slice>[start, len] T
    \<transforms> take (j - start) y \<Ztypecolon> \<mem>[addr] \<slice>[start, j - start] T \<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<mem>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T\<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<mem>[addr] \<slice>[j + 1, start + len - j - 1] T\<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by hammer_or_aoa .

lemma
  \<open> \<premise> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<mem>[addr] \<slice>[start, len]  T
    \<transforms> take (j - start) y \<Ztypecolon> \<mem>[addr] \<slice>[start, j - start] T \<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<mem>[addr] \<slice>[j + 1, start + len - j - 1] T \<heavy_comma>
             y ! (j - start) \<Ztypecolon> \<mem>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T \<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by hammer_or_aoa .

lemma
  \<open> \<premise> start \<le> j \<and> j < start + len
\<Longrightarrow> y \<Ztypecolon> \<mem>[addr] \<slice>[start, len] T
    \<transforms> take (j - start) y \<Ztypecolon> \<mem>[addr] \<slice>[start, j - start] T \<heavy_comma>
              y ! (j - start) \<Ztypecolon> \<mem>[addr \<tribullet> j\<^sup>\<t>\<^sup>\<h>] T \<heavy_comma>
             drop (j - start + 1) y \<Ztypecolon> \<mem>[addr] \<slice>[j + 1, start + len - j - 1] T \<close>
  for T :: \<open>(mem_fic, 'a) \<phi>\<close>
  \<medium_left_bracket> 
  \<medium_right_bracket> certified by hammer_or_aoa .



end