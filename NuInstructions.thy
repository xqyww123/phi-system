theory NuInstructions
  imports NuPrime NuLLReps
begin

subsection \<open>Basic sequential instructions\<close>

definition op_crash :: "('x::stack) \<longmapsto> ('y::stack)" where "op_crash _ = PartialCorrect"

definition op_drop :: "('a::lrep) \<times> ('r::stack) \<longmapsto> 'r" where
  "op_drop x = (case x of (h,a,r) \<Rightarrow> Success (h,r))"

definition op_dup :: "('a::lrep) \<times> ('r::stack) \<longmapsto> ('a \<times> 'a \<times> 'r)"
  where "op_dup x = (case x of (h,a,r) \<Rightarrow> Success (h, a, a, r))"

definition op_pair :: "('a::lrep) \<times> ('b::lrep) \<times> ('r::stack) \<longmapsto> (('b \<times> 'a) \<times> 'r)"
  where "op_pair = (\<lambda>(h,a,b,r). Success (h,(b,a),r))"

definition op_depair :: "(('b::lrep) \<times> ('a::lrep)) \<times> ('r::stack) \<longmapsto> ('a \<times> 'b \<times> 'r)"
  where "op_depair = (\<lambda>(h,(b,a),r). Success (h,a,b,r))"

definition op_let :: " ('v::lrep \<Rightarrow> 's::stack \<longmapsto> 't::stack) \<Rightarrow> ('v \<times> 's \<longmapsto> 't)"
  where "op_let body = (\<lambda>(h,v,s). body v (h,s))"

definition op_local_value :: " 'v::lrep \<Rightarrow> 's::stack \<longmapsto> 'v \<times> 's "
  where "op_local_value v = (\<lambda>(h,s). Success (h,v,s))"


subsection \<open>Branches & Loops\<close>

definition op_sel :: " 'a itself \<Rightarrow> (1 word \<times> 'a \<times> 'a \<times> 'r) \<longmapsto> ('a \<times> 'r)"
  where "op_sel _ s = (case s of (heap,c,b,a,r) \<Rightarrow> if c = 1 then Success (heap,a,r) else Success (heap,b,r))"

definition op_if :: " 't itself \<Rightarrow> ('s::stack \<longmapsto> 't::stack) \<Rightarrow> ('s \<longmapsto> 't) \<Rightarrow> (1 word \<times> 's) \<longmapsto> 't"
  where "op_if _ brT brF s = (case s of (heap,c,r) \<Rightarrow> if c = 1 then brT (heap,r) else brF (heap,r))"

inductive SemDoWhile :: "('r \<longmapsto> 1 word \<times> 'r) \<Rightarrow> heap \<times> 'r \<Rightarrow> 'r state \<Rightarrow> bool" where
  "f s = Success (h,0,r) \<Longrightarrow> SemDoWhile f s (Success (h,r))"
| "f s = PartialCorrect \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "f s = Fail \<Longrightarrow> SemDoWhile f s Fail"
| "f s = Success (h,1,r) \<Longrightarrow> SemDoWhile f (h,r) s'' \<Longrightarrow> SemDoWhile f s s''"

definition op_do_while :: " 'r itself \<Rightarrow> ('r \<longmapsto> 1 word \<times> 'r) \<Rightarrow> 'r \<longmapsto> 'r" where
  "op_do_while _ f s = (if (\<exists>y. SemDoWhile f s y) then The (SemDoWhile f s) else PartialCorrect)"

inductive SemRec :: "(('x \<longmapsto> 'y) \<Rightarrow> ('x \<longmapsto> 'y)) \<Rightarrow> heap \<times> 'x \<Rightarrow> 'y state \<Rightarrow> bool" where
  SemRec_I0: "(\<And>g. F g x = y) \<Longrightarrow> SemRec F x y"
| SemRec_IS: "SemRec (F o F) x y \<Longrightarrow> SemRec F x y"

definition op_recursion' :: "(('x \<longmapsto> 'y) \<Rightarrow> ('x \<longmapsto> 'y)) \<Rightarrow> 'x \<longmapsto> 'y"
  where "op_recursion' F s = (if (\<exists>t. SemRec F s t) then The (SemRec F s) else PartialCorrect)"

definition op_recursion :: "uniq_id \<Rightarrow> 'x itself \<Rightarrow> 'y itself \<Rightarrow> (('x \<longmapsto>\<^sub>f 'y) \<Rightarrow> ('x \<longmapsto> 'y)) \<Rightarrow> 'x \<longmapsto>\<^sub>f 'y"
  where "op_recursion _ _ _ F = func (op_recursion' (F o func))"

section \<open>Arithmetic instructions\<close>

subsection \<open>Integer arithmetic\<close>

definition op_const_int :: "('w::len) itself \<Rightarrow> nat \<Rightarrow> ('r::stack) \<longmapsto> 'w word \<times> 'r"
  where "op_const_int _ c = (\<lambda>(heap,r). Success (heap,of_nat c,r))"

definition op_const_size_t :: " nat \<Rightarrow> ('r::stack) \<longmapsto> size_t word \<times> 'r"
  where "op_const_size_t c = (\<lambda>(heap,r).
    if c < 2 ^ addrspace_capacity then Success (heap,of_nat c,r) else PartialCorrect)"
    \<comment> \<open> `op_const_size_t` checks overflow during the compilation towards certain decided platform.  \<close>

definition op_add :: "'a itself \<Rightarrow> ('a::len) word \<times> ('a::len) word \<times> ('r::lrep) \<longmapsto> ('a::len) word \<times> 'r"
  where "op_add _ = (\<lambda>(h,a,b,r). Success (h,a+b, r))"
declare op_add_def[\<nu>instr]

definition op_sub :: "('a::len) itself \<Rightarrow> 'a word \<times> 'a word \<times> ('r::lrep) \<longmapsto> 'a word \<times> 'r"
  where "op_sub _ = (\<lambda>(h,a,b,r) \<Rightarrow> Success (h,b - a, r))"
declare op_sub_def[\<nu>instr]

definition op_udiv ::  "('a::len) itself \<Rightarrow> 'a word \<times> 'a word \<times> ('r::lrep) \<longmapsto> 'a word \<times> 'r"
  where "op_udiv _ = (\<lambda>(h,a,b,r) \<Rightarrow> Success (h,b div a, r))"
declare op_udiv_def[\<nu>instr]

definition op_lt :: " ('w::len) itself \<Rightarrow> 'w word \<times> 'w word \<times> ('r::lrep) \<longmapsto> 1 word \<times> 'r"
  where "op_lt _ = (\<lambda>(h,a,b,r).  Success (h, (if  b < a then 1 else 0), r))"
declare op_lt_def[\<nu>instr]

definition op_le :: " ('w::len) itself \<Rightarrow> 'w word \<times> 'w word \<times> ('r::lrep) \<longmapsto> 1 word \<times> 'r "
  where "op_le _ = (\<lambda>(h,a,b,r).  Success (h, (if  b \<le> a then 1 else 0), r))"

definition op_not :: "('w::len) itself \<Rightarrow> 'w word \<times> ('r::stack) \<longmapsto> 'w word \<times> 'r"
  where "op_not len = (\<lambda>(h,x,r). Success (h,not x,r))"

definition op_equal :: " 'a itself \<Rightarrow> ('a::{ceq,lrep}) \<times> 'a \<times> ('r::stack) \<longmapsto> 1 word \<times> 'r"
  where "op_equal _ = (\<lambda>(h,a,b,r). if ceqable h b a then Success (h,(if ceq b a then 1 else 0), r) else Fail)"


section \<open>Tuple Operations\<close>

definition cons_tup :: " 'a itself \<Rightarrow> ('a::field_list) \<times> ('r::stack) \<longmapsto> 'a tuple \<times> 'r"
  where "cons_tup _ = (\<lambda>(h,a,r). Success (h, Tuple a, r))"

definition op_dest_tup :: "('a::field_list) tuple \<times> ('r::stack) \<longmapsto> 'a \<times> 'r"
  where "op_dest_tup s = (case s of (h,Tuple a, r) \<Rightarrow> Success (h,a,r))"

definition op_get_tuple :: "('a tuple,'a tuple,'x,'x) index \<Rightarrow> 'a itself \<Rightarrow> 'a tuple \<times> ('r::stack) \<longmapsto> ('x::lrep) \<times> 'r"
  where "op_get_tuple idx _ = (\<lambda>(h,a,r). Success (h,get_idx idx a,r))"

definition op_set_tuple ::
    "('a tuple,'b tuple,'x,'y) index \<Rightarrow> 'a itself \<Rightarrow> 'y itself \<Rightarrow> ('y::lrep) \<times> 'a tuple \<times> ('r::stack) \<longmapsto> 'b tuple \<times> 'r"
  where "op_set_tuple idx _ _ = (\<lambda>(h,y,a,r). Success (h, map_idx idx (\<lambda>_. y) a, r))"

section \<open>Field Index\<close>

definition index_enter_tup :: "(('a::field_list),('b::field_list),'x,'y) index \<Rightarrow> ('a tuple, 'b tuple, 'x, 'y) index"
  where "index_enter_tup adr = (case adr of Index g m \<Rightarrow> Index (case_tuple g) (map_tuple o m))"

section \<open>Memory & Pointer Operations\<close>

definition op_shift_pointer :: "'y::lrep itself \<Rightarrow> size_t word \<times> memptr \<times> 'r::stack \<longmapsto> memptr \<times> 'r::stack"
  where "op_shift_pointer ty s = (case s of (heap, delta, memptr (seg |+ ofs), r) \<Rightarrow>
    Success (heap, memptr (seg |+ (ofs + delta * of_nat (size_of LLTY('y)))), r))"

definition "heap_assignN n v seg heap = (\<lambda>key. case key of MemAddress (seg' |+ ofs') \<Rightarrow>
      if seg' = seg \<and> ofs' < n then v else
      if seg' = seg \<and> ofs' = n then Some DM_none else heap key | _ \<Rightarrow> heap key)"

definition op_alloc :: "('x::{zero,field}) itself \<Rightarrow> size_t word \<times> ('r::stack) \<longmapsto> memptr \<times>'r"
  where "op_alloc _ s = (case s of (heap,n,r) \<Rightarrow>  let seg = malloc heap in
  if segment_len seg = unat n \<and> segment_llty seg = LLTY('x) then
    Success (heap_assignN (unat n) (Some (deepize (0 :: 'x))) seg heap, memptr (seg |+ 0), r)
  else PartialCorrect)"

definition op_load :: " 'x itself \<Rightarrow> 'a itself \<Rightarrow> ('a::lrep,'a,'x,'x) index \<Rightarrow> memptr \<times> ('r::stack) \<longmapsto> 'x::field \<times>'r "
  where "op_load _ _ idx s = (case s of (heap, memptr adr, r) \<Rightarrow>
    (case heap (MemAddress (logical_addr_of adr)) of Some data \<Rightarrow>
       Success (heap, get_idx idx (shallowize data), r) | _ \<Rightarrow> Fail))"

definition op_store :: " 'x itself \<Rightarrow> 'a itself \<Rightarrow> ('a::lrep,'a,'x,'x) index \<Rightarrow> 'x::field \<times> memptr \<times> ('r::stack) \<longmapsto> 'r "
  where "op_store _ _ idx s = (case s of (heap, x, memptr addr, r) \<Rightarrow>
    (let key = MemAddress (logical_addr_of addr) in
    case heap key of Some data \<Rightarrow>
      Success (heap(key \<mapsto> map_deepmodel (map_idx idx (\<lambda>_. x)) data), r) | _ \<Rightarrow> Fail))"



end
