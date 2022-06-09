theory NuInstructions
  imports NuPrime NuLLReps
begin

subsection \<open>Basic sequential instructions\<close>


context std_sem begin

definition op_drop :: "('VAL,'RES_N,'RES) proc" where
  "op_drop = (\<lambda>(v#vs,res). Success (vs,res))"

definition op_dup :: "('VAL,'RES_N,'RES) proc"
  where "op_dup = (\<lambda>(v#vs,res). Success (v#v#vs,res))"

definition op_set_var :: "string \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_var name' T = (\<lambda>(v#vs, res).
    if v \<in> Well_Type T \<and> pred_option1 (\<lambda>v. v \<in> Well_Type T) (!! (R_var.get res) name')
    then Success (vs, R_var.updt (map_fine (\<lambda>vars. vars(name' \<mapsto> v))) res)
    else Fail)"

definition op_get_var :: "string \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_var name' T = (\<lambda>(vs, res).
    let v = !! (R_var.get res) name'
    in if option_pred1 (\<lambda>v. v \<in> Well_Type T) v
       then Success (the v # vs, res) else Fail)"


subsection \<open>Branches & Loops\<close>

definition op_sel :: "('VAL,'RES_N,'RES) proc"
  where "op_sel = (\<lambda>(c#b#a#vs,res).
    Success ((if snd (V_int.dest c) = 1 then a else b) # vs, res))"

definition op_if :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_if brT brF = (\<lambda>(c#vs,res).
    if snd (V_int.dest c) = 1 then brT (vs,res) else brF (vs,res))"

inductive SemDoWhile :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) comp \<Rightarrow> ('VAL,'RES_N,'RES) state \<Rightarrow> bool" where
  "f s = Success (V_int.mk (1,0) # vs, res) \<Longrightarrow> SemDoWhile f s (Success (vs,res))"
| "f s = PartialCorrect \<Longrightarrow> SemDoWhile f s PartialCorrect"
| "f s = Fail \<Longrightarrow> SemDoWhile f s Fail"
| "f s = Success (V_int.mk (1,1) # vs, res) \<Longrightarrow> SemDoWhile f (vs,res) s'' \<Longrightarrow> SemDoWhile f s s''"

lemma "\<nexists> y. SemDoWhile (\<lambda>(vs,res). Success (V_int.mk (1,1) # vs, res)) (vs,res) y"
  apply rule apply (elim exE) subgoal for y 
    thm SemDoWhile.induct
    apply (induct "(\<lambda>(vs,res). Success (V_int.mk (1,1) # vs, (res::'RES_N \<Rightarrow> 'RES)))" "(vs, res)" y
           rule: SemDoWhile.induct)
       apply simp_all
    done done

definition op_do_while :: "('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc" where
  "op_do_while f s = (if (\<exists>y. SemDoWhile f s y) then The (SemDoWhile f s) else PartialCorrect)"

inductive SemRec :: "(('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) comp \<Rightarrow> ('VAL,'RES_N,'RES) state \<Rightarrow> bool" where
  SemRec_I0: "(\<And>g. F g x = y) \<Longrightarrow> SemRec F x y"
| SemRec_IS: "SemRec (F o F) x y \<Longrightarrow> SemRec F x y"

definition op_recursion :: "'TY \<Rightarrow> 'TY \<Rightarrow> (('VAL,'RES_N,'RES) proc \<Rightarrow> ('VAL,'RES_N,'RES) proc) \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_recursion _ _ F s = (if (\<exists>t. SemRec F s t) then The (SemRec F s) else PartialCorrect)"

section \<open>Arithmetic instructions\<close>

subsection \<open>Integer arithmetic\<close>

definition op_const_int :: "nat \<Rightarrow> nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_int bits const = \<phi>M_put_Val (V_int.mk (bits,const))"

definition op_const_size_t :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_const_size_t c = \<phi>M_assume (c < 2 ^ addrspace_bits)
                          \<ggreater> \<phi>M_put_Val (V_int.mk (addrspace_bits,c))"
  \<comment> \<open> `op_const_size_t` checks overflow during the compilation towards certain decided platform.  \<close>

definition op_add :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_add bits =
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_a.
      \<phi>M_getV (\<tau>Int bits) (snd o V_int.dest) (\<lambda>val_b.
      \<phi>M_put_Val (V_int.mk (bits, (val_a + val_b mod 2^bits)))
  ))"

definition op_sub :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_sub bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (bits, (2^bits + val_b - val_a mod 2^bits)) # vs, res)
      else Fail)"

definition op_udiv :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_udiv bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (bits, (val_b div val_a)) # vs, res)
      else Fail)"

definition op_lt :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_lt bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (1, (if val_b < val_a then 1 else 0)) # vs, res)
      else Fail)"

definition op_le :: "nat \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_le bits = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (_, val_a) \<Rightarrow>
    case V_int.dest vb of (_, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int bits) \<and> vb \<in> Well_Type (\<tau>Int bits)
      then Success (V_int.mk (1, (if val_b \<le> val_a then 1 else 0)) # vs, res)
      else Fail)"

definition op_not :: "('VAL,'RES_N,'RES) proc"
  where "op_not = (\<lambda>(v#vs, res).
    case V_int.dest v of (bits, v') \<Rightarrow>
      if v \<in> Well_Type (\<tau>Int 1)
      then Success (V_int.mk (1, (1 - v')) # vs, res)
      else Fail)"

definition op_and :: "('VAL,'RES_N,'RES) proc"
  where "op_and = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (bit_a, val_a) \<Rightarrow>
    case V_int.dest vb of (bit_b, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int 1) \<and> vb \<in> Well_Type (\<tau>Int 1)
      then Success (V_int.mk (1, (val_a + val_b - 1)) # vs, res)
      else Fail)"

definition op_or :: "('VAL,'RES_N,'RES) proc"
  where "op_or = (\<lambda>(va#vb#vs, res).
    case V_int.dest va of (bit_a, val_a) \<Rightarrow>
    case V_int.dest vb of (bit_b, val_b) \<Rightarrow>
      if va \<in> Well_Type (\<tau>Int 1) \<and> vb \<in> Well_Type (\<tau>Int 1)
      then Success (V_int.mk (1, (val_a + val_b)) # vs, res)
      else Fail)"

definition op_equal :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_equal T = (\<lambda>(va#vb#vs, res).
    if va \<in> Well_Type T \<and> vb \<in> Well_Type T \<and> Can_EqCompare res va vb
    then Success (V_int.mk (1, (if EqCompare va vb then 1 else 0)) # vs, res)
    else Fail)"


section \<open>Tuple Operations\<close>

definition cons_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "cons_tup tys = (\<lambda>(vs,res).
    let N = length tys in
    if N \<le> length vs \<and> list_all2 (\<lambda>v t. v \<in> Well_Type t) (take N vs) tys
    then Success (V_tup.mk (take N vs) # drop N vs, res)
    else Fail)"

definition op_dest_tup :: "'TY list \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_dest_tup tys = (\<lambda>(v#vs,res).
    let tup = V_tup.dest v in
    if list_all2 (\<lambda>v t. v \<in> Well_Type t) tup tys
    then Success (tup @ vs, res)
    else Fail)"

definition op_get_tuple :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_get_tuple idx T = (\<lambda>(v#vs,res).
    if valid_index T idx \<and> v \<in> Well_Type T
    then Success (index_value idx v # vs, res)
    else Fail)"

definition op_set_tuple :: "nat list \<Rightarrow> 'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_set_tuple idx T = (\<lambda>(v#tup#vs,res).
    if valid_index T idx \<and> tup \<in> Well_Type T \<and> v \<in> Well_Type (index_type idx T)
    then Success (index_mod_value idx (\<lambda>_. v) tup # vs, res)
    else Fail)"


section \<open>Memory & Pointer Operations\<close>

definition op_get_element_pointer :: "'TY \<Rightarrow> nat list \<Rightarrow>('VAL,'RES_N,'RES) proc"
  where \<open>op_get_element_pointer T idx = (\<lambda>(raddr#vs, res).
    case V_pointer.dest raddr of seg |: ofst \<Rightarrow>
      Success (V_pointer.mk (seg |: ofst + to_size_t (index_offset T idx)) # vs, res))\<close>

definition op_add_pointer :: "('VAL,'RES_N,'RES) proc"
  where "op_add_pointer = (\<lambda>(raddr1#raddr2#vs, res) \<Rightarrow>
    case V_pointer.dest raddr1 of seg1 |: ofst1 \<Rightarrow>
    case V_pointer.dest raddr2 of seg2 |: ofst2 \<Rightarrow>
    if (seg1 = Null \<or> seg2 = Null)
    then let seg = if seg1 = Null then seg2 else seg1
          in Success (V_pointer.mk (seg |: ofst1 + ofst2) # vs, res)
    else Fail)"


definition op_load :: "'TY \<Rightarrow> ('VAL,'RES_N,'RES) proc"
  where "op_load TY = (\<lambda>(raddr'#vs, res) \<Rightarrow>
    let raddr = V_pointer.dest raddr'
      ; laddr = rawaddr_to_log TY raddr
      ; mem = the_fine (R_mem.get res)
     in if (\<exists>laddr'. valid_logaddr laddr' \<and> logaddr_type laddr' = TY \<and> logaddr_to_raw laddr' = raddr)
           \<and> 0 < MemObj_Size TY
           \<and> memaddr.segment laddr \<in> dom mem
        then Success (sem_read_mem laddr res # vs,res)
        else Fail)"

(* definition "heap_assignN n v seg heap = (\<lambda>key. case key of MemAddress (seg' |+ ofs') \<Rightarrow>
      if seg' = seg \<and> ofs' < n then v else
      if seg' = seg \<and> ofs' = n then Some DM_void else heap key | _ \<Rightarrow> heap key)"

definition op_alloc :: "('x::{zero,field}) itself \<Rightarrow> size_t word \<times> ('r::stack) \<longmapsto> memptr \<times>'r"
  where "op_alloc _ s = (case s of (heap,n,r) \<Rightarrow>  let seg = malloc heap in
  if segment_len seg = unat n \<and> segment_llty seg = LLTY('x) then
    Success (heap_assignN (unat n) (Some (deepize (0 :: 'x))) seg heap, memptr (seg |+ 0), r)
  else PartialCorrect)"

definition op_store :: " 'x itself \<Rightarrow> 'a itself \<Rightarrow> ('a::lrep,'a,'x,'x) index \<Rightarrow> 'x::field \<times> memptr \<times> ('r::stack) \<longmapsto> 'r "
  where "op_store _ _ idx s = (case s of (heap, x, memptr addr, r) \<Rightarrow>
    (let key = MemAddress (logical_addr_of addr) in
    case heap key of Some data \<Rightarrow>
      Success (heap(key \<mapsto> map_deepmodel (map_idx idx (\<lambda>_. x)) data), r) | _ \<Rightarrow> Fail))"

definition op_free :: " memptr \<times> ('r::stack) \<longmapsto> 'r "
  where "op_free s = (case s of (h,memptr (base |+ ofs),r) \<Rightarrow>
    (if ofs = 0 then Success (h |` (-{MemAddress (base |+ ofs) | ofs. True}), r) else Fail))"

*)

end

end
