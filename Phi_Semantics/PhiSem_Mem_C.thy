theory PhiSem_Mem_C
  imports PhiSem_Mem_Pointer
  abbrevs "<mem>" = "\<m>\<e>\<m>"
      and "<mem-blk>" = "\<m>\<e>\<m>-\<b>\<l>\<k>"
      and "<slice>" = "\<s>\<l>\<i>\<c>\<e>"
begin

section \<open>Semantics\<close>

subsection \<open>Models\<close>

(* For technical reasons, the memory resource is installed in \<^file>\<open>PhiSem_Mem_Pointer.thy\<close> *)

(*
definition Valid_Mem :: "('TY,'VAL) R_mem set"
  where "Valid_Mem = { Fine h |h. finite (dom h)
                                \<and> (\<forall>seg \<in> dom h. h seg \<in> Some ` Well_Type (segidx.layout seg))}"

lemma Valid_Mem_1[simp]: \<open>1 \<in> Valid_Mem\<close>
  unfolding Valid_Mem_def one_fun_def one_fine_def by simp
*)


subsection \<open>Fiction\<close>

declare [[\<phi>trace_reasoning = 0]]

type_synonym mem_fic = \<open>aggregate_path \<Rightarrow> VAL discrete share option\<close> \<comment> \<open>fiction of a single memory object\<close>

fiction_space aggregate_mem =
  aggregate_mem :: \<open>RES.aggregate_mem.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>blk. \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (memblk.layout blk)))\<close>
     (perm_aggregate_mem_fiction RES.aggregate_mem memblk.layout)
  by (standard; simp)


section \<open>Basic \<phi>Types for Semantic Models\<close>


(* subsubsection \<open>Slice Pointer\<close>

text \<open>A limitation of TypPtr is that it cannot point to the end of an array,
  because there is no object exists at the end. To address this, we provide slice pointer which
  can range over a piece of the array including the end.\<close>

definition SlicePtr :: "TY \<Rightarrow> (VAL, logaddr \<times> nat \<times> nat) \<phi>"
  where "SlicePtr TY = (\<lambda>(base,i,len).
    if valid_logaddr base \<and> base \<noteq> 0 \<and> (\<exists>N. logaddr_type base = array N TY \<and> len \<le> N)
        \<and> 0 < MemObj_Size TY \<and> i \<le> len
    then { V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY)) }
    else {})"

lemma SlicePtr_expn[\<phi>expns]:
  \<open>v \<in> ((base, i, len) \<Ztypecolon> SlicePtr TY) \<longleftrightarrow>
      valid_logaddr base \<and> base \<noteq> 0
      \<and> (\<exists>N. logaddr_type base = \<tau>Array N TY \<and> len \<le> N)
      \<and> 0 < MemObj_Size TY \<and> i \<le> len
      \<and> v = V_pointer.mk (logaddr_to_raw base ||+ of_nat (i * MemObj_Size TY))\<close>
  unfolding SlicePtr_def \<phi>Type_def by simp blast

lemma SlicePtr_inhabited[\<phi>reason_elim!,elim!]:
  \<open>Inhabited ((base, i, len) \<Ztypecolon> SlicePtr TY)
\<Longrightarrow> (\<And>N. valid_logaddr base \<Longrightarrow> base \<noteq> 0 \<Longrightarrow> logaddr_type base = \<tau>Array N TY \<Longrightarrow> len \<le> N
          \<Longrightarrow> 0 < MemObj_Size TY \<Longrightarrow> i \<le> len \<Longrightarrow> C)
\<Longrightarrow> C\<close>
  unfolding Inhabited_def SlicePtr_expn by simp blast

lemma SlicePtr_eqcmp[\<phi>reason on \<open>\<phi>Equal (SlicePtr ?TY) ?c ?eq\<close>]:
    "\<phi>Equal (SlicePtr TY) (\<lambda>x y. fst x = fst y) (\<lambda>(_,i1,_) (_,i2,_). i1 = i2)"
  unfolding \<phi>Equal_def
  apply (clarsimp simp add: \<phi>expns word_of_nat_eq_iff take_bit_nat_def simp del: of_nat_mult)
  subgoal premises for addr i1 n1 i2 N n2 proof -
    note logaddr_storable_in_mem[OF \<open>valid_logaddr addr\<close> \<open>addr \<noteq> 0\<close>,
            unfolded \<open>logaddr_type addr = \<tau>Array N TY\<close>, unfolded memobj_size_arr]
    then have \<open>i1 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
          and \<open>i2 * MemObj_Size TY < 2 ^ addrspace_bits\<close>
      by (meson \<open>i1 \<le> n1\<close> \<open>n1 \<le> N\<close> \<open>i2 \<le> n2\<close> \<open>n2 \<le> N\<close> dual_order.strict_trans2 mult_le_mono1)+
    then show ?thesis
      using \<open>0 < MemObj_Size TY\<close> by fastforce 
  qed
  done

lemma SlicePtr_semty[\<phi>reason on \<open>\<phi>SemType (?x \<Ztypecolon> SlicePtr ?TY) ?ty\<close>]:
  \<open>\<phi>SemType (x \<Ztypecolon> SlicePtr TY) \<tau>Pointer\<close>
  unfolding \<phi>SemType_def subset_iff
  by (cases x, simp add: \<phi>expns valid_logaddr_def)

*)



subsection \<open>Coercion from Value Spec to Mem Spec\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def Mem_Coercion :: \<open>(VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> _" [81] 80)
  where \<open>Mem_Coercion T \<equiv> (o) (to_share o map_option discrete) o Map_of_Val \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Commutativity_Deriver

definition Guided_Mem_Coercion :: \<open>TY \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[_] _" [50,81] 80)
  where \<open>\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T \<equiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T\<close>



  

(* \<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 Mem_Coercion Mem_Coercion Mem_Coercion (\<^emph>) (\<^emph>) T U (\<lambda>_. True) (embedded_func (\<lambda>x. x) (\<lambda>_. True)) \<close> *)


subsection \<open>Memory Object\<close>

declare [[\<phi>trace_reasoning = 0]]

\<phi>type_def MemBlk :: \<open>memblk \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<m>\<e>\<m>-\<b>\<l>\<k>[_]")
  where \<open>MemBlk blk T \<equiv> FIC.aggregate_mem.\<phi> (blk \<^bold>\<rightarrow> T)\<close>
  deriving Sep_Functor_1


subsubsection \<open>Syntax\<close>

paragraph \<open>Memory Object\<close>

consts Mem_synt :: \<open>logaddr \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<m>\<e>\<m>[_] _" [10,901] 900)

ML \<open>
structure Phi_Mem_Parser = Handlers (
  type arg = (Proof.context * int (*index in \<open>*\<close>-sequence*)) * (Proof.context * int -> term -> term) * term
  type ret = term
)
structure Phi_Mem_Printer = Handlers (
  type arg = Proof.context * (Proof.context -> term -> term) * term
  type ret = term
)
\<close>

print_translation \<open>
  [(\<^const_syntax>\<open>MemBlk\<close>, fn ctxt => fn [Const(\<^const_syntax>\<open>memaddr.blk\<close>, _) $ addr,
                                         Const(\<^const_syntax>\<open>\<phi>MapAt_L\<close>, _) $ (Const(\<^const_syntax>\<open>memaddr.index\<close>, _) $ addr') $ T] =>
  let val _ = if addr aconv addr' then () else raise Match
      val printers = Phi_Mem_Printer.invoke (Context.Proof ctxt)
      fun print ctxt term =
        case printers (ctxt, print, term)
          of SOME ret => ret
           | NONE => (case term of Const(\<^const_syntax>\<open>Mem_Coercion\<close>, _) $ X => X
                                 | _ => term)
   in Const(\<^const_syntax>\<open>Mem_synt\<close>, dummyT)
    $ addr
    $ print ctxt T
  end )]
\<close>

parse_translation \<open>[
  (\<^const_syntax>\<open>Mem_synt\<close>, fn ctxt => fn [addr, T] =>
  let val parsers = Phi_Mem_Parser.invoke (Context.Proof ctxt)
      fun parse ctxt term =
        case parsers (ctxt, parse, term)
          of SOME ret => ret
           | NONE => if Term.exists_Const (fn (\<^const_syntax>\<open>Mem_Coercion\<close>, _) => true
                                            | (\<^const_syntax>\<open>Guided_Mem_Coercion\<close>, _) => true
                                            | _ => false) term
                     then term
                     else Const(\<^const_syntax>\<open>Mem_Coercion\<close>, dummyT) $ term
  in Const(\<^const_name>\<open>MemBlk\<close>, dummyT)
      $ (Const(\<^const_name>\<open>memaddr.blk\<close>, dummyT) $ addr)
      $ (
     Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, dummyT)
      $ (Const(\<^const_name>\<open>memaddr.index\<close>, dummyT) $ addr)
      $ parse (ctxt, 0) T)
  end)
]\<close>

setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 100 (
    fn ((ctxt,i), f, Const(\<^const_syntax>\<open>\<phi>Prod\<close>, T) $ A $ B) =>
         (case A of Const(\<^const_syntax>\<open>\<phi>Prod\<close>, _) => NONE (*nested product-sequence is rejected*)
             | _ => SOME (Const(\<^const_syntax>\<open>\<phi>Prod\<close>, T) $ f (ctxt,i) A $ f (ctxt,i+1) B))
     | (ctxt, f, Const(\<^const_syntax>\<open>\<phi>Share\<close>, Ty) $ n $ T) =>
          SOME (Const(\<^const_syntax>\<open>\<phi>Share\<close>, Ty) $ n $ f ctxt T)
     | _ => NONE)

#>Phi_Mem_Printer.add 100 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>\<phi>Prod\<close>, T) $ A $ B) =>
          SOME (Const(\<^const_syntax>\<open>\<phi>Prod\<close>, T) $ f ctxt A $ f ctxt B)
     | _ => NONE)
)\<close>

(* examples
term \<open>n \<odiv> T\<close>
term \<open>\<m>\<e>\<m>[addr] T\<close>
term \<open>MAKE\<close>
ML \<open>\<^const_name>\<open>MAKE\<close>\<close>
ML \<open>@{term \<open>MAKE (n \<odiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)\<close>}\<close>
ML \<open>@{term \<open>\<m>\<e>\<m>[addr] (MAKE (n \<odiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T))\<close>}\<close>
*)

paragraph \<open>Slice\<close>

consts Slice_synt :: \<open>nat \<Rightarrow> nat \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (mem_fic, 'a list) \<phi>\<close> ("\<s>\<l>\<i>\<c>\<e>[_, _] _" [10,10,911] 910)

translations "\<s>\<l>\<i>\<c>\<e>[start, len] T" == "\<big_ast>\<^sub>\<bbbT> CONST AgIdx_N \<lbrakk>start : len\<rwpar> T"

setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 101 (
    fn ((ctxt,_), f, Const(\<^const_syntax>\<open>\<phi>Mul_Quant_Tree\<close>, Ty)
                        $ Const(\<^const_syntax>\<open>AgIdx_N\<close>, Ty2)
                        $ iv
                        $ T ) =>
          SOME (Const(\<^const_name>\<open>\<phi>Mul_Quant_Tree\<close>, Ty)
                        $ Const(\<^const_name>\<open>AgIdx_N\<close>, Ty2)
                        $ iv
                        $ f (ctxt,0) T )
     | ((ctxt,_), f, Const(\<^const_name>\<open>\<phi>Mul_Quant_Tree\<close>, Ty)
                        $ Const(\<^const_name>\<open>AgIdx_N\<close>, Ty2) $ n $ m $ A
                        $ iv
                        $ T ) =>
          SOME (Const(\<^const_syntax>\<open>\<phi>Mul_Quant_Tree\<close>, Ty)
                        $ Const(\<^const_syntax>\<open>AgIdx_N\<close>, Ty2) $ n $ m $ A
                        $ iv
                        $ f (ctxt,0) T )
     | X => NONE)

#>Phi_Mem_Printer.add 101 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>\<phi>Mul_Quant_Tree\<close>, Ty)
                        $ Const(\<^const_syntax>\<open>AgIdx_N\<close>, Ty2)
                        $ iv
                        $ T) =>
          SOME (Const(\<^const_syntax>\<open>\<phi>Mul_Quant_Tree\<close>, Ty)
                        $ Const(\<^const_syntax>\<open>AgIdx_N\<close>, Ty2)
                        $ iv
                        $ f ctxt T)
     | _ => NONE)
)\<close>

(* example
term \<open>\<m>\<e>\<m>[addr] \<s>\<l>\<i>\<c>\<e>[start, len] T\<close>
*)

section \<open>Instructions & Their Specifications\<close>


proc op_load_mem:
  input \<open>state\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<close>
  requires Extr: \<open>\<g>\<e>\<t> x \<Ztypecolon> \<m>\<e>\<m>[addr] (n \<odiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T) \<f>\<r>\<o>\<m> state \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  output \<open>state\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> T\<close>
  unfolding Guided_Mem_Coercion_def
  including \<phi>sem_type_sat_EIF
\<medium_left_bracket>
  $addr semantic_local_value \<open>pointer\<close>

  apply_rule ToA_Extract_onward[OF Extr, unfolded Remains_\<phi>Cond_Item]

  have [useful]: \<open>0 < n\<close>
    by (simp add: the_\<phi>(2)) ;;

  to \<open>OPEN _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  apply_rule FIC.aggregate_mem.getter_rule[where u_idx=v and n=n
                and cblk=\<open>memaddr.blk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1))\<close>
                and blk=\<open>memaddr.blk addr\<close>
                and idx=\<open>memaddr.index addr\<close>]

  \<open>x \<Ztypecolon> MAKE (\<m>\<e>\<m>[addr] (n \<odiv> MAKE (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)))\<close>

  apply_rule ToA_Extract_backward[OF Extr, unfolded Remains_\<phi>Cond_Item] 

  semantic_assert \<open>index_value (memaddr.index (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)))) (discrete.dest (\<phi>arg.dest \<v>1)) \<in> Well_Type TY\<close>
  semantic_return \<open>index_value (memaddr.index (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)))) (discrete.dest (\<phi>arg.dest \<v>1)) \<Turnstile> (x \<Ztypecolon> T)\<close>
\<medium_right_bracket> .


proc op_store_mem:
  input  \<open>State\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U\<close>
  requires Map: \<open>\<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] U)
                   \<f>\<o>\<r> x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)
                 \<f>\<r>\<o>\<m> State \<t>\<o> State' \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
       and \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  output \<open>\<lambda>_::unit \<phi>arg. State'\<close>
  including \<phi>sem_type_sat_EIF
  unfolding Guided_Mem_Coercion_def
\<medium_left_bracket>
  apply_rule ToA_Subst_onward[OF Map, unfolded Remains_\<phi>Cond_Item]

  to \<open>OPEN _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  $addr semantic_local_value \<open>pointer\<close>
  $y semantic_local_value \<open>TY\<close>

  apply_rule FIC.aggregate_mem.setter_rule[
        where u_idx=v and idx=\<open>memaddr.index addr\<close>
          and v=\<open>\<phi>arg.dest \<a>\<r>\<g>2\<close>
          and blk=\<open>memaddr.blk addr\<close>
          and cblk = \<open>memaddr.blk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1))\<close>
          and cidx = \<open>memaddr.index (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)))\<close>]

  \<open>y \<Ztypecolon> MAKE (\<m>\<e>\<m>[addr] (MAKE (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U)))\<close>

  apply_rule ToA_Subst_backward[OF Map, unfolded Remains_\<phi>Cond_Item]
\<medium_right_bracket> .


text \<open>(depreciated! as we can have non-deterministic monad)
  A simplification in the semantics is, we only consider allocation with zero initialization
  (i.e., \<open>calloc\<close> but not \<open>malloc\<close>), which frees us from modelling uninitialized memory state so
  simplifies the system a lot. We can do so because we aim to provide a certified language
  over a subset of C semantics. The absence of non-initialized allocation does not affect the functionality
  but only little performance which we believe worthy against the simplification in reasoning. \<close>

proc op_allocate_mem_1:
  input \<open>Void\<close>
  requires \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>z \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY \<s>\<u>\<b>\<j> addr. memaddr.index addr = 0\<close>
  including Semantic_Zero_Val_EIF_brute
\<medium_left_bracket>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=TY and v=\<open>the (Zero TY)\<close>]

  \<open>z \<Ztypecolon> MAKE (\<m>\<e>\<m>[memaddr blk 0] (MAKE (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)))\<close>

  semantic_assumption \<open>type_storable_in_mem TY\<close>

  have t1: \<open>valid_logaddr (memaddr blk [])\<close>
    unfolding valid_logaddr_def Valid_MemBlk_def
    using \<open>memblk.layout blk = TY\<close>
    by (cases blk; clarsimp simp: \<open>type_storable_in_mem TY\<close>) ;;

  semantic_return \<open>V_pointer.mk (memaddr (\<phi>arg.dest \<v>1) 0) \<Turnstile> (memaddr blk 0 \<Ztypecolon> Ptr TY)\<close>
    
\<medium_right_bracket> .
 
proc op_free_mem:
  input \<open>x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<close>
  requires \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  premises \<open>memaddr.index addr = 0\<close>
  output \<open>Void\<close>
  including \<phi>sem_type_sat_EIF
\<medium_left_bracket>
  to \<open>OPEN _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  apply_rule FIC.aggregate_mem.deallocate_rule[where v=v and blk=\<open>memaddr.blk addr\<close>]

\<medium_right_bracket> .


section \<open>IDE-CP Interfaces\<close>

declare_\<phi>lang_operator postfix %\<phi>lang_deref "!"

declare op_load_mem_\<phi>app[\<phi>overload "!"]
        op_store_mem_\<phi>app[\<phi>overload ":="]

thm "!_\<phi>app"

text \<open>We differentiate \<open>\<leftarrow>\<close> and \<open>:=\<close>.
  \<open>\<leftarrow>\<close> is used to update the value of a local variable.
  \<open>:=\<close> is used to change the value of a memory object.
  Without this differentiation, ambiguity occurs when we have a local variable of a pointer
  pointing to a memory object which also stores a pointer, and an assignment can ambiguously refer
  to updating the variable or writing to the memory object.
\<close>


(*
setup \<open>fn thy => thy
|> Phi_Opr_Stack.decl_postfix (@{priority %\<phi>lang_deref}, "!", SOME 0) |> snd
\<close>
*)

proc(nodef) "_load_mem_bracket_"[\<phi>overload "[]"]:
  input \<open>state\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY0\<close>
  requires L1[]: \<open>parse_eleidx_input TY0 input_index sem_idx spec_idx pidx reject\<close>
       and L2[]: \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and L3[]: \<open>is_valid_index_of spec_idx TY0 TY\<close>
       and L4[]: \<open>report_unprocessed_element_index reject\<close>
  requires Extr[]: \<open>\<g>\<e>\<t> x \<Ztypecolon> \<m>\<e>\<m>[addr_geps addr pidx] (n \<odiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T) \<f>\<r>\<o>\<m> state \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and L01[]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  output \<open>state\<heavy_comma> x \<Ztypecolon> \<v>\<a>\<l> T\<close>
\<medium_left_bracket>
  $addr apply_rule op_get_element_pointer[OF L1 Premise_I[OF L2] L3 L4]
  apply_rule op_load_mem[OF Extr L01]
\<medium_right_bracket> .


proc(nodef) "_store_mem_bracket_"[\<phi>overload "[]:="]:
  input \<open>state\<heavy_comma> addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY0\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U\<close>
  requires L1[]: \<open>parse_eleidx_input TY0 input_index sem_idx spec_idx pidx reject\<close>
       and L2[]: \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and L3[]: \<open>is_valid_index_of spec_idx TY0 TY\<close>
       and L4[]: \<open>report_unprocessed_element_index reject\<close>
  requires Map[]: \<open>\<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> \<m>\<e>\<m>[addr_geps addr pidx] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] U)
                     \<f>\<o>\<r> x \<Ztypecolon> \<m>\<e>\<m>[addr_geps addr pidx] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)
                   \<f>\<r>\<o>\<m> state \<t>\<o> state' \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and L01[]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
       and L02[]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  output \<open>\<lambda>_::unit \<phi>arg. state'\<close>
\<medium_left_bracket>
  $addr apply_rule op_get_element_pointer[OF L1 Premise_I[OF L2] L3 L4]
  $y apply_rule op_store_mem[OF Map L01 L02]
\<medium_right_bracket> .

section \<open>Reasoning Setup\<close>

\<phi>reasoner_group mapToA_mem_coerce_all = (%\<phi>mapToA_norm, [%\<phi>mapToA_norm, %\<phi>mapToA_norm+100])
    \<open>rules resolving the memory coercion. Given a target like \<open>\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] \<lbrace> a: T, b: U \<rbrace>\<close>,
      the rules reduce it by moving \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> inside, to \<open>a \<^bold>\<rightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] T \<^emph> b \<^bold>\<rightarrow> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] U \<rbrace>,
      untill atomic types are reached.\<close>\<close>
  and mapToA_mem_coerce = (%mapToA_mem_coerce_all+5, [%mapToA_mem_coerce_all+5, %mapToA_mem_coerce_all+100])
    \<open>user rules\<close>
  and mapToA_mem_coerce_end = (%mapToA_mem_coerce_all, [%mapToA_mem_coerce_all, %mapToA_mem_coerce_all+4])
        < mapToA_mem_coerce
    \<open>system end\<close>

lemma [\<phi>reason %mapToA_mem_coerce_end]:
  \<open> Atomic_SemTyp ty \<or>\<^sub>c\<^sub>u\<^sub>t ERROR TEXT(\<open>\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> rule for semantic type\<close> ty \<open>is not given\<close>)

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U \<^emph>[C\<^sub>R] R \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D

\<Longrightarrow> \<m>\<a>\<p> g : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] U \<^emph>[C\<^sub>R] R \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[ty] U' \<^emph>[C\<^sub>R] R'
    \<o>\<v>\<e>\<r> f : T \<^emph>[C\<^sub>W] W \<mapsto> T' \<^emph>[C\<^sub>W] W'
    \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> getter \<s>\<e>\<t>\<t>\<e>\<r> setter \<i>\<n> D \<close>
  unfolding Guided_Mem_Coercion_def .


end