theory PhiSem_Mem_C
  imports PhiSem_Mem_Pointer
  abbrevs "<mem>" = "\<m>\<e>\<m>"
      and "<mem-blk>" = "\<m>\<e>\<m>-\<b>\<l>\<k>"
      and "<slice>" = "\<s>\<l>\<i>\<c>\<e>"
      and "<ref>" = "\<r>\<e>\<f>"
begin

section \<open>Semantics\<close>

subsection \<open>Fiction\<close>

type_synonym mem_fic = \<open>aggregate_path \<Rightarrow> VAL discrete share option\<close> \<comment> \<open>fiction of a single memory object\<close>

fiction_space aggregate_mem =
  aggregate_mem :: \<open>RES.aggregate_mem.basic_fiction \<Zcomp>\<^sub>\<I> \<F>_pointwise (\<lambda>blk. \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (memblk.layout blk)))\<close>
     (perm_aggregate_mem_fiction RES.aggregate_mem memblk.layout Null)
  by (standard; simp)


section \<open>Basic \<phi>Types for Semantic Models\<close>


subsection \<open>Coercion from Value Spec to Mem Spec\<close>

\<phi>type_def Mem_Coercion :: \<open>(VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> _" [81] 80)
  where \<open>Mem_Coercion T \<equiv> (o) (to_share o map_option discrete) o Map_of_Val \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Commutativity_Deriver

\<phi>type_def Guided_Mem_Coercion :: \<open>TY \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[_] _" [50,81] 80)
  where \<open>\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T \<equiv> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T\<close>


subsection \<open>Memory Object\<close>


\<phi>type_def MemBlk :: \<open>memblk \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<m>\<e>\<m>-\<b>\<l>\<k>[_]")
  where \<open>x \<Ztypecolon> MemBlk blk T \<equiv> x \<Ztypecolon> FIC.aggregate_mem.\<phi> (blk \<^bold>\<rightarrow> T) \<s>\<u>\<b>\<j> blk \<noteq> Null\<close>
  deriving Sep_Functor_1

\<phi>type_def Mem :: \<open>logaddr \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close>
  where \<open>Mem addr T \<equiv> \<m>\<e>\<m>-\<b>\<l>\<k>[memaddr.blk addr] (memaddr.index addr \<^bold>\<rightarrow>\<^sub>@ T) \<close>
  deriving Sep_Functor_1

declare Mem.intro_reasoning[\<phi>reason default]
        Mem.elim_reasoning [\<phi>reason default]
        Mem.intro_map[where \<phi>'=\<open>\<lambda>x. x\<close>, simplified, \<phi>reason %\<phi>mapToA_mapper]
        Mem.elim_map [where \<phi> =\<open>\<lambda>x. x\<close>, simplified, \<phi>reason %\<phi>mapToA_mapper]


subsubsection \<open>Syntax\<close>

paragraph \<open>Memory Object\<close>

consts Mem_synt :: \<open>logaddr \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<m>\<e>\<m>[_] _" [10,901] 900)
       may_mem_coerce :: \<open>('c, 'a) \<phi> \<Rightarrow> (mem_fic, 'a) \<phi>\<close>

\<phi>adhoc_overloading may_mem_coerce \<open>\<lambda>x. x\<close> Mem_Coercion

abbreviation ("input") no_mem_coerce :: \<open>(mem_fic, 'a) \<phi> \<Rightarrow> (mem_fic, 'a) \<phi>\<close> ("\<r>\<e>\<f> _" [910] 910)
  where \<open>no_mem_coerce \<equiv> (\<lambda>x. x)\<close>

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
  [(\<^const_syntax>\<open>Mem\<close>, fn ctxt => fn [addr, T] =>
  let val printers = Phi_Mem_Printer.invoke (Context.Proof ctxt)
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
                     else Const(\<^const_syntax>\<open>may_mem_coerce\<close>, dummyT) $ term
  in Const(\<^const_name>\<open>Mem\<close>, dummyT) $ addr $ parse (ctxt, 0) T
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


paragraph \<open>Slice\<close>

consts Slice_synt :: \<open>nat \<Rightarrow> nat \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (mem_fic, 'a list) \<phi>\<close> ("\<s>\<l>\<i>\<c>\<e>[_, _] _" [10,10,910] 911)

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


section \<open>Instructions & Their Specifications\<close>

subsection \<open>Auxiliary\<close>

definition \<open>address_to_base addr \<equiv> memaddr.index addr = 0\<close>
  \<comment> \<open>\<open>addr\<close> points to the base of an allocation block\<close>
  \<comment> \<open>wraps and prevents the rewrite \<open>memaddr.index addr = 0\<close>,
      as \<open>address_to_base addr\<close> should be treated as an atom\<close>

subsection \<open>Main\<close>

proc op_load_mem:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> state\<close>
  requires Extr: \<open>\<g>\<e>\<t> x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T) \<f>\<r>\<o>\<m> state \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> state\<close>
  unfolding Guided_Mem_Coercion_def
  including \<phi>sem_type_sat_EIF
\<medium_left_bracket>
  $addr semantic_local_value \<open>pointer\<close>

  apply_rule ToA_Extract_onward[OF Extr, unfolded Remains_\<phi>Cond_Item]

  to \<open>OPEN _ _\<close> to \<open>OPEN _ _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  apply_rule FIC.aggregate_mem.getter_rule[where u_idx=v and n=1
                and cblk=\<open>memaddr.blk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1))\<close>
                and blk=\<open>memaddr.blk addr\<close>
                and idx=\<open>memaddr.index addr\<close>]

  \<open>x \<Ztypecolon> MAKE _ (\<m>\<e>\<m>-\<b>\<l>\<k>[memaddr.blk addr] (memaddr.index addr \<^bold>\<rightarrow>\<^sub>@ (MAKE _ (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T))))\<close>
  \<open>x \<Ztypecolon> MAKE _ (\<m>\<e>\<m>[addr] T)\<close>

  apply_rule ToA_Extract_backward[OF Extr, unfolded Remains_\<phi>Cond_Item] 

  semantic_assert \<open>index_value (memaddr.index (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)))) (discrete.dest (\<phi>arg.dest \<v>1)) \<in> Well_Type TY\<close>
  semantic_return \<open>index_value (memaddr.index (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)))) (discrete.dest (\<phi>arg.dest \<v>1)) \<Turnstile> (x \<Ztypecolon> T)\<close>
\<medium_right_bracket> .

proc op_store_mem:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U\<heavy_comma> State\<close>
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

  to \<open>OPEN _ _\<close> to \<open>OPEN _ _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  $addr semantic_local_value \<open>pointer\<close>
  $y semantic_local_value \<open>TY\<close>

  apply_rule FIC.aggregate_mem.setter_rule[
        where u_idx=v and idx=\<open>memaddr.index addr\<close>
          and v=\<open>\<phi>arg.dest \<a>\<r>\<g>2\<close>
          and blk=\<open>memaddr.blk addr\<close>
          and cblk = \<open>memaddr.blk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1))\<close>
          and cidx = \<open>memaddr.index (rawaddr_to_log TY (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1)))\<close>]

  \<open>y \<Ztypecolon> MAKE _ (\<m>\<e>\<m>-\<b>\<l>\<k>[memaddr.blk addr] (memaddr.index addr \<^bold>\<rightarrow>\<^sub>@ (MAKE _ (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> U))))\<close>
  \<open>y \<Ztypecolon> MAKE _ (\<m>\<e>\<m>[addr] U)\<close>
  
  apply_rule ToA_Subst_backward[OF Map, unfolded Remains_\<phi>Cond_Item]
\<medium_right_bracket> .


(*
proc op_store_mem:
  input  \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U\<heavy_comma> State\<close>
  requires \<open>parse_eleidx_input TY input_index sem_idx spec_idx reject\<close>
       and \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and [unfolded is_valid_index_of_def, useful]: \<open>is_valid_index_of spec_idx TY TY'\<close>
       and \<open>report_unprocessed_element_index reject\<close>
  requires Map: \<open>\<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] U)
                   \<f>\<o>\<r> x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)
                 \<f>\<r>\<o>\<m> State \<t>\<o> State' \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
       and \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  output \<open>\<lambda>_::unit \<phi>arg. State'\<close>
\<medium_left_bracket>
*)


text \<open>(deprecated! as we can have non-deterministic monad)
  A simplification in the semantics is, we only consider allocation with zero initialization
  (i.e., \<open>calloc\<close> but not \<open>malloc\<close>), which frees us from modelling uninitialized memory state so
  simplifies the system a lot. We can do so because we aim to provide a certified language
  over a subset of C semantics. The absence of non-initialized allocation does not affect the functionality
  but only little performance which we believe worthy against the simplification in reasoning. \<close>


proc calloc1:
  input \<open>Void\<close>
  requires \<open>\<p>\<a>\<r>\<a>\<m> T\<close>
       and \<open>Semantic_Zero_Val TY T z\<close>
  output \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> z \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T) \<s>\<u>\<b>\<j> addr. address_to_base addr\<close>
  including Semantic_Zero_Val_EIF_brute
  unfolding address_to_base_def
\<medium_left_bracket>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=TY and v=\<open>the (Zero TY)\<close>]

  \<open>z \<Ztypecolon> MAKE _ (\<m>\<e>\<m>-\<b>\<l>\<k>[blk] (MAKE _ (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e> T)))\<close>
  \<open>z \<Ztypecolon> MAKE _ (\<m>\<e>\<m>[memaddr blk 0] T)\<close>

  semantic_assumption \<open>type_storable_in_mem TY\<close>

  have t1: \<open>valid_logaddr (memaddr blk [])\<close>
    by (insert \<phi>; auto simp add: Valid_MemBlk_def split: memblk.split) ;;

  semantic_return \<open>V_pointer.mk (memaddr (\<phi>arg.dest \<v>1) 0) \<Turnstile> (memaddr blk 0 \<Ztypecolon> Ptr TY)\<close>
    
\<medium_right_bracket> .

 
proc mfree:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY\<heavy_comma> x \<Ztypecolon> \<m>\<e>\<m>[addr] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)\<close>
  requires \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  premises \<open>address_to_base addr\<close>
  output \<open>Void\<close>
  including \<phi>sem_type_sat_EIF
  unfolding address_to_base_def Guided_Mem_Coercion_def
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> to \<open>OPEN _ _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v
  $addr semantic_local_value \<open>pointer\<close>

  apply_rule FIC.aggregate_mem.deallocate_rule
             [where v=v and blk=\<open>memaddr.blk (V_pointer.dest (\<phi>arg.dest \<a>\<r>\<g>1))\<close>]

\<medium_right_bracket> .


section \<open>IDE-CP Interfaces\<close>

declare_\<phi>lang_operator postfix %\<phi>lang_deref "!" \<comment> \<open>dereference operator\<close>

declare op_load_mem_\<phi>app[\<phi>overload "!"]
        op_store_mem_\<phi>app[\<phi>overload ":="]

text \<open>We differentiate \<open>\<leftarrow>\<close> and \<open>:=\<close>.
  \<open>\<leftarrow>\<close> is used to update the value of a local variable.
  \<open>:=\<close> is used to change the value of a memory object.
  Without this differentiation, ambiguity occurs when we have a local variable of a pointer
  pointing to a memory object which also stores a pointer, and an assignment can ambiguously refer
  to updating the variable or writing to the memory object.
\<close>


proc(nodef) "_load_mem_bracket_"[\<phi>overload "[]"]:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY0\<heavy_comma> state\<close>
  requires L1[]: \<open>parse_eleidx_input TY0 input_index sem_idx spec_idx reject\<close>
       and L2[]: \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and L3[]: \<open>is_valid_index_of spec_idx TY0 TY\<close>
       and L4[]: \<open>report_unprocessed_element_index reject\<close>
  requires Extr[]: \<open>\<g>\<e>\<t> x \<Ztypecolon> \<m>\<e>\<m>[addr_geps addr spec_idx] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T) \<f>\<r>\<o>\<m> state \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and L01[]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>x \<Ztypecolon> \<v>\<a>\<l> T\<heavy_comma> state\<close>
\<medium_left_bracket>
  $addr apply_rule op_get_element_pointer[OF L1 Premise_I[OF L2] L3 L4]
  apply_rule op_load_mem[OF Extr L01]
\<medium_right_bracket> .

proc(nodef) "_store_mem_bracket_"[\<phi>overload "[]:="]:
  input \<open>addr \<Ztypecolon> \<v>\<a>\<l> Ptr TY0\<heavy_comma> y \<Ztypecolon> \<v>\<a>\<l> U\<heavy_comma> state\<close>
  requires L1[]: \<open>parse_eleidx_input TY0 input_index sem_idx spec_idx reject\<close>
       and L2[]: \<open>\<c>\<o>\<n>\<d>\<i>\<t>\<i>\<o>\<n> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and L3[]: \<open>is_valid_index_of spec_idx TY0 TY\<close>
       and L4[]: \<open>report_unprocessed_element_index reject\<close>
  requires Map[]: \<open>\<s>\<u>\<b>\<s>\<t> y \<Ztypecolon> \<m>\<e>\<m>[addr_geps addr spec_idx] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] U)
                     \<f>\<o>\<r> x \<Ztypecolon> \<m>\<e>\<m>[addr_geps addr spec_idx] (\<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[TY] T)
                   \<f>\<r>\<o>\<m> state \<t>\<o> state' \<r>\<e>\<m>\<a>\<i>\<n>\<i>\<n>\<g>[C\<^sub>R] R\<close>
       and L01[]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
       and L02[]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>\<lambda>_::unit \<phi>arg. state'\<close>
\<medium_left_bracket>
  $addr apply_rule op_get_element_pointer[OF L1 Premise_I[OF L2] L3 L4] \<rightarrow> val ptr \<semicolon>
  apply_rule op_store_mem[OF Map L01 L02] ($ptr, $y)
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
  and ToA_mem_coerce = (%ToA_cut+100, [%ToA_cut+100, %ToA_cut+300])
    \<open>mem_coerce in transformation\<close>
  and ToA_mem_coerce_end = (%ToA_cut+90, [%ToA_cut+90, %ToA_cut+99])
      < ToA_mem_coerce
    \<open>system end\<close>

declare [[\<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow> \<open>_ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ \<close> (1000)
  and \<open>_ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow> \<open>_ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<w>\<i>\<t>\<h> _ \<close> (1000)
  and \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<w>\<i>\<t>\<h> _ \<close> (1000)
  and \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _ \<close> \<Rightarrow> \<open>_ \<t>\<r>\<a>\<n>\<s>\<f>\<o>\<r>\<m>\<s> _ \<Ztypecolon> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<w>\<i>\<t>\<h> _ \<close> (1000)
  and \<open>\<m>\<a>\<p> _ : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY'] _ \<^emph>[_] _
       \<o>\<v>\<e>\<r> _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close> \<Rightarrow>
      \<open>\<m>\<a>\<p> _ : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY'] _ \<^emph>[_] _
       \<o>\<v>\<e>\<r> _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>         (1000)
  and \<open>\<m>\<a>\<p> _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
       \<o>\<v>\<e>\<r> _ : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY'] _ \<^emph>[_] _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close> \<Rightarrow>
      \<open>\<m>\<a>\<p> _ : _ \<^emph>[_] _ \<mapsto> _ \<^emph>[_] _
       \<o>\<v>\<e>\<r> _ : \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY] _ \<^emph>[_] _ \<mapsto> \<m>\<e>\<m>-\<c>\<o>\<e>\<r>\<c>\<e>[?TY'] _ \<^emph>[_] _ \<w>\<i>\<t>\<h> \<g>\<e>\<t>\<t>\<e>\<r> _ \<s>\<e>\<t>\<t>\<e>\<r> _ \<i>\<n> _\<close>         (1000)
]]

consts \<A>_mem_coerce :: mode

declare Guided_Mem_Coercion.elim_map[where \<phi>=\<open>\<lambda>x. x\<close>, simplified, \<phi>reason %mapToA_mem_coerce_end]
        Guided_Mem_Coercion.elim_reasoning(1)[\<phi>reason %ToA_mem_coerce_end]
        Guided_Mem_Coercion.intro_reasoning(2)[where x=\<open>fst x\<close> and r=\<open>snd x\<close> for x, simplified,
                                               \<phi>reason %ToA_mem_coerce_end]

subsection \<open>Auxiliary Simplification\<close>

subsubsection \<open>Converting \<open>\<m>\<e>\<m>-\<b>\<l>\<k>[memaddr.blk a] ((memaddr.index a @ [i\<^sup>\<t>\<^sup>\<h>]) \<^bold>\<rightarrow>\<^sub>@ \<dots>\<close>
                          \<open>\<m>\<e>\<m>-\<b>\<l>\<k>[memaddr.blk a] (memaddr.index a \<^bold>\<rightarrow>\<^sub>@ [i\<^sup>\<t>\<^sup>\<h>]) \<^bold>\<rightarrow>\<^sub>@ \<dots>\<close>
                      to \<open>\<m>\<e>\<m>[a \<tribullet> i\<^sup>\<t>\<^sup>\<h>] \<dots>\<close>\<close>

lemma MemBlk_\<phi>MapAt_L_assoc[no_atp, \<phi>programming_simps, \<phi>programming_base_simps]:
  \<open> \<m>\<e>\<m>-\<b>\<l>\<k>[blk] (a \<^bold>\<rightarrow>\<^sub>@ b \<^bold>\<rightarrow>\<^sub>@ T) = \<m>\<e>\<m>-\<b>\<l>\<k>[blk] ((a @ b) \<^bold>\<rightarrow>\<^sub>@ T) \<close>
  by (simp add: \<phi>MapAt_L.scalar_assoc[simplified times_list_def])

simproc_setup MemBlk_\<phi>MapAt_repair (\<open>\<m>\<e>\<m>-\<b>\<l>\<k>[memaddr.blk addr] (idx \<^bold>\<rightarrow>\<^sub>@ T)\<close>) = \<open>fn _ => fn ctxt => fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>MemBlk\<close>, _) $ (Const(\<^const_name>\<open>memaddr.blk\<close>, _) $ a0)
                                    $ (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, _) $ idx $ _) =>
        let fun quick_chk (Const(\<^const_name>\<open>List.append\<close>, _) $ L $ _) = quick_chk L
              | quick_chk (Const(\<^const_name>\<open>list.Cons\<close>, _) $ _ $ L) = quick_chk L
              | quick_chk (Const(\<^const_name>\<open>list.Nil\<close>, _)) = true
              | quick_chk (Const(\<^const_name>\<open>memaddr.index\<close>, _) $ a1) = a0 aconv a1
         in if quick_chk idx then
        let fun parse_idx ctmx (Const(\<^const_name>\<open>List.append\<close>, _) $ L $ R)
                  = parse_idx (Thm.dest_arg1 ctmx) L @ parse_idx (Thm.dest_arg ctmx) R
              | parse_idx ctmx (Const(\<^const_name>\<open>list.Cons\<close>, _) $ _ $ L)
                  = Thm.dest_arg1 ctmx :: parse_idx (Thm.dest_arg ctmx) L
              | parse_idx _ (Const(\<^const_name>\<open>list.Nil\<close>, _)) = []
              | parse_idx ctmx (Const(\<^const_name>\<open>memaddr.index\<close>, _) $ a1) =
                    if a0 aconv a1 then [] else raise Match
            val cidx = Thm.dest_arg1 (Thm.dest_arg ctm)
            val cT = Thm.dest_arg (Thm.dest_arg ctm)
            val idxs = parse_idx cidx idx
            val cblk = Thm.dest_arg1 ctm
            val caddr'= fold (fn i => fn a => Thm.apply (Thm.apply \<^cterm>\<open>addr_gep\<close> a) i) idxs
                             (Thm.dest_arg cblk)
            val rule = \<^instantiate>\<open>blk=cblk and idx=cidx and addr=caddr' and T=cT and 'a=\<open>Thm.dest_ctyp0 (Thm.ctyp_of_cterm cT)\<close>
                                in lemma \<open>memaddr.blk addr = blk
                                      \<Longrightarrow> memaddr.index addr = idx
                                      \<Longrightarrow> \<m>\<e>\<m>-\<b>\<l>\<k>[blk] (idx \<^bold>\<rightarrow>\<^sub>@ T) \<equiv> \<m>\<e>\<m>[addr] T\<close>
                                      by (simp add: Mem_def)\<close>
         in SOME rule
        end else NONE end \<close>


end