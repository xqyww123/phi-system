theory PhiSem_Mem_C
  imports PhiSem_Mem_Pointer
  abbrevs "<mem>" = "\<mem>"
      and "<mem-blk>" = "\<mem>-\<blk>"
      and "<slice>" = "\<slice>"
      and "<ref>" = "\<ref>"
begin

section \<open>Semantics\<close>

subsection \<open>Fiction\<close>

type_synonym mem_fic = \<open>aggregate_path \<Rightarrow> VAL discrete share option\<close> \<comment> \<open>fiction of a single memory object\<close>

fiction_space aggregate_mem =
  aggregate_mem :: \<open>RES.aggregate_mem.basic_fiction \<Zcomp>
                    \<F>_pointwise (\<lambda>blk.
                        \<F>_functional (Mem.Rep_of_Val_ins (block.layout blk)) (Mem.Rep_of_Val_ins_dom (block.layout blk)) \<Zcomp>
                        \<F>_functional ((\<circ>) to_share \<circ> Map_of_Val_ins) (Map_of_Val_ins_dom (block.layout blk)))\<close>
     (perm_MoV_fiction RES.aggregate_mem Byte_Rep_of_Val block.layout Null)
  by (standard, auto simp add: Mem.Rep_of_Val_ins_def BI_eq_iff)


section \<open>Basic \<phi>Types for Semantic Models\<close>


subsection \<open>Coercion from Value Spec to Mem Spec\<close>

\<phi>type_def Mem_Coercion :: \<open>(VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<mem>-\<coerce> _" [81] 80)
  where \<open>Mem_Coercion T \<equiv> (o) (to_share o map_option discrete) o Map_of_Val \<Zcomp>\<^sub>f T\<close>
  deriving Basic
       and Functional_Transformation_Functor
       and Commutativity_Deriver

\<phi>type_def Guided_Mem_Coercion :: \<open>TY \<Rightarrow> (VAL,'a) \<phi> \<Rightarrow> (mem_fic,'a) \<phi>\<close> ("\<mem>-\<coerce>[_] _" [50,81] 80)
  where \<open>\<mem>-\<coerce>[TY] T \<equiv> \<mem>-\<coerce> T\<close>


subsection \<open>Memory Object\<close>

\<phi>type_def MemBlk :: \<open>block \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<mem>-\<blk>[_]")
  where \<open>x \<Ztypecolon> MemBlk blk T \<equiv> x \<Ztypecolon> FIC.aggregate_mem.\<phi> (blk \<^bold>\<rightarrow> T) \<subj> blk \<noteq> Null\<close>
  deriving Sep_Functor_1

\<phi>type_def Mem :: \<open>address \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close>
  where \<open>Mem addr T \<equiv> \<mem>-\<blk>[addr.blk addr] (addr.offset addr \<^bold>\<rightarrow>\<^sub>@ T) \<close>
  deriving Sep_Functor_1

declare Mem.intro_reasoning[\<phi>reason default]
        Mem.elim_reasoning [\<phi>reason default]
        Mem.intro_map[where \<phi>'=\<open>\<lambda>x. x\<close>, simplified, \<phi>reason %\<phi>mapToA_mapper]
        Mem.elim_map [where \<phi> =\<open>\<lambda>x. x\<close>, simplified, \<phi>reason %\<phi>mapToA_mapper]

subsubsection \<open>Syntax\<close>
(*
paragraph \<open>Memory Object\<close>

abbreviation MemObj ("\<obj>[_] _" [10,901] 900)
  where \<open>\<obj>[addr] T \<equiv> Mem addr (\<mem>-\<coerce> T) \<phi>\<subj> address_to_base addr \<and> \<typeof> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
*)

consts may_mem_coerce :: \<open>('c, 'a) \<phi> \<Rightarrow> (mem_fic, 'a) \<phi>\<close>

(*\<open>\<mem>[_] _\<close> is a syntax constant, not a logical one: a parse translation is dispatched on the head
  of the application (\<^ML>\<open>Syntax_Phases\<close>, \<open>ast_to_term\<close>), and since Isabelle2025 the head of an
  application is wrapped in a positional constraint whenever it is a LOGICAL constant carrying
  mixfix syntax -- upon which the dispatch no longer reaches it, and the translation below is handed
  an empty argument list instead of \<open>[addr, T]\<close>.  A syntax constant is never wrapped, which is why
  every parse translation in the Isabelle distribution is keyed on one.*)
syntax "_Mem_synt" :: \<open>address \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (fiction, 'a) \<phi>\<close> ("\<mem>[_] _" [10,901] 900)
syntax_consts "_Mem_synt" \<rightleftharpoons> Mem

\<phi>adhoc_overloading may_mem_coerce \<open>\<lambda>x. x\<close> Mem_Coercion


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
   in Const(\<^syntax_const>\<open>_Mem_synt\<close>, dummyT)
    $ addr
    $ print ctxt T
  end )]
\<close>

parse_translation \<open>[
  (\<^syntax_const>\<open>_Mem_synt\<close>, fn ctxt => fn [addr, T] =>
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

(*\<open>\<^emph>\<close> and \<open>\<phi>Share\<close> are notated, so since Isabelle2025 their heads arrive wrapped in a positional
  constraint; the heads are recognized through the wrapper and the term is rebuilt from the ORIGINAL
  head, so that the wrapper -- and the source markup it carries -- survives.  Note \<^ML>\<open>Phi_Syntax_Constraint.is_head\<close>
  answers only for a bare constant underneath, so the nested-product test below still means "A IS the
  bare \<open>\<^emph>\<close> constant", exactly as the literal \<^ML>\<open>Const\<close> pattern it replaces did.*)
setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 100 (
    fn ((ctxt,i), f, tm) =>
      (case Phi_Syntax_Constraint.dest_comb_pos tm
         of (Const _, h, [A, B]) =>
              if Phi_Syntax_Constraint.is_head [\<^const_syntax>\<open>\<phi>Prod\<close>] h
              then if Phi_Syntax_Constraint.is_head [\<^const_syntax>\<open>\<phi>Prod\<close>] A
                   then NONE (*nested product-sequence is rejected*)
                   else SOME (Term.list_comb (h, [f (ctxt,i) A, f (ctxt,i+1) B]))
              else if Phi_Syntax_Constraint.is_head [\<^const_syntax>\<open>\<phi>Share\<close>] h
              then SOME (Term.list_comb (h, [A (*the share*), f (ctxt,i) B]))
              else NONE
          | _ => NONE))

#>Phi_Mem_Printer.add 100 (
    fn (ctxt, f, Const(\<^const_syntax>\<open>\<phi>Prod\<close>, T) $ A $ B) =>
          SOME (Const(\<^const_syntax>\<open>\<phi>Prod\<close>, T) $ f ctxt A $ f ctxt B)
     | _ => NONE)
)\<close>


paragraph \<open>Slice\<close>

consts Slice_synt :: \<open>nat \<Rightarrow> nat \<Rightarrow> (mem_fic,'a) \<phi> \<Rightarrow> (mem_fic, 'a list) \<phi>\<close> ("\<slice>[_, _] _" [10,10,910] 911)

translations "\<slice>[start, len] T" == "\<big_ast>\<^sub>\<bbbT> CONST AgIdx_N \<lbrakk>start : len\<rwpar> T"

(*This handler is reached only through the \<open>\<slice>\<close> rule above -- the only producer of the shape --
  and a rule's \<open>CONST c\<close> arrives bare, so the Isabelle2025 head wrapping does not actually reach it
  and the literal \<^ML>\<open>Const\<close> patterns it replaces still matched.  The head test is made wrapper-aware
  anyway, so that a producer added later through ordinary notation does not fail silently; the node
  is rebuilt from its ORIGINAL parts, which keeps whatever markup they carry.

  The \<^const>\<open>AgIdx_N\<close> position genuinely requires a \<open>CONST\<close> and always did: written as a plain
  identifier it is still a \<^ML>\<open>Free\<close> at this stage, since it is \<open>decode_term\<close> -- which runs after the
  parse translations -- that resolves an identifier to a constant.*)
setup \<open>Context.theory_map (
  Phi_Mem_Parser.add 101 (
    fn ((ctxt,_), f, tm) =>
      (case Phi_Syntax_Constraint.dest_comb_pos tm
         of (Const _, h, [idx, iv, T]) =>
              if Phi_Syntax_Constraint.is_head [\<^const_syntax>\<open>\<phi>Mul_Quant_Tree\<close>] h
                 andalso Phi_Syntax_Constraint.is_head [\<^const_syntax>\<open>AgIdx_N\<close>] idx
              then SOME (Term.list_comb (h, [idx, iv, f (ctxt,0) T]))
              else NONE
          | (Const _, h, [idx, n, m, A, iv, T]) =>
              if Phi_Syntax_Constraint.is_head [\<^const_name>\<open>\<phi>Mul_Quant_Tree\<close>] h
                 andalso Phi_Syntax_Constraint.is_head [\<^const_name>\<open>AgIdx_N\<close>] idx
              then SOME (Term.list_comb (h, [idx, n, m, A, iv, f (ctxt,0) T]))
              else NONE
          | _ => NONE))

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

definition \<open>address_to_base addr \<equiv> addr.offset addr = 0\<close>
  \<comment> \<open>\<open>addr\<close> points to the base of an allocation block\<close>
  \<comment> \<open>wraps and prevents the rewrite \<open>addr.offset addr = 0\<close>,
      as \<open>address_to_base addr\<close> should be treated as an atom\<close>

abbreviation MemObj ("\<obj>[_] _" [10,901] 900)
  where \<open>\<obj>[addr] T \<equiv> Mem addr (\<mem>-\<coerce> T) \<phi>\<subj> address_to_base addr \<and> \<typeof> addr = \<typeof> T \<and> \<typeof> T \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>



subsection \<open>Main\<close>

proc op_load_mem:
  input \<open>addr \<Ztypecolon> \<val> TypedPtr TY\<heavy_comma> state\<close>
  requires Extr: \<open>\<get> x \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce>[TY] T) \<from> state \<remaining> R\<close>
       and \<open>Semantic_Type' (x \<Ztypecolon> T) TY\<close>
  output \<open>x \<Ztypecolon> \<val> T\<heavy_comma> state\<close>
  unfolding Guided_Mem_Coercion_def
  including \<phi>sem_type_sat_EIF
\<medium_left_bracket>
  semantic_local_value(addr) \<ptr>

  apply_rule ToA_Extract_onward[OF Extr]

  to \<open>OPEN _ _\<close> to \<open>OPEN _ _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v \<semicolon>

  apply_rule FIC.aggregate_mem.getter_rule[where u_idx=v and n=1
                and cblk=\<open>addr.blk (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1))\<close>
                and blk=\<open>addr.blk addr\<close>
                and idx=\<open>addr.offset addr\<close>] \<semicolon>

  \<open>x \<Ztypecolon> MAKE _ (\<mem>-\<blk>[addr.blk addr] (addr.offset addr \<^bold>\<rightarrow>\<^sub>@ (MAKE _ (\<mem>-\<coerce> T))))\<close>
  \<open>x \<Ztypecolon> MAKE _ (\<mem>[addr] T)\<close>
  apply_rule ToA_Extract_backward[OF Extr]

  holds_fact [simp]: \<open>\<typeof> addr = TY\<close>
         and \<open>Mem.Val_of_Rep (block.layout (addr.blk addr)) (Byte_Rep_of_Val xa) = xa\<close> \<semicolon>

  semantic_assert \<open>let addr = rawaddr_to_log TY (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1))
                    in index_value (addr.offset addr)
                        (Mem.Val_of_Rep (block.layout (addr.blk addr)) (discrete.dest (\<phi>arg.dest \<v>1))) \<in> Well_Type TY\<close>
  semantic_return \<open>(let addr = rawaddr_to_log TY (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1))
                     in index_value (addr.offset addr)
                            (Mem.Val_of_Rep (block.layout (addr.blk addr)) (discrete.dest (\<phi>arg.dest \<v>1)))) \<Turnstile> (x \<Ztypecolon> T)\<close>
\<medium_right_bracket> .

declare [[\<phi>trace_reasoning = 1]]

proc op_store_mem:
  input  \<open>addr \<Ztypecolon> \<val> TypedPtr TY\<heavy_comma> y \<Ztypecolon> \<val> U\<heavy_comma> State\<close>
  requires \<open>report_unprocessed_element_index input_index EIHOOK_Addr_Of\<close>
       and Map: \<open>\<subst> y \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce> U)
                   \<for> x \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce>[TY] T)
                 \<from> State \<to> State' \<remaining> R\<close>
       and \<open>Semantic_Type T TY\<close>
       and \<open>Semantic_Type U TY\<close>
  output \<open>\<lambda>_::unit \<phi>arg. State'\<close>
  including \<phi>sem_type_sat_EIF
  unfolding Guided_Mem_Coercion_def
\<medium_left_bracket>
  apply_rule ToA_Subst_onward[OF Map]

  to \<open>OPEN _ _\<close> to \<open>OPEN _ _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v

  $addr semantic_local_value \<ptr>
  $y semantic_local_value \<open>TY\<close>

  apply_rule FIC.aggregate_mem.setter_rule[
        where u_idx=v and idx=\<open>addr.offset addr\<close>
          and v=\<open>\<phi>arg.dest \<a>\<r>\<g>2\<close>
          and blk=\<open>addr.blk addr\<close>
          and cblk = \<open>addr.blk (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1))\<close>
          and cidx = \<open>addr.offset (rawaddr_to_log TY (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1)))\<close>]

  \<open>y \<Ztypecolon> MAKE _ (\<mem>-\<blk>[addr.blk addr] (addr.offset addr \<^bold>\<rightarrow>\<^sub>@ (MAKE _ (\<mem>-\<coerce> U))))\<close>
  \<open>y \<Ztypecolon> MAKE _ (\<mem>[addr] U)\<close>
  
  apply_rule ToA_Subst_backward[OF Map]
\<medium_right_bracket> .

lemma op_load_mem_triangle_opr_\<phi>app[\<phi>overload \<tribullet> 10]:
  \<open> \<condition> TY = \<ptr>
\<Longrightarrow> \<get> x \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce>[TY] T) \<from> state \<remaining> R
\<Longrightarrow> Semantic_Type' (x \<Ztypecolon> T) TY
\<Longrightarrow> report_unprocessed_element_index input_index EIHOOK_Addr_Of
\<Longrightarrow> \<proc> op_load_mem TY v \<lbrace> addr \<Ztypecolon> \<val>[v] TypedPtr TY\<heavy_comma> state \<longmapsto> x \<Ztypecolon> \<val> T\<heavy_comma> state \<rbrace>\<close>
  by (rule op_load_mem_\<phi>app, blast+)



(*
proc op_store_mem:
  input  \<open>addr \<Ztypecolon> \<val> Ptr TY\<heavy_comma> y \<Ztypecolon> \<val> U\<heavy_comma> State\<close>
  requires \<open>parse_eleidx_input TY input_index sem_idx spec_idx reject\<close>
       and \<open>\<condition> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and [unfolded is_valid_index_of_def, useful]: \<open>is_valid_index_of spec_idx TY TY'\<close>
       and \<open>report_unprocessed_element_index reject\<close>
  requires Map: \<open>\<subst> y \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce>[TY] U)
                   \<for> x \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce>[TY] T)
                 \<from> State \<to> State' \<remaining>[C\<^sub>R] R\<close>
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
  requires \<open>\<param> T\<close>
       and \<open>Semantic_Zero_Val TY T z\<close>
  premises \<open>TY \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  output \<open>addr \<Ztypecolon> \<val> TypedPtr TY\<heavy_comma> z \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce> T) \<subj> addr. address_to_base addr\<close>
  including Semantic_Zero_Val_EIF_brute
  unfolding address_to_base_def
\<medium_left_bracket>
  semantic_assert \<open>Zero TY \<noteq> None\<close>
  apply_rule FIC.aggregate_mem.allocate_rule[where TY=TY and U=\<open>{the (Zero TY)}\<close>]

  \<open>z \<Ztypecolon> MAKE _ (\<mem>-\<blk>[blk] (MAKE _ (\<mem>-\<coerce> T)))\<close>
  \<open>z \<Ztypecolon> MAKE _ (\<mem>[Addr blk 0] T)\<close>

  semantic_assumption \<open>type_storable_in_mem TY\<close>

  have t1: \<open>valid_memaddr (Addr blk [])\<close>
    by (insert \<phi>; auto simp add: Valid_MemBlk_def split: block.split) \<semicolon>

  semantic_return \<open>sem_mk_pointer (Addr (\<phi>arg.dest \<v>1) 0) \<Turnstile> (Addr blk 0 \<Ztypecolon> TypedPtr TY)\<close>
    
\<medium_right_bracket> .

\<phi>overloads calloc \<comment> \<open>for allocating multiple elements\<close>
       and memcpy

thm \<phi>MapAt_L.mapper_wrap_module_src

(*
proc malloc:
  input Void
  requires \<open>\<param> T\<close>
       and \<open>Semantic_Type T TY\<close>
  premises \<open>TY \<noteq> \<p>\<o>\<i>\<s>\<o>\<n>\<close>
  output \<open>addr \<Ztypecolon> \<val> TypedPtr TY\<heavy_comma> z \<Ztypecolon> \<obj>[addr] T\<close>
  including Semantic_Zero_Val_EIF_brute
  unfolding address_to_base_def
  \<medium_left_bracket>
    apply_rule FIC.aggregate_mem.allocate_rule[where TY=TY and U=\<open>Well_Type TY\<close>]


    term \<open>Abstract_Domain\<^sub>L T (\<lambda>x. x \<in> Well_Type TY)\<close>

*)









proc mfree:
  input \<open>addr \<Ztypecolon> \<val> TypedPtr TY\<heavy_comma> x \<Ztypecolon> \<mem>[addr] (\<mem>-\<coerce>[TY] T)\<close>
  requires \<open>Semantic_Type T TY\<close>
  premises \<open>address_to_base addr\<close>
  output \<open>Void\<close>
  including \<phi>sem_type_sat_EIF
  unfolding address_to_base_def Guided_Mem_Coercion_def
\<medium_left_bracket>
  to \<open>OPEN _ _\<close> to \<open>OPEN _ _\<close>
  to \<open>FIC.aggregate_mem.\<phi> Itself\<close> \<exists>v
  $addr semantic_local_value \<ptr>

  apply_rule FIC.aggregate_mem.deallocate_rule
             [where v=v and blk=\<open>addr.blk (sem_dest_pointer (\<phi>arg.dest \<a>\<r>\<g>1))\<close>]

\<medium_right_bracket> .


section \<open>IDE-CP Interfaces\<close>

declare op_load_mem_\<phi>app[\<phi>overload "!", \<phi>overload "&"]
        op_store_mem_\<phi>app[\<phi>overload ":="]

text \<open>We differentiate \<open>\<leftarrow>\<close> and \<open>:=\<close>.
  \<open>\<leftarrow>\<close> is used to update the value of a local variable.
  \<open>:=\<close> is used to change the value of a memory object.
  Without this differentiation, ambiguity occurs when we have a local variable of a pointer
  pointing to a memory object which also stores a pointer, and an assignment can ambiguously refer
  to updating the variable or writing to the memory object.
\<close>

(*
proc(nodef) "_load_mem_bracket_"[\<phi>overload "[]"]:
  input \<open>addr \<Ztypecolon> \<val> Ptr TY0\<heavy_comma> state\<close>
  requires L1[]: \<open>parse_eleidx_input TY0 input_index sem_idx spec_idx reject\<close>
       and L2[]: \<open>\<condition> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and L3[]: \<open>is_valid_index_of spec_idx TY0 TY\<close>
       and L4[]: \<open>report_unprocessed_element_index reject\<close>
  requires Extr[]: \<open>\<get> x \<Ztypecolon> \<mem>[addr_geps addr spec_idx] (\<mem>-\<coerce>[TY] T) \<from> state \<remaining>[C\<^sub>R] R\<close>
       and L01[]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>x \<Ztypecolon> \<val> T\<heavy_comma> state\<close>
\<medium_left_bracket>
  $addr apply_rule op_get_element_pointer[OF L1 Premise_I[OF L2] L3 L4]
  apply_rule op_load_mem[OF Extr L01]
\<medium_right_bracket> .

proc(nodef) "_store_mem_bracket_"[\<phi>overload "[]:="]:
  input \<open>addr \<Ztypecolon> \<val> Ptr TY0\<heavy_comma> y \<Ztypecolon> \<val> U\<heavy_comma> state\<close>
  requires L1[]: \<open>parse_eleidx_input TY0 input_index sem_idx spec_idx reject\<close>
       and L2[]: \<open>\<condition> input_index = [] \<or> spec_idx \<noteq> []\<close>
       and L3[]: \<open>is_valid_index_of spec_idx TY0 TY\<close>
       and L4[]: \<open>report_unprocessed_element_index reject\<close>
  requires Map[]: \<open>\<subst> y \<Ztypecolon> \<mem>[addr_geps addr spec_idx] (\<mem>-\<coerce>[TY] U)
                     \<for> x \<Ztypecolon> \<mem>[addr_geps addr spec_idx] (\<mem>-\<coerce>[TY] T)
                   \<from> state \<to> state' \<remaining>[C\<^sub>R] R\<close>
       and L01[]: \<open>\<phi>SemType (x \<Ztypecolon> T) TY\<close>
       and L02[]: \<open>\<phi>SemType (y \<Ztypecolon> U) TY\<close>
  premises \<open>addr \<noteq> 0\<close>
  output \<open>\<lambda>_::unit \<phi>arg. state'\<close>
\<medium_left_bracket>
  $addr apply_rule op_get_element_pointer[OF L1 Premise_I[OF L2] L3 L4] \<rightarrow> val ptr \<semicolon>
  apply_rule op_store_mem[OF Map L01 L02] ($ptr, $y)
\<medium_right_bracket> .
*)

section \<open>Reasoning Setup\<close>

\<phi>reasoner_group mapToA_mem_coerce_all = (%\<phi>mapToA_norm, [%\<phi>mapToA_norm, %\<phi>mapToA_norm+100])
    \<open>rules resolving the memory coercion. Given a target like \<open>\<mem>-\<coerce>[ty] \<lbrace> a: T, b: U \<rbrace>\<close>,
      the rules reduce it by moving \<mem>-\<coerce> inside, to \<open>a \<^bold>\<rightarrow> \<mem>-\<coerce>[ty] T \<^emph> b \<^bold>\<rightarrow> \<mem>-\<coerce>[ty] U \<rbrace>,
      untill atomic types are reached.\<close>\<close>
  and mapToA_mem_coerce = (%mapToA_mem_coerce_all+5, [%mapToA_mem_coerce_all+5, %mapToA_mem_coerce_all+79])
    \<open>user rules\<close>
  and mapToA_mem_coerce_end = (%mapToA_mem_coerce_all, [%mapToA_mem_coerce_all, %mapToA_mem_coerce_all+4])
        < mapToA_mem_coerce
    \<open>system end\<close>
  and mapToA_mem_coerce_norm = (%mapToA_mem_coerce_all+80, [%mapToA_mem_coerce_all+80, %mapToA_mem_coerce_all+100])
        > mapToA_mem_coerce \<open>normalization\<close>
  and ToA_mem_coerce = (%ToA_cut+100, [%ToA_cut+100, %ToA_cut+300])
    \<open>mem_coerce in transformation\<close>
  and ToA_mem_coerce_end = (%ToA_cut+90, [%ToA_cut+90, %ToA_cut+99])
      < ToA_mem_coerce
    \<open>system end\<close>



declare [[
  \<phi>reason_default_pattern
      \<open>_ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<transforms> _ \<with> _ @tag \<T>\<P> \<close> \<Rightarrow> \<open>_ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<transforms> _ \<with> _ @tag \<T>\<P> \<close> (1000)
  and \<open>_ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<OTast> _ \<transforms> _ \<with> _ @tag \<T>\<P>' \<close> \<Rightarrow> \<open>_ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<OTast> _ \<transforms> _ \<with> _ @tag \<T>\<P>' \<close> (1000)
  and \<open>_ \<transforms> _ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<with> _ @tag \<T>\<P> \<close> \<Rightarrow> \<open>_ \<transforms> _ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<with> _ \<close> (1000)
  and \<open>_ \<transforms> _ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<OTast> _ \<with> _ @tag \<T>\<P>' \<close> \<Rightarrow> \<open>_ \<transforms> _ \<Ztypecolon> \<mem>-\<coerce>[?TY] _ \<OTast> _ \<with> _ @tag \<T>\<P>' \<close> (1000)
  and \<open>\<m>\<a>\<p> _ : \<mem>-\<coerce>[?TY] _ \<OTast> _ \<mapsto> \<mem>-\<coerce> _ \<OTast> _
       \<over> _ : _ \<OTast> _ \<mapsto> _ \<OTast> _ \<with> \<getter> _ \<setter> _ \<in'> _\<close> \<Rightarrow>
      \<open>\<m>\<a>\<p> _ : \<mem>-\<coerce>[?TY] _ \<OTast> _ \<mapsto> \<mem>-\<coerce> _ \<OTast> _
       \<over> _ : _ \<OTast> _ \<mapsto> _ \<OTast> _ \<with> \<getter> _ \<setter> _ \<in'> _\<close>         (1000)
  and \<open>\<m>\<a>\<p> _ : _ \<OTast> _ \<mapsto> _ \<OTast> _
       \<over> _ : \<mem>-\<coerce>[?TY] _ \<OTast> _ \<mapsto> \<mem>-\<coerce> _ \<OTast> _ \<with> \<getter> _ \<setter> _ \<in'> _\<close> \<Rightarrow>
      \<open>\<m>\<a>\<p> _ : _ \<OTast> _ \<mapsto> _ \<OTast> _
       \<over> _ : \<mem>-\<coerce>[?TY] _ \<OTast> _ \<mapsto> \<mem>-\<coerce> _ \<OTast> _ \<with> \<getter> _ \<setter> _ \<in'> _\<close>         (1000)
]]

consts \<A>_mem_coerce :: mode

(*declare Guided_Mem_Coercion.elim_map[where \<phi>=\<open>\<lambda>x. x\<close>, simplified,
            OF ToA_Mapper_fallback_remainder, OF Mem_Coercion.ToA_mapper, \<phi>reason %mapToA_mem_coerce_end]*)
declare Guided_Mem_Coercion.elim_reasoning(1)[\<phi>reason %ToA_mem_coerce_end]
        Guided_Mem_Coercion.intro_reasoning(2)[\<phi>reason %ToA_mem_coerce_end]

thm ToA_Mapper_fallback_remainder
thm Guided_Mem_Coercion.elim_map[where \<phi>=\<open>\<lambda>x. x\<close>, simplified]
thm Guided_Mem_Coercion.elim_map[where \<phi>=\<open>\<lambda>x. x\<close>, simplified,
      OF ToA_Mapper_fallback_remainder, OF Mem_Coercion.ToA_mapper]
thm ToA_Mapper_fallback_remainder

lemma [\<phi>reason %mapToA_mem_coerce_norm]:
  \<open> Semantic_Type T TY
\<Longrightarrow> \<m>\<a>\<p> g : \<mem>-\<coerce>[TY\<^sub>U] U \<OTast> R \<mapsto> U' \<OTast> R'
    \<over> f : \<mem>-\<coerce>[TY] T \<OTast> W \<mapsto> T' \<OTast> W'
    \<with> \<getter> h \<setter> s \<in'> D
\<Longrightarrow> \<m>\<a>\<p> g : \<mem>-\<coerce>[TY\<^sub>U] U \<OTast> R \<mapsto> U' \<OTast> R'
    \<over> f : \<mem>-\<coerce> T \<OTast> W \<mapsto> T' \<OTast> W'
    \<with> \<getter> h \<setter> s \<in'> D \<close>
  unfolding Guided_Mem_Coercion_def . 

thm Guided_Mem_Coercion.elim_map[where \<phi>=\<open>\<lambda>x. x\<close>, simplified,
      OF ToA_Mapper_fallback_remainder, OF Mem_Coercion.ToA_mapper]

lemma [\<phi>reason %mapToA_mem_coerce_norm
        for \<open>\<m>\<a>\<p> _ : \<mem>-\<coerce>[_] _ \<OTast> _ \<mapsto> \<mem>-\<coerce> _ \<OTast> _
             \<over> _ : \<mem>-\<coerce>[_] _ \<OTast> _ \<mapsto> \<mem>-\<coerce> _ \<OTast> _
             \<with> \<getter> _ \<setter> _ \<in'> _ \<close>]:
  \<comment> \<open>This rule assumes \<open>Semantic_Type\<close> reduces \<open>TY\<close> to the normal form!\<close>
  \<open> \<m>\<a>\<p> g : U \<mapsto> U' \<over> f : T \<mapsto> T' \<with> \<getter> h \<setter> s \<in'> fst ` D
\<Longrightarrow> \<m>\<a>\<p> g \<otimes>\<^sub>f r : \<mem>-\<coerce>[TY] U \<OTast> \<circle> \<mapsto> \<mem>-\<coerce> U' \<OTast> \<circle>
    \<over> f \<otimes>\<^sub>f r : \<mem>-\<coerce>[TY] T \<OTast> \<circle> \<mapsto> \<mem>-\<coerce> T' \<OTast> \<circle>
    \<with> \<getter> apfst h \<setter> apfst s \<in'> D \<close>
  unfolding Guided_Mem_Coercion_def
  by (rule ToA_Mapper_fallback_remainder, rule Mem_Coercion.ToA_mapper)

lemma [\<phi>reason %mapToA_mem_coerce_norm]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> \<mem>-\<coerce> U' \<OTast> R'
    \<over> f : T \<mapsto> T'
    \<with> \<getter> h \<setter> s \<in'> D
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> \<mem>-\<coerce>[TY] U' \<OTast> R'
    \<over> f : T \<mapsto> T'
    \<with> \<getter> h \<setter> s \<in'> D \<close>
  unfolding Guided_Mem_Coercion_def .

(*
lemma [\<phi>reason %mapToA_mem_coerce_norm]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U'
    \<over> f : T \<mapsto> \<mem>-\<coerce> T' \<^emph>[C\<^sub>W] W'
    \<with> \<getter> h \<setter> s \<in'> D
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U'
    \<over> f : T \<mapsto> \<mem>-\<coerce>[TY] T' \<^emph>[C\<^sub>W] W'
    \<with> \<getter> h \<setter> s \<in'> D \<close>
  unfolding Guided_Mem_Coercion_def .

lemma [\<phi>reason %mapToA_mem_coerce_norm]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> U'
    \<over> f : T \<mapsto> \<mem>-\<coerce> T'
    \<with> \<getter> h \<setter> s \<in'> D
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> U'
    \<over> f : T \<mapsto> \<mem>-\<coerce>[TY] T'
    \<with> \<getter> h \<setter> s \<in'> D \<close>
  unfolding Guided_Mem_Coercion_def .
*)

lemma [\<phi>reason %mapToA_mem_coerce_norm]:
  \<open> \<m>\<a>\<p> g : U \<mapsto> \<mem>-\<coerce> U'
    \<over> f : T \<mapsto> T'
    \<with> \<getter> h \<setter> s \<in'> D
\<Longrightarrow> \<m>\<a>\<p> g : U \<mapsto> \<mem>-\<coerce>[TY] U'
    \<over> f : T \<mapsto> T'
    \<with> \<getter> h \<setter> s \<in'> D \<close>
  unfolding Guided_Mem_Coercion_def .

thm \<phi>mapToA_refl'
thm Guided_Mem_Coercion.elim_map[where \<phi>=\<open>\<lambda>x. x\<close>, simplified, OF \<phi>mapToA_refl', \<phi>reason %mapToA_mem_coerce_end]


subsection \<open>Auxiliary Simplification\<close>

subsubsection \<open>Converting \<open>\<mem>-\<blk>[addr.blk a] ((addr.offset a @ [i\<^sup>\<t>\<^sup>\<h>]) \<^bold>\<rightarrow>\<^sub>@ \<dots>\<close>
                          \<open>\<mem>-\<blk>[addr.blk a] (addr.offset a \<^bold>\<rightarrow>\<^sub>@ [i\<^sup>\<t>\<^sup>\<h>]) \<^bold>\<rightarrow>\<^sub>@ \<dots>\<close>
                      to \<open>\<mem>[a \<tribullet> i\<^sup>\<t>\<^sup>\<h>] \<dots>\<close>\<close>

lemma MemBlk_\<phi>MapAt_L_assoc[no_atp, \<phi>programming_simps, \<phi>programming_base_simps]:
  \<open> \<mem>-\<blk>[blk] (a \<^bold>\<rightarrow>\<^sub>@ b \<^bold>\<rightarrow>\<^sub>@ T) = \<mem>-\<blk>[blk] ((a @ b) \<^bold>\<rightarrow>\<^sub>@ T) \<close>
  by (simp add: \<phi>MapAt_L.scalar_assoc[simplified times_list_def])

simproc_setup MemBlk_\<phi>MapAt_repair (\<open>\<mem>-\<blk>[addr.blk addr] (idx \<^bold>\<rightarrow>\<^sub>@ T)\<close>) = \<open>fn _ => fn ctxt => fn ctm =>
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>MemBlk\<close>, _) $ (Const(\<^const_name>\<open>addr.blk\<close>, _) $ a0)
                                    $ (Const(\<^const_name>\<open>\<phi>MapAt_L\<close>, _) $ idx $ _) =>
        let fun quick_chk (Const(\<^const_name>\<open>List.append\<close>, _) $ L $ _) = quick_chk L
              | quick_chk (Const(\<^const_name>\<open>list.Cons\<close>, _) $ _ $ L) = quick_chk L
              | quick_chk (Const(\<^const_name>\<open>list.Nil\<close>, _)) = true
              | quick_chk (Const(\<^const_name>\<open>addr.offset\<close>, _) $ a1) = a0 aconv a1
         in if quick_chk idx then
        let fun parse_idx ctmx (Const(\<^const_name>\<open>List.append\<close>, _) $ L $ R)
                  = parse_idx (Thm.dest_arg1 ctmx) L @ parse_idx (Thm.dest_arg ctmx) R
              | parse_idx ctmx (Const(\<^const_name>\<open>list.Cons\<close>, _) $ _ $ L)
                  = Thm.dest_arg1 ctmx :: parse_idx (Thm.dest_arg ctmx) L
              | parse_idx _ (Const(\<^const_name>\<open>list.Nil\<close>, _)) = []
              | parse_idx ctmx (Const(\<^const_name>\<open>addr.offset\<close>, _) $ a1) =
                    if a0 aconv a1 then [] else raise Match
            val cidx = Thm.dest_arg1 (Thm.dest_arg ctm)
            val cT = Thm.dest_arg (Thm.dest_arg ctm)
            val idxs = parse_idx cidx idx
            val cblk = Thm.dest_arg1 ctm
            val caddr'= fold (fn i => fn a => Thm.apply (Thm.apply \<^cterm>\<open>addr_gep\<close> a) i) idxs
                             (Thm.dest_arg cblk)
            val rule = \<^instantiate>\<open>blk=cblk and idx=cidx and addr=caddr' and T=cT and 'a=\<open>Thm.dest_ctyp0 (Thm.ctyp_of_cterm cT)\<close>
                                in lemma \<open>addr.blk addr = blk
                                      \<Longrightarrow> addr.offset addr = idx
                                      \<Longrightarrow> \<mem>-\<blk>[blk] (idx \<^bold>\<rightarrow>\<^sub>@ T) \<equiv> \<mem>[addr] T\<close>
                                      by (simp add: Mem_def)\<close>
         in SOME rule
        end else NONE end \<close>


subsection \<open>Pointer Of\<close>

subsubsection \<open>Preliminary - Modifier\<close>

definition \<A>sem_typ_mod1 :: \<open>'any \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> bool\<close>
  where \<open>\<A>sem_typ_mod1 param TY TY' \<equiv> True\<close>

definition \<A>sem_typ_mod2 :: \<open>'any \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> TY \<Rightarrow> bool\<close>
  where \<open>\<A>sem_typ_mod2 param TY\<^sub>1 TY\<^sub>2 TY \<equiv> True\<close>

\<phi>reasoner_group \<A>sem_typ_mod = (100, [1,3000])
        \<open>modifying the given semantic type(s) syntactically according to the given parameter\<close>
  and \<A>sem_typ_mod_cut = (1000, [1000,1030]) in \<A>sem_typ_mod \<open>cut\<close>

declare [[\<phi>reason_default_pattern
     \<open>\<A>sem_typ_mod1 ?p ?TY _\<close> \<Rightarrow> \<open>\<A>sem_typ_mod1 ?p ?TY _\<close> (100)
 and \<open>\<A>sem_typ_mod2 ?p ?TY1 ?TY2 _\<close> \<Rightarrow> \<open>\<A>sem_typ_mod2 ?p ?TY1 ?TY2 _\<close> (100)
]]




subsubsection \<open>Reasoning Rules\<close>


lemma [\<phi>reason %deriving_pointer_cut]:
  \<open> Derive_Pointer_Of (x \<Ztypecolon> \<mem>[addr] T) (Some (addr \<Ztypecolon> Ptr)) \<close>
  for T :: \<open>(mem_fic,'x) \<phi>\<close>
  unfolding Derive_Pointer_Of_def ..

(*
lemma [\<phi>reason %generalized_sematic_type_cut]:
  \<open> Generalized_Semantic_Type T TY\<^sub>1
\<Longrightarrow> Generalized_Semantic_Type U TY\<^sub>2
\<Longrightarrow> \<A>sem_typ_mod2 (\<^emph>) TY\<^sub>1 TY\<^sub>2 TY
\<Longrightarrow> Generalized_Semantic_Type (T \<^emph> U) TY \<close>
  unfolding Generalized_Semantic_Type_def ..

lemma [\<phi>reason %generalized_sematic_type_cut]:
  \<open> Generalized_Semantic_Type T TY
\<Longrightarrow> Generalized_Semantic_Type (Mem_Coercion T) TY \<close>
  unfolding Generalized_Semantic_Type_def ..
*)

end
