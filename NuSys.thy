(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrim NuSyntax NuBasicAbstractors
  keywords
    "proc" :: thy_decl_block
  and "\<medium_left_bracket>" "as" :: quasi_command
  and "\<medium_right_bracket>" :: thy_end
 and "xnote" :: prf_decl % "proof"
 and "block" :: prf_decl % "proof"
 and "xtheorem" "xlemma" "xcorollary" "xproposition" :: thy_goal_stmt
 and "xdbg" :: prf_decl % "proof"
  and "print_goal" :: diag
  and "xlemma" :: thy_goal_stmt
  and "finish" :: qed_block % "proof"
  and "end_at_procedure" :: qed_block % "proof"
  and "build" :: quasi_command
  and "\<lbrace>" :: qed_block % "proof"
begin

definition nop :: "'a \<Rightarrow> 'a state" where nop_def: "nop =  StatOn"
lemma nop: "s \<in> T \<Longrightarrow> True \<and> nop s \<in> \<S_S> T" by (simp add: nop_def State_def)

lemma contract_spec1: "PROP Pure.prop (PROP U \<Longrightarrow> PROP P \<Longrightarrow> PROP Q \<Longrightarrow> V)
    \<equiv> PROP Pure.prop (PROP U \<Longrightarrow> PROP P &&& PROP Q \<Longrightarrow> V)"
  unfolding prop_def conjunction_imp by this
lemma contract_spec2: "PROP Pure.prop (U \<Longrightarrow> V) \<equiv> PROP Pure.prop (U \<Longrightarrow> True \<Longrightarrow> V)"
  unfolding prop_def by simp
lemmas contract_spec = contract_spec1 contract_spec2
lemmas extract_spec = contract_spec[symmetric]

lemma
  assumes f: "\<And>s. PROP Pure.prop (s \<in> T \<Longrightarrow> PROP P \<Longrightarrow> f s \<in> \<S_S> U)"
  assumes s: "s' \<in> (T with_set V)"
  assumes P: "PROP P"
  shows instr:"instr f s' \<in> \<S_S> (U with_set V)"
proof (cases s')
  case s':(WithRegisters s r)
  then have s: "s \<in> T" and r: "r \<in> V" using s by (simp add: ContextTy_def)+
  consider (a) y where "f s = StatOn y \<and> y \<in> U" | (b) "f s = SNeg"
      using f[unfolded prop_def, OF s P] by (cases "f s") (auto simp add: State_def)
    then show ?thesis using s' r s by cases (simp add: instr_def call_def State_def ContextTy_def)+
  qed

lemma impIp: "PROP Pure.prop (P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q" by (auto simp add: prop_def)


definition init_proc :: " 'a \<Rightarrow> ('a with void) state " where
  init_proc_def: "init_proc s = StatOn (s with_registers Void)"

lemma InitProcConstruction: "a \<in> T \<Longrightarrow> CodeBlock v a s \<Longrightarrow> p \<in> \<B_S>\<B_t>\<B_r>\<B_i>\<B_c>\<B_t>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e> (T with_set VoidSet)"

notepad begin
  fix Aa :: bool

  ML_val \<open>  \<close>
ML_val \<open> Variable.variant_frees @{context} [@{term "A \<and> a \<and> C"}] [("A",()),("",())] \<close>
end
ML_val \<open>Term.dest_Type @{typ "('a * 'b) set"}\<close>
ML_val \<open>Term.dest_Type @{typ "ind"}\<close>
ML_val \<open>Term.dest_Type (Term.type_of @{term "A \<times> B"})\<close>
ML \<open>Option.map\<close>
ML_val \<open> ( @{term "A \<times> B"})\<close>

context lcls begin
lemmas x = conjI
ML_val \<open>app\<close>
ML_val \<open>Proof_Context.full_name @{context} @{binding NuPrim.x}\<close>
end

ML_file_debug NuHelp.ML
ML_file_debug NuBasics.ML
ML_file_debug NuSys.ML
ML_val \<open>(fn x => fn y => x + y)\<close>
ML_val \<open>Term.dest_Type @{typ name_tag}\<close>
ML_val \<open>   local open NuBasics in
  val x1 = map ((dest_named >> (Term.dest_Free #> fst #> SOME)) || pair NONE) 
end\<close>


attribute_setup show_proc_expression = \<open>NuSys.show_proc_expression_attr\<close>
declare [[show_proc_expression = false]]

ML \<open>

local open Parse Scan in
val bracket_begin = $$$ "\<medium_left_bracket>";
end

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((Parse.position Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []) --| bracket_begin >>
        (fn ((stat,fixes),inc_bundles) =>  NuHelp.UI_top_handler_local
            (NuSys.begin_proc_cmd (stat,fixes,inc_bundles))));
\<close>

proc "(x \<tycolon> \<nat>[32] named x) \<times> (y \<tycolon> \<nat>[32])"  for x :: nat \<medium_left_bracket>
  then 
term y
  fix xxx
  term "xxx::nat"
  term "xxx::bool"
  ML_val \<open>@{term "a \<in> B"}\<close>
term "\<R>"
typ '\<R>
\<medium_right_bracket>


ML \<open> 

fun ctx_parser_wrap f (ctx,tok) = case f tok of (x,tok') => (x,(ctx,tok'))
val ctx_parser_wrap : 'a parser -> 'a context_parser = ctx_parser_wrap
fun thm_name ctx : Thm.binding parser
   = Parse.binding -- (Parse.opt_attribs #>> map (Attrib.attribute_cmd ctx))
val for_fixes : NuSyntax.fixes parser = Parse.for_fixes

fun short_statement x =
(  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows))) x;

local open Parse in
val arg_list = list (binding --| $$$ ":" -- (term -- term))
val arg_list_p = $$$ "(" |-- arg_list --| $$$ ")"
fun iden_with pred = Scan.one (pred o Token.content_of) >> Token.content_of;
fun sym_iden_key x =
  group (fn () => Token.str_of_kind Token.Sym_Ident ^ " " ^ quote x)
    (iden_with (fn y => x = y));
end


val build = Parse.$$$ "\<medium_left_bracket>";
val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((Parse.position Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []) --| build >> NuSys.begin_proc_cmd);
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>block\<close> "begin a procedure construction"
    ( build >> K (Toplevel.proof Proof.begin_block));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<lbrace>\<close> "begin a procedure construction"
    ( build >> K (Toplevel.proof Proof.begin_block));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finish\<close> "end context"
    (Scan.succeed (Toplevel.proof Proof.end_block));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "end context"
    (Scan.succeed
      (Toplevel.exit o Toplevel.end_main_target o Toplevel.end_nested_target o
        Toplevel.end_proof (K Proof.end_notepad #> (fn x => ( x)))));

 \<close>

notepad begin
end

term \<open>x \<tycolon> \<nat>[32] \<close>     







(*   require "x < 100" and "y < 100"
  x y + 10 + \<rightarrow> z
  z' z *
  cast 2 () *)

value 1

final_procedure pproc[] : "p \<nuLinkL>... \<nuLinkR> ..."

lemma "P" proof -
end



ML_val \<open> Expression.read_statement \<close>

ML_val \<open>
  val s1 = "1"
  val s2 = "2"
  val t = Syntax.parse_term @{context} ("("^s1^","^s2^")")\<close>

ML \<open>
local

val _ = Outer_Syntax.command \<^command_keyword>\<open>print_goal\<close> "print"
    (Scan.succeed (Toplevel.proof (fn s =>
      (@{print} (Proof.raw_goal s); s))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>xnote\<close> "define facts"
    (Parse_Spec.name_facts >> @{print} >> (Toplevel.proof o Proof.note_thmss_cmd));
val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem spec schematic descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((long_statement || short_statement) >> (fn (long, binding, includes, elems, concl) =>
      (@{print} (long, binding, includes, elems, concl);
(if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
        long Thm.theoremK NONE (K I) binding includes elems concl)));
val _ = theorem \<^command_keyword>\<open>xtheorem\<close> false "theorem";
val _ = theorem \<^command_keyword>\<open>xlemma\<close> false "lemma";

fun xdbg_proof prf = prf |> Proof.set_facts [@{thm conjI}]

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>xdbg\<close> "begin explicit proof block"
    (Scan.succeed (Toplevel.proof xdbg_proof));

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.cond_statement -- Parse.for_fixes
    >> (fn ((shows, (strict, assumes)), fixes) => (strict, fixes, assumes, shows));

(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>have\<close> "state local goal"
    (structured_statement >> (fn (a, b, c, d) =>
      Toplevel.proof' (fn int => Proof.have_cmd a NONE (K I) b c d int #> #2))); *)

in end\<close>

ML_val \<open> fold (fold (Proof_Context.augment o fst) o snd) \<close>

xlemma "A + B = B" if "A = B" for A B :: nat 
begin
end_proc

xlemma nth_equal_first_eq:
  fixes x :: nat
  notes conjI3 = conjI
  assumes "x \<notin> set xs"
  assumes "n \<le> length xs"
  shows xx[]:"(x # xs) ! n = x \<longleftrightarrow> n = 0" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  thm conjI3
  print_goal
  term ?lhs
  assume ?lhs
  show ?rhs
  proof (rule ccontr)
    assume "n \<noteq> 0"
    then have "n > 0" by simp
    with \<open>?lhs\<close> have "xs ! (n - 1) = x" by simp
    moreover from \<open>n > 0\<close> \<open>n \<le> length xs\<close> have "n - 1 < length xs" by simp
    ultimately have "\<exists>i<length xs. xs ! i = x" by auto
    with \<open>x \<notin> set xs\<close> in_set_conv_nth [of x xs] show False by simp
  qed
next
  assume ?rhs then show ?lhs by simp
qed


ML \<open>local open Parse in
val is_props = Scan.repeat1 ($$$ "is" |-- prop);
 val propp = Parse.prop -- Scan.optional ($$$ "(" |-- !!! (is_props --| $$$ ")")) []
end\<close>
ML \<open> Parse.and_list1  \<close>

interface pproc[simp] : "sss"


ML \<open> 

local

val thm_name = Parse_Spec.thm_name ":" #>> apsnd (map (Attrib.attribute_cmd ctx))

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>mkproc\<close> "begin a procedure construction"
    ((Parse_Spec.thm_name "+" >> \<^print>) |-- Parse.begin >> K Proof.begin_notepad);

in end \<close>

  note

ML_val \<open>
op ||>
 \<close>

  ML_val \<open>
Parse.and_list1;
 (--) \<close>

ML_val \<open>
local open Proof in
fun these_factss more_facts (named_factss, state) =
  (named_factss, state |> set_facts (maps snd named_factss @ more_facts));

fun gen_thmss more_facts opt_chain opt_result prep_atts prep_fact args state =
  state
  |> assert_forward
  |> map_context_result (fn ctxt => ctxt |> Proof_Context.note_thmss ""
    (Attrib.map_facts_refs (map (prep_atts ctxt)) (prep_fact ctxt) args))
  |> these_factss (more_facts state)
  ||> opt_chain
  |> opt_result;
end

val local_results = gen_thmss (K []) I I (K I) (K I) o map (apsnd Thm.simple_fact);x`
  \<close>

ML_val \<open>
fun empty_bindings args = map (pair Binding.empty_atts) args; \<close>

lemma "P \<and> Q" if asm: "Q \<and> P" for P Q :: bool
proof (rule conjI)
  from that have a:"P" and b:"Q" by (blast, blast)
  with this print_goal
   have "Q" using b 
    print_goal
    by fast
  print_goal
  thm this
  xdbg
  thm this
  print_goal
end

notepad begin
  print_goal
end


  {
ML_val \<open> (true ? (fn x => x +  1)) 1 \<close>
lemma x:"x = x" proof qed

  
  ML_val \<open>
    val th1 = Thm.assume @{cterm "\<And>x y. P x y"}
    val th3 = Drule.forall_elim_list [Thm.cterm_of @{context} (Var (("aa",1),@{typ 'a}))] th1
    val th2 = Drule.infer_instantiate @{context} [(("?x",0), @{cterm "x::'a"})] th1
(* (Drule.forall_intr_vars  @{thm as}) *)
 \<close>


lemma
  assumes asm: "P"
  shows th: "P"
proof -
  from asm show ?thesis by this
qed

thm th
value "len_of (TYPE (2))"

lemma ex: "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then obtain B and A ..
  then show "B \<and> A" ..
qed

notepad begin
  include show_more
  fix P Q A B C :: bool
  assume t1: "P \<Longrightarrow> A \<Longrightarrow> P \<Longrightarrow> Q"
  ML_val \<open> Simplifier.norm_hhf @{context} @{thm t1} \<close>
  assume t2: "B \<Longrightarrow> C \<Longrightarrow> P"
  assume t3: "A \<Longrightarrow> (P \<Longrightarrow> Q \<Longrightarrow> C)"
  assume t4: "A"
  note t1[OF t2]
  note x1 = t1[OF t2 t4]

  thm conjI
  ML_val \<open>
  val thm = @{thm x1};
val prf = Thm.proof_of thm

 \<close>



  thm t1
  have t1: "B \<Longrightarrow> C \<Longrightarrow> P" using t2 by this
  thm t1

  ML_val \<open>
type lthy =
 {background_naming: Name_Space.naming,
  operations: Local_Theory.operations,
  conclude: Proof.context -> Proof.context,
  target: Proof.context};
structure Data = Proof_Data
(
  type T = lthy list;
  fun init _ = [];
);
val x = hd o Data.get
val y = Binding.name

\<close>

  ML_val \<open>
val zz= Facts.dest_all (Context.Proof @{context}) false []
  (Proof_Context.facts_of @{context})
\<close>

  have "\<And> x. P x"
proof -
    have "P x" for x sorry
  thus "\<And> x. P x"
    by fast
qed

  assume as:"\<And>x y. P x y" 
  thm as
  ML_val \<open>
   Thm.tpairs_of ( (Goal.init @{cterm "PROP PP"}))
\<close>
  {
    fix x :: "'a"
    {
      have "x \<equiv> x" by (rule reflexive)
    }
    thm this
  }
  
end

context 
  includes show_more
  fixes P :: "'a \<Rightarrow> bool"
  assumes as:"\<And>x. P x" 
begin

  

ML_val \<open>
val prep_att = Attrib.check_src
val lthy = @{context}
val ((name, raw_atts),raw_includes,raw_elems,raw_concl,int) = 
val y = (Element.map_ctxt_attrib (prep_att lthy)) 
val x = Local_Theory.assert  @{context}\<close>
  xlemma x: "P \<and> Q" and y:"P" if "Q" for Q :: bool by (simp add: as add: that)+
end


notepad begin
  fix P Q A B C :: bool
  fix S T :: "'a \<Rightarrow> bool"
  assume x: "P = Q"
  assume A: "P \<Longrightarrow> P \<Longrightarrow> Q"
  assume B: "A \<Longrightarrow> B \<Longrightarrow> C"
  assume C: "P \<Longrightarrow> P \<longrightarrow> Q"
  assume D: "\<forall>x. S x \<longrightarrow> T x"
  include show_more
  thm ac_simps
  have ac_simps: "P = Q" by (simp add: x)
thm ac_simps
  thm spec
  note d = mp[OF spec[OF D]]
  ML_val \<open>
local
val ctxt = @{context}
val facts = Proof_Context.facts_of @{context}
val x = Global_Theory.facts_of (Proof_Context.theory_of ctxt)
in
val f2 = Facts.dest_static true [x] facts;
val f1= (Facts.props facts)
   end
  
\<close>

  ML_val \<open>
structure Data = Generic_Data
(
  type T = thm Item_Net.T;
  val empty = Thm.full_rules;
  val extend = I;
  val merge = Item_Net.merge;
);
val content = Item_Net.content o Data.get;\<close>
  ML_val \<open> Symtab.lookup \<close>

  ML_val \<open> 
  val th3 = Thm.RS (@{thm spec}, @{thm D})
(*  val th2 = Thm.RS (@{thm spec}, @{thm D}) *)
  val th1 = Thm.assume @{cterm "P \<Longrightarrow> W"}
  val xx1 = Thm.RS ( @{thm mp}, @{thm B})
 (* val tP = @{cterm "HOL.Trueprop P"}
  val th1 = Thm.assume tP
  val th2 = Drule.OF (@{thm A}, [th1,th1])
  val th3 = Thm.implies_intr tP (Thm.implies_elim (Thm.implies_elim @{thm A} th1) th1) *) \<close>
  
ML_val \<open> Thm.get_tags (Thm.put_name_hint "s" @{thm x})\<close>
ML_val \<open>
local val fc = Proof_Context.facts_of @{context}
  val names = map #1 (Facts.dest_all (Context.Proof @{context}) false [] fc)
in
  val x = map @{print} (filter (Facts.is_dynamic fc) names)
end \<close>
  note x[symmetric]
  xnote y[simp] = x[symmetric] \<open>P = Q\<close>
    and z = x
  note ac_simps = y
  
  
end

mkproc asd[simp]+ begin

ML_val \<open> @{Isar.state} \<close>
  ML_val \<open> Proof.init ( \<^context>) \<close>

  have
  note this
end
end