theory NuTest
  imports NuStd_Base NuInstructions "HOL-Library.Permutation"
begin

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

  proc sub1:  \<open>x \<tycolon> \<nat>[32]\<close> \<longmapsto> \<open>x -1 \<tycolon> \<nat>[32]\<close>
    requires [used]: \<open>0 < x\<close>
    \<bullet> 1 -
  finish
term sort
lemma [simp]: "j + 1 = length xs \<Longrightarrow> length xs - 1 = j" by auto
lemma [elim]: "a < b + 1 \<Longrightarrow> (a < b \<Longrightarrow> C) \<Longrightarrow> (a = b \<Longrightarrow> C) \<Longrightarrow> C" for a :: nat
  by linarith
declare nth_list_update[simp] not_le[simp]
thm "\<up>_\<nu>app"
ML \<open>@{term "case x of (i,j,k) \<Rightarrow> f i j k"}\<close>
term \<open>case_prod\<close>
term perm
thm Variant_Cast_I_always
ML \<open>Seq.the_result\<close>
declare [ [ML_print_depth = 100] ]
Variant_Cast_I
ML \<open>@{term op_recursion}\<close>
thm op_recursion

ML \<open>val th = Goal.init @{cterm "P \<Longrightarrow> Q \<Longrightarrow> P"} |> Thm.eq_assumption 1\<close>

rec_proc qsort: \<open>ptr \<tycolon> Pointer\<heavy_comma> n \<tycolon> \<nat>[size_t]\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<heavy_asterisk> ptr \<R_arr_tail> xs \<tycolon> Array \<nat>[32]\<close>
  \<longmapsto> \<open>(Void\<heavy_comma> \<^bold>h\<^bold>e\<^bold>a\<^bold>p h \<tycolon> H \<heavy_asterisk> ptr \<R_arr_tail> sort xs \<tycolon> Array \<nat>[32])\<close>
  var ptr xs h H premises [used]: "length xs = n"
apply simp
thm qsort_\<nu>proc
  \<bullet> -- n 0 = if \<medium_left_bracket> \<medium_right_bracket> \<medium_left_bracket> -- ptr n 1 - \<up> \<rightarrow> pivot \<open>0 \<tycolon> \<nat>[size_t]\<close> 0
  \<bullet> while
  \<bullet> var i, j, ys in i, j heap "ptr \<R_arr_tail> ys" always 
    \<open>i \<le> j \<and> j \<le> n \<and> length ys = n \<and>
    (if j = n then 0 < i \<and> ys ! (i-1) = xs ! (n-1) else ys ! (n-1) = xs ! (n-1)) \<and>
    (\<forall>k. k <i \<longrightarrow> ys ! k \<le> xs ! (n-1)) \<and> (\<forall>k. i \<le> k \<and> k < j \<longrightarrow> xs ! (n-1) < ys ! k)\<close>
  \<bullet> \<medium_left_bracket> dup n < \<medium_right_bracket>
  \<bullet> \<medium_left_bracket> \<rightarrow> i,j ptr i \<up>\<rightarrow> i' ptr j \<up>-- j' pivot \<le> if
  \<bullet> \<medium_left_bracket> ptr j i' \<down> ptr i j' \<down> n i 1 
  \<bullet> + \<rightarrow> i1 drop i1 \<medium_right_bracket> \<medium_left_bracket> i \<medium_right_bracket>
  \<bullet> n j 1 + \<rightarrow> j1 drop j1
  \<bullet> \<medium_right_bracket>
  \<nu>have a1[used]: "j = n \<and> 0 < i" using used by auto
  \<bullet> drop 1 - \<rightarrow> i ptr i 
  \<bullet> split_array ptr n
  \<bullet> qsor
  thm qsort_\<nu>proc
  
  \<bullet> 
  \<bullet> xs2, i, j \<Longrightarrow> x[used] \<bullet> drop 1 - \<rightarrow> i i split \<bullet> i qsort
  \<nu>debug 
  thm qsort_\<nu>proc

(*   \<bullet> \<Longrightarrow> precondition[used] \<bullet> \<rightarrow> (v,n) n 0 = if \<medium_left_bracket> \<bullet> $v \<medium_right_bracket> \<medium_left_bracket> \<bullet> $v \<open>0\<tycolon>\<nat>[32]\<close> \<up>\<rightarrow> pivot \<open>1\<tycolon>\<nat>[32]\<close> \<open>1\<tycolon>\<nat>[32]\<close>
  \<bullet> while xs' i j in \<open>((seg |+ ofs) \<R_arr_tail> xs', i, j)\<close> subj \<open>j \<noteq> n\<close>
      always \<open>0 < i \<and> i \<le> j \<and> j \<le> n \<and> length xs' = n \<and> xs' ! 0 = xs ! 0 \<and> (\<forall>k. k <i \<longrightarrow> xs' ! k \<le> xs ! 0) \<and> (\<forall>k. i \<le> k \<and> k < j \<longrightarrow> xs ! 0 < xs' ! k) \<close>
  \<medium_left_bracket> \<bullet> \<Longrightarrow> x[used] \<bullet> \<rightarrow> (a,b,c) c n < $a b c pr^3 \<medium_right_bracket> \<medium_left_bracket> \<bullet> \<Longrightarrow> x[used] \<bullet> \<rightarrow> (xs,i,j) $xs j \<up>\<rightarrow> j' i \<up>\<rightarrow> i' \<rightarrow> xs
  \<bullet> j' pivot \<le> if \<medium_left_bracket> \<bullet> $xs i' j \<Down> j' i \<Down> \<rightarrow> xs i 1 + \<rightarrow> i \<medium_right_bracket> \<medium_left_bracket> \<medium_right_bracket> \<bullet> $xs i j 1 + pr^2 \<medium_right_bracket>
  \<bullet> xs2, i, j \<Longrightarrow> x[used] \<bullet> drop 1 - \<rightarrow> i i \<up>0 \<Down>pivot i \<Down> *)

end


lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X = f x \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X = SchemaTag f x"
  unfolding Premise_def Simplify_def SchemaTag_def by auto

lemma [\<nu>intro]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X = f x y \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e X = (case_prod f) (x,y)"
  unfolding Premise_def Simplify_def SchemaTag_def by auto


proc AA: \<open>i \<tycolon> \<nat>[32]\<heavy_comma>  zp \<left_fish_tail> adr \<R_arr_tail> Gi 0 \<left_fish_tail> i \<tycolon> Ref \<nat>[32]\<close> \<longmapsto> \<open>i \<tycolon> \<nat>[32]\<close>
  \<bullet> i $v while i j in \<open>(i, zp \<left_fish_tail> adr \<R_arr_tail> Gi 0 \<left_fish_tail> j)\<close> subj \<open>i < j\<close>   \<medium_left_bracket> \<bullet> \<up>\<rightarrow> (a,b,c) a c < a $b pr^2\<medium_right_bracket> 
  \<medium_left_bracket> \<bullet> \<Longrightarrow> A[used] \<bullet> \<up> 1 - \<Down> pr \<medium_right_bracket> \<bullet> aa, bb \<rightarrow> v



proc add2: "(x \<tycolon> \<nat>[32]\<heavy_comma> y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  requires [used]: "x < 100" and [used]:"y < 100"
  \<bullet> x x y + +
  finish

thm add2_\<nu>proc



thm i_while_\<nu>compilation





proc' [\<nu>overload pop]: \<open>R\<heavy_comma> (seg |+ i) \<R_arr_tail> xs \<tycolon> Array N\<close> \<longmapsto> \<open>R\<heavy_comma> (seg |+ i + 1) \<R_arr_tail> tl xs \<tycolon> Array N\<heavy_comma> (seg |+ i) \<R_arr_tail> hd xs \<tycolon> FullRef N\<close>
  requires [simp]: "xs \<noteq> []"
  \<bullet> pop finish


lemma [\<nu>overload pop]: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e xs \<noteq> [] \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>o\<^bold>c i_pop_refs \<blangle> R\<heavy_comma> (seg |+ i) \<R_arr_tail> xs \<tycolon> Array N
      \<longmapsto>  R\<heavy_comma> (seg |+ i + 1) \<R_arr_tail> tl xs \<tycolon> Array N\<heavy_comma> (seg |+ i) \<R_arr_tail> hd xs \<tycolon> FullRef N \<brangle>" sorry

abbreviation "permuted l1 l2 \<equiv> set l1 = set l2"

declare pair_forall[simp]

proc qsort: \<open> (seg |+ i) \<R_arr_tail> xs \<tycolon> Array \<nat>[32]\<heavy_comma> n \<tycolon> \<nat>[32]\<close>
  \<longmapsto> \<open>{ (seg |+ i) \<R_arr_tail> ys | ys. permuted xs ys \<and> sorted ys } \<tycolon> \<^bold>s\<^bold>o\<^bold>m\<^bold>e (Array \<nat>[32])\<close>
  requires "length xs = n"
  \<bullet> \<leftarrow> (v,n) pr recursion \<open>(\<lambda>x. case x of ((seg |+ i) \<R_arr_tail> xs, n) \<Rightarrow>
        { (seg |+ i) \<R_arr_tail> ys | ys. permuted xs ys \<and> sorted ys })\<close> \<open>\<^bold>s\<^bold>o\<^bold>m\<^bold>e (Array \<nat>[32])\<close>
  \<medium_left_bracket> (g_\<nu>proc) \<nu>obtain seg i xs n  where [simp]: "x' = ((seg |+ i) \<R_arr_tail> xs, n)"
  by (metis memadr.exhaust object.exhaust old.prod.exhaust) \<bullet>
  \<nu>obtain seg i xs n  where B[simp]: "x' = ((seg |+ i) \<R_arr_tail> xs, n)"
by (metis memadr.exhaust object.exhaust old.prod.exhaust) \<bullet>
  \<bullet> dpr \<rightarrow> (xs, n) n 0 = if 
  \<nu>debug note g_\<nu>proc

ML \<open>Locale.get_locales @{theory}\<close>
ML \<open>val ctx = Locale.init "NuPrime.ceq_lrep" @{theory}
val x = Assumption.all_prems_of ctx\<close>

(* schematic_goal [simplified, simplified \<nu>post_construct]:
  "\<^bold>c\<^bold>o\<^bold>n\<^bold>s\<^bold>t\<^bold>r\<^bold>u\<^bold>c\<^bold>t (233 \<tycolon> \<nat>[32], ((copy_reg::((32 word register \<times> 32 word register), (32 word register \<times> 32 word register), (32 word) register, 32 word register) address \<Rightarrow> (32 word, nat) typing)) (address_left address_here)
+ (233 \<tycolon>  \<nat>[32])) \<^bold>b\<^bold>y \<^bold>p\<^bold>r\<^bold>o\<^bold>c ?f \<blangle>((?Z1::(?'a::lrep) set) \<flower> \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r A = \<tort_lbrace> 16 \<tycolon> \<nat>[32]\<tort_rbrace> and_ty \<^bold>r\<^bold>e\<^bold>g\<^bold>i\<^bold>s\<^bold>t\<^bold>e\<^bold>r B = \<tort_lbrace> 0 \<tycolon> \<nat>[32] \<tort_rbrace>) \<longmapsto> (?Z2::(?'b::lrep) set) \<brangle>"
  by  (\<nu>resolve \<nu>intro (\<nu>intro'))  *)




fun fib :: "nat \<Rightarrow> nat"
  where "fib x = (if x = 0 then 1 else if x = 1 then 1 else fib (x-1) + fib (x-2))"

proc fibx : "x \<tycolon> \<nat>[32]" \<longmapsto> "fib x \<tycolon> \<nat>\<^sup>r[32]"
  \<bullet> x recursion fib \<open>\<nat>\<^sup>r[32]\<close> less_than \<medium_left_bracket> (g_\<nu>proc)
  \<bullet> \<rightarrow> x x 0 = if \<medium_left_bracket> \<bullet> \<open>1\<tycolon>\<nat>\<^sup>r[32]\<close> \<medium_right_bracket> \<medium_left_bracket> (c0[used])
      \<bullet> x 1 = if \<medium_left_bracket> \<bullet> \<open>1\<tycolon>\<nat>\<^sup>r[32]\<close> \<medium_right_bracket> \<medium_left_bracket> (c1[used]) \<bullet> x 1 - g \<rightarrow> f1 x 2 - g \<rightarrow> f2 f1 f2 + \<medium_right_bracket>
  \<medium_right_bracket> \<medium_right_bracket>
  finish

  thm fibx_\<nu>proc

fun ackman :: "(nat \<times> nat) \<Rightarrow> nat"
  where "ackman (0,n) = Suc n"
  | "ackman (Suc m, 0) = ackman (m,1)"
  | "ackman (Suc m, Suc n) = ackman (m, ackman (Suc m, n))"

thm begin_proc_ctx
proc ackman : "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "ackman (x,y) \<tycolon> \<nat>[32]" if cond: "ackman (x,y) < 2^32"
  \<bullet> x y pr cast where \<open>{xy. ackman xy < 2^32}\<close> affirm using cond by simp
  \<bullet> recursion ackman \<open>\<nat>[32]\<close> \<open>less_than <*lex*> less_than\<close> \<medium_left_bracket> (g_\<nu>proc)
  \<nu>obtain m n where th1[simp]: "x' = (m,n)" by (cases x')
  \<bullet> cast E \<Longrightarrow> th2[used] \<bullet> dpr \<rightarrow> (m,n) m 0 = if \<medium_left_bracket> \<bullet> n 1 + \<medium_right_bracket> \<medium_left_bracket> \<bullet> m 1 -
  \<bullet> n 0 = if \<medium_left_bracket> \<bullet> 1 pr 
  \<bullet> cast where \<open>{xy. ackman xy < 2^32}\<close> affirm apply (cases m) by auto
  \<bullet> g \<medium_right_bracket> \<medium_left_bracket> \<bullet> m n 1 - pr
\<bullet> cast where \<open>{xy. ackman xy < 2^32}\<close> affirm apply (cases m; cases n) by auto
  note c
  \<nu>debug 
  note c

end

definition [simp]:"difference x y = (if x < y then y - x else x - y)"
xproc diff : "(x \<tycolon> \<nat>[32], y \<tycolon> \<nat>[32])" \<longmapsto> "(difference x y \<tycolon> \<nat>[32])"
  \<bullet> x while \<open>{x. 0 < x}\<close> Id less_than \<medium_left_bracket> \<bullet> \<rightarrow> a a 0 a < pr \<medium_right_bracket> \<medium_left_bracket> \<bullet> cast E \<Longrightarrow> th1[used] \<bullet> 1 -  \<medium_right_bracket>
  \<bullet> cast E \<nu>choose a where "some = a" by auto
  \<bullet> \<Longrightarrow> th1[simp] drop_fact th1
  \<bullet> drop x y < if \<medium_left_bracket> \<bullet> y x - \<medium_right_bracket> \<medium_left_bracket> \<bullet> x y - \<medium_right_bracket>
  finish

end

proc add2 : "(( x \<tycolon> \<nat>[32]) named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
  if "x < 100" and "y < 100"
  \<nu>have x[used]: "x < 100 \<and> y < 100" using that by auto
  \<bullet> x x y + < if \<medium_left_bracket>
  \<nu>obtain z where c: "x < z" by auto \<medium_right_bracket>
  finish


proc add02: "(( x \<tycolon> \<nat>[32]) named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])"
if A[used]:"x < 100" and [used]:"y < 100"
    \<bullet> x x y + +
    \<nu>obtain z where c: "x < z" by auto
  finish

thm add2_\<nu>proc





proc xxx: "(x \<tycolon> \<nat>[32] named x, y \<tycolon> \<nat>[32])" \<longmapsto> "(x + x + y \<tycolon> \<nat>[32])" for x :: nat  if A:"x < 100" and B:"y < 100" \<medium_left_bracket>
  \<bullet> \<rightarrow> (x,y) x y +
(* , x !!!  -- by (myrule \<nu>disposable) *)
  thm \<nu>aux'raw


(* 

  \<nu>have xL10: "x < 10" 
  have
!!!  -- by (myrule \<nu>disposable)
print_rules
ML_val \<open>Context_Rules.print_rules @{context}\<close>
term ?thesis
  include show_more1 *)
  
(*  \<bullet> x y + !! -- by auto  \<bullet> 
  \<bullet>  *)






ML \<open>(fold o fold) Variable.declare_term\<close>
ML \<open>(map o Proof_Context.cert_prop)\<close>
ML \<open>
local open Proof_Context in
val prep_props = (map o cert_prop)
val raw_args = [[]]
val ctxt = @{context}
    val props = prep_props ctxt (maps (map fst) raw_args);

val patss = maps (map (prep_props (set_mode mode_pattern @{context}) o snd)) raw_args
    val propps = unflat raw_args (props ~~ patss);

end
\<close>
ML \<open>
structure Data = Generic_Data
(
  type T = int Name_Space.table; (* key : the constant name, value: the definition *)
  val empty: T = Name_Space.empty_table "\<nu>hehe";
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>test\<close> "define \<nu>processor"
      (Parse.name_position >> (fn x => Toplevel.proof (Proof.map_context  (fn ctx =>
          let
            val gtx = (Context.Proof ctx)
            val tab =Data.get gtx
val (x',a) = Name_Space.check gtx tab x 
val _ = @{print} x'
val _ = @{print} a
in ctx end
    ))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>test2\<close> "define \<nu>processor"
      (Scan.succeed () >> (fn _ => Toplevel.proof (Proof.map_contexts  (fn ctx =>
let val data = Data.get (Context.Proof ctx)
        val (_,tab2) = Name_Space.define (Context.Proof ctx) false (@{binding h1}, 233) data 
in Context.proof_map (Data.put tab2) ctx end
))))
\<close>

  notepad
begin
  fix P Q A :: bool
  assume A: "A" and B: "Q" apply
ML_val \<open>
val th = Goal.init @{cprop "P"}
val th2 = (ALLGOALS (Method.insert_tac @{context} @{thms A B}) THEN (auto_tac @{context} |> CHANGED_PROP)) th |> Seq.list_of
\<close>
end

notepad
begin

  {
    fix P :: bool
    ML_prf \<open>Theory.local_setup (Proof_Context.bind_term (("x",0), @{term P}))\<close>
    ML_prf \<open>Theory.local_setup (Proof_Context.put_thms false ("haha", SOME @{thms conjI}))\<close>

test2
    test h1
    thm haha
    term ?x
    ML_prf \<open>Proof_Context.cert_term @{context} @{term "?x"}\<close>
  

    presume "P"
    then have "P" .
    note this
  }
test h1
  ML_val \<open>burrow\<close>
end
  
(*  \<nu> x y + ! by some \<nu> ! by some 
  ML_val \<open>Thm.prop_of  @{thm this} \<close>
  note conjI[\<nu>\<rho>_accept_proc]*)
\<medium_right_bracket>

ML \<open>val auto_method =
  Scan.lift (Scan.option (Parse.nat -- Parse.nat)) --|
    Method.sections clasimp_modifiers >>
  (fn NONE => (fn ctx => SOLVED' (K (auto_tac ctx)) |> SIMPLE_METHOD')
    | SOME (m, n) => (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mk_auto_tac ctxt m n))));
val _ = Theory.setup (Method.setup \<^binding>\<open>myauto\<close> auto_method "myauto" #>
Method.setup \<^binding>\<open>myrule\<close>
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o Method.some_rule_tac ctxt rules)))
      "apply some intro/elim rule (potentially classical)")
\<close>
  notepad
begin
  fix A B C :: bool
  assume A: A and B : "A \<Longrightarrow> C" and th2 : "D"
  have "C  \<and> C" using B B apply (myrule conjI)
    thm conjI[OF B]
    (* using A B th2 apply myauto *)
end




term NuPrime.CodeBlock
ML \<open>\<^const_name>\<open>CodeBlock\<close>\<close>
term "NuPrime.CurrentConstruction"
ML_val \<open>HOLogic.strip_tuple @{term "(A,B,C)"}\<close>
proc "(x \<tycolon> \<nat>[32] named x, y \<tycolon> \<nat>[32])" for x :: nat \<medium_left_bracket> 
    x y y + + 
\<medium_right_bracket>
ML_val \<open>NuBasics.mk_PropBlock 0 @{thm this}\<close>
ML_val \<open>fold\<close>
thm protectI
thm PropBlock_I
  \<rightarrow> x \<rightarrow> a \<rightarrow> p
  note
term y
  fix xxx
  term "xxx::nat"
  term "xxx::bool"
  ML_val \<open>@{term "a \<in> B"}\<close>
term "\<R>"
typ '\<R>
\<medium_right_bracket>

  

ML_val \<open>
val ctx = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
val (Term.Var xxx) = Syntax.read_term ctx "(?a::nat)"
val tm1 = Syntax.read_term ctx "(A \<longrightarrow> X x \<longrightarrow> X x)"
val tm2 = Syntax.read_term ctx "\<lambda>x z. (x  \<longrightarrow> z \<longrightarrow> z)"
val x = Pattern.unify (Context.Proof ctx) (tm1,tm2) Envir.init
val y = Envir.lookup x xxx
\<close>



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
