(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrim NuLLReps
  keywords
    "proc" :: thy_goal_stmt
  and "as" "\<rightarrow>" "\<longmapsto>" "\<leftarrow>" "^" "^*" "cast" "requires" :: quasi_command
  and "\<bullet>" "affirm" "\<nu>have" "\<nu>obtain" "\<nu>choose" "\<medium_left_bracket>" "\<medium_right_bracket>" "reg" "\<Longrightarrow>" "drop_fact" "\<nu>debug" :: prf_decl % "proof"
  and "\<nu>processor" "\<nu>processor_resolver" "\<nu>exty_simproc" :: thy_decl % "ML"
  and "\<nu>overloads" "\<nu>cast_overloads" :: thy_decl
  and "finish" :: "qed" % "proof"
abbrevs
  "!!" = "!!"
begin

section \<open>Preliminary constants and settings used in the system\<close>

named_theorems used \<open>theorems that will be inserted in ANY proof environments,
which basically has the same effect as the using command.\<close>
  and final_proc_rewrite \<open>rules used to rewrite the generated procedure theorem in the final stage\<close>
lemmas [final_proc_rewrite] = Premise_Irew End_of_Contextual_Stack_def[THEN eq_reflection]

definition  FailedPremise :: "bool \<Rightarrow> prop" where "FailedPremise \<equiv> Premise"
lemma FailedPremise_I: "\<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P \<Longrightarrow> PROP FailedPremise P" unfolding FailedPremise_def .
lemma FailedPremise_D: "PROP FailedPremise P \<Longrightarrow> \<^bold>p\<^bold>r\<^bold>e\<^bold>m\<^bold>i\<^bold>s\<^bold>e P" unfolding FailedPremise_def .

section \<open>Main implementation of the system\<close>

ML_file_debug NuHelp.ML
ML_file "./general/binary_tree.ML"
ML_file "./general/auto_level.ML"
ML_file "./library/path.ML"
ML_file_debug NuBasics.ML
ML_file "./library/general.ML"
ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/procedure.ML"
ML_file "./library/exty.ML"
ML_file NuSys.ML
ML_file "./library/registers.ML"
ML_file "./library/processors.ML"
ML_file NuToplevel.ML
ML_file "./library/obtain.ML"

section \<open>Attributes and Commands\<close>

ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<nu>instr"}, NuInstructions.list_definitions #> map snd))  \<close>
attribute_setup \<nu>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
  \<open>Instructions of \<nu>-system\<close>

attribute_setup \<nu>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position --| Parse.$$$ ")") #>
    (fn (name,(ctx,toks)) => Scan.lift (NuProcessor.get_attr ctx name) (ctx,toks))
  || Scan.lift NuProcessor.process_attr\<close>
  \<open>Evaluate the \<nu>-system process or the process of the given processor on the target theorem\<close>

method_setup \<nu>resolve = \<open>let open Scan Parse in
  option (Attrib.thms -- option (lift ($$$ "(") |-- Attrib.thms --| lift ($$$ ")"))) >> (fn ths => fn ctx =>
    Method.METHOD (fn th2 => NuSys.auto_resolve ths th2 ctx))
end\<close>

ML \<open>

local open Scan NuToplevel NuSys Parse 
val nustatement = Parse.and_list1 (Parse_Spec.thm_name ":" -- opt_attribs -- Scan.repeat1 Parse.propp);
val structured_statement =
  nustatement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));
in

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>exty_simproc\<close> "setup the pecific simproc for \<^const>\<open>ExTy\<close>"
  (Parse.binding >> NuExTyp.set_simproc_cmd)

val requires_statement = Scan.optional (Parse.$$$ "requires" |-- Parse.!!! Parse_Spec.statement) [];
val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((Parse_Spec.thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- requires_statement) >>
        (fn (((((b,arg),ret),fixes),includes),preconds) =>  
            (begin_proc_cmd b arg ret fixes includes preconds)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finish\<close> "Finish the procedure construction"
    (Scan.succeed (Toplevel.end_proof NuToplevel.finish_proc_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>debug\<close> "The \<nu>construction"
    (Scan.succeed (Toplevel.proof (fn stat =>
      stat |> Proof.map_context (NuSys.load_specthm (Proof.the_fact stat)))))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<bullet>\<close> "The \<nu>construction"
    (fn toks => (Toplevel.proof (NuToplevel.process_cmd (toks @ [Token.eof])),
      if hd toks |> Token.is_eof then [Token.eof] else []))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>affirm\<close> "proof for premise"
    (Scan.succeed (Toplevel.proof' (snd oo NuToplevel.prove_prem)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>have\<close> "proof for premise"
    (and_list1 ((binding -- opt_attribs -- opt_attribs --| $$$ ":") -- and_list1 (prop -- repeat prop)) >>
      (Toplevel.proof' o (snd ooo NuToplevel.have_aux_cmd)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>obtain\<close> "generalized elimination"
    (Parse.parbinding -- Scan.optional (Parse.vars --| Parse.where_) [] -- structured_statement
      >> (fn ((a, b), (c, d, e)) => Toplevel.proof' (NuObtain.obtain_cmd a b c d e)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<nu>choose\<close> "existential elimination"
    ( !!! vars --| $$$ "where" -- Scan.repeat1 Parse.prop
      >> (fn (b, c) => Toplevel.proof' (NuObtain.choose_cmd b c)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_left_bracket>\<close> "construct nested sub-procedure"
    (optional ($$$ "(" |-- and_list (binding -- opt_attribs) --| $$$ ")") [] >> (Toplevel.proof' o NuToplevel.begin_block_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<medium_right_bracket>\<close> "finish the nested sub-procedure construction"
    (Scan.succeed (Toplevel.proof' NuToplevel.end_block_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>reg\<close> "declare local registers"
    (Scan.repeat Parse.short_ident >> (fn names => Toplevel.proof (fn stat =>
      Proof.set_facts [Proof.the_fact stat |> NuRegisters.new_regs (Proof.context_of stat) names] stat)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<Longrightarrow>\<close> "name the star fact"
    (Parse.binding -- Parse.opt_attribs >> (Toplevel.proof o NuToplevel.name_star_fact_cmd))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>drop_fact\<close> "drop a fact"
    (Parse.list Parse.binding >> (fn names => Toplevel.proof (fold NuToplevel.drop_fact_cmd names)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor\<close> "define \<nu>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword) -- Parse.nat -- Parse.term -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
        >> NuProcessor.setup_cmd)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor_resolver\<close> "define \<nu>processor resolver"
      (Parse.binding -- Parse.nat -- (Parse.term -- Parse.for_fixes) -- Parse.name_position -- Scan.optional Parse.text ""
        >> (fn ((((b,precedence),pattern),facts),comment) => NuProcessors.setup_resolver b precedence pattern facts comment))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>overloads\<close> "declare procedure overloads"
    (and_list1 (binding -- Scan.optional Parse.text "") >>
        (fold (fn (b,s) => NuProcedure.declare_overloading b s #> #2)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>cast_overloads\<close> "declare cast overloads"
    (and_list1 (binding -- Scan.optional Parse.text "") >>
        (fold (fn (b,s) => NuProcedure.declare_overloading_cast b s #> #2)))

end
\<close>

attribute_setup \<nu>overload = \<open>Scan.lift (Parse.and_list1 NuProcedure.parser) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuProcedure.overload th) bindings))\<close>
attribute_setup \<nu>cast_overload = \<open>Scan.lift (Parse.and_list1 NuProcedure.parser) >> (fn bindings => 
  Thm.declaration_attribute (fn th => fold (NuProcedure.overload_cast th) bindings))\<close>

section \<open>Processors\<close>

\<nu>processor set_auto_level 10 \<open>PROP P\<close> \<open>(fn ctx => fn th => NuParse.auto_level_force #->
  (fn auto_level' => NuProcessor.process (AutoLevel.reduce auto_level' ctx) th #> (fn x => raise ProcessTerminated x)))\<close>
\<nu>processor repeat 12 \<open>PROP P\<close> \<open>let
    fun repeat n f x = if n <= 0 then x else ((repeat (n-1) f (f x)) handle _ => x)
  in fn ctx => fn th => Parse.not_eof -- ((Parse.$$$ "^" |-- Parse.number) || Parse.$$$ "^*")
    >> (fn (tok,n) => fn _ => (case Int.fromString n of SOME n => funpow n | _ => repeat 32)
        (NuProcessor.process ctx #> (fn p => p [tok,Token.eof] |> #1)) th)
  end\<close>

\<nu>processor accept_proc 300 \<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn th => Scan.succeed (fn _ => NuSys.accept_proc ctx th)\<close>

\<nu>processor assign_register 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  (fn ctx => fn th => ($$$ "\<rightarrow>" |-- (short_ident >> single || $$$ "(" |-- list1 short_ident --| $$$ ")")) >>
    (fn idts => fn _ => fold_rev (fn idt =>
      NuRegisters.assign_reg ctx idt
        #> NuProcessor.process_no_input (AutoLevel.reduce 1 ctx)) idts th))
end\<close>
\<nu>processor  load_register 100 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  fn ctx => fn th => short_ident >> (fn idt => fn _ => NuRegisters.load_reg ctx idt th
      handle NuRegisters.NoSuchRegister _ => raise Bypass)
end\<close>
\<nu>processor move_register 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  (fn ctx => fn th => ($$$ "\<leftarrow>" |-- (short_ident >> single || $$$ "(" |-- list1 short_ident --| $$$ ")")) >>
    (fn idts => fn _ => fold (fn idt => NuRegisters.move_reg ctx idt #> NuProcessor.process_no_input (AutoLevel.reduce 1 ctx)) idts th))
end\<close>

\<nu>processor \<nu>simplifier 40 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>NuProcessors.simplifier []\<close>
\<nu>processor \<nu>simplifier_final 10000 \<open>PROP P\<close>  \<open>NuProcessors.simplifier []\<close>

\<nu>processor move_fact 50 \<open>(\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T) \<and> P\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  meta RS @{thm move_fact_to_star1} handle THM _ => meta RS @{thm move_fact_to_star2})\<close>

\<nu>processor \<nu>resolver 9000 \<open>PROP P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Scan.succeed (fn _ =>
  NuBasics.elim_SPEC meta |> apfst (fn major =>
  case Seq.pull (NuSys.auto_resolve NONE [] (NuSys.load_specthm meta ctx) major)
    of SOME (major', _) => major' | _ => raise Bypass) |> NuBasics.intro_SPEC)\<close>

\<nu>processor call 9000 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open> fn ctx => fn meta => NuProcedure.parser >> (fn binding => fn _ =>
    let val ctx = NuSys.load_specthm meta ctx
    in NuSys.apply_procs ctx (NuProcedure.procedure_thm ctx binding) meta end)\<close>

\<nu>processor cast 8900 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>
  \<open> fn ctx => fn meta => (Parse.$$$ "cast" |-- (Parse.$$$ "(" |-- Parse.list NuProcedure.parser --| Parse.$$$ ")" || (NuProcedure.parser >> single)))
    >> (fn bindings => fn _ =>
      let val ctx = NuSys.load_specthm meta ctx
      in fold (NuSys.apply_casts ctx o NuProcedure.cast_thm ctx) bindings meta end)\<close>

\<nu>processor set_param 5000 \<open>\<^bold>p\<^bold>a\<^bold>r\<^bold>a\<^bold>m P \<Longrightarrow> PROP Q\<close> \<open>fn ctx => fn meta => Parse.term >> (fn term => fn _ =>
    NuBasics.elim_SPEC meta |> apfst (fn th =>
      let val mapty = map_atyps (fn ty => case ty of TVar _ => dummyT | _ => ty)
      in (Syntax.parse_term ctx term |> Type.constraint (NuBasics.param_type th |> mapty) |> Syntax.check_term ctx
          |> Thm.cterm_of ctx |> NuBasics.intro_param) RS th
      end) |> NuBasics.intro_SPEC)\<close>

\<nu>processor literal_constructor 9500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.cartouche >> (fn term => fn _ =>
  let val term = Syntax.read_term ctx term |> Thm.cterm_of ctx |> Simplifier.rewrite ctx |> Thm.rhs_of
        val ctx = NuSys.load_specthm meta ctx
  in NuSys.auto_construct ctx term meta end)\<close>

\<nu>processor literal_number 9500\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>fn ctx => fn meta => Parse.number >> (fn num => fn _ =>
  let open NuBasics
    val term = (stack_of_meta meta |> hd |> dest_RepSet |> dest_nuTy |> #2) handle TERM _ => @{term \<open>\<nat>[32]\<close>}
    val term = mk_nuTy (Syntax.parse_term ctx num, term) |> Syntax.check_term ctx |> Thm.cterm_of ctx
    val ctx = NuSys.load_specthm meta ctx
  in NuSys.auto_construct ctx term meta  end)
\<close>

\<nu>cast_overloads E I

end