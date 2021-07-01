(* FIX ME: I have tried the best but the sidekick won't work right. Isabelle is not quite flexible in
  outer syntax and it is already the best hack can be given. *)
theory NuSys
  imports NuPrim NuSyntax NuBasicAbstractors
  keywords
    "proc" :: thy_decl_block
  and "\<medium_left_bracket>" "as" "\<rightarrow>" "\<longmapsto>" :: quasi_command
  and "\<bullet>" "premise" :: prf_decl % "proof"
  and "\<nu>processor" "\<nu>processor_resolver" :: thy_decl % "ML"
  and "\<nu>procedure" :: thy_decl
  and "finish" :: qed_block % "proof"
abbrevs
  "!!" = "!!"
begin

ML_file_debug NuHelp.ML
ML_file "./general/binary_tree.ML"
ML_file "./library/path.ML"
ML_file_debug NuBasics.ML
ML_file "./library/general.ML"
ML_file "./library/registers.ML"
ML_file "./library/instructions.ML"
ML_file "./general/parser.ML"
ML_file "./library/processor.ML"
ML_file "./library/processors.ML"
ML_file "./library/procedure.ML"
ML_file NuSys.ML
ML_file_debug NuToplevel.ML


ML \<open>Theory.setup (Global_Theory.add_thms_dynamic (@{binding "\<nu>instr"}, NuInstructions.list_definitions #> map snd))  \<close>
attribute_setup \<nu>instr = \<open>Scan.succeed (Thm.declaration_attribute NuInstructions.add) \<close>
attribute_setup \<nu>process = \<open>Scan.lift (Parse.$$$ "(" |-- Parse.name_position -- NuParse.auto_level --| Parse.$$$ ")") #>
    (fn ((name,auto_level),(ctx,toks)) =>
        Scan.lift (NuProcessor.get_attr ctx (name |> @{print}) auto_level) (ctx,toks))
  || Scan.lift (NuParse.auto_level #-> NuProcessor.process_attr)\<close>
attribute_setup show_proc_expression = \<open>NuToplevel.show_proc_expression_attr\<close>
(* declare [[show_proc_expression = false]] *)

ML \<open>

local open Scan NuToplevel NuSys Parse in
val bracket_begin = $$$ "\<medium_left_bracket>";

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>proc\<close> "begin a procedure construction"
    ((Parse_Spec.thm_name ":" -- Parse.term --| $$$ "\<longmapsto>" -- Parse.term -- Parse.for_fixes -- Scan.optional Parse_Spec.includes []
            -- Parse_Spec.if_statement) --| $$$ "begin" >>
        (fn (((((b,arg),ret),fixes),includes),preconds) =>  
            (begin_proc_cmd b arg ret fixes includes preconds)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finish\<close> "Finish the procedure construction"
    (Scan.succeed NuToplevel.finish_proc_cmd)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<bullet>\<close> "The \<nu>construction"
    (fn toks => (Toplevel.proof (NuToplevel.process_cmd (toks @ [Token.eof])), []))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>premise\<close> "proof for premise"
    (Scan.succeed (Toplevel.proof NuToplevel.prove_prem))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor\<close> "define \<nu>processor"
      (Parse.position (Parse.short_ident || Parse.sym_ident || Parse.keyword) -- Parse.nat -- Parse.term -- Parse.for_fixes -- Parse.ML_source -- Scan.optional Parse.text ""
        >> NuProcessor.setup_cmd)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>processor_resolver\<close> "define \<nu>processor"
      (Parse.binding -- Parse.nat -- (Parse.term -- Parse.for_fixes) -- Parse.name_position -- Scan.optional Parse.text ""
        >> (fn ((((b,precedence),pattern),facts),comment) => NuProcessor.setup_resolver b precedence pattern facts comment))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>\<nu>procedure\<close> "declare \<nu>procedure"
    (and_list1 binding >> (Context.proof_map o fold NuProcedure.declare))

end
\<close>

attribute_setup \<nu>proc = \<open>Scan.lift (Parse.name_position) >> (fn name => fn (ctx,th) =>
  if Thm.is_dummy th
  then (NONE, SOME (foldr1 (uncurry Conjunction.intr) (NuProcedure.check ctx name)))
  else (SOME (NuProcedure.define name th ctx), NONE))\<close>

(* \<nu>processor set_auto_level 10 \<open>PROP P\<close> \<open>(fn auto_level => fn ctx => fn th => NuParse.auto_level_force #->
  (fn auto_level' => NuProcessor.process (Int.min (auto_level, auto_level')) ctx th #> (fn x => raise ProcessTerminated x)))\<close> *)
\<nu>processor accept_proc 300 \<open>\<^bold>p\<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>n\<^bold>g f \<^bold>o\<^bold>n blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>safe (Scan.succeed oo NuSys.accept_proc)\<close>
\<nu>processor assign_register 500 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  (fn auto_level => fn ctx => fn th => ($$$ "\<rightarrow>" |-- (short_ident >> single || $$$ "(" |-- list1 short_ident --| $$$ ")")) >>
    (fn idts => fold (fn idt => NuSys.assign_reg ctx idt #> NuProcessor.process_no_input (Int.min (auto_level,1)) ctx) idts th))
end\<close>
\<nu>processor  load_register 100 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>let open Parse in
  safe (fn ctx => fn th => short_ident >> (fn idt => NuSys.load_reg ctx idt th
      handle NuRegisters.NoSuchRegister _ => raise Bypass))
end\<close>
\<nu>processor \<nu>simplifier 40 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close>  \<open>NuProcessors.simplifier\<close>
\<nu>processor \<nu>autoprover 9000 \<open>P \<Longrightarrow> PROP Q\<close>
  \<open>let open Tactical Method in 
    premise_prover (not_safe (fn ctx => SOLVED' (K (ALLGOALS (insert_tac ctx (Proof_Context.get_thms ctx "that")) THEN Simpdata.auto_tac ctx)) 0))
  end\<close>
\<nu>processor call 9000 \<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t blk \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n T\<close> \<open>safe (fn ctx => fn focus =>
  Parse.position (Parse.short_ident || Parse.keyword || Parse.sym_ident) >> (fn proc =>
    NuSys.apply_procs ctx (NuProcedure.check (Context.Proof ctx) proc) focus))\<close>

\<nu>processor_resolver resolve_disposable 100  \<open>\<nu>Disposable T \<Longrightarrow> PROP P\<close> \<nu>disposable
\<nu>processor_resolver resolve_share 100  \<open>Nu_Share N sh f \<Longrightarrow> PROP P\<close> \<nu>share
end