(*
The file provides an alternative of the antiquotation @{thm}, @{thms} and @{lemmas}
  in which, the stored lemmas are context-free, so that the total memory usage may be saved.
*)

signature PHI_ML_THMS =
sig
  (*val the_attributes: Proof.context -> int -> Token.src list*)
  val the_thmss: Proof.context -> thm list list
  (* val embedded_lemma: (Proof.context -> thm list * (term list * Proof.context)) parser *)
end

structure Phi_ML_Thms: PHI_ML_THMS =
struct

(* auxiliary data *)

type thms = (string * bool) * thm list;  (*name, single, value*)

structure Data = Proof_Data
(
  type T = Token.src list Inttab.table * thms list;
  fun init _ = (Inttab.empty, []);
);

(*val put_attributes = Data.map o apfst o Inttab.update;
fun the_attributes ctxt name = the (Inttab.lookup (fst (Data.get ctxt)) name); *)

val get_thmss = snd o Data.get;
val the_thmss = map snd o get_thmss;
val cons_thms = Data.map o apsnd o cons;

(*
(* attribute source *)

val _ = Theory.setup
  (ML_Antiquotation.declaration \<^binding>\<open>attributes\<close> Attrib.attribs
    (fn _ => fn srcs => fn ctxt =>
      let val i = serial () in
        ctxt
        |> put_attributes (i, srcs)
        |> ML_Antiquotation.value_decl "attributes"
            ("Phi_ML_Thms.the_attributes ML_context " ^ string_of_int i)
      end)); *)


(* fact references *)

fun thm_binding kind is_single thms ctxt =
  let
    val initial = null (get_thmss ctxt);
    val (name, ctxt') = ML_Context.variant kind ctxt;
    val ctxt'' = cons_thms ((name, is_single), map Thm.trim_context thms) ctxt';

    val ml_body = ML_Context.struct_name ctxt ^ "." ^ name;
    fun decl final_ctxt =
      if initial then
        let
          val binds = get_thmss final_ctxt |> map (fn ((a, b), _) => (b ? enclose "[" "]") a);
          val ml_env = "val [" ^ commas binds ^ "] = Phi_ML_Thms.the_thmss ML_context;\n";
        in (ml_env, ml_body) end
      else ("", ml_body);
  in (decl, ctxt'') end;

val embedded_lemma =
  Args.mode "open" -- Parse.and_list1 (Scan.repeat1 Parse.embedded_inner_syntax)
    -- Parse.for_fixes -- Method.parse_by
    >> (fn (((is_open, raw_stmt), fixes), (methods, reports)) => fn ctxt =>
        let
          val _ = Context_Position.reports ctxt reports;

          val fixes_ctxt = #2 (Proof_Context.add_fixes_cmd fixes ctxt);
          val stmt = burrow (map (rpair []) o Syntax.read_props fixes_ctxt) raw_stmt;
          val stmt_ctxt = (fold o fold) (Proof_Context.augment o #1) stmt fixes_ctxt;

          val prep_result = Goal.norm_result ctxt #> not is_open ? Thm.close_derivation \<^here>;
          fun after_qed res goal_ctxt =
            Proof_Context.put_thms false (Auto_Bind.thisN,
              SOME (map prep_result (Proof_Context.export goal_ctxt ctxt (flat res)))) goal_ctxt;

          val thms_ctxt = stmt_ctxt
            |> Proof.theorem NONE after_qed stmt
            |> Proof.global_terminal_proof methods;
          val thms =
            Proof_Context.get_fact thms_ctxt
              (Facts.named (Proof_Context.full_name thms_ctxt (Binding.name Auto_Bind.thisN)))
            |> map Thm.trim_context
        in (thms, (map #1 (flat stmt), stmt_ctxt)) end);


val _ = Theory.setup
  (ML_Antiquotation.declaration \<^binding>\<open>thm'\<close> (Attrib.thm >> single) (K (thm_binding "thm" true)) #>
   ML_Antiquotation.declaration \<^binding>\<open>thms'\<close> Attrib.thms (K (thm_binding "thms" false)) #>
   ML_Antiquotation.declaration \<^binding>\<open>lemma'\<close> (Scan.lift embedded_lemma)
    (fn _ => fn make_lemma => fn ctxt =>
      let val thms = #1 (make_lemma ctxt)
      in thm_binding "lemma" (length thms = 1) thms ctxt end));

(*
(* embedded lemma *)

val embedded_lemma =
  Args.mode "open" -- Parse.and_list1 (Scan.repeat1 Parse.embedded_inner_syntax)
    -- Parse.for_fixes -- Method.parse_by
    >> (fn (((is_open, raw_stmt), fixes), (methods, reports)) => fn ctxt =>
        let
          val _ = Context_Position.reports ctxt reports;

          val fixes_ctxt = #2 (Proof_Context.add_fixes_cmd fixes ctxt);
          val stmt = burrow (map (rpair []) o Syntax.read_props fixes_ctxt) raw_stmt;
          val stmt_ctxt = (fold o fold) (Proof_Context.augment o #1) stmt fixes_ctxt;

          val prep_result = Goal.norm_result ctxt #> not is_open ? Thm.close_derivation \<^here>;
          fun after_qed res goal_ctxt =
            Proof_Context.put_thms false (Auto_Bind.thisN,
              SOME (map prep_result (Proof_Context.export goal_ctxt ctxt (flat res)))) goal_ctxt;

          val thms_ctxt = stmt_ctxt
            |> Proof.theorem NONE after_qed stmt
            |> Proof.global_terminal_proof methods;
          val thms =
            Proof_Context.get_fact thms_ctxt
              (Facts.named (Proof_Context.full_name thms_ctxt (Binding.name Auto_Bind.thisN)))
        in (thms, (map #1 (flat stmt), stmt_ctxt)) end);

val _ = Theory.setup
  (ML_Antiquotation.declaration \<^binding>\<open>lemma\<close> (Scan.lift embedded_lemma)
    (fn _ => fn make_lemma => fn ctxt =>
      let val thms = #1 (make_lemma ctxt)
      in thm_binding "lemma" (length thms = 1) thms ctxt end)); *)


end;
