theory Ledger_Dump
  imports "../Current/MLML/contrib/phi-system/Phi_Examples/PhiEx_All"
begin

text \<open>Ledger dump for DEBT_AXIOM_POLY_SUPPORT_PLAN.md section 8.3-1.
  Per LEDGER ENTRY (a term): the proposition with sorts (exact ML syntax and a
  show_sorts pretty rendering) and Term.maxidx_of_term.
  Per DEBT FACT (the noted global fact of the same name): proposition with
  sorts, Thm.maxidx_of, tags, shyps, hyps count.
  Output: /home/xero/debt_dump_20260902/ledger_dump.out.txt (mv'd by the
  driver to ledger_dump.pre.txt / ledger_dump.post.txt).\<close>

ML_command \<open>
  let
    val thy = \<^theory>;
    val ctxt = Proof_Context.init_global thy |> Config.put show_sorts true;
    fun pretty_term t = Syntax.string_of_term ctxt t;
    val debts = Symtab.dest (Debt_Axiom.debts thy);
    fun fact_lines N =
      (case try (Global_Theory.get_thms thy) N of
        NONE => ["FACT: NONE"]
      | SOME ths =>
          map_index (fn (i, th) =>
            let val tag = "FACT[" ^ string_of_int i ^ "] "
            in [tag ^ "prop_ml: " ^ ML_Syntax.print_term (Thm.full_prop_of th),
                tag ^ "prop_pretty: " ^ pretty_term (Thm.full_prop_of th),
                tag ^ "maxidx: " ^ string_of_int (Thm.maxidx_of th),
                tag ^ "tags: " ^ commas (map (fn (a, b) => a ^ "=" ^ b) (Thm.get_tags th)),
                tag ^ "shyps: " ^ commas (map ML_Syntax.print_sort (Thm.shyps_of th)),
                tag ^ "hyps_count: " ^ string_of_int (length (Thm.hyps_of th))]
            end) ths |> flat);
    fun entry_block (N, tm) =
      cat_lines
        (["ENTRY: " ^ N,
          "LEDGER prop_ml: " ^ ML_Syntax.print_term tm,
          "LEDGER prop_pretty: " ^ pretty_term tm,
          "LEDGER maxidx: " ^ string_of_int (Term.maxidx_of_term tm)]
         @ fact_lines N);
    val out =
      "DEBT COUNT: " ^ string_of_int (length debts) ^ "\n" ^
      cat_lines (map entry_block debts) ^ "\n";
  in File.write (Path.explode "/home/xero/debt_dump_20260902/ledger_dump.out.txt") out end
\<close>

end
