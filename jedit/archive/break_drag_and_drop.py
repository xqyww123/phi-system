"""Show that every check of the drag-and-drop handler can fail.

Sections 23 to 25 of ../test_word_clipboard.bsh cover the handler
`Phi_Text_Area_Transfer_Handler`, the two functions it leans on -- `phi_unexpand` and
`phi_delegating` -- and the EditBus component `phi_install_drag` puts on the bus.  Each case
below writes one of them wrong in exactly one way and expects the suite to refuse the run --
by the named check, not merely by failing somewhere.  `UI_FONT_PLAN.md` made this a standard
-- "a check nobody has seen fail is not a check" -- and a harness that only ever lived in a
scratch directory could not hold anyone to it, which is why this is committed.

Run it from anywhere:  python3 jedit/archive/break_drag_and_drop.py
It takes several minutes: every case runs the whole suite, which builds a million-character
sample for the performance floor.

The component is never touched.  Each case builds a scratch PHI_SYSTEM_HOME of symlinks
whose only real file is the damaged script, and runs ../run_word_clipboard_test.sh inside
it -- the same runner a developer runs, so the timeout, the display and the three ways it
reports a failure are exercised too, rather than reimplemented here.

Not every property is guarded here.  This harness damages only the drag-and-drop code;
../archive/break_primary_selection.py does the same for the `%` register wrapper, and the
two generated halves of the table are guarded by ../../fonts/archive/break_checks.py.
"""
import os, pathlib, shutil, subprocess, sys, tempfile

COMPONENT = pathlib.Path(__file__).resolve().parents[2]
ISABELLE = pathlib.Path(os.environ.get(
    "ISABELLE_HOME", COMPONENT.parent / "Isabelle2025-2"))
SCRIPT = COMPONENT / "jedit/phi_word_clipboard.bsh"
LINKED = ("symbols-words", "fonts/PhiSymbols.ttf", "jedit/word-clipboard-text",
          "jedit/test_word_clipboard.bsh", "jedit/run_word_clipboard_test.sh")

# (what is written wrong, the check that must catch it, [(before, after), ...])
CASES = [
    ("nothing is damaged at all", None, []),

    ("phi_word_install never registers the component",
     "drag components on the bus at load time, not one",
     [("    phi_install_drag();\n", "")]),

    ("expanding and folding are swapped on the way out",
     "a drag out of a buffer carries the letters",
     [("\n                String phi_expanded = phi_word_expand(phi_t, phi_original);",
       "\n                String phi_expanded = phi_word_fold(phi_t, phi_original);")]),

    ("the drag remembers nothing it handed out",
     "createTransferable did not fill the slots",
     [('                phi_drag.put("original", phi_original);\n'
       '                phi_drag.put("expanded", phi_expanded);\n', "")]),

    ("what arrives is always folded, never restored",
     "a drag we started comes back as the text it was made from",
     [('        if (phi_sent != null && phi_sent.equals(phi_s)) '
       'phi_out = phi_drag.get("original");\n'
       '        else phi_out = phi_word_fold(phi_t, phi_s);'
       '                   // not a drag we started\n',
       "        phi_out = phi_word_fold(phi_t, phi_s);\n")]),

    ("the incoming transferable is replaced rather than delegated to",
     "the wrapper did not delegate a flavor it does not replace",
     [("        return phi_delegating(phi_in, phi_out);",
       "        return new StringSelection(phi_out);")]),

    ("with nothing to fold the original transferable is handed back",
     "the transferable was handed back rather than wrapped",
     [("        return phi_delegating(phi_in, phi_out);",
       "        if (phi_out.equals(phi_s)) return phi_in;\n"
       "        return phi_delegating(phi_in, phi_out);")]),

    ("the file-list guard is gone",
     "a file drop did not come back untouched",
     [("        if (phi_in.isDataFlavorSupported(DataFlavor.javaFileListFlavor)) "
       "return phi_in;\n", "")]),

    ("the uri-list guard is gone",
     "a uri-list drop did not come back untouched",
     [('''        for (DataFlavor phi_fl : phi_in.getTransferDataFlavors()) {   // jEdit's own uri-list
            if ("text".equals(phi_fl.getPrimaryType())                // test, which is private
                    && "uri-list".equals(phi_fl.getSubType())
                    && phi_fl.getRepresentationClass() == String.class)
                return phi_in;
        }
''', "")]),

    ("the overrides are declared protected, as the superclass declares them",
     "not public; bsh cannot reach super",
     [("    public Transferable createTransferable(javax.swing.JComponent phi_c) {",
       "    protected Transferable createTransferable(javax.swing.JComponent phi_c) {")]),

    ("exportDone re-inserts what arrived, without folding it",
     "a drag within one text area moves the glyphs, not their letters",
     [("        try { super.exportDone(phi_c, phi_unexpand(phi_tr), phi_action); }",
       "        try { super.exportDone(phi_c, phi_tr, phi_action); }")]),

    ("exportDone does not clear the slots",
     "exportDone left the slots filled",
     [("        finally { phi_drag.clear(); }", "")]),

    ("createTransferable does not clear the slots on the way in",
     "createTransferable did not clear the slots first",
     [("        phi_drag.clear();          "
       "// a drag that skipped exportDone may have left slots\n", "")]),

    ("importData has no guard of its own",
     "a throw out of super escaped importData",
     [("        try { return super.importData(phi_c, phi_unexpand(phi_tr)); }\n"
       "        catch (Exception e) { Log.log(Log.ERROR, this, e); return false; }",
       "        return super.importData(phi_c, phi_unexpand(phi_tr));")]),

    ("the bus component has no guard, so a throw stops the bus",
     "stopped the bus",
     [("            try {\n"
       "                // CREATED is declared Object, so its identity is not part of the "
       "contract\n"
       "                if (phi_msg instanceof EditPaneUpdate\n"
       "                        && EditPaneUpdate.CREATED.equals(phi_msg.getWhat()))\n"
       "                    phi_msg.getEditPane().getTextArea()\n"
       "                           .setTransferHandler(new Phi_Text_Area_Transfer_Handler());\n"
       "            }\n"
       "            catch (Exception e) { Log.log(Log.ERROR, this, e); }\n",
       "            if (phi_msg instanceof EditPaneUpdate\n"
       "                    && EditPaneUpdate.CREATED.equals(phi_msg.getWhat()))\n"
       "                phi_msg.getEditPane().getTextArea()\n"
       "                       .setTransferHandler(new Phi_Text_Area_Transfer_Handler());\n")]),

    ("one local of the drag code is not declared with a type",
     "wrote through to the global phi_out",
     [("        String phi_out;\n", "")]),
]


def run(script_text):
    """The suite, over a component whose only real file is the damaged script."""
    root = pathlib.Path(tempfile.mkdtemp(prefix="phi-break-"))
    try:
        for rel in LINKED:
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).symlink_to(COMPONENT / rel)
        (root / "jedit/phi_word_clipboard.bsh").write_text(script_text, encoding="utf-8")
        done = subprocess.run([str(root / "jedit/run_word_clipboard_test.sh")],
                              capture_output=True, text=True,
                              env=dict(os.environ, ISABELLE_HOME=str(ISABELLE)))
        return done.returncode, (done.stdout + done.stderr)[:200000]
    finally:
        shutil.rmtree(root)


original = SCRIPT.read_text(encoding="utf-8")
failures = 0
for what, caught_by, edits in CASES:
    text = original
    for before, after in edits:
        if text.count(before) != 1:
            sys.exit("%s: %d matches for %r -- the script has moved on"
                     % (what, text.count(before), before[:60]))
        text = text.replace(before, after)

    code, out = run(text)
    refused = code != 0
    lines = [l for l in out.splitlines() if l.startswith("FAIL ")]   # not the summary
    named = caught_by is None or any(caught_by in l for l in lines)
    ok = refused == bool(edits) and named
    failures += not ok
    print("%-4s %-58s %s" % ("ok" if ok else "BAD", what,
                             "refused" if refused else "accepted"))
    for line in lines[:3]:
        print("       " + line[:100])
    if not named:
        print("       (nothing said %r)" % caught_by)

sys.exit(failures and "%d case(s) behaved unexpectedly" % failures)
