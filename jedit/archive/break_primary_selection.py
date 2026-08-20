"""Show that every check of the primary-selection wrapper can fail.

Section 22 of ../test_word_clipboard.bsh covers the wrapper `phi_install_primary_selection`
puts on jEdit's `%` register.  Each case below writes that wrapper wrong in exactly one way
and expects the suite to refuse the run -- by the named check, not merely by failing
somewhere.  `UI_FONT_PLAN.md` made this a standard -- "a check nobody has seen fail is not
a check" -- and a harness that only ever lived in a scratch directory could not hold anyone
to it, which is why this is committed.

Run it from anywhere:  python3 jedit/archive/break_primary_selection.py
It takes a few minutes: every case runs the whole suite, which builds a million-character
sample for the performance floor.

The component is never touched.  Each case builds a scratch PHI_SYSTEM_HOME of symlinks
whose only real file is the damaged script, and runs ../run_word_clipboard_test.sh inside
it -- the same runner a developer runs, so the timeout, the display and the three ways it
reports a failure are exercised too, rather than reimplemented here.

Not every property is guarded here.  This harness damages only the primary-selection
wrapper; the rest of the script has no such harness, and the two generated halves of the
table are guarded by ../../fonts/archive/break_checks.py instead.  The last case has no
named check: with no local declared at all the wrapper recurses into itself until the stack
runs out, and what refuses the run is the runner's own error detection.
"""
import os, pathlib, re, shutil, subprocess, sys, tempfile

COMPONENT = pathlib.Path(__file__).resolve().parents[2]
ISABELLE = pathlib.Path(os.environ.get(
    "ISABELLE_HOME", COMPONENT.parent / "Isabelle2025-2"))
SCRIPT = COMPONENT / "jedit/phi_word_clipboard.bsh"
LINKED = ("symbols-words", "fonts/PhiSymbols.ttf", "jedit/word-clipboard-text",
          "jedit/test_word_clipboard.bsh", "jedit/run_word_clipboard_test.sh")

# (what is written wrong, the check that must catch it, [(before, after), ...])
CASES = [
    ("nothing is damaged at all", None, []),

    ("phi_word_install never calls the install",
     "the load-time install reaches the platform's primary selection",
     [("    phi_install_primary_selection();\n", "")]),

    ("expanding and folding are swapped",
     "a selected glyph leaves as letters",
     [("phi_word_expand(phi_t, phi_original)", "phi_word_fold(phi_t, phi_original)"),
      ("phi_word_fold(phi_t, phi_now)", "phi_word_expand(phi_t, phi_now)")]),

    ("toString answers for itself instead of delegating",
     "toString delegates to the register underneath",
     [("public String toString() { return phi_primary.toString(); }",
       'public String toString() { return "something else"; }')]),

    ("the wrapper remembers nothing it published",
     "and the memo makes that round trip exact",
     [('                        phi_memo.put("original", phi_original);\n'
       '                        phi_memo.put("expanded", phi_expanded);\n', "")]),

    ("one memo is shared by every install",
     "installed twice, it still reads back as the glyph",
     [("    Object phi_memo = new java.util.HashMap();",
       "    Object phi_memo = phi_one_shared_memo;"),
      ("phi_install_primary_selection()\n{",
       "phi_one_shared_memo = new java.util.HashMap();\n\n"
       "phi_install_primary_selection()\n{")]),

    ("the failure path fetches the selection a second time",
     "the failure path fetched the selection",
     [("            // the transferable already in hand, not a second "
       "phi_primary.getTransferable():\n"
       "            // that would cost another blocking fetch from the selection's owner\n"
       "            catch (Exception e) { return phi_outer; }",
       "            catch (Exception e) { return phi_primary.getTransferable(); }")]),

    ("the pass-through write sits after the try, not inside it",
     "a throwing selection escaped the pass-through path",
     [("""                // inside the try, not after it: written after, a selection that throws
                // would be caught here and then written again unguarded, and the second
                // throw would escape onto the AWT event thread
                phi_primary.setTransferable(t2);
            }
            catch (Exception e) { }""",
       """            }
            catch (Exception e) { }
            phi_primary.setTransferable(t2);""")]),

    ("the guard for a platform with no primary selection is gone",
     "the install did not return early where there is no primary selection",
     [("    if (phi_primary == null) return;            "
       "// no primary selection on this platform\n", "")]),

    ("one local in the writing path is not declared with a type",
     "wrote through to a global sharing a local's name",
     [("String phi_original = t2.getTransferData", "phi_original = t2.getTransferData"),
      ("String phi_expanded = phi_word_expand", "phi_expanded = phi_word_expand")]),

    ("no local is declared with a type", None,
     [("Object phi_primary = Registers", "phi_primary = Registers"),
      ("Object phi_memo = new java.util.HashMap();", "phi_memo = new java.util.HashMap();"),
      ("Object phi_selection = new Registers.Register()",
       "phi_selection = new Registers.Register()"),
      ("String phi_original = t2.getTransferData", "phi_original = t2.getTransferData"),
      ("String phi_expanded = phi_word_expand", "phi_expanded = phi_word_expand"),
      ("Transferable phi_outer = null;", "phi_outer = null;"),
      ("String phi_now = phi_outer.getTransferData", "phi_now = phi_outer.getTransferData"),
      ("String phi_sent = phi_memo.get", "phi_sent = phi_memo.get")]),
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
