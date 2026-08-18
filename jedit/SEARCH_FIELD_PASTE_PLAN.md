# Making paste into jEdit's text input fields fold word glyphs

Read `WORD_CLIPBOARD_PLANS.md` beside this file first: it carries the implementation
order, the decisions the user has settled, the conventions all four plans follow, and what
has already been reviewed.

A work plan, the **third** of four. `WORD_BOUNDARY_PLAN.md` goes in first and rewrites the
two functions this one calls; `PRIMARY_SELECTION_PLAN.md` and `DRAG_AND_DROP_PLAN.md` are
the other two. Read `../fonts/WORD_GLYPHS.md` first; it defines the feature all four extend.

Source read from the Isabelle component's own jEdit tree:

    contrib/Isabelle2025-2/contrib/jedit-20251128/jedit5.7.0-patched/jEdit/

**Convention.** A claim marked *measured* was produced by running code — jEdit's repackaged
BeanShell out of `jedit.jar`, under `xvfb-run` where Swing components or a clipboard were
needed.


## The problem

Copy a word glyph out of a buffer and paste it into jEdit's own Find box, then search. The
search finds nothing.

This is a consequence of the copy fix, not of any missing fix. `phi_word_clipboard.bsh`
deliberately replaces the **plain-text** flavor on the clipboard with the word in
mathematical letters — that is the point, so another application shows `pending` rather than
a blank box. Pasting back into a **buffer** is exact because jEdit's own rich-text flavor
still carries the glyph. But the Find box is not a jEdit text area: it is a plain Swing text
component whose stock transfer handler reads only the plain-text flavor, so it receives the
letters, and the buffer holds U+E048.


## What is broken, verified

The widgets:

* Search and Replace dialog — `find` is `new HistoryTextArea("find")`
  (`search/SearchDialog.java:415`), `replace` likewise (`:452`); `HistoryTextArea extends
  javax.swing.JTextArea` (`gui/HistoryTextArea.java:38`). Neither reaches a container
  directly: each is wrapped, `fieldPanel.add(new JScrollPane(find),cons)` at `:430` and the
  same shape at `:461`.
* Quick-search bar — `add(find = new HistoryTextField("find"))` (`search/SearchBar.java:63`);
  `HistoryTextField extends javax.swing.JTextField` (`gui/HistoryTextField.java:41`).
* The dialog's file filter and directory boxes are `HistoryTextField` too (`:616`, `:656`).

Neither class defines any paste handling — `grep` for `TransferHandler|paste|Registers|DataFlavor`
over both files returns nothing — so both use Swing's stock handler, and
`SearchDialog.java:898` feeds `find.getText()` straight to `SearchAndReplace.setSearchString`
with no normalisation.

**Measured**, end to end, with the phi service registered and a real system clipboard:

```
what Registers.copy puts on the clipboard, stringFlavor: U+1D429 U+1D41E U+1D427 U+1D41D U+1D422 U+1D427 U+1D420
Find field class      : org.gjt.sp.jedit.gui.HistoryTextArea  (a javax.swing.JTextArea)
its TransferHandler   : javax.swing.plaf.basic.BasicTextUI$TextTransferHandler
PASTED INTO FIND BOX  : U+1D429 U+1D41E U+1D427 U+1D41D U+1D422 U+1D427 U+1D420
the buffer contains   : U+E048
would the search match? false
```

**The common path is fine**, which is worth knowing before deciding how much this matters.
jEdit's `find` action passes the current selection to the dialog directly —
`actions.xml:395` is `SearchDialog.showSearchDialog(view,textArea.getSelectedText(),SearchDialog.CURRENT_BUFFER)`
— never touching the clipboard. Measured with the same harness: the pre-filled field holds
U+E048 and the search matches. So "select the word, press Ctrl-F" works today; it is "copy,
then paste into the box" that does not.


## The mechanism

Wrap each field's existing `javax.swing.TransferHandler` in a delegating subclass that
rewrites the incoming string and forwards everything else. The methods needed for the
clipboard route are all public on `javax.swing.TransferHandler`, so unlike the drag work
there is no protected-`super` obstacle: the wrapper holds the original handler and calls it.

### Prefer jEdit's own rich text; fold only what is not ours

The first draft folded the plain-text flavor and nothing else. That is lossy, and the exact
text is sitting on the same clipboard: for any copy made inside jEdit, the original — glyphs
and all — is under `JEditDataFlavor.jEditRichTextDataFlavor`, registered as a default service
(`org/gjt/sp/jedit/services.xml:179`, built by `RichJEditTextTransferableService.java:43`).
**Measured**: after a `JEditTransferable` holding `stringFlavor`=letters and the rich flavor
carrying U+E048 is put on the clipboard, `getContents(null)` returns a proxy for which
`isDataFlavorSupported(jEditRichTextDataFlavor)` is true and the text is U+E048.

**This is not a new technique in this file** — `phi_word_clipboard.bsh:345` already does
exactly it for the `$` register, with the comment "text jEdit itself put there: it still
carries the glyphs, take it as is".  (That citation is post-`WORD_BOUNDARY_PLAN.md`; it was
`:177` before that rewrite.) Reusing it makes an intra-jEdit copy **exact**: no
dependence on the fold rule, so none of the shapes `WORD_BOUNDARY_PLAN.md` cannot repair —
a glyph against the user's own mathematical letters, a glyph separated by `_` — can reach
the search box at all.

So the order is: rich flavor if present, else fold the plain text, else leave alone.

**Write it as an anonymous subclass bound to a name, not as a scripted class.** Two
measured facts about jEdit's BeanShell force this, and both cost an afternoon to find:
a scripted class's constructor is not found when its parameter has no declared type
(`Can't find constructor: Phi_Field_Transfer_Handler( ... )`), and the anonymous subclass bsh
generates has **only a no-arg constructor** — it does not forward arguments to the superclass,
so `new javax.swing.TransferHandler("phi") { ... }` fails the same way. The form that works is
`new javax.swing.TransferHandler() { ... }`, which reaches the superclass's protected no-arg
constructor as a subclass may. Everything the wrapper overrides returns a primitive or void,
which is the shape bsh's anonymous-class parser handles, so the body parses in any position.
A function returning the wrapper gives the test a way to wrap a recording handler:

```
phi_field_handler(phi_inner)              // one wrapper per field, closing over its handler
{
    phi_handler = new javax.swing.TransferHandler() {
        public boolean canImport(JComponent c, DataFlavor[] f) {
            return phi_inner.canImport(c, f);
        }
        public boolean canImport(javax.swing.TransferHandler.TransferSupport s) {
            return phi_inner.canImport(s);
        }
        public int getSourceActions(JComponent c) { return phi_inner.getSourceActions(c); }
        public void exportToClipboard(JComponent c, Clipboard cb, int a) {
            phi_inner.exportToClipboard(c, cb, a);
        }
        public void exportAsDrag(JComponent c, java.awt.event.InputEvent e, int a) {
            phi_inner.exportAsDrag(c, e, a);
        }
        public boolean importData(JComponent c, Transferable t) {
            try {
                if (t != null && t.isDataFlavorSupported(JEditDataFlavor.jEditRichTextDataFlavor)) {
                    phi_rich = t.getTransferData(JEditDataFlavor.jEditRichTextDataFlavor);
                    if (phi_rich != null)
                        return phi_inner.importData(c, new StringSelection(phi_rich.getText()));
                }
                if (t != null && t.isDataFlavorSupported(DataFlavor.stringFlavor)) {
                    phi_plain = t.getTransferData(DataFlavor.stringFlavor);
                    if (phi_plain != null) {
                        phi_folded = phi_word_fold(phi_t, phi_plain);
                        if (!phi_folded.equals(phi_plain))
                            return phi_inner.importData(c, new StringSelection(phi_folded));
                    }
                }
            }
            catch (Exception e) { }
            return phi_inner.importData(c, t);
        }
    };
    return phi_handler;
}
```

`phi_wrap_field` installs one and marks the field, and the mark rather than an `instanceof`
test is what makes it idempotent: jEdit resets the BeanShell class manager when a plugin is
unloaded, and against a fresh class object `instanceof` would answer "not ours" and wrap a
wrapper, folding twice.

```
phi_wrap_field(phi_field)
{
    if (phi_field == null) return false;
    if (phi_field.getClientProperty("phi_word_wrapped") != null) return false;
    phi_inner = phi_field.getTransferHandler();
    if (phi_inner == null) return false;
    phi_field.setTransferHandler(phi_field_handler(phi_inner));
    phi_field.putClientProperty("phi_word_wrapped", Boolean.TRUE);
    return true;
}
```

`phi_t` comes from `WORD_BOUNDARY_PLAN.md`, which hoists the table to a top-level name.
Joiner removal needs no call here: that plan puts the strip inside `phi_word_fold` itself
precisely so no consumer has to remember it, and this plan was one of two that forgot the
helper an earlier draft proposed.

### What the delegation does not cover, and why that is accepted

**`importData(TransferSupport)` is inherited, not overridden, and that is a real divergence,
not a no-op.** The JDK's base implementation does forward to the two-argument form
(`TransferHandler.java:825-829`), so our `importData` runs. But the handler being wrapped
overrides that method itself — `BasicTextUI.java:2537-2556` records `isDrop`, `modeBetween`,
`dropBias` and `dropAction` from the `TransferSupport`, calls `super.importData(support)`,
then clears them in a `finally`. Because Swing calls the *wrapper's* inherited version, the
inner override never runs, so on a **drop** into a field the inner two-argument body sees
`isDrop == false`: no `requestFocus`, the dropped text is not selected afterwards, and
`dropAction` stays at its initialiser. Paste is unaffected. Accepted, and stated here so it
is not discovered as a mystery.

**The export direction is delegated only for the clipboard route.**
`createTransferable` and `exportDone` are `protected` (`TransferHandler.java:1029`,
`BasicTextUI.java:2509`), so they cannot be called on the inner handler and are not
overridden — yet the drag machinery reaches them on the **outer** object:
`dragGestureRecognized` does `TransferHandler th = c.getTransferHandler(); th.createTransferable(c)`
(`TransferHandler.java:1599-1601`) and `dragDropEnd` does
`c.getTransferHandler().exportDone(...)` (`:1648-1650`). So a drag *out* of a wrapped field
would produce nothing. It is dormant — `JTextComponent`'s `dragEnabled` is false unless a
caller turns it on, and nothing in jEdit turns it on for these fields — and it is left
dormant rather than repaired. (An earlier draft said repairing it would mean reimplementing
Swing's text export. That is wrong: delegating `exportToClipboard` into a scratch
`java.awt.datatransfer.Clipboard` captures what the inner handler produces, since
`exportToClipboard` writes to whatever `Clipboard` it is handed. Cheap enough if the case
ever stops being dormant.)

**Copying *out* of a wrapped field yields the raw glyph**, because the export methods are
delegated whole and nothing expands on the way out. These are input boxes and copying out of
one into another application is rare; the asymmetry is accepted and belongs in
`WORD_GLYPHS.md` rather than being left to be discovered.

### Finding the fields

They are created lazily, inside dialogs jEdit constructs on demand, and no message announces
them. The hook is a global AWT event listener on container events:

```
phi_awt_listener = new java.awt.event.AWTEventListener() {
    public void eventDispatched(java.awt.AWTEvent e) {
        try {
            if (e.getID() != java.awt.event.ContainerEvent.COMPONENT_ADDED) return;
            phi_child = e.getChild();
            if (phi_child instanceof HistoryTextArea || phi_child instanceof HistoryTextField)
                phi_wrap_field(phi_child);
        } catch (Throwable ex) { }
    }
};
java.awt.Toolkit.getDefaultToolkit().addAWTEventListener(phi_awt_listener, java.awt.AWTEvent.CONTAINER_EVENT_MASK);
```

`phi_wrap_field` is idempotent — it returns immediately if the field's handler is already one
of ours — so a component added twice, or re-parented, is harmless. **Measured**: the listener
sees the dialog's fields even though each arrives inside a `new JScrollPane(find)`, because
the `COMPONENT_ADDED` event for the field itself comes from the scroll pane's viewport.

**The `try`/`catch` is required but is not sufficient, and the plan says so.** A BeanShell
script-level error is an `EvalError` that neither `catch (Exception)` nor `catch (Throwable)`
intercepts inside bsh — **measured**: with a listener whose body raises one, the error escapes
both guards and comes out of `java.awt.Container.add()` as an
`UndeclaredThrowableException`. Since the listener runs on **every** container event in the
application, that would break arbitrary UI construction. A realistic trigger exists: jEdit
calls `BeanShell.resetClassManager()` from `PluginJAR.uninit`, so removing a plugin can
invalidate a scripted class. The mitigations are to keep the listener body as small as
possible — an `instanceof` test and a call — and to have the automated test load the whole
script, which is what catches an unbound name or an unresolved method.

### What the instanceof test catches — deliberately, everything

`instanceof HistoryTextField` matches every subclass, and there are more than the search
widgets. In this tree: `browser/VFSFileNameField.java:44`, `browser/VFSBrowser.java:221`'s
`pathField` and `:2077`'s `HistoryComboBoxEditor`, `gui/ActionBar.java`'s action input, and
the help viewer's search field, besides
`Completion_Popup.History_Text_Field` (`src/completion_popup.scala:396-401`), which backs
Isabelle's Query and Debugger panels (`query_dockable.scala:40,91,148`,
`debugger_dockable.scala:190,207`) and the search box of `Pretty_Text_Area`
(`pretty_text_area.scala:275`). Isabelle's Sledgehammer provers field
(`sledgehammer_dockable.scala:70`) is a plain `HistoryTextField`, not the completion
subclass — the `instanceof` still catches it.

**Wrapping all of them is the intended scope**, decided deliberately. Folding only ever
touches mathematical letters, so an ordinary file path or action name pasted into any of
these boxes is untouched; and a user who pastes a phi-System word into any input field
plausibly wants the glyph. The alternative — filtering by field name or by enclosing dialog —
would be narrower but would miss Isabelle's panels and would add a second thing to keep
correct.


## Measured

```
1. wrap by hand, then paste
   pasted: U+E048            matches the buffer? true
2. does the other direction still work (copy out of the field)?
   copied out of the field: U+E048
3. ordinary text is untouched
   pasted: int foo = 1;
4. auto-install through the global AWT container listener
   auto-wrapped? true        pasted: U+E048   matches the buffer? true
```


## Risks

- **Fold, not expand, is what an input box wants.** Folding letters to glyphs makes a pasted
  search string match the buffer. It also means a user who genuinely wants to search for
  literal mathematical letters cannot paste them in — the same trade the paste direction
  already makes everywhere else, with the same escape hatch: a run containing a mathematical
  letter no word claims is abandoned untouched. Preferring the rich flavor removes the
  question entirely for anything copied inside jEdit.
- **The listener stays for the life of the session.** Registered once at startup, never
  removed; `removeAWTEventListener` is available if that ever needs to change.
- **A field created before the listener is registered would be missed.** Startup scripts run
  at `jEdit.java:553` and `:568`, and `finishStartup` — which creates the first view — at
  `:612`, so no view-borne field can predate the listener. The guarantee also rests on no
  startup-activated plugin building a history field in `start()`: those plugins are activated
  at `jEdit.java:528-531`, before the startup scripts run.
- **Adjacent glyphs and the shapes `WORD_BOUNDARY_PLAN.md` cannot repair** reach this path
  only for text that came from outside jEdit; anything copied inside it arrives on the rich
  flavor and is exact.


## What is NOT verified

Nothing has been done in a running jEdit. Four checks by hand:

1. **Copy a word glyph out of a buffer, open Search and Replace (Ctrl-F), paste into the Find
   box, and search.** Expect the glyph in the box and a match in the buffer. Do the same with
   the quick-search bar, and once into the **Replace** box, which the same test wraps.
2. **Paste a word glyph into Isabelle's Query panel input.** This is the plan's main scope
   claim — that Isabelle's own fields come along for free — and it is otherwise untested.
3. **Paste ordinary text** into the Find box, and a real directory path into the file browser's
   filename box and the dialog's directory box; expect them untouched and still working.
4. **Type into a search box normally**, recall history with the up arrow, and let Isabelle's
   completion popup appear. The wrapper touches only paste and drop, but these fields carry
   that popup and it is worth one look.


## Procedure

1. **Extend `phi_word_clipboard.bsh`** with `Phi_Field_Transfer_Handler`, `phi_wrap_field`
   and the AWT listener, installed from `phi_word_install` after the `n == 0` guard. About 35
   lines, no new text-transformation logic. Prefix every new bare name, method locals
   included.
   **Imports the bare test harness needs**: `org.gjt.sp.jedit.gui.HistoryTextField`,
   `org.gjt.sp.jedit.gui.HistoryTextArea` and `java.awt.datatransfer.Clipboard`; and write
   the nested type as `javax.swing.TransferHandler.TransferSupport`, because bsh's default
   `javax.swing` import does not bring nested names in — **measured**, the bare name makes the
   wrapper fail at **construction**, not at load, with
   `InterpreterError: Class: TransferSupport not found in namespace`. A running jEdit imports
   `org.gjt.sp.jedit.gui` itself (`BeanShell.java:501`), so as with the sibling plans these
   exist for the harness.
2. **Extend `test_word_clipboard.bsh`** to cover:
   - a wrapped `HistoryTextArea` takes the rich flavor when present and reproduces the
     original exactly, including a shape the fold cannot repair;
   - with no rich flavor, it folds a pasted string of letters to glyphs;
   - it leaves ordinary text alone, and a transferable that throws;
   - it forwards `canImport`, `getSourceActions` and `exportToClipboard` to the inner handler;
   - `phi_wrap_field` is idempotent, including on a re-parented field;
   - the listener wraps a `HistoryTextField` added to a panel and a `HistoryTextArea` added
     inside a `JScrollPane`;
   - the whole script still loads, and the existing round trip still passes.
   The suite runs under `xvfb-run`; `WORD_BOUNDARY_PLAN.md` makes that explicit.
3. **Ask the user to run the four manual checks.**
4. **Update `../fonts/WORD_GLYPHS.md`** by striking one line — the input-field-paste entry's
   "covered by a plan not yet landed" marker, in the list `WORD_BOUNDARY_PLAN.md` rewrote —
   and by filling in the one-way asymmetry that list holds a place for: copying *out* of a
   wrapped field still yields the raw glyph, described under "What the delegation does not
   cover, and why that is accepted" above. Do **not** write the step as "remove it from the
   list": before plan 1 lands there is no such entry.


## Constraints on whoever implements this

- **Never run `isabelle build`**, in any session, with any flags.
- Never run `git clean`, `git stash`, `git checkout`, or `git reset --hard`. Shared tree.
- Do not modify anything under `contrib/Isabelle2025-2/`, `ICSE27/` or `ICSE27-x/`.
- Do not test against the live X11 display; use `xvfb-run`.
- `contrib/phi-system` is its own git repository; commit there and bump the super-repo.
