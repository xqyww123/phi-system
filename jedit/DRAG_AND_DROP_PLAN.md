# Making drag and drop fold word glyphs, as copy and paste already do

Read `WORD_CLIPBOARD_PLANS.md` beside this file first: it carries the implementation
order, the decisions the user has settled, the conventions all four plans follow, and what
has already been reviewed.

A work plan, the **fourth and last** of four. `WORD_BOUNDARY_PLAN.md` goes in first and
rewrites the two text functions this one reuses; `PRIMARY_SELECTION_PLAN.md` and
`SEARCH_FIELD_PASTE_PLAN.md` are the other two. Read `../fonts/WORD_GLYPHS.md` first — it
defines the feature all four extend.

**What changed after this plan was reviewed.** `WORD_BOUNDARY_PLAN.md` was written later and
repairs the 51 adjacent-glyph sequences described under "Correction 2" below. Three
consequences, and only three. The two-slot memory is **still justified**: it rests on the
other mechanism, a glyph written against mathematical letters no word claims. That plan
widens what counts as one run — the whole mathematical alphanumeric block rather than the
letters the table happens to use — which changes *which* letters take a glyph down with
them, but not that they do; so Correction 2 needs no rewrite. Second, manual checks 1 and 2
used `\<has>\<has>`, which round-trips on its own once that plan lands and would therefore
pass even with the memory disabled; they now use a shape that still discriminates. Third,
two pieces of work this plan used to carry moved into that one: the hoist of the table to a
top-level `phi_t`, and the correction of the wrong comment at `phi_word_clipboard.bsh:158-159`.
Do neither of them here. Nothing else depends on it: the joiner that plan introduces is
stripped inside `phi_word_fold` itself, so `phi_unexpand` needs no extra call.

Everything cited below was read from **Java source**, which ships in full inside the
Isabelle component (not only as a jar):

    contrib/Isabelle2025-2/contrib/jedit-20251128/jedit5.7.0-patched/jEdit/

Line numbers are against that tree, and against JDK 21's `src.zip` for the `javax.swing`
claims. The shipped `jedit.jar` was checked against that tree with `javap`: the members of
`TextAreaTransferHandler` in the jar match the source file exactly, so the line numbers
describe the code that actually runs.

**Convention used throughout.** A claim marked *measured* was produced by running code —
jEdit's own repackaged BeanShell out of `jedit.jar`, the way `run_word_clipboard_test.sh`
does, sometimes under `xvfb-run` for a real X11 clipboard. Everything else was read.
Nothing here rests on recollection of how jEdit "usually" behaves.

**Earlier drafts of this plan got several claims wrong.** They are called out where they
appear, because a reader who absorbed one will otherwise carry it forward: that `super`
can be called on a protected method from BeanShell; that expansion and folding are exact
inverses; that text dropped in from another application is reliably ignored by jEdit; that
`phi_unexpand` being total makes the overrides total; and that BeanShell cannot parse an
anonymous class body written as a call argument.


## The problem, in one paragraph

phi-System declares 135 Isabelle symbols whose code points lie in the Unicode Private Use
Area, U+E000..U+E086; each draws a whole keyword as one wide glyph, so `\<transforms>`
renders as the word. A private-use code point means only what the drawing font says, so
handing one to another application yields a blank box. `phi_word_clipboard.bsh` already
fixes the **copy** direction (a copied word becomes mathematical letters) and the
**paste** direction (those letters fold back to the glyph). Drag and drop is fixed by
neither.


## What is broken, verified

**Dragging out of a buffer carries the raw code point.**
`textarea/TextAreaTransferHandler.java:73-85` — `createTransferable` returns
`new TextAreaSelection(textArea)`, and `TextAreaSelection` (same file, `:475-484`) is a
bare `StringSelection` over `textArea.getSelectedText()`. Nothing in the class body
mentions `Registers` or `org.gjt.sp.jedit.datatransfer.TransferHandler`, so the service
list that the copy fix hooks is never consulted. (The class does import
`org.gjt.sp.jedit.*` at `:26`, which brings `Registers` into scope — it simply never uses
it. An earlier draft claimed the import was absent; that was wrong, and the conclusion
does not depend on it.)

**Dragging from one buffer text area into another one, inside jEdit, is equally
unreached.** `importData` → `importText` reads `DataFlavor.stringFlavor` directly
(`:265-269`), never `Registers`, so the mathematical letters our drag now produces would
be inserted verbatim into the destination pane. The same holds for the same-text-area
branch of `exportDone` (`:381-399`).

**The gap is narrower than "dragging out of jEdit".** Only the main buffer text area has
a transfer handler at all: `EditPane.java:814` is the sole call that installs one on a
text area (the other `setTransferHandler` call sites in the tree are the HyperSearch
result tree, `PingPongList` and `BufferSwitcher`). `StandaloneTextArea.java:121` has the
call commented out, and `JEditEmbeddedTextArea` never makes it — which matters because
Isabelle's Output, State and Query panels are `Pretty_Text_Area extends
JEditEmbeddedTextArea` (`contrib/Isabelle2025-2/src/Tools/jEdit/src/pretty_text_area.scala:110-114`).
`TextArea.startDragAndDrop` (`TextArea.java:5202-5212`) no-ops when `getTransferHandler()`
is null, so you cannot drag out of those panels in the first place.

This plan covers **drag and drop in buffer text areas**. Four further problems with word
glyphs at jEdit's edge are outside it — two other routes that carry raw private-use code
points out (the X11 primary selection and HyperSearch's "copy results"), one gap on the way
*in* (pasting into jEdit's own search fields), and one defect in the already-shipped copy
and paste directions. All four are listed under "What this plan does not cover" at the end. Do not write into
`WORD_GLYPHS.md` that only buffer text areas ever had the problem — that sentence would be
false.


## A jEdit defect this plan must work around: `dragSource` goes stale

`TextAreaTransferHandler` keeps `private static JEditTextArea dragSource` (`:53`), set in
`createTransferable` (`:82`) and cleared at `:418`. Those are the only two writes in the
file. `:418` is the last statement of `exportDone` — and it sits **after** the
`try`/`finally`, while `exportDone` begins

```java
try {
    if (action == NONE) { Log.log(Log.DEBUG,this,"Export impossible"); return; }   // :366-370
    ...
}
finally { if (compoundEdit) { ... } }                                              // :409-416
dragSource = null;                                                                 // :418
```

so the early `return` skips the clearing. `action == NONE` is an ordinary outcome, not an
exotic one: JDK `javax/swing/TransferHandler.java:1650` passes `NONE` whenever
`dsde.getDropSuccess()` is false — Escape pressed mid-drag, a rejecting target, a drop
outside any window — `:1618` passes it when `startDrag` throws, and jEdit's own comment at
`:365` names a third case, `importData` returning false, which `importText:319-322` does
when the user drops back into the selection they started from.

**Measured**, on real `JEditTextArea`s with the private statics read by reflection:
after `exportDone(NONE)` the field is still non-null, where after `exportDone(COPY)` it is
null. So one aborted drag arms the condition for the rest of the session, and then:

* text dropped in from another application into a **different** text area really is
  inserted (measured: the seven mathematical letters appeared in the buffer);
* text dropped into the **stale** text area's own buffer sets `sameTextArea` at `:311`,
  takes the `insertPos`/`insertOffset` branch at `:332-342`, inserts nothing, and returns
  `true` — the text vanishes (measured);
* the compound edit leaks on a **wider** condition than that, because the two tests use
  different identities: `:302-304` opens `beginCompoundEdit()` when
  `textArea.getBuffer() == dragSource.getBuffer()` — **buffer** identity — while `:311`
  sets `sameTextArea` on **text area** identity. So a foreign drop into a split view
  showing the same buffer both inserts the text *and* leaves the buffer inside a compound
  edit that no `exportDone` will ever close, since no `exportDone` runs for a drag that
  started in another application (measured on two text areas sharing one `JEditBuffer`);
* `canImport(TransferSupport)` at `:431-440` returns `true` before reaching
  `support.setDropAction(COPY)` at `:437`, so an external MOVE stays a MOVE and the source
  application may delete its own copy.

**We do not repair this.** Clearing `dragSource` would mean writing jEdit's private static
from the script, which is possible but means carrying a patch to upstream state inside
phi-System for a defect that has nothing to do with word glyphs. That is out of scope.
The list above is what was found, not a proof that nothing else follows; what it means for
this plan is:

1. The folding branch of `phi_unexpand` (below) is **not** dead code. It fires whenever a
   foreign drop reaches `importText`'s insertion path, and **measured**, it folds
   correctly. Do not comment it as dormant.
2. Manual check 6 observes what happens; neither outcome is evidence about this work.
3. Nothing in this plan may claim that a foreign text drop is a no-op.


## Why the existing fix does not reach any of this

Copy goes: selection → `Registers.copy` (`Registers.java:80-90`) →
`datatransfer.TransferHandler.getInstance().getTransferable(...)` → that singleton's
**service list** (`datatransfer/TransferHandler.java:53-77`), in which later services
overwrite earlier ones per flavor. `jEdit.java:534-539` registers the built-in services,
`jEdit.java:546-578` then runs startup scripts, and only afterwards does
`jEdit.java:612` call `finishStartup`, which creates the first view — so
`phi_word_clipboard.bsh:160-166` lands last and claims `stringFlavor`.

Paste is separate and has no service list: `Registers.paste` reads `reg.getTransferable()`
(`Registers.java:244`) and prefers jEdit's rich-text flavor, which is why the existing fix
wraps register `$` (`phi_word_clipboard.bsh:168-185`) instead of registering a service.

Drag goes: mouse gesture → `TextAreaMouseHandler.java:308` → `TextArea.startDragAndDrop`
→ `javax.swing.TransferHandler.exportAsDrag` → the drag gesture handler, which calls
`createTransferable` at `TransferHandler.java:1601` → `StringSelection`. The three paths
share nothing.


## What Isabelle occupies, and what it leaves alone

Isabelle's `src/Tools/jEdit/patches/main` *adds* the factory indirection that `EditPane`
uses, and `src/Tools/jEdit/jedit_base/services.xml` fills `textarea-factory`,
`view-factory`, `editpane-factory`, `mouse-handler-factory` and `painter-factory`. It does
**not** touch transfer, drag or drop — the `setTransferHandler` line in that patch hunk
(`patches/main:1225`) is unchanged context. Isabelle's own clipboard contact is
`Registers.copy` (`pretty_text_area.scala:350`) and `Registers.cut`/`Registers.paste`
(`jedit_accessible.scala:239,245`); the first two route through the service list, the
paste through the register `$` wrapper. Both mechanisms are already installed.

**Do not claim `textarea-factory` or any of those other service names.** Taking
`textarea-factory` would also drop Isabelle's screen-reader support.

**Isabelle does gate the drag gesture, though**, and a tester needs to know it.
`jedit_base/services.xml` fills `mouse-handler-factory` with
`isabelle.jedit.JEdit_Mouse_Handler$Factory`, and `src/jedit_mouse_handler.scala:60-62` is

```scala
override def mouseDragged(evt: MouseEvent): Unit = {
  if (active_buffer == edit_pane.getBuffer && !after_jump) super.mouseDragged(evt)
}
```

`super.mouseDragged` is the only route to `startDragAndDrop` (`TextAreaMouseHandler.java:308`),
and `after_jump` is set by a hyperlink jump and cleared on a delay. So for a short window
after every Ctrl-click navigation — which is how one moves around Isabelle sources — a drag
simply does not start. "I dragged and nothing happened" is not evidence that this work is
broken.


## The mechanism

Subclass `TextAreaTransferHandler` in BeanShell and install it per EditPane through the
public setter `TextArea.setTransferHandler` (`TextArea.java:204`).

### What BeanShell can do here, measured

`phi_word_clipboard.bsh:158-159` records bsh's limits with anonymous class bodies, so this
was the real unknown. Running jEdit's repackaged interpreter headlessly, all of the
following were observed:

* `class X extends TextAreaTransferHandler` instantiates; `instanceof` holds for both
  `TextAreaTransferHandler` and `javax.swing.TransferHandler`; reflection on the generated
  class shows genuine declared overrides with exact signatures;
* `((javax.swing.TransferHandler) h).exportToClipboard(new JPanel(), clip, COPY)` — JDK
  code inside `javax.swing`, the same code the drag path reaches at
  `TransferHandler.java:1601` — dispatched to the scripted `createTransferable`, and the
  scripted string arrived on the clipboard;
* the same with construction deferred to another thread after the script's top level had
  finished, which is the shape the real installation has;
* a method of the scripted class can call a method defined at the script's top level —
  this is what lets the overrides reuse `phi_word_expand` and `phi_word_fold`;
* a method of the scripted class can read a top-level variable holding a
  `java.util.HashMap` and mutate it in place, and the mutation is visible to a **different
  instance** of the same scripted class, which is what the shared drag state below needs;
* an anonymous `java.awt.datatransfer.Transferable` written in bsh is accepted by Java
  code calling `getTransferDataFlavors`, `isDataFlavorSupported` and `getTransferData`,
  and it keeps `javaFileListFlavor` and a `text/uri-list` flavor while rewriting only the
  string;
* an anonymous bsh class implementing `EBComponent` satisfies `instanceof EBComponent` and
  receives `handleMessage`.

### Correction 1: the three overrides must be declared `public`, not `protected`

An earlier draft wrote them with the superclass's own modifiers — `protected
createTransferable`, `protected exportDone` — and claimed `super.<method>` works.
**Measured, it does not:**

* `super.canImport(...)`, **public** in `TextAreaTransferHandler`, resolves and runs;
* `super.createTransferable(...)` and `super.exportDone(...)`, **protected**, fail with
  `Method createTransferable( ... ) not found in class
  'org.gjt.sp.jedit.textarea.TextAreaTransferHandler'`.

bsh resolves `super.foo()` by a public-method lookup on the superclass, and the usual
escape hatch is shut by construction: `Capabilities.setAccessibility(true)` throws
`Unavailable` unconditionally (`org/gjt/sp/jedit/bsh/Capabilities.java:78-84`) — it is not
a flag that can be turned on.

Declaring the overrides `public` fixes it. Java permits widening access when overriding;
the JVM still dispatches to the override (**measured**: a `public`-declared
`createTransferable` was the one `exportToClipboard` called, identified by its return
value); and bsh then emits its `_bshSuper…` bridge as public, so both `super` calls
resolve and reach the superclass body (**measured** by the `ClassCastException` a `JPanel`
argument must produce there).

This is invisible until the first drag, so the code carries a comment saying why, and the
automated test asserts the declared modifiers.

### Correction 2: expansion and folding are not exact inverses, in two different ways

An earlier draft claimed they are and concluded that no bookkeeping was needed. They are
not, and the reason is not one mechanism but two. Both were **measured** against the
committed table by running the script's own functions.

**Mechanism one: a glyph against mathematical letters that no word claims.**

```
in    U+E048  U+1D433 U+1D433 U+1D433                        the `pending` glyph, then bold zzz
out   U+1D429 U+1D41E U+1D427 U+1D41D U+1D422 U+1D427 U+1D420 U+1D433 U+1D433 U+1D433
```

`phi_word_expand` turns the glyph into its seven letters, which then sit against the three
that were already there; `phi_word_fold` reads that as one run, finds a mathematical letter
no word claims, and abandons the whole run (`phi_word_clipboard.bsh:113-115` — the rule
`WORD_GLYPHS.md` describes under "What the paste direction folds"). The glyph does not
come back.

**Mechanism two: adjacent glyphs whose letters re-segment differently.** No unclaimed
letter is involved here at all; the concatenation of two perfectly ordinary words is
re-read by the longest-match-first scan as a different parse. This class is **finite and
fully enumerated**: exactly **51 sequences** fail, 49 of two glyphs and 2 of three. Only 13
of the 135 words can begin one — precisely those that are a proper prefix of another word
(`in`, `change`, `get`, `has`, `no`, `or`, `prem`, `ref`, `ret`, `size`, `subj`, `val`,
`var`) — and no failure can span more than three glyphs, because the longest overshooting
tail is 5 letters, the shortest word is 2, and neither `ia` nor `it` (the first two letters
of the only 5-letter tails) is a word. The enumeration was cross-checked three ways: the
real BeanShell run over all 18225 ordered pairs, a validated Python port agreeing on every
one of them and on a checksum of all outputs, and a 236925-triple brute force. Two flavours
of outcome:

```
\<has>\<has>    U+E024 U+E024  ->  hashas  ->  U+1D421 U+1D41A U+1D42C U+1D421 U+1D41A U+1D42C
                                   `hash` matches first, `as` is claimed by no word,
                                   so the whole run is abandoned: two glyphs become six letters

\<or'>\<else>   U+E041 U+E01A  ->  orelse  ->  U+E042
                                   `orelse` is itself a word (0x00E042), so two symbols
                                   silently become one *different* symbol
```

**The second flavour has exactly one instance in the whole table**: `\<or'>\<else>`. Every
one of the other 50 sequences takes the first flavour and comes back as mathematical
letters. `WORD_BOUNDARY_PLAN.md` calls the second flavour the **clean-but-wrong** kind and
the first the **visible** kind; this one is the clean-but-wrong one, because it does not
merely fail to fold — it changes what the text says.

**None of the 51 occurs in phi-System's sources today.** Scanning all 352 `.thy` and `.ML`
files: 14719 word symbols, and **zero** places where two of them are written with nothing
at all between them. Every failing sequence requires exactly that, so the defect is real
but currently unreached by the sources themselves.

Copy and paste inside jEdit never hit either mechanism, because jEdit prefers its own
rich-text flavor for an internal paste and the script leaves that flavor alone. Drag has no
such flavor, and a **move** drag deletes the source text before re-inserting, so an inexact
round trip would not merely fail to fold — it would rewrite the user's buffer. Hence the
shared drag state, which sidesteps both mechanisms by never folding a string it produced
itself.

**A consequence outside this plan's scope, recorded because it was found here.** Mechanism
two also defeats the promise `WORD_GLYPHS.md` makes for the shipped copy direction, that
"a round trip through another application loses nothing": copying `\<or'>\<else>` to
another application and pasting it back yields `\<orelse>`. That is a defect in the
existing feature, not something this work introduces, and it is not fixed here. It needs
its own decision — see "What this plan does not cover".

### The shared drag state

`TextAreaTransferHandler` keeps `dragSource`, `sameTextArea`, `insertPos` and
`insertOffset` as `private static` fields (`:53-57`) — one set for the whole application.
It has to: a drag started in one EditPane is completed by the other EditPane's handler
instance, `importData` runs on the destination's handler and `exportDone` on the source's.
Our state must be shared the same way.

In BeanShell, a method assigning to a bare name walks the namespace chain and writes
through to an existing binding; it creates a local **only when no binding is found**
(**measured** both ways — an earlier draft stated the flat rule "a top-level variable
cannot be written to from inside the class", which is wrong). Rather than depend on that,
use a single top-level `java.util.HashMap` that is only ever **mutated in place**:

```
phi_drag = new java.util.HashMap();      // slots "original" and "expanded"
```

**That same rule makes every bare name inside the new methods a hazard, not only the
top-level ones.** Startup scripts share one global namespace (see "Hoisting the table"),
so a method-local `s = ...` overwrites a global `s` that some other macro left behind.
**Measured**: after one call to a `phi_unexpand` written with bare locals, the globals `s`
and `out` held the values the method had assigned, while a name with no global binding
stayed local. Every new bare name therefore carries the `phi_` prefix too — `phi_s`,
`phi_out`, `phi_t0`, `phi_original`, `phi_expanded`, `phi_fl`, `phi_w`, `phi_bus_listener` —
and the code below is written that way.

**`phi_drag` is emptied at both ends of a drag**: `exportDone` clears it in a `finally`,
and `createTransferable` clears it as its **first** statement. Clearing at only one end
would not be enough, because a caller can skip `exportDone` entirely: JDK
`javax/swing/TransferHandler.java:783-796` calls `createTransferable`, then
`clip.setContents(t, null)`, and reaches `exportDone` only on success or on an
`IllegalStateException` — any other `RuntimeException` out of `setContents` propagates and
skips it (**measured** with a `Clipboard` that throws `IllegalArgumentException`: the slots
were left populated). Clearing on entry makes the exact-match rule below safe against a
slot left over from any earlier drag, whatever happened to it.

The rule the two slots implement:

> When the string arriving at `importData` or `exportDone` is character-for-character the
> string `createTransferable` handed out, put back the original text it was expanded from,
> instead of folding. Fold only strings we did not produce.

With it, an intra-jEdit drag preserves the glyphs for every input, including the case
above. It does **not** make such a drag byte-for-byte lossless, for a reason outside our
control — see "Risks".

### The three overrides

```
class Phi_Text_Area_Transfer_Handler extends TextAreaTransferHandler {

    // public, NOT protected: bsh resolves super.<method> by a public-method lookup and
    // jEdit's bsh cannot enable accessibility.  protected here installs fine and then
    // fails at the first drag.
    public Transferable createTransferable(JComponent c) {
        phi_drag.clear();                        // a previous drag may have skipped exportDone
        phi_t0 = super.createTransferable(c);    // also sets super's private dragSource
        if (phi_t0 == null) return null;
        try {
            phi_original = phi_t0.getTransferData(DataFlavor.stringFlavor);
            if (phi_original != null) {
                phi_expanded = phi_word_expand(phi_t, phi_original);
                phi_drag.put("original", phi_original);
                phi_drag.put("expanded", phi_expanded);
                return new StringSelection(phi_expanded);
            }
        }
        catch (Exception e) { }                  // degrade to jEdit's own transferable
        return phi_t0;
    }

    public boolean importData(JComponent c, Transferable t) {
        try { return super.importData(c, phi_unexpand(t)); }
        catch (Exception e) { Log.log(Log.ERROR, this, e); return false; }
    }

    public void exportDone(JComponent c, Transferable t, int action) {
        try { super.exportDone(c, phi_unexpand(t), action); }
        catch (Exception e) { Log.log(Log.ERROR, this, e); }
        finally { phi_drag.clear(); }
    }
}
```

`createTransferable` must call `super` before building anything of its own: the superclass
sets `dragSource` there, and every branch of `importText` and `exportDone` keys off it. On
the failure path it returns `phi_t0`, so the drag carries glyphs — degraded but never
wrong, and `phi_drag` stays empty so no later match can fire.

**Each override carries its own `try`/`catch`, and that is not belt-and-braces.** Two
separate throw routes reach a Java caller that will not handle them:

* `super.importData` and `super.exportDone` can throw, and BeanShell **re-types** whatever
  comes out as `TargetError`, which extends `EvalError`, which extends
  `java.lang.Exception` — **checked**. The JDK's drop path catches only `RuntimeException`
  (`javax/swing/TransferHandler.java:1543-1547`, and it does not log), and `dragDropEnd` →
  `exportDone` (`:1644-1651`) catches nothing at all. **Measured** side by side through a
  Java caller shaped like the JDK's: the stock handler's `NullPointerException` was caught
  as a `RuntimeException`; ours escaped as a checked `TargetError`.
* BeanShell's **own interpreter errors** — an unbound variable, a method that does not
  resolve — are `EvalError`s that a bsh `catch (Exception e)` **and** a bsh
  `catch (Throwable e)` both fail to catch (**measured**: the plan's own `phi_unexpand`
  body run with `phi_t` left unbound, exactly the hoisting mistake documented below,
  escaped both). No script-level guard can stop these. They are caught instead by the
  automated test, which is why step 2 of the Procedure exercises every new function at
  load time.

An earlier draft said `phi_unexpand`'s totality meant "`importData` and `exportDone` need
no further guard of their own". That was wrong on both counts above.

`exportDone` needs the folding because its same-text-area branch re-inserts from
`stringFlavor` (`:390-392`); without it an intra-pane drag would deposit mathematical
letters. It is reached with the very transferable `createTransferable` produced (JDK
`TransferHandler.java:1648` reads `dsc.getTransferable()`, the object passed to
`startDrag`).

### `phi_unexpand`

```
phi_unexpand(t)
{
    try {
        if (t == null) return t;

        // jEdit dispatches on these two before it ever looks at text (:107-133): a file
        // dragged in from a file manager must still be opened.  Return before touching
        // stringFlavor -- fetching it here would force a blocking cross-process transfer
        // that jEdit would never have requested, on the AWT thread, for a string that is
        // then discarded.
        if (t.isDataFlavorSupported(DataFlavor.javaFileListFlavor)) return t;
        for (phi_fl : t.getTransferDataFlavors()) {      // restates isUriList (:422-427),
            if ("text".equals(phi_fl.getPrimaryType())   // which is private
                && "uri-list".equals(phi_fl.getSubType())
                && phi_fl.getRepresentationClass() == String.class) return t;
        }

        if (!t.isDataFlavorSupported(DataFlavor.stringFlavor)) return t;
        phi_s = t.getTransferData(DataFlavor.stringFlavor);
        if (phi_s == null) return t;                     // legal, if unusual

        phi_expanded = phi_drag.get("expanded");
        if (phi_expanded != null && phi_expanded.equals(phi_s))
             phi_out = phi_drag.get("original");
        else phi_out = phi_word_fold(phi_t, phi_s);      // a drag we did not start
        if (phi_out == null) phi_out = phi_s;

        // Always hand back a wrapper, even when nothing changed: we have already paid for
        // the string, and returning `t` would make jEdit fetch it a second time.
        return phi_delegating(t, phi_out);
    }
    catch (Exception e) { return t; }
}
```

**It swallows every Java exception**, which matters because
`Transferable.getTransferData` declares `UnsupportedFlavorException` and `IOException`, and
on X11 an `IOException` from a foreign drag source is routine. An uncaught one leaves
`compoundEdit` true and `dragSource` non-null where the stock handler leaves both clean
(**measured**). It does **not** make the overrides total — see the two throw routes listed
with the overrides above, which is why each of them has its own guard as well.

**Why the no-change case still returns a wrapper.** An earlier draft returned `t` unchanged
when there was nothing to fold. That doubles the number of times `stringFlavor` is fetched
on the commonest path of all — any ordinary text drop, and any intra-jEdit drag whose text
contains no glyph — because `phi_unexpand` has already read it and `importText:268-269`
then reads it again. **Measured** through `importText` on a real text area with a
counting `Transferable`: stock `stringFlavor` reads = 1, ours = 2. On X11 each read is a
blocking selection transfer on the AWT thread, so the wrapper is returned unconditionally
and the second read is served from memory.

The delegating wrapper. It is bound to a name before being returned, and the reason is
narrower than the comment at `phi_word_clipboard.bsh:158-159` currently claims. That
comment says bsh "cannot parse an anonymous class body written directly as an argument",
and that is false as a general rule — 85 lines earlier, `:73-75` of the same file passes
`new java.util.Comparator() { public int compare(a, b) {...} }` straight to
`Collections.sort`, and the shipped test exercises it. **Measured**: an anonymous class
body as a call argument parses when the methods inside declare primitive return types and
fails with `Parse error ... Encountered: (` when one declares a **reference** return type.
Every method of a `Transferable` returns a reference type, which is why this one has to be
bound first. **The existing comment is wrong, and `WORD_BOUNDARY_PLAN.md` corrects it** as part of its
own step 1 — not here (see Procedure step 1).

```
phi_delegating(inner, replacement)
{
    phi_w = new Transferable() {
        public DataFlavor[] getTransferDataFlavors() { return inner.getTransferDataFlavors(); }
        public boolean isDataFlavorSupported(DataFlavor f) { return inner.isDataFlavorSupported(f); }
        public Object getTransferData(DataFlavor f) {
            if (DataFlavor.stringFlavor.equals(f)) return replacement;
            return inner.getTransferData(f);
        }
    };
    return phi_w;
}
```

It must delegate rather than return a bare `StringSelection`: replacing the transferable
would strip every other flavor, and `importData`'s dispatch (`:107-133`) needs them.
Delegation plus the early returns above give two independent guards on the file-drop path;
an earlier draft had neither and asserted that none was needed.

### The table, and where it comes from

The overrides need the generated table. `WORD_BOUNDARY_PLAN.md`, which lands first, hoists
it to a top-level `phi_t`; this plan only consumes that name. The two hazards it had to
solve are recorded there and are repeated here only so that nobody re-does the work:

* **The assignment must sit at the script's top level.** Writing
  `phi_t = phi_word_table();` inside `phi_word_install()` leaves the top-level name unset
  (`void`): the script loads cleanly, the existing test still passes, and it fails at the
  first drag.
* **Declare every function-local with a type, and name no bare `t`.** The closures inside
  `phi_word_install` name the global `phi_t` directly; an earlier draft bound a local
  `t = phi_t;` because the closure bodies said `t`, and that local is gone. The typing
  matters more: in BeanShell an untyped assignment inside a method writes through to any
  global of that name, and two functions sharing an untyped local name clobber each other
  mid-call. `WORD_BOUNDARY_PLAN.md` records the measurement.

Startup scripts run with `ownNamespace = false` — `jEdit.java:4005` calls
`handler.runMacro(null, newMacro, false)` and `Macros.BeanShellHandler.runMacro`
(`Macros.java:1113-1116`) forwards it to `BeanShell.runScript` — i.e. in the interpreter's
global namespace. That is what lets a top-level `class` declaration, the top-level methods
and `phi_t` persist and find each other after the script returns. It also means these names
share a namespace with every other non-own-namespace macro and every BeanShell action
snippet. The `phi_` prefix covers that — but note it has to cover the **method-local** bare
names too, for the reason given under "The shared drag state"; the prefix is not just a
courtesy to other macros, it is what stops our methods writing through to their variables.

### The imports the new code needs — five of them, and only for the test harness

`phi_word_clipboard.bsh:31-38` imports nothing from `org.gjt.sp.jedit.textarea` or
`org.gjt.sp.jedit.msg`, and imports `Registers`, `TransferHandler` and `Log` by name rather
than by package. The new code needs all five of:

    import org.gjt.sp.jedit.textarea.TextAreaTransferHandler;
    import org.gjt.sp.jedit.EBComponent;
    import org.gjt.sp.jedit.EBMessage;
    import org.gjt.sp.jedit.EditBus;
    import org.gjt.sp.jedit.msg.EditPaneUpdate;

**Measured**: with only the first one added, the script still aborts at load with
`Unknown class: EBComponent`, and `test_word_clipboard.bsh` never runs because its
`source()` threw. With all five, the existing test prints `PASS: 135 entries round-tripped`.
`JComponent` needs no import; bsh default-imports `javax.swing.*`.

**None of these is needed in a running jEdit**, and the plan says so rather than leaving a
reader to wonder why working code carries redundant imports: `BeanShellFacade.init()`
(`BeanShellFacade.java:65-71`) does `importPackage` on `org.gjt.sp.jedit`,
`org.gjt.sp.jedit.buffer`, `org.gjt.sp.jedit.syntax`, `org.gjt.sp.jedit.textarea` and
`org.gjt.sp.util`, and `BeanShell.java:505` adds `org.gjt.sp.jedit.msg`. The imports exist
solely so the script also loads in the bare interpreter the test harness uses — which is
the whole point of that harness.

### Installation

Add an `EBComponent` to the EditBus (`EditBus.addToBus`, `EditBus.java:129`):

```
phi_bus_listener = new EBComponent() {
    public void handleMessage(EBMessage msg) {
        try {
            if (msg instanceof EditPaneUpdate
                && EditPaneUpdate.CREATED.equals(msg.getWhat()))
                msg.getEditPane().getTextArea()
                   .setTransferHandler(new Phi_Text_Area_Transfer_Handler());
        }
        catch (Exception e) { Log.log(Log.ERROR, this, e); }
    }
};
EditBus.addToBus(phi_bus_listener);
```

Points that are not decoration:

* **The `try`/`catch` is required, and what it protects is other people's subscribers.**
  An `EBComponent` is registered under `EBMessage.class` (`EditBus.java:417-418`), so
  `handleMessage` is called for every message on the bus; and `sendImpl`'s own `try` opens
  at `:260` and wraps the **whole handler loop** at `:262-282`, with the catches at
  `:284-295`. **Measured**: when one handler throws, a handler registered after it receives
  the message **zero** times. The subscribers behind us are real — jEdit's own
  `DockingLayoutManager` (`DockingLayoutManager.java:135`, registered from
  `jEdit.java:608`, i.e. after startup scripts have run) and Isabelle's symbols dockable
  (`symbols_dockable.scala:205`). Note what the guard does **not** buy: it cannot keep a
  pane from missing its handler, because if `setTransferHandler` itself throws, that pane
  keeps jEdit's stock handler whether we catch or not, and our component stays registered
  either way, so a later `CREATED` is unaffected.
* **Compare with `.equals`.** `EditPaneUpdate.CREATED` is declared `Object`
  (`msg/EditPaneUpdate.java:39`); its identity is not part of the contract.
* **Every EditPane comes through `View.createEditPane`** (`View.java:2066-2079`), which is
  the only place an `EditPane` is constructed — `View.java` has seven call sites covering
  the first pane, every split and every layout restore — and Isabelle's `editpane-factory`
  is consulted *inside* it, so Isabelle's own edit panes arrive here too.
* **`EditBus.send` delivers on the AWT thread** (`EditBus.java:200-212`), which is where
  `setTransferHandler` belongs.
* **Startup scripts run before any view exists** — `jEdit.java:546-578` runs them and only
  `jEdit.java:612` calls `finishStartup`, which creates the first view.
* **Register after the `n == 0` guard** (`phi_word_clipboard.bsh:153-156`). With no table
  there is nothing to expand or fold, and drag should stay at jEdit's stock behaviour.

### Calling `setTransferHandler` a second time is clean

`TextArea.setTransferHandler` (`TextArea.java:204-215`) calls `super.setTransferHandler`
and then adds a fresh `TextAreaDropHandler` to the component's drop target, catching
`TooManyListenersException`. Ours is the second call on that text area — `EditPane` made
the first — so the question is whether the listener accumulates. It does not: JDK 21
`JComponent.java:3299-3306` calls `SwingUtilities.installSwingDropTargetAsNecessary`
(`SwingUtilities.java:93-106`), which replaces the drop target outright whenever the
current one is null or a `UIResource`, and `TransferHandler.SwingDropTarget` is a
`UIResource` (`TransferHandler.java:1208`). The old drop target, with jEdit's listener on
it, is discarded whole. **Measured** on a real text area: the `SwingDropTarget` instance is
replaced on the second call and again on a third.


## Approaches that do not work, so they are not retried

- **Another `datatransfer` service**, like the existing fix uses. Drag never calls that
  singleton.
- **A plugin jar with `services.xml`.** Same reason; and phi-System ships no jar.
- **A `DropTargetListener` on the text area's drop target.** `SwingDropTarget.drop` calls
  `super.drop(e)` first — which runs `importData`, i.e. the text is already inserted — and
  multicasts to added listeners only afterwards (JDK `TransferHandler.java:1281-1291`,
  `:1219-1227`). jEdit's own `TextAreaDropHandler.drop` (`TextAreaDropHandler.java:94-100`)
  confirms the shape: it clears one field and inserts nothing.
- **jEdit properties.** The only relevant one, `view.dragAndDrop` (`EditPane.java:964`),
  merely disables drag.
- **`FlavorMap` / `SystemFlavorMap`.** They map flavors to natives; no content hook.
- **Compiling a small Java class instead of scripting one.** It removes the `super`
  restriction, but phi-System ships no jar and has no Java build step; adding one to avoid
  writing `public` three times is not a trade worth making.
- **Patching the Isabelle distribution.** It would work, and it is exactly what
  `WORD_GLYPHS.md` rules out for the hardcoded-letter-list problem, for the same reason:
  the distribution is not under version control here, so every person building phi-System
  would have to re-apply it.


## Risks

- **Ordinary text is untouched.** `phi_word_expand` copies through any code point not in
  the table, and `phi_word_fold` abandons a whole run of mathematical letters when one of
  them is unclaimed (`phi_word_clipboard.bsh:113-115`). Same rule and same limits as the
  paste direction.
- **A drag out of jEdit goes through `phi_word_expand` only**, so it inherits the copy
  direction's behaviour exactly, including the glyph-against-unclaimed-letters case: the
  letters are what leaves. That is the intended outcome for leaving jEdit.
- **An intra-jEdit drag preserves glyphs but is not byte-for-byte lossless, and the two
  intra-jEdit paths disagree with each other.** `importText:270` does `str = str.trim()`
  before every insertion it performs, while the same-text-area branch of `exportDone:390`
  does not. So a cross-pane drag of a selection with leading or trailing whitespace arrives
  trimmed, and a same-text-area drag of the same selection does not (**measured**, both
  ways). This is jEdit's behaviour, present with or without these overrides, and the
  two-slot state cannot fix it because the trim happens downstream of the restore.
- **Dropping a file into a buffer must keep opening the file.** This is the one existing
  behaviour these overrides could plausibly break. Two guards keep it: `phi_unexpand`
  returns before touching `stringFlavor` when a file-list or uri-list flavor is present,
  and the wrapper delegates rather than replaces. It is on the manual check list.
- **API stability.** This depends on the public `TextArea.setTransferHandler`, on
  `EditPaneUpdate.CREATED`, and on the three standard Swing extension points. The one
  behavioural assumption is that `importText` and `exportDone` keep reading `stringFlavor`.
  If a future jEdit rewrote them to use `Registers`, this fix would become redundant rather
  than broken. `TextAreaTransferHandler` has barely changed since 2013.
- **jEdit corrupts the source buffer on some outbound MOVE drags, with or without this
  work.** `sameTextArea` is a `private static` assigned in exactly one place,
  `importText:311`, and it is `false` at session start. On a drag that leaves jEdit,
  `importText` never runs, so `exportDone` reads whatever an earlier drop left there; if
  that was `true`, `exportDone:381-399` re-inserts the dragged text at a stale `insertPos`
  in the source buffer. Note that only the *deletion* of the source selection sits inside
  the `action == MOVE` test at `:383`; the `buffer.insert(insertPos,str)` at `:391` runs
  for any action that got past the `action == NONE` early return, so a plain **COPY** drop
  into another application corrupts the buffer too. **Measured**: the resulting buffer is
  byte-identical with the stock handler and with ours, so this plan neither causes nor
  worsens it — but a tester who sees it will blame this work, which is why the manual list
  puts a source-buffer inspection *after* an intra-jEdit drop has armed the condition.
- **`getSelectedText()` on a multiple or rectangular selection** joins the pieces with
  newlines and `exportDone` re-inserts them flat. Existing behaviour; expansion and folding
  are per-code-point and per-run and are indifferent to where the newlines are.


## What is NOT verified, and must be before this is called done

**No end-to-end drag has been performed in a running jEdit.** Everything above marked
*measured* was produced headlessly; the gesture itself was not, and cannot be — a real
`JEditTextArea` inside a `View` needs a running jEdit. Someone has to open an
Isabelle/jEdit session and work through the list below **in order** — the order matters,
for the reason given at check 3.

Two things to know before starting.

*If a drag will not start at all*, that is Isabelle's gate, not this work: see the note
under "What Isabelle occupies" about `jedit_mouse_handler.scala:60-62`. Click somewhere
neutral and try again.

*The test input.* Checks 1 and 2 need a selection that a plain fold would **not** restore,
because a selection whose expansion folds back cleanly would pass even if the two-slot state
never fired (**measured**). Type `<size>`, then an underscore, then `<then>`, giving
`\<size>_\<then'>` — two word glyphs with an underscore between them, all three typeable
from the keyboard. Expanded that reads `size_then`; the fold matches `size_t` (a word in its
own right, `\<size_t>`) and is then left with `hen`, which no word claims, so it abandons
the whole run. Without the two-slot state the two glyphs come back as **eight mathematical
letters and an underscore**, unmistakable on screen. `WORD_BOUNDARY_PLAN.md` deliberately
does not repair this shape — the underscore is a run-forming character its narrow insertion
rule does not mark — so this input keeps its discriminating power after that plan lands
(**measured**). Do **not** use `\<has>\<has>`, which that plan does repair.

1. **Drag `\<size>_\<then'>` within one text area**, dropping it **outside** the selection you
   started from. Dropping inside it makes `importText:319-322` return false and
   `exportDone` return at `:366-370`, so nothing happens at all and you cannot tell that
   from a broken fix. Expect the two glyphs back, unchanged.
2. **Split the view and drag `\<size>_\<then'>` from one pane to the other** — expect the two
   glyphs in the destination.
3. **Drag a word glyph out of a buffer into another application** — expect the word in
   mathematical letters there. Then look back at the **source buffer** and confirm nothing
   was spliced into it at an unrelated position. This must come *after* checks 1 and 2:
   the stale-`sameTextArea` defect described under Risks needs an earlier intra-jEdit drop
   to arm it, and `sameTextArea` is `false` at session start, so running this check first
   would prove nothing. If you do see a splice, it is jEdit's defect and not this work —
   the measurement showing it is byte-identical with the stock handler is in Risks.
4. **Drag ordinary text**, containing no word glyph and no mathematical letters, out of a
   buffer and within one — expect it untouched. The same stale-`sameTextArea` caveat as
   check 3 applies here.
5. **Drag a file from the desktop file manager onto a buffer** — expect jEdit to open it,
   exactly as before. This is the regression check for `phi_unexpand`'s early returns.

And one case to observe rather than pass:

6. **Drag mathematical letters in from another application.** What happens depends on
   whether any drag has been aborted earlier in the session — see "A jEdit defect this
   plan must work around". If nothing is inserted, that is jEdit's early return. If the
   letters are inserted as glyphs, that is our folding branch working. If the text vanishes
   into a stale text area, that is jEdit's defect. None of the three is evidence for or
   against this work; record which one happened.

Also worth one line in the activity log check: jEdit logs `TooManyListenersException` at
ERROR if the second `setTransferHandler` ever failed to replace the drop target. It is
ruled out by JDK source and by measurement, but it is cheap to glance at, and the symptom
if it were wrong is not cosmetic — `TextAreaDropHandler.dragOver` (`:60-77`) is what moves
the caret that `importText:313` reads, so every drop would land at the pre-drag caret.

That session is the user's to run. Do not report success without it.


## Procedure

1. **Extend `phi_word_clipboard.bsh`.** `WORD_BOUNDARY_PLAN.md` has already created the
   top-level `phi_t`, rewritten both text
   functions and corrected the comment at `:158-159`; do none of that again. Add the five
   imports; add the top-level
   `phi_drag` map, `phi_delegating` and `phi_unexpand`; add the
   `Phi_Text_Area_Transfer_Handler` class with three **public** overrides; add the
   `EBComponent` and register it from `phi_word_install`, after the `n == 0` guard.
   Every new bare name, including method locals, carries the `phi_` prefix.
   About 65 lines, and **no new text-transformation logic** — `phi_word_expand` and
   `phi_word_fold` are reused as they stand.

   **The comment at `phi_word_clipboard.bsh:158-159`** states a rule about BeanShell that is
   not true; `WORD_BOUNDARY_PLAN.md` corrects it as part of its own step 1, so leave it
   alone here. The measured rule is repeated below because this plan's wrapper depends on
   it. It reads "BeanShell cannot parse an anonymous
   class body written directly as an argument, so both of these are bound to a name first."
   The narrow, measured rule is in "The delegating wrapper" above: such a body parses as an
   argument, and fails only when a method inside it declares a reference return type — as
   `:73-75` of that same file demonstrates, passing a `Comparator` whose `compare` returns
   `int` straight to `Collections.sort`. Both objects at `:158-159` do declare reference
   return types, so the code is right and only the reason is wrong — which is why the
   rewrite of that comment belongs to `WORD_BOUNDARY_PLAN.md` and not to this step.

2. **Extend `run_word_clipboard_test.sh` / `test_word_clipboard.bsh`.**
   `WORD_GLYPHS.md` warns that the halves of this feature are generated apart and that
   nothing but this test makes them agree; that argument now covers a third half. What the
   test can reach without a running jEdit:
   - the class instantiates, `instanceof TextAreaTransferHandler` holds, and the three
     overrides are declared **public** with exact signatures — a direct guard against the
     `protected` mistake, which is otherwise invisible until the first drag;
   - `super.createTransferable` is reachable, checked by observing that it enters the
     superclass and throws the `ClassCastException` a non-`JEditTextArea` argument must
     produce there;
   - `phi_unexpand` restores the original when handed exactly what `createTransferable`
     would have produced, **including** the glyph-against-unclaimed-letters case;
   - `phi_unexpand` folds a string it did not produce, and yields the string unchanged
     when there is nothing to fold **while still returning a wrapper** — count the
     `getTransferData` calls and assert the string is fetched exactly once;
   - `phi_unexpand` returns the *same object* for `null`, for a transferable with no
     `stringFlavor`, and for one whose `stringFlavor` data is `null`;
   - `phi_unexpand` returns the transferable untouched when `javaFileListFlavor` or a
     `text/uri-list` flavor is present, **and does not fetch the string in that case** —
     the file-drop guard, testable with a transferable that records whether it was asked;
   - `phi_unexpand` does not propagate an exception from a transferable that throws;
   - `phi_drag` is empty after `exportDone`, empty again after a fresh
     `createTransferable` on an empty selection, and populated between the two on a real
     one;
   - **the whole script loads in the bare interpreter** — this is what catches an unbound
     name or an unresolved method, which no runtime guard can catch (see "`phi_unexpand`");
   - the existing round trip still passes.

   **A real `JEditTextArea` can be built headlessly, and the test should use one.** This
   lifts the automated coverage from "the helper functions behave" to "a drop through
   jEdit's own `importText` puts the right characters in a real buffer", which is most of
   what manual checks 1 and 2 do. The recipe, **measured**:

   ```
   ta = new JEditTextArea(null);
   ta.getPainter().setFont(new java.awt.Font("Monospaced", 0, 12));   // before setBuffer
   ta.getPainter().setStyles(new SyntaxStyle[Token.ID_COUNT]);        // before setBuffer
   ta.setBuffer(new JEditBuffer());
   ```

   Four things make the difference between this working and an afternoon lost, all of them
   hit while writing this plan:
   - the classpath needs the FlatLaf jar beside `jedit.jar`
     (`contrib/flatlaf-3.6.2/lib/flatlaf-3.6.2-no-natives.jar`), or the constructor fails
     with `NoClassDefFoundError: com/formdev/flatlaf/FlatLaf`;
   - the painter's font **and** styles must be set before `setBuffer`, or
     `TextAreaPainter.getLineHeight` throws on a null `FontMetrics` and the syntax chunker
     throws on null styles;
   - **do not call `StandaloneTextArea.createTextArea()`** to obtain styles. It needs a
     properties resource that is not in `jedit.jar`, and it re-registers jEdit's built-in
     datatransfer services, which would clobber the phi service in the same interpreter.
     A bare `new SyntaxStyle[Token.ID_COUNT]` is enough;
   - `exportDone`, `createTransferable` and `importText` are `protected` or `private` on
     `TextAreaTransferHandler`, so the test reaches them by reflection with
     `setAccessible(true)` — the same way it reads `dragSource` to set up a stale-state
     case.

   With that, the test can also cover: a same-text-area MOVE of `\<size>_\<then'>` coming back
   unchanged; a cross-text-area drop landing glyphs; and the `stringFlavor` fetch count
   through `importText` being 1, not 2.

3. **Ask the user to run the six manual checks.**

4. **Update `../fonts/WORD_GLYPHS.md` — one line struck, nothing rewritten.**
   `WORD_BOUNDARY_PLAN.md` step 6 has already rewritten the paragraph that used to open
   "Two places this does not reach." into a list that is correct once all four plans have
   landed, with four entries — drag and drop, the X11 primary selection, input-field paste,
   and the copy-out asymmetry plan 3 introduces — each marked as **covered by a plan not yet
   landed**. By the time this plan lands the other three markers are already struck, so
   there is exactly one edit here: **strike the drag-and-drop line's
   "not yet landed" marker** — the line itself stays, as a statement of what now works —
   and do not touch the other entries. In particular do not re-add the primary selection or
   input-field paste as unreached: plans 2 and 3 landed before this one and struck them.

   Leave the following paragraph alone as well. It begins "Outside jEdit,
   `Isabelle_RPC_Host.unicode` keeps a private-use symbol as its `\<name>` escape" and says
   at `:112-113` that a raw private-use character "that came out of a drag can be repaired"
   by its reverse direction. `WORD_BOUNDARY_PLAN.md` step 6 re-aims that clause once, in a
   wording that stays true before, between and after all four plans, so there is nothing to
   do to it here — and in particular do not re-aim it at the X11 primary selection, which by
   the time this plan lands no longer produces such characters either.

**Gotcha found while probing:** in jEdit's repackaged BeanShell, calling `print()` on a
`getClass()` result throws `Class: bsh.ClassIdentifier not found`. Use `System.out.println`.


## What this plan does not cover

Four problems remain, none of them drag and drop in a buffer text area. Three now have
plans of their own; only HyperSearch's "copy results" has none. Items 1 and 4 are routes
that hand raw private-use code points out of jEdit; item 2 is the reverse, a paste *into*
jEdit that arrives as letters and never folds; item 3 is a defect in the copy and paste
directions this feature already ships, repaired by `WORD_BOUNDARY_PLAN.md`. All four were
confirmed against source, and all but HyperSearch against running code.

1. **The X11 primary selection.** `TextAreaMouseHandler.java:541` runs
   `Registers.setRegister('%', textArea.getSelectedText(sel))` after any mouse
   drag-selection, and `Gutter.java:1152` does the same for a gutter line selection. That
   line is **outside** the quick-copy guard at `:542`, so the default
   `view.middleMousePaste=false` (`jedit.props:292`) does not disable it.
   `Registers.setRegister(char,String)` is `new StringSelection(value)` (`:464-467`), and
   `Registers.java:610-612` binds `'%'` to `Toolkit.getSystemSelection()`. So selecting a
   word glyph with the mouse and middle-clicking into another application yields U+E048
   today, in the default configuration. **Has its own plan** — wrapping the `'%'` register
   the way `'$'` is already wrapped, with expansion added on the write side; prototyped
   against a real X11 primary selection and working.
2. **Pasting into jEdit's own search fields.** The Search and Replace dialog's find field
   is a `HistoryTextArea extends javax.swing.JTextArea` (`SearchDialog.java:415`) and the
   quick-search bar's is a `HistoryTextField extends JTextField` (`SearchBar.java:63`);
   neither has any custom paste, so both use Swing's stock
   `BasicTextUI$TextTransferHandler`, which reads exactly the plain-text flavor the copy
   fix replaced. **Measured**: copying a word glyph out of a buffer and pasting it into the
   find field yields the mathematical letters, and the search then matches nothing, because
   the buffer holds U+E048. The common path is unaffected — the `find` action pre-fills the
   field with `textArea.getSelectedText()` directly (`actions.xml:395`), never touching the
   clipboard, so "select the word, press Ctrl-F" works. **Has its own plan** — wrapping the
   fields' transfer handlers, discovered through a global AWT container-event listener;
   prototyped and working, and it covers Isabelle's Query, Sledgehammer and Debugger fields
   too, since `Completion_Popup.History_Text_Field extends HistoryTextField`
   (`completion_popup.scala:396-401`).
3. **A round trip through another application can merge two adjacent glyphs — now fixed
   elsewhere.** Described under "Correction 2": exactly 51 sequences of adjacent word glyphs
   do not survive expand-then-fold, one of which, `\<or'>\<else>`, comes back as the single
   symbol `\<orelse>`. This was open when this plan was written; it is now the subject of
   `WORD_BOUNDARY_PLAN.md`, which repairs all 51 and goes in first. What that plan leaves
   unrepaired — 9 sequences bridged by an underscore and 26 in which a glyph meets the user's
   own mathematical letters — is recorded there as a known limit, and one of them is the
   manual-check input above. Nothing in this plan makes it worse — the two-slot state means an
   intra-jEdit drag never folds a string we produced — and nothing here fixes it either.
4. **HyperSearch's "copy results".** `HyperSearchResults.java:791-794` and `:1049-1052`
   call `Toolkit.getDefaultToolkit().getSystemClipboard()` and `setContents` directly,
   bypassing both the register and the service list. There is no interception point from a
   startup script. **Not fixable this way**; record it as a known limitation.


## Constraints on whoever implements this

- **Never run `isabelle build`**, in any session, with any flags, however small.
- Never run `git clean`, `git stash`, `git checkout`, or `git reset --hard`. This is a
  shared working tree with other agents in it.
- Do not modify anything under `contrib/Isabelle2025-2/` — see the patching note above.
- Do not modify anything under `ICSE27/` or `ICSE27-x/`.
- `contrib/phi-system` is its own git repository; commit there and bump the pointer in the
  super-repo.
