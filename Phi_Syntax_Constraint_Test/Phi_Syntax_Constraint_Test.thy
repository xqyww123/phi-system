(* FILE: Phi_Syntax_Constraint_Test.thy

   A regression net for the positional constraints that Isabelle wraps around the head of a
   notated application.  Since Isabelle2025 the head of an application whose mixfix has reported
   literal delimiter positions arrives wrapped in \<open>_constrain\<close> / \<open>_type_constraint_\<close>, so a syntax
   translation that destructures a pre-term by a literal \<^ML>\<open>Const\<close> pattern silently stops
   matching.  The failures are silent -- a value list comes out short, a subjection collapses --
   so nothing here can be left to the ordinary sessions to catch.

   Everything below is driven from real \<open>.thy\<close> source through \<^ML>\<open>Syntax.implode_input\<close>.  That is
   essential: the wrapping only happens for REPORTED source positions, and a term parsed from a
   bare ML string carries none, so a probe written that way passes even when the code is broken.

   Each spelling is exercised BOTH directly and through a translation rule, because a rule's
   right-hand side \<open>CONST c\<close> arrives bare -- a green result on the rule-borne spelling alone
   proves nothing.
*)
theory Phi_Syntax_Constraint_Test
  imports Phi_System.Spec_Framework
begin

ML \<open>
(*parse from real source, keeping the reported positions*)
fun pre (src: Input.source) = Syntax.parse_term \<^context> (Syntax.implode_input src)

fun expect lbl exp got =
  if exp = got then writeln ("ok    " ^ lbl ^ "  =  " ^ got)
  else error ("GOLDEN MISMATCH at " ^ lbl ^
              "\n  expected: " ^ exp ^
              "\n  actual:   " ^ got)

(*which wrapper layers sit on the head of an application, and what is underneath*)
fun head_report t =
  let fun go acc (Const ("_type_constraint_", Type ("fun", [A, B])) $ x) =
            go (acc ^ (if A = B andalso not (null (Term_Position.decode_positionT A))
                       then "[pos]" else "[ascription]")) x
        | go acc (Const ("_constrain", _) $ x $ v) =
            go (acc ^ (if Term_Position.detect_position v then "[pos]" else "[ascription]")) x
        | go acc (x $ _) = go acc x
        | go acc (Const (c, _)) = acc ^ Long_Name.base_name c
        | go acc (Free (x, _)) = acc ^ "Free " ^ x
        | go acc _ = acc ^ "?"
   in go "" t end
\<close>

subsection \<open>A. the mechanism itself\<close>

text \<open>If Isabelle ever changes when it wraps a head, this section fires first and says so, instead
      of leaving a downstream translation to fail in a way that looks like a \<phi>-system bug.\<close>

ML \<open>
val _ = expect "notated head is wrapped"      "[pos]\<phi>Type"  (head_report (pre \<open>x \<Ztypecolon> T\<close>))
val _ = expect "nested notated head"          "[pos]Val"    (head_report (pre \<open>\<val>[v] T\<close>))
val _ = expect "rule-borne head stays bare"   "Val"         (head_report (pre \<open>\<val> T\<close>))
\<close>

subsection \<open>B. value collection -- \<^ML>\<open>Procedure_Syntax.translate_ret\<close>\<close>

text \<open>The binder a procedure's return specification is abstracted over must have one component per
      value mentioned.  When a head test stops matching, values are dropped silently and the binder
      degenerates -- in the worst case to \<^typ>\<open>unit \<phi>arg\<close>, i.e. "this procedure returns nothing".\<close>

ML \<open>
(*number of components of the \<phi>arg tuple the return binder ranges over*)
fun ret_arity_of t =
  (case Procedure_Syntax.translate_ret t of
     Abs (_, Type (\<^type_name>\<open>\<phi>arg\<close>, [T]), _) =>
       let fun cnt (Type (\<^type_name>\<open>prod\<close>, [_, B])) = 1 + cnt B
             | cnt (Type (\<^type_name>\<open>unit\<close>, [])) = 0
             | cnt _ = 1
        in string_of_int (cnt T) end
   | Abs _ => "NOT-A-\<phi>arg-BINDER"
   | _ => "NOT-AN-ABS")

fun ret_arity src = ret_arity_of (pre src)

val _ = expect "direct      [v]"           "1" (ret_arity \<open>x \<Ztypecolon> \<val>[v] T\<close>)
val _ = expect "rule-borne  \<val>"           "1" (ret_arity \<open>x \<Ztypecolon> \<val> T\<close>)
val _ = expect "two direct  [v] [w]"       "2" (ret_arity \<open>x \<Ztypecolon> \<val>[v] T\<heavy_comma> y \<Ztypecolon> \<val>[w] U\<close>)
val _ = expect "mixed       \<val> [v] \<val>"   "3" (ret_arity \<open>x \<Ztypecolon> \<val> T\<heavy_comma> y \<Ztypecolon> \<val>[v] U\<heavy_comma> z \<Ztypecolon> \<val> W\<close>)
val _ = expect "two rule-borne"            "2" (ret_arity \<open>x \<Ztypecolon> \<val> T\<heavy_comma> y \<Ztypecolon> \<val> U\<close>)

(*A value name written twice yields TWO components, not one, because the two occurrences carry
  different source positions and the collected entries are compared verbatim.  That is inherited
  behaviour, not something the head-wrapping introduced -- the position sits on the value name's own
  \<^ML>\<open>Free\<close>, and Isabelle2024 already made two such occurrences unequal.  It is pinned here so that a
  later attempt to normalize positions away -- which would merge the two and silently halve the
  procedure's arity -- cannot pass unnoticed.*)
val _ = expect "same name twice"           "2" (ret_arity \<open>x \<Ztypecolon> \<val>[v] T\<heavy_comma> y \<Ztypecolon> \<val>[v] U\<close>)
\<close>

text \<open>and the split is caused by the positions alone: peel every positional wrapper off the parsed
      specification first, and the very same input collapses to one component.  (\<^ML>\<open>Term_Position.strip_positions\<close>
      is NOT enough here -- it removes \<open>_constrain\<close>-borne positions, whereas an atom's position is
      carried by a \<open>_type_constraint_\<close> whose type is the encoded position.)\<close>

ML \<open>
val _ = expect "same name twice, positions peeled" "1"
          (ret_arity_of (Phi_Syntax_Constraint.strip_pos_deep
                          (pre \<open>x \<Ztypecolon> \<val>[v] T\<heavy_comma> y \<Ztypecolon> \<val>[v] U\<close>)))
\<close>

subsection \<open>C. the \<open>\<a>\<r>\<g>i\<close> naming -- a user-facing interface\<close>

text \<open>\<open>\<a>\<r>\<g>1, \<a>\<r>\<g>2, \<dots>\<close> name the anonymous values of a procedure's argument specification, left to
      right, skipping the ones the user named.  Roughly forty-five \<open>.thy\<close> sources refer to these
      names literally, so both the spelling and the counting rule are load-bearing.\<close>

ML \<open>
fun arg_names src =
  let val t = Procedure_Syntax.translate_arg (pre src)
      val ns = fold_aterms (fn Free (n, _) =>
                                 (fn L => if String.isPrefix "\<a>\<r>\<g>" n then insert (op =) n L else L)
                             | _ => I) t []
   in commas (rev ns) end

val _ = expect "one anonymous"       "\<a>\<r>\<g>1"              (arg_names \<open>x \<Ztypecolon> \<val> T\<close>)
val _ = expect "three anonymous"     "\<a>\<r>\<g>1, \<a>\<r>\<g>2, \<a>\<r>\<g>3"
          (arg_names \<open>x \<Ztypecolon> \<val> T\<heavy_comma> y \<Ztypecolon> \<val> U\<heavy_comma> z \<Ztypecolon> \<val> W\<close>)
val _ = expect "named ones skipped"  "\<a>\<r>\<g>1"              (arg_names \<open>x \<Ztypecolon> \<val>[w] T\<heavy_comma> y \<Ztypecolon> \<val> U\<close>)
\<close>

subsection \<open>D. \<^const>\<open>anonymous\<close> spelled out\<close>

text \<open>\<open>\<val> T\<close> expands to \<open>Val anonymous T\<close> through a translation rule, so its \<^const>\<open>anonymous\<close>
      arrives bare.  Written literally it arrives wrapped instead.  The two must behave alike: the
      classifier that decides "this is an anonymous value" and the scan that later looks the value
      up in the collected list have to agree, or the lookup walks straight past the entry the
      classifier just made and the translation fails with "Insufficient values".\<close>

ML \<open>
val _ = expect "anonymous written out is wrapped" "[pos]anonymous"
          (head_report (pre \<open>anonymous\<close>))

val _ = expect "literal anonymous, alone"     "1" (ret_arity \<open>x \<Ztypecolon> \<val>[anonymous] T\<close>)
val _ = expect "literal anonymous, then \<val>"   "2"
          (ret_arity \<open>x \<Ztypecolon> \<val>[anonymous] T\<heavy_comma> y \<Ztypecolon> \<val> U\<close>)
val _ = expect "two literal anonymous"        "2"
          (ret_arity \<open>x \<Ztypecolon> \<val>[anonymous] T\<heavy_comma> y \<Ztypecolon> \<val>[anonymous] U\<close>)
val _ = expect "literal anonymous is named"   "\<a>\<r>\<g>1"
          (arg_names \<open>x \<Ztypecolon> \<val>[anonymous] T\<close>)
\<close>

subsection \<open>E. \<open>\<subj> \<top>\<close> is a plain existential\<close>

text \<open>The parse translation for \<open>\<subj>\<close> drops the side condition when it is \<^const>\<open>top\<close>.  When
      the test stopped matching, \<open>A \<subj> x. \<top>\<close> kept a \<^const>\<open>Subjection\<close> node, which no longer
      matches the pattern the simplification procedure for embedded existentials destructures --
      so the procedure quietly stopped firing, in a session that still built green.\<close>

ML \<open>
val _ = expect "subj-top is EX*" "true"
          (@{make_string} (Term.aconv_untyped (\<^term>\<open>A \<subj> x. \<top>\<close>, \<^term>\<open>\<exists>*x. A\<close>)))

val _ = expect "and it has the shape the embedded-existential procedure expects" "true"
          (@{make_string}
            (case \<^pattern>\<open>_ \<Ztypecolon> _ \<subj> x. \<top>\<close> of
               Const (\<^const_name>\<open>ExBI\<close>, _) $
                 Abs (_, _, Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _) => true
             | _ => false))
\<close>

end
