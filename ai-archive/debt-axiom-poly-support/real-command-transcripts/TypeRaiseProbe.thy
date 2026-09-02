theory TypeRaiseProbe
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>The is_debt totality boundary (review items m6/R5).  A query whose sort
  names a class NOT declared in the theory value passed to is_debt is the one
  input that used to raise: before R5 the matching path certified the query's
  sorts eagerly (the recover field), and this exact theory ran into
  TYPE "Undeclared class" -- recorded in the review.  After R5 (recover built
  lazily, consumed by the declaration path only) the matching path performs
  no certification and the same call returns false, so the signature's
  "Total: never raises" holds unconditionally.  Positive control first.\<close>

ML \<open>val thy_before = \<^theory>\<close>

class tiny =
  fixes tinyc :: 'a

ML \<open>
  val q = \<^prop>\<open>(x::'a::tiny) = x\<close>
  (*positive control: same query, the CURRENT theory (class tiny declared)*)
  val false = Debt_Axiom.is_debt \<^theory> q
  (*the boundary case: same query, the theory value snapshotted BEFORE the
    class existed; R5 makes this return false instead of raising TYPE*)
  val false = Debt_Axiom.is_debt thy_before q
  val _ = writeln "TypeRaiseProbe assertions PASS (total on undeclared-sort query)"
\<close>

end
