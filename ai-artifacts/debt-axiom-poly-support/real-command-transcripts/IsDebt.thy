theory IsDebt
  imports Main "Debt_Axiom.Debt_Axiom"
begin

text \<open>Plan sections 8.3-3 and 8.4-6: is_debt in situ.  Queries are read via
  Spec_Rules.get (the consumer's literal input space) --- never via the theorem
  debt_axiomatization returns.\<close>

debt_axiomatization d1: \<open>n < m \<Longrightarrow> n \<le> (m::nat)\<close>
debt_axiomatization d2: \<open>x + y = y + (x::'a::comm_monoid_add)\<close>

unspecified_type utype
specify_type ubij: utype = nat

ML \<open>
  val thy = \<^theory>
  val ctxt = Proof_Context.init_global thy
  val unknowns =
    Spec_Rules.get ctxt
    |> filter (fn {rough_classification = Spec_Rules.Unknown, ...} => true | _ => false)
  fun props_of_name s =
    unknowns |> filter (fn {name, ...} => String.isSubstring s name)
             |> maps #rules |> map Thm.prop_of
  val [p_d1] = props_of_name "d1"
  val [p_d2] = props_of_name "d2"
  val true = Debt_Axiom.is_debt thy p_d1
  val true = Debt_Axiom.is_debt thy p_d2
  (*the nat INSTANCE of d2 is not the debt*)
  val p_d2_nat = Term.map_types (Term.map_atyps (fn TVar _ => \<^typ>\<open>nat\<close> | A => A)) p_d2
  val false = Debt_Axiom.is_debt thy p_d2_nat
  (*a library fact and a specify_type bijection axiom: false, no exception*)
  val false = Debt_Axiom.is_debt thy (Thm.prop_of @{thm add.commute})
  val false = Debt_Axiom.is_debt thy (Thm.prop_of @{thm ubij(1)})
  val _ = writeln "IsDebt PRE-discharge checks PASS"
\<close>

lemma d1_cert: \<open>n < m \<Longrightarrow> n \<le> (m::nat)\<close> by (rule less_imp_le)

discharge_debt_axiom d1 : d1_cert

ML \<open>
  val thy = \<^theory>
  val ctxt = Proof_Context.init_global thy
  val unknowns =
    Spec_Rules.get ctxt
    |> filter (fn {rough_classification = Spec_Rules.Unknown, ...} => true | _ => false)
  fun props_of_name s =
    unknowns |> filter (fn {name, ...} => String.isSubstring s name)
             |> maps #rules |> map Thm.prop_of
  (*the Spec_Rules entry of d1 SURVIVES its discharge; is_debt on it flips*)
  val [p_d1] = props_of_name "d1"
  val [p_d2] = props_of_name "d2"
  val false = Debt_Axiom.is_debt thy p_d1
  val true = Debt_Axiom.is_debt thy p_d2
  val _ = writeln "IsDebt POST-discharge checks PASS"
\<close>

print_debt_axiom

end
