theory PhiSem_Common_Int
  imports PhiSem_Generic_Boolean "HOL-Library.Signed_Division"
begin

section \<open>Common Integer Base\<close>

subsection \<open>Logic Syntax and Isabelle Syntax Hijack\<close>

ML \<open>structure PhiSem_Common_Int_Notation_Patch = Theory_Data (
  type T = string; val empty = ""; val merge = K ""
)\<close>

setup \<open>
let val remove_synt = Sign.notation false Syntax.mode_default [
    (Const (\<^const_abbrev>\<open>inter\<close>, dummyT), Infixl (Input.string "Int", 70, Position.no_range)),
    (Const (\<^const_abbrev>\<open>union\<close>, dummyT), Infixl (Input.string "Un", 65, Position.no_range)),
    (Const (\<^const_name>\<open>Nats\<close>, dummyT), Mixfix (Input.string "\<nat>", [], 1000, Position.no_range)),
    (Const (\<^const_name>\<open>Ints\<close>, dummyT), Mixfix (Input.string "\<int>", [], 1000, Position.no_range)),
    (Const (\<^const_name>\<open>Rats\<close>, dummyT), Mixfix (Input.string "\<rat>", [], 1000, Position.no_range)),
    (Const ("Real_Vector_Spaces.Reals", dummyT), Mixfix (Input.string "\<real>", [], 1000, Position.no_range))
  ]
in remove_synt
#> Theory.at_begin (fn thy =>
      if PhiSem_Common_Int_Notation_Patch.get thy = Context.theory_long_name thy
      then NONE
      else SOME (thy |> PhiSem_Common_Int_Notation_Patch.put (Context.theory_long_name thy)
                     |> remove_synt))
end\<close>

declare Nat.One_nat_def[simp del] Num.add_2_eq_Suc'[simp del] split_paired_All[simp del]

abbreviation LshR (infixl "LSHR" 70) where \<open>x LSHR y \<equiv> x div 2 ^ Big y\<close>
abbreviation LshL (infixl "LSHL" 70) where \<open>x LSHL y \<equiv> x  *  2 ^ Big y\<close>


subsection \<open>Semantic Base\<close>

debt_axiomatization \<phi>Sem_int_to_logic_int :: \<open>VAL \<Rightarrow> int option\<close>
                and \<phi>Sem_int_to_logic_nat :: \<open>VAL \<Rightarrow> nat option\<close>

subsubsection \<open>Reasoner Base for getting the logical int from a semantic int spec\<close>

definition get_logical_int_from_semantic_int :: \<open>VAL set \<Rightarrow> int \<Rightarrow> bool\<close>
  where \<open>get_logical_int_from_semantic_int S i = (\<forall>v \<in> S. Some i = \<phi>Sem_int_to_logic_int v)\<close>

definition get_logical_nat_from_semantic_int :: \<open>VAL set \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>get_logical_nat_from_semantic_int S i = (\<forall>v \<in> S. Some i = \<phi>Sem_int_to_logic_nat v)\<close>

declare [[\<phi>reason_default_pattern
    \<open>get_logical_nat_from_semantic_int ?S _\<close> \<Rightarrow> \<open>get_logical_nat_from_semantic_int ?S _\<close> (100)
and \<open>get_logical_int_from_semantic_int ?S _\<close> \<Rightarrow> \<open>get_logical_int_from_semantic_int ?S _\<close> (100)
]]





definition \<r>nat_to_suc_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>
  where [simp]: \<open>\<r>nat_to_suc_nat n sn \<longleftrightarrow> n = sn\<close>

definition \<r>int_to_suc_nat :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close>
  where [simp]: \<open>\<r>int_to_suc_nat z n \<longleftrightarrow> z = of_nat n\<close>

\<phi>reasoner_ML \<r>nat_to_suc_nat 1000 (\<open>\<r>nat_to_suc_nat _ _\<close> | \<open>\<r>int_to_suc_nat _ _\<close>) =
\<open>fn (ctxt,sequent) =>
let
 exception Not_A_Number
 fun dest_number (Const ("Groups.zero_class.zero", _)) = 0
  | dest_number (Const ("Groups.one_class.one", _)) = 1
  | dest_number (Const (\<^const_name>\<open>Suc\<close>, _) $ X) = 1 + dest_number X
  | dest_number (Const ("Num.numeral_class.numeral", _) $ t) = HOLogic.dest_numeral t
  | dest_number (Const ("Groups.uminus_class.uminus", _) $ t) = ~ (dest_number t)
  | dest_number t = raise Not_A_Number;
in
  case Thm.major_prem_of sequent
    of (_ (*Trueprop*) $ ( _ (*\<r>nat_to_suc_nat*) $ Z $ Var v))
        => Seq.make (fn () =>
          let val z = dest_number Z
           in if z < 0 then NONE
              else let
                val v' = funpow z (fn x => \<^const>\<open>Suc\<close> $ x) \<^term>\<open>0::nat\<close>
                in case Seq.pull (
                    Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt v')]) sequent
                        |> SOLVED' (Simplifier.simp_tac ctxt) 1
                        |> Seq.map (pair ctxt)
                    ) of NONE => (
                          warning (Pretty.string_of (Pretty.block [
                              Syntax.pretty_term ctxt Z,
                              Pretty.str " is not a literal number"
                          ]));
                          NONE)
                       | some => some
               end
          end
        handle Not_A_Number => NONE
         )
     | _ => Seq.empty
end
\<close>


subsection \<open>Operator Overloading\<close>

\<phi>overloads nat and int


\<phi>overloads mod and floor and ceiling

declare [[
    overloaded_operator_in_synthesis \<open>(+)\<close>,
    overloaded_operator_in_synthesis \<open>(-)\<close>,
    overloaded_operator_in_synthesis \<open>uminus\<close>,
    overloaded_operator_in_synthesis \<open>(*)\<close>,
    overloaded_operator_in_synthesis \<open>(div)\<close>,
    overloaded_operator_in_synthesis \<open>(mod)\<close>,
    overloaded_operator_in_synthesis \<open>(sdiv)\<close>,
    overloaded_operator_in_synthesis \<open>(/)\<close>,
    overloaded_operator_in_synthesis \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 < x2 \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>\<lambda>v. x1 \<Ztypecolon> T1 v\<close> \<open>\<lambda>v. x2 \<Ztypecolon> T2 v\<close> \<Rightarrow> \<open>\<lambda>v. x1 \<le> x2 \<Ztypecolon> \<v>\<a>\<l>[v] \<bool>\<close>,
    overloaded_operator_in_synthesis \<open>drop_bit\<close>,
    overloaded_operator_in_synthesis \<open>push_bit\<close>
]]

declare_\<phi>operator
  infixl 65 +
  infixl 65 -
  prefix 80 ~
  infixl 70 *
  infixl 70 /
  infix  50 <
  infix  50 \<le>
  infix  50 >
  infix  50 \<ge>

definition \<open>MK_CONST x \<equiv> x\<close>

lemma overloaded_synthesis_const:
  \<open>OPTIMAL_SYNTHESIS
   (\<p>\<r>\<o>\<c> H \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action overloaded_synthesis)
\<Longrightarrow> \<p>\<r>\<o>\<c> H \<lbrace> R \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding Optimal_Synthesis_def Action_Tag_def MK_CONST_def .

lemma make_overloaded_synthesis_rule_for_const:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs::unit \<phi>arg. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. const \<Ztypecolon> T ret \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          (X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<phi>V_none \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<a>\<n>\<d> Any1
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<p>\<r>\<o>\<c> F \<phi>V_none \<lbrace> X' \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action overloaded_synthesis)\<close>
  unfolding MK_CONST_def split_paired_All_\<phi>arg_unit
  using make_overloaded_synthesis_rule[where 'a = \<open>unit \<phi>arg\<close> and X' = \<open>\<lambda>_. X'\<close>,
      unfolded split_paired_All_\<phi>arg_unit split_paired_all_\<phi>arg_unit] .

lemma make_overloaded_synthesis_rule'_for_const:
  \<open> Simplify (assertion_simps ABNORMAL) E' (\<lambda>e. R'\<heavy_comma> E e)
\<Longrightarrow> PROP Gen_Synthesis_Rule
          (Trueprop (\<forall>vs::unit \<phi>arg. \<p>\<r>\<o>\<c> F vs \<lbrace> X vs \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E))
          Ant
          (X' \<i>\<m>\<p>\<l>\<i>\<e>\<s> X \<phi>V_none \<r>\<e>\<m>\<a>\<i>\<n>\<s> R' \<a>\<n>\<d> Any1
       \<Longrightarrow> PROP Ant
       \<Longrightarrow> \<p>\<r>\<o>\<c> F \<phi>V_none \<lbrace> X' \<longmapsto> \<lambda>ret. R'\<heavy_comma> R\<heavy_comma> \<blangle> MK_CONST const \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E'
           @action overloaded_synthesis)\<close>
  unfolding MK_CONST_def split_paired_All_\<phi>arg_unit
  using make_overloaded_synthesis_rule'[where 'a = \<open>unit \<phi>arg\<close>,
      unfolded split_paired_All_\<phi>arg_unit split_paired_all_\<phi>arg_unit] .


lemmas [\<phi>reason 160]
  = overloaded_synthesis_const[where const=\<open>0\<close>]
lemmas [\<phi>reason 160]
  = overloaded_synthesis_const[where const=\<open>1\<close>]
lemmas [\<phi>reason 160]
  = overloaded_synthesis_const[where const=\<open>numeral x\<close> for x]
lemmas [\<phi>reason 160]
  = overloaded_synthesis_const[where const=\<open>- numeral x\<close> for x]

lemmas [\<phi>reason 2000 for \<open>PROP Gen_Synthesis_Rule (
          Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<v>\<a>\<l>[ret] ?T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) _ _ \<close>]
  = make_overloaded_synthesis_rule_for_const [where const = x for x :: \<open>'a::numeral\<close>]
lemmas [\<phi>reason 2010 for \<open>PROP Gen_Synthesis_Rule (
          Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<v>\<a>\<l>[ret] ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) _ _ \<close>]
  = make_overloaded_synthesis_rule'_for_const[where const = x for x :: \<open>'a::numeral\<close>]

lemma [\<phi>reason 200]:
  \<open> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> 1 \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. R2\<heavy_comma> \<blangle> Suc 0 \<Ztypecolon> T ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding One_nat_def .

lemma [\<phi>reason 200]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> push_bit n x \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x * 2 ^ n \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  for x :: nat
  unfolding push_bit_nat_def .

lemma [\<phi>reason 200]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> push_bit n x \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. R\<heavy_comma> \<blangle> x * 2 ^ n \<Ztypecolon> Y ret \<brangle> \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  for x :: int
  unfolding push_bit_int_def .


(*TODO:

disable the auto evaluation when the exponent is too large!

declare power_numeral[simp del]
*)
end