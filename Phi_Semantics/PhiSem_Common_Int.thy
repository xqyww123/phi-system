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

definition get_logical_int_from_semantic_int :: \<open>VAL BI \<Rightarrow> int \<Rightarrow> bool\<close>
  where \<open>get_logical_int_from_semantic_int S i = (\<forall>v. v \<Turnstile> S \<longrightarrow> Some i = \<phi>Sem_int_to_logic_int v)\<close>

definition get_logical_nat_from_semantic_int :: \<open>VAL BI \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>get_logical_nat_from_semantic_int S i = (\<forall>v. v \<Turnstile> S \<longrightarrow> Some i = \<phi>Sem_int_to_logic_nat v)\<close>

declare [[\<phi>reason_default_pattern
    \<open>get_logical_nat_from_semantic_int ?S _\<close> \<Rightarrow> \<open>get_logical_nat_from_semantic_int ?S _\<close> (100)
and \<open>get_logical_int_from_semantic_int ?S _\<close> \<Rightarrow> \<open>get_logical_int_from_semantic_int ?S _\<close> (100)
]]

\<phi>reasoner_group logical_spec_of_semantics = (1000, [1000,1000])
                 for (\<open>get_logical_int_from_semantic_int S i\<close>, \<open>get_logical_nat_from_semantic_int S i\<close>)
  \<open>returning logical images of semantic representations.\<close>



definition \<r>nat_to_suc_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>
  where [simp, \<phi>safe_simp]: \<open>\<r>nat_to_suc_nat n sn \<longleftrightarrow> n = sn\<close>

definition \<r>int_to_suc_nat :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close>
  where [simp, \<phi>safe_simp]: \<open>\<r>int_to_suc_nat z n \<longleftrightarrow> z = of_nat n\<close>

\<phi>reasoner_ML \<r>nat_to_suc_nat 1000 (\<open>\<r>nat_to_suc_nat _ _\<close> | \<open>\<r>int_to_suc_nat _ _\<close>) =
\<open>fn (_, (ctxt,sequent0)) => let
 exception Not_A_Number
 fun dest_number (Const ("Groups.zero_class.zero", _)) = 0
  | dest_number (Const ("Groups.one_class.one", _)) = 1
  | dest_number (Const (\<^const_name>\<open>Suc\<close>, _) $ X) = 1 + dest_number X
  | dest_number (Const ("Num.numeral_class.numeral", _) $ t) = HOLogic.dest_numeral t
  | dest_number (Const ("Groups.uminus_class.uminus", _) $ t) = ~ (dest_number t)
  | dest_number t = raise Not_A_Number;
 val sequent = Conv.gconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                  Conv.arg_conv (Conv.arg1_conv (Simplifier.rewrite ctxt))) ctxt) 1 sequent0
in case Thm.major_prem_of sequent
     of (_ (*Trueprop*) $ (Const(N, _) (*\<r>nat_to_suc_nat*) $ Z $ Var v))
        => Seq.make (fn () =>
          let val z = dest_number Z
           in if z < 0 then NONE
              else let
                val v' = funpow z (fn x => \<^const>\<open>Suc\<close> $ x) \<^term>\<open>0::nat\<close>
                in case Seq.pull (
                    Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt v')]) sequent
                        |> SOLVED' (Simplifier.simp_tac (Phi_Safe_Simps.equip ctxt)) 1
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


subsection \<open>Conventions\<close>

\<phi>reasoner_group ToA_num_conv = (800, [800, 830]) in ToA_bk
      \<open>Conversion between abstractions of numbers\<close>
  and ToA_num_conv_cut = (1000, [1000, 1030]) in ToA_cut
      \<open>Conversion between abstractions of numbers\<close>


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


declare_\<phi>lang_operator
  infixl 65 +
  infixl 65 -
  prefix 80 ~
  infixl 70 *
  infixl 70 /
  infix  50 <
  infix  50 \<le>
  infix  50 >
  infix  50 \<ge>
  infixl 40 "<<"
  infixl 40 ">>"



\<phi>reasoner_group \<phi>synthesis_literal_number = (%\<phi>synthesis_literal, [%\<phi>synthesis_literal, %\<phi>synthesis_literal+10])
                                             in \<phi>synthesis_literal
      \<open>literal number\<close>
  and \<phi>synthesis_transformation = (300, [300, 330]) in \<phi>synthesis < \<phi>synthesis_literal
      \<open>transformation between abstractions, no opcode emits\<close>
  and synthesis_arith = (100, [100,120]) in \<phi>synthesis and < \<phi>synthesis_transformation
      \<open>arithmetic operations\<close>
  and synthesis_arith_cut = (1000, [1000,1020]) in \<phi>synthesis_cut
      \<open>cutting arithmetic operations\<close>


lemmas [\<phi>reason %\<phi>synthesis_literal_number] = "_synthesis_literal_"[where const=\<open>0\<close>]
lemmas [\<phi>reason %\<phi>synthesis_literal_number] = "_synthesis_literal_"[where const=\<open>1\<close>]
lemmas [\<phi>reason %\<phi>synthesis_literal_number] = "_synthesis_literal_"[where const=\<open>numeral x\<close> for x]
lemmas [\<phi>reason %\<phi>synthesis_literal_number] = "_synthesis_literal_"[where const=\<open>- numeral x\<close> for x]

(*
lemmas [\<phi>reason 2000 for \<open>PROP Gen_Synthesis_Rule (
          Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<v>\<a>\<l>[ret] ?T \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) _ _ \<close>]
  = make_synthesis_rule_for_const [where const = x for x :: \<open>'a::numeral\<close>]
lemmas [\<phi>reason 2010 for \<open>PROP Gen_Synthesis_Rule (
          Trueprop (\<forall>vs. \<p>\<r>\<o>\<c> _ \<lbrace> _ \<longmapsto> \<lambda>ret. (?var_x::?'x::numeral) \<Ztypecolon> \<v>\<a>\<l>[ret] ?T \<r>\<e>\<m>\<a>\<i>\<n>\<s> ?R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> ?E )) _ _ \<close>]
  = make_synthesis_rule'_for_const[where const = x for x :: \<open>'a::numeral\<close>]
*)

lemma [\<phi>reason %\<phi>synthesis_normalize]:
  \<open> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. 1 \<Ztypecolon> T ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> H \<lbrace> R1 \<longmapsto> \<lambda>ret. Suc 0 \<Ztypecolon> T ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R2 \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  unfolding One_nat_def .

lemma [\<phi>reason %\<phi>synthesis_weak_normalize]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. push_bit n x \<Ztypecolon> Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. x * 2 ^ n \<Ztypecolon> Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  for x :: nat
  unfolding push_bit_nat_def .

lemma [\<phi>reason %\<phi>synthesis_weak_normalize]:
  \<open> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. push_bit n x \<Ztypecolon> Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis
\<Longrightarrow> \<p>\<r>\<o>\<c> f \<lbrace> X \<longmapsto> \<lambda>ret. x * 2 ^ n \<Ztypecolon> Y ret \<r>\<e>\<m>\<a>\<i>\<n>\<s> R \<rbrace> \<t>\<h>\<r>\<o>\<w>\<s> E @action synthesis\<close>
  for x :: int
  unfolding push_bit_int_def .


(*TODO:

disable the auto evaluation when the exponent is too large!

declare power_numeral[simp del]
*)
end