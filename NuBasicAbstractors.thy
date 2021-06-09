theory NuBasicAbstractors
  imports NuLLReps
  abbrevs "SState" = "\<B_S>\<B_t>\<B_r>\<B_i>\<B_c>\<B_t>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e>"
      and "LState" = "\<B_L>\<B_o>\<B_o>\<B_s>\<B_e>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e>" 
      and "with_registers" = "\<B_w>\<B_i>\<B_t>\<B_h>_\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r>\<B_s>"
      and "wreg" = "\<B_w>\<B_i>\<B_t>\<B_h>_\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r>\<B_s>"
begin

definition Fusion :: "('a1::llty,'b1) nu \<Rightarrow> ('a2::llty,'b2) nu \<Rightarrow> ('a1 \<times> 'a2, 'b1 \<times> 'b2) nu"
    (infixr "\<nuFusion>" 70) where
  Fusion_def: "Fusion N M = Nu (\<lambda>px. case px of ((p1,p2),(x1,x2)) \<Rightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2))"
lemma Fusion_abst_ex[abst_expn]: "(p \<nuLinkL> N \<nuFusion> M \<nuLinkR> x) \<longleftrightarrow> (case p of (p1,p2) \<Rightarrow> case x of (x1,x2) \<Rightarrow>
        (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2))"
  by (auto simp add: abstraction_def simp add: Fusion_def)
lemma Fusion_abst[simp]: "((p1,p2) \<nuLinkL> N \<nuFusion> M \<nuLinkR> (x1,x2)) \<longleftrightarrow> (p1 \<nuLinkL> N \<nuLinkR> x1) \<and> (p2 \<nuLinkL> M \<nuLinkR> x2)"
  by (auto simp add: abst_expn)
lemma "Nu_SE (N \<nuFusion> M) x \<longleftrightarrow> (case x of (x1,x2) \<Rightarrow> Nu_SE N x1 \<and> Nu_SE M x2)"
  by (auto simp add: Nu_SE_def)

lemma Fusion_sh: "Nu_Share N f1 \<Longrightarrow> Nu_Share M f2 \<Longrightarrow>
  Nu_Share (N \<nuFusion> M) (\<lambda>x z. case x of (x1,x2) \<Rightarrow> (f1 x1 z, f2 x2 z))"
  by (auto simp add: Nu_Share_def)

(* definition NuStateLoose :: "(('a::llty),'b) nu \<Rightarrow> ('a state, 'b) nu" ("\<S> _" [27] 27) where
  NuStateLoose_def: "NuStateLoose N px = (case px of (StatOn p, x) \<Rightarrow> N (p,x) |
    (SNeg,_) \<Rightarrow> True | (STrap,_) \<Rightarrow> False)"
definition NuStateStrict :: "(('a::llty),'b) nu \<Rightarrow> ('a state, 'b) nu" ("\<S_S> _" [27] 27) where
  NuStateStrict_def: "NuStateStrict N px = (case px of (StatOn p, x) \<Rightarrow> N (p,x) | _ \<Rightarrow> False)"
*)
definition StateSetStrict :: "('a::llty) set \<Rightarrow> 'a state set" ("\<B_S>\<B_t>\<B_r>\<B_i>\<B_c>\<B_t>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e> _" [27] 27)  where
  StateSetStrict_def: "StateSetStrict S = {s. case s of StatOn p \<Rightarrow> p \<in> S | _ \<Rightarrow> False}"
definition StateSetLoose :: "('a::llty) set \<Rightarrow> 'a state set" ("\<B_L>\<B_o>\<B_o>\<B_s>\<B_e>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e> _" [27] 27)  where
  StateSetLoose_def: "StateSetLoose S = {s. case s of StatOn p \<Rightarrow> p \<in> S | SNeg \<Rightarrow> True | STrap \<Rightarrow> False}"

(* lemma NuStateStrict_tr_c: "p \<nuLinkL> \<S_S> N \<nuLinkR> x \<longleftrightarrow> (case p of
  StatOn p' \<Rightarrow> p' \<nuLinkL> N \<nuLinkR> x | _ \<Rightarrow> False)"
    by (auto simp add: NuStateStrict_def simp add: abstraction_def split: state.split)
*)
definition op_add :: "nat \<Rightarrow> (('a::len) word \<times> ('a::len) word \<times> 'r) state \<Rightarrow> (('a::len) word \<times> 'r) state"
  where op_add_def: "op_add w p = (case p of StatOn (a,b,r) \<Rightarrow>
    if LENGTH('a) = w then StatOn (a+b, r) else STrap | STrap \<Rightarrow> STrap | SNeg \<Rightarrow> SNeg)"

theorem add_nat: "p \<nuLinkL> \<S_S> (NuNat b \<nuFusion> NuNat b \<nuFusion> R) \<nuLinkR> (x,y,r) \<Longrightarrow> x + y < 2^(LENGTH('b))
  \<Longrightarrow> op_add (LENGTH('b)) p \<nuLinkL> \<S_S> (NuNat b \<nuFusion> R) \<nuLinkR> (x+y,r)" for b :: "('b::len) itself"
  by (auto simp add: op_add_def simp add: NuStateStrict_tr_c simp add: NuNat_tr_c split: state.split)

theorem add_nat_mod: "p \<nuLinkL> NuStateStrict (NuNat b \<nuFusion> NuNat b \<nuFusion> R) \<nuLinkR> (x,y,r)
    \<Longrightarrow> op_add (LENGTH('b)) p \<nuLinkL> NuStateStrict (NuNat b \<nuFusion> R) \<nuLinkR> (x+y mod 2^(LENGTH('b)),r)"
  for b :: "('b::len) itself"
  by (auto simp add: op_add_def simp add: NuStateStrict_tr_c simp add: NuNat_tr_c split: state.split)
    (metis of_nat_unat ucast_id unat_of_nat)

proc "p \<in> \<B_S>\<B_t>\<B_r>\<B_i>\<B_c>\<B_t>\<B_S>\<B_t>\<B_a>\<B_t>\<B_e> (x \<B_a>\<B_s> x ⦂ \<nat> 32) \<times> (y as y ⦂ \<nat> 32) \<B_w>\<B_i>\<B_t>\<B_h>_\<B_r>\<B_e>\<B_g>\<B_i>\<B_s>\<B_t>\<B_e>\<B_r>\<B_s> " for x y :: nat begin
  require "x < 100" and "y < 100"
  x y + y +
finish add2

context includes show_more begin

end

end