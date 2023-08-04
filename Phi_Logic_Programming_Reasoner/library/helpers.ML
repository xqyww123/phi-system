exception REQUIRE_LAMBDA_NORMLAIZTION

signature PHI_HELP = sig

val leading_antecedent' : thm -> term

val pos_parser : string -> Position.T parser
val beta_eta_conversion : conv
val beta_eta_contract : thm -> thm
val beta_eta_contract_cterm : cterm -> cterm

val lambda_normalization_ctac : ('a * thm -> 'b) -> ('a * thm -> 'b)
val lambda_normalization_conv : conv -> conv
val lambda_normalization_rule : (thm -> thm) -> thm -> thm

val unique_flexflex : Proof.context option -> thm -> thm

end

structure Phi_Help : PHI_HELP = struct

fun leading_antecedent' thm = fst (Logic.dest_implies (Thm.prop_of thm))

fun pos_parser name =
  let val msg = name ^ " cannot capture the position of your rule \
                  \when no argument is given to the attribute.\n\
                  \Please use \<open>" ^ name ^" add\<close> to address it.\n\
                  \The recorded position can be very helpful for debuging, albeit it \
                  \is not mandatory.\n\
                  \It is a technical limitation of Isar."
   in fn x => let val pos = Token.pos_of (hd x)
                  val _ = if pos = Position.none
                          then warning msg
                           else ()
               in (pos,x) end
  end

fun beta_eta_contract th =
  if Term.could_beta_eta_contract (Thm.prop_of th)
  then Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th
  else th

fun beta_eta_contract_cterm x =
  Thm.dest_arg (Thm.cprop_of (Drule.beta_eta_conversion x));

fun beta_eta_conversion ctm =
  if Term.could_beta_eta_contract (Thm.term_of ctm)
  then Drule.beta_eta_conversion ctm
  else Conv.all_conv ctm

fun lambda_normalization_ctac S s =
  let fun fallback exn =
        if Term.could_beta_eta_contract (Thm.prop_of (snd s))
        then S (apsnd beta_eta_contract s)
        else Exn.reraise exn
   in S s
      handle REQUIRE_LAMBDA_NORMLAIZTION => fallback (Fail "Internal Bug: is already normalized")
           | e as CTERM _ => fallback e
           | e as TERM _  => fallback e
           | e as THM _   => fallback e
  end

fun lambda_normalization_conv C ctm =
  let fun fallback exn =
        if Term.could_beta_eta_contract (Thm.term_of ctm)
        then (Drule.beta_eta_conversion then_conv C) ctm
        else Exn.reraise exn
   in C ctm
      handle REQUIRE_LAMBDA_NORMLAIZTION => fallback (Fail "Internal Bug: is already normalized")
           | e as CTERM _ => fallback e
           | e as TERM _  => fallback e
           | e as THM _   => fallback e
  end

fun lambda_normalization_rule R thm =
  let fun fallback exn =
        if Term.could_beta_eta_contract (Thm.prop_of thm)
        then R (beta_eta_contract thm)
        else Exn.reraise exn
   in R thm
      handle REQUIRE_LAMBDA_NORMLAIZTION => fallback (Fail "Internal Bug: is already normalized")
           | e as CTERM _ => fallback e
           | e as THM _   => fallback e
           | e as TERM _  => fallback e
  end

fun unique_flexflex ctxt thm =
  case Seq.chop 2 (Thm.flexflex_rule ctxt thm)
    of ([], _) => raise THM ("unique_flexflex: fail to solve flex-flex pairs", 0, [thm])
     | ([th'], _) => th'
     | (L, _) => raise THM ("unique_flexflex: multi unification of flex-flex pairs", 0, L)

end

signature PHI_CONV = sig

val may_Trueprop_conv : conv -> conv

val protect_conv : conv
val unprotect_conv : conv

val inverse_eta_conv : conv
val quant_conv : string -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_alls_conv : (Proof.context -> conv) -> Proof.context -> conv
val meta_all_body_conv : (Proof.context -> conv) -> Proof.context -> conv
val hol_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val hol_alls_to_meta_alls: (Proof.context -> conv) -> Proof.context -> conv

val hol_imp_conv : conv -> conv -> conv

val leading_antecedent_conv : conv -> conv
val hhf_concl_conv : (Proof.context -> conv) -> Proof.context -> conv
val hhf_conv : (Proof.context -> conv) (*premise conv*)
            -> (Proof.context -> conv) (*concl conv*)
            -> Proof.context -> conv
(*for any meta premise or HOL premise, meta quantification or HOL quantification*)
val premises_conv : (Proof.context -> conv) (*premise conv*)
                  -> (Proof.context -> conv) (*concl conv*)
                  -> Proof.context -> conv
val recursive_premises_conv : (Proof.context -> conv) -> Proof.context -> conv

val rewrite_leading_antecedent : Proof.context -> thm list -> thm -> thm
val simplify_leading_antecedent : Proof.context -> thm -> thm
val simplify_leading_antecedent_hhf_concl : Proof.context -> thm -> thm

val conj_sequence_conv : conv -> conv
      (*applies the conv to every element in a HOL.conj sequent (or a tree)*)

end

structure Phi_Conv : PHI_CONV = struct
open Conv

fun may_Trueprop_conv C ctm =
  case Thm.term_of ctm
    of \<^Const>\<open>Trueprop\<close> $ _ => Conv.arg_conv C ctm
     | _ => C ctm

val protect_conv = rewr_conv @{thm Pure.prop_def[symmetric]}
val unprotect_conv = rewr_conv @{thm Pure.prop_def}



val inverse_eta = Thm.eta_conversion \<^schematic_cterm>\<open>\<lambda>x. (?f::'a::{} \<Rightarrow> 'b::{}) x\<close>
               |> Thm.symmetric
               |> Thm.trim_context
fun inverse_eta_conv ctm =
  case Thm.typ_of_cterm ctm
    of Type (\<^type_name>\<open>fun\<close>, _) =>
          Thm.instantiate (TVars.make [((("'a",0),[]), Thm.dest_ctyp0 (Thm.ctyp_of_cterm ctm)),
                                       ((("'b",0),[]), Thm.dest_ctyp1(Thm.ctyp_of_cterm ctm))],
                           Vars.make [((("f",0), Thm.typ_of_cterm ctm), ctm)])
                          inverse_eta
     | _ => raise CTERM ("inverse_eta_conv: not a function", [ctm])

fun meta_all_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const ("Pure.all", _) $ Abs _ => arg_conv (abs_conv cv ctxt) ct
  | Const ("Pure.all", _) $ _ => arg_conv (inverse_eta_conv then_conv abs_conv cv ctxt) ct
  | _ => raise CTERM ("meta_all_conv", [ct]))

fun meta_alls_conv cv ctxt ctm =
  case Thm.term_of ctm
    of Const ("Pure.all", _) $ _ => meta_all_conv (meta_alls_conv cv o snd) ctxt ctm
     | _ => cv ctxt ctm

fun is_strict_reflexive th = (op =) (Logic.dest_equals (Thm.prop_of th))
  handle TERM _ => false;

fun abs_conv cv ctxt ct =
  (case Thm.term_of ct of
    Abs (a, _, _) =>
      let
        val ((v, ct'), ctxt') = Variable.dest_abs_cterm ct ctxt;
        val eq = cv (v, ctxt') ct';
      in if is_strict_reflexive eq then all_conv ct else Thm.abstract_rule a v eq end
  | _ => raise CTERM ("abs_conv", [ct]));

fun quant_conv head cv ctxt ct =
  (case Thm.term_of ct
     of Const (N, _) $ Abs _ =>
          if N = head then Conv.arg_conv (abs_conv cv ctxt) ct
                      else raise CTERM ("quant_conv", [ct])
      | Const (N, _) $ _ =>
          if N = head then Conv.arg_conv (inverse_eta_conv then_conv abs_conv cv ctxt) ct
                      else raise CTERM ("quant_conv", [ct])
      | _ => raise CTERM ("quant_conv", [ct]))

val hol_all_conv = quant_conv \<^const_name>\<open>All\<close>

fun meta_all_body_conv C ctxt =
  meta_all_conv (fn (_, ctxt) => meta_all_body_conv C ctxt) ctxt
  else_conv C ctxt

fun hol_alls_to_meta_alls C ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>All\<close>, _) $ _) =>
         (Conv.rewr_conv @{thm' atomize_all[symmetric]} then_conv
          meta_all_conv (hol_alls_to_meta_alls C o snd) ctxt) ctm
     | _ => C ctxt ctm

fun hol_imp_conv cv1 cv2 ct =
  (case Thm.term_of ct
     of Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv cv1) cv2 ct
      | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (hol_imp_conv cv1 cv2) ct
      | _ => raise CTERM ("imp_conv", [ct]));



fun leading_antecedent_conv C = implies_conv C all_conv
fun hhf_concl_conv C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (hhf_concl_conv C o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.arg_conv (hhf_concl_conv C ctxt) ctm
     | _ => C ctxt ctm

fun hhf_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (hhf_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (hhf_conv Cp Cc ctxt) ctm
     | _ => Cc ctxt ctm

fun premises_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (premises_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (Cp ctxt)) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.All\<close>, _) $ Abs _ =>
          Conv.arg_conv (Conv.abs_conv (premises_conv Cp Cc o snd) ctxt) ctm
     | _ => Cc ctxt ctm

fun recursive_premises_conv C ctxt ctm =
  premises_conv (fn ctxt => fn ctm =>
      case Thm.term_of ctm
        of Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.All\<close>, _) $ _ ) =>
              recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ ) =>
              recursive_premises_conv C ctxt ctm
         | _ => C ctxt ctm)
    (K Conv.all_conv) ctxt ctm


fun rewrite_leading_antecedent ctxt rules =
  Conv.gconv_rule (Raw_Simplifier.rewrite ctxt true rules) 1

fun simplify_leading_antecedent ctxt =
  Conv.gconv_rule (Simplifier.rewrite ctxt) 1

fun simplify_leading_antecedent_hhf_concl ctxt =
  Conv.gconv_rule (hhf_concl_conv Simplifier.rewrite ctxt) 1

fun conj_sequence_conv C ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
       Conv.combination_conv (Conv.arg_conv (conj_sequence_conv C)) (conj_sequence_conv C) ctm
     | _ => C ctm


end

infix 0 RS' RSN'

fun tha RSN' (ctxt, i, thb) =
  (case Seq.chop 2 (Thm.biresolution (SOME ctxt) false [(false, tha)] i thb) of
    ([th], _) => Thm.solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", i, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", i, [tha, thb]));

(*Resolution: P \<Longrightarrow> Q, Q \<Longrightarrow> R gives P \<Longrightarrow> R*)
fun tha RS' (ctxt, thb) = tha RSN' (ctxt, 1,thb);


signature HOLOGIC = sig
include HOLOGIC

val imp_conv : conv -> conv -> conv
val All_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val Ex_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv

end

structure HOLogic : HOLOGIC = struct
open HOLogic

val imp_conv = Phi_Conv.hol_imp_conv
val All_conv = Phi_Conv.hol_all_conv
val Ex_conv = Phi_Conv.quant_conv \<^const_name>\<open>Ex\<close>

end

