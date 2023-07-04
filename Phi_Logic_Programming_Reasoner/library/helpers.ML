signature PHI_HELP = sig

val pos_parser : string -> Position.T parser
val beta_eta_contract : thm -> thm
val beta_eta_contract_cterm : cterm -> cterm
val lambda_normalization_conv : conv -> conv
val lambda_normalization_rule : (thm -> thm) -> thm -> thm

end

structure Phi_Help : PHI_HELP = struct

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

fun lambda_normalization_conv C ctm =
  C ctm
  handle CTERM _ => (Drule.beta_eta_conversion then_conv C) ctm
       | TERM _  => (Drule.beta_eta_conversion then_conv C) ctm
       | THM _   => (Drule.beta_eta_conversion then_conv C) ctm

fun lambda_normalization_rule R thm =
  R thm
  handle CTERM _ => R (beta_eta_contract thm)
       | THM _   => R (beta_eta_contract thm)
       | TERM _  => R (beta_eta_contract thm)

end

signature PHI_CONV = sig

val may_Trueprop_conv : conv -> conv

val inverse_eta_conv : conv
val quant_conv : string -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_alls_conv : (Proof.context -> conv) -> Proof.context -> conv
val meta_all_body_conv : (Proof.context -> conv) -> Proof.context -> conv
val hol_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv

val move_Ex_inside_All : Proof.context -> conv

end

structure Phi_Conv : PHI_CONV = struct
open Conv

fun may_Trueprop_conv C ctm =
  case Thm.term_of ctm
    of \<^Const>\<open>Trueprop\<close> $ _ => Conv.arg_conv C ctm
     | _ => C ctm

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

fun move_Ex_inside_All ctxt ctm =
  Phi_Help.lambda_normalization_conv (fn ctm =>
    let val (Ex, ctm1) = Thm.dest_comb ctm
        val ( f, ctm2) = Thm.dest_abs_global ctm1
        val (Al, ctm3) = Thm.dest_comb ctm2
        val ( x, body) = Thm.dest_abs_global ctm3
        val fx = Thm.apply f x
        val Q = Thm.lambda x (Thm.lambda fx body)
        val rule = Drule.infer_instantiate ctxt [(("Q",0),Q)]
                      @{thm' choice_iff[folded atomize_eq, symmetric]}
     in Conv.rewr_conv rule ctm
    end
  ) ctm


end

infix 0 RS' RSN'

fun tha RSN' (ctxt, i, thb) =
  (case Seq.chop 2 (Thm.biresolution (SOME ctxt) false [(false, tha)] i thb) of
    ([th], _) => Thm.solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", i, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", i, [tha, thb]));

(*Resolution: P \<Longrightarrow> Q, Q \<Longrightarrow> R gives P \<Longrightarrow> R*)
fun tha RS' (ctxt, thb) = tha RSN' (ctxt, 1,thb);

