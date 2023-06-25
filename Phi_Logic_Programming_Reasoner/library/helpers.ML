signature PHI_REASONER_HELPERS = sig

val pos_parser : string -> Position.T parser

end

structure Phi_Reasoner_Helpers : PHI_REASONER_HELPERS = struct

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
end

signature PHI_HELPER_CONV = sig

val inverse_eta_conv : conv
val quant_conv : string -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val exhaustive_meta_all_conv : (Proof.context -> conv) -> Proof.context -> conv
val meta_all_body_conv : (Proof.context -> conv) -> Proof.context -> conv
val hol_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv


end

structure Phi_Helper_Conv : PHI_HELPER_CONV = struct
open Conv

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

fun exhaustive_meta_all_conv cv ctxt ctm =
  case Thm.term_of ctm
    of Const ("Pure.all", _) $ _ => meta_all_conv (exhaustive_meta_all_conv cv o snd) ctxt ctm
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

end