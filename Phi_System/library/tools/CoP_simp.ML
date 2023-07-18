signature PHI_COP_SIMP = sig

(* check if the simplification is required *)

val is_simp_needed : Context.generic -> term -> bool
val add_simp_pattern : term -> Context.generic -> Context.generic
val add_simp_checker : Symtab.key * (term -> bool) -> Context.generic -> Context.generic

(* invoke the simplification if needed *)

val invoke_when_needed : Proof.context * Phi_Working_Mode.working_mode -> thm -> thm
val force_invoke : Proof.context * Phi_Working_Mode.working_mode -> thm -> thm (*no matter if is needed*)

end

structure Phi_CoP_Simp : PHI_COP_SIMP = struct

(*** Check the need of simplification ***)

datatype checker = Chk_Pattern of term | Chk_ML of term -> bool

structure Checkers = Generic_Data (
  type T  = (serial * checker) list Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (eq_set ((op =) o apply2 fst))
)

fun is_simp_needed ctxt =
  let val chkers = Checkers.get ctxt
      val thy = Context.theory_of ctxt
      fun apply_chk N tm =
        let val chks = the_default [] (Symtab.lookup chkers N)
         in exists (fn (_, Chk_Pattern pat) => PLPR_Pattern.matches thy (pat,tm)
                     | (_, Chk_ML f) => f tm) chks
        end
      fun chk tm =
        let val (h,args) = Term.strip_comb tm
         in (case h
         of Const (N, _) => apply_chk N tm
          | Abs (_, _, X) => if null args then chk X
                             else raise Phi_Help.REQUIRE_LAMBDA_NORMLAIZTION
          | _ => false)
         orelse exists chk args
        end
        handle Phi_Help.REQUIRE_LAMBDA_NORMLAIZTION =>
          chk (Envir.beta_eta_contract tm)
      fun chk' tm = apply_chk "" tm orelse chk tm
   in Phi_Syntax.exists_item_of_assertion chk'
  end

(*the (type part of) \<phi>-types matching this pattern will invoke the simplification*)
fun add_simp_pattern pat ctxt =
  let val N = case Term.head_of pat
                of Const (N,_) => N
                 | _ => raise TERM ("Phi_CoP_Simp.add_simp_pattern: The pattern must be leaded by a constant", [pat])
   in Checkers.map (Symtab.map_default (N,[]) (fn L => (serial(), Chk_Pattern pat) :: L)) ctxt
  end

fun add_simp_checker (N,chker) ctxt =
  Checkers.map (Symtab.map_default (N,[]) (fn L => (serial(), Chk_ML chker) :: L)) ctxt


(* invoke the simplification if needed *)

fun force_invoke (ctxt, mode) sequent =
  let val sequent' = @{thm' \<A>simp_stage_1} RS (sequent RS' (ctxt, #transformation_rule mode))
   in Phi_Reasoner.reason1 (fn () => "Simplification fails") (SOME 1) ctxt sequent'
  end

fun invoke_when_needed (ctxt, mode) sequent =
  let val assertion = #spec_of mode (Thm.prop_of sequent)
   in if is_simp_needed (Context.Proof ctxt) assertion
   then force_invoke (ctxt, mode) sequent
   else sequent
  end


end