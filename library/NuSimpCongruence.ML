signature NU_SIMP_CONG = sig
  val simproc : thm -> Proof.context -> cterm -> thm option
  val simproc_qualifier : thm -> Proof.context -> cterm -> thm option
end

structure NuSimpCong : NU_SIMP_CONG = struct
open NuHelp

fun chk_simplified NONE = NONE
  | chk_simplified (SOME th) =
      case Thm.prop_of th of Const (@{const_name Pure.eq}, _) $ a $ b =>
        if Envir.aeconv (a,b) then NONE else SOME th

fun simproc cong ctx cterm =
  let
    val (lhs,_) = Thm.cconcl_of cong |> @{print} |> dest_binop_c @{const_name "Pure.eq"}
    val cong = Thm.instantiate (Thm.first_order_match (lhs,cterm)) cong
  in
    SINGLE (ALLGOALS (SOLVED' (Simplifier.asm_simp_tac ctx))) cong |> chk_simplified
  end handle Pattern.MATCH => NONE

(* the version preserving name of the qualifier, useful for @{term ExNu}. *)
fun simproc_qualifier cong ctx cterm =
  let
    fun norm_name name th =
      let
        val (Const (@{const_name Pure.eq}, x1) $ x2 $
          (Const (@{const_name RepSet}, x3) $ (Const (@{const_name typing}, x4)
            $ image $ (Const qualifier $ nu))))
          = Thm.prop_of th
        val image = case image of Abs (_, ty, body) => Abs (name, ty, body) | tm => tm
        val nu = case nu of Abs (_, ty, body) => Abs (name, ty, body) | tm => tm
        val renamed = (Const (@{const_name Pure.eq}, x1) $ x2 $
          (Const (@{const_name RepSet}, x3) $ (Const (@{const_name typing}, x4)
            $ image $ (Const qualifier $ nu))))
      in
        Thm.renamed_prop renamed th
      end
  in
    case Thm.term_of cterm
      of (Const (@{const_name RepSet},_) $ (Const (@{const_name typing}, _)
          $ _ $ (Const _ $ Abs (name, _, _))))
        => Option.map (norm_name name) (simproc cong ctx cterm)
      | _ => NONE
  end
  
end
