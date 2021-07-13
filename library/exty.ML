signature NU_EXTYP = sig
  val set_simproc : binding -> thm -> local_theory -> local_theory
  val set_simproc_cmd : binding -> local_theory -> local_theory
end
structure NuExTyp : NU_EXTYP = struct
open Thm NuBasics NuHelp HOLogic

fun exty_name_of_impl ret [] = rev ret
  | exty_name_of_impl ret ((Const ("NuPrim.ExTyp",_) $ Abs (name,_,tm)) :: remain)
      = exty_name_of_impl (SOME name :: ret) (tm::remain)
    (* the case in which the name is lost *)
  | exty_name_of_impl ret ((Const ("NuPrim.ExTyp",_) $ tm) :: remain)
      = exty_name_of_impl (NONE :: ret) ((@{print} tm)::remain)
  | exty_name_of_impl ret ((t $ u)::remain) = exty_name_of_impl ret (t::u::remain)
  | exty_name_of_impl ret (Abs (_,_,tm) :: remain)
      = exty_name_of_impl ret (tm::remain)
  | exty_name_of_impl ret (_ :: remain) = exty_name_of_impl ret remain
val exty_name_of = exty_name_of_impl [] o single

val name_perfix = "x\<^sub>"
val name_perfix_len = String.size name_perfix
fun set_simproc binding th lthy =
  let
    val th = unvarify_global (Proof_Context.theory_of lthy) th
    val th = case Simplifier.mksimps lthy th
               of [th] => th
                | _ => raise THM ("bad simp theorem", 0, [th])
    val (lhs,rhs) = prop_of th |> Logic.dest_equals
    fun proc _ _ tm =
      let
        val names = exty_name_of (term_of (tm |> @{print})) |> @{print}
        val renamed_rhs = map_abs_vars (fn name =>
          if String.isPrefix name_perfix name then
            case List.nth
              (names,
               int_of_string
                (String.substring (name, name_perfix_len, String.size name - name_perfix_len)))
              of SOME name' => name'
               | NONE => name
          else name) rhs
      in
        SOME (Thm.renamed_prop (Logic.mk_equals (lhs,renamed_rhs)) th |> @{print})
      end
  in
    Simplifier.define_simproc binding {lhss = [lhs], proc = proc} lthy
  end

fun set_simproc_cmd binding lthy =
  set_simproc binding (Proof_Context.get_thm lthy (Binding.name_of binding)) lthy
end
