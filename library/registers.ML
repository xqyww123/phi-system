signature NU_REGISTERS = sig
  exception NameConfliction of string
  exception NoSuchRegister of string
  val new_locale : Proof.context -> thm (*meta*) -> thm (*meta*)
  val delete_locale : Proof.context -> thm (*meta*) -> thm (*meta*)
  val new_reg : Proof.context -> string (*name*) -> thm (*meta*) -> thm (*meta*)
  val new_regs : Proof.context -> string list (*names*) -> thm (*meta*) -> thm (*meta*)

  val store_reg : Proof.context -> string (*name*) -> thm (*meta*) -> thm (*meta*)
  (* store to an existing register or create a new one *)
  val assign_reg : Proof.context -> string (*name*) -> thm (*meta*) -> thm (*meta*)
  val load_reg : Proof.context -> string (*name*) -> thm (*meta*) -> thm (*meta*)
  val move_reg : Proof.context -> string (*name*) -> thm (*meta*) -> thm (*meta*)
end
structure NuRegisters : NU_REGISTERS = struct
open NuGeneral NuBasics Term Thm

exception NameConfliction of string
exception NoSuchRegister of string

fun find_path_i name (Const (@{const_name "AndTy"}, _) $ t1 $ t2)
      = (case find_path_i name t1 of SOME x => SOME (NuPath.L :: x)
           | NONE => case find_path_i name t2 of SOME x => SOME (NuPath.R :: x)
           | NONE => NONE)
  | find_path_i name (Const (@{const_name "Named"},_) $ name' $ _)
      = if dest_name_tag name' = name then SOME [] else NONE
  | find_path_i name (Const (@{const_name "Stack_Delimiter"},_) $ a $ _)
      = Option.map (fn path => NuPath.Stack :: path) (find_path_i name a)
  | find_path_i name (Const (@{const_name "RegisterCollection"},_) $ a)
      = Option.map (fn path => NuPath.Reg :: path) (find_path_i name a)
  | find_path_i name _ = NONE
fun find_path2 name regs =
  case find_path_i name regs of SOME x => x | _ => raise NoSuchRegister name
fun exists_name name regs = Option.isSome (find_path_i name regs)
fun chk_confliction name regs =
  if exists_name name regs then raise NameConfliction name else ()

fun mapper_index_of meta locale =
  funpow (length (stack_of_meta meta) - 1) (fn th => th RS @{thm index_stack_mapper})
    ((funpow locale (fn th => th RS @{thm index_left_mapper}) @{thm index_here_mapper})
      RS @{thm index_reg_mapper})
fun new_locale ctx meta = 
  apply_proc_naive
    (mapper_index_of meta 0 RS @{thm new_reg}) meta
  |> NuSys.accept_proc ctx
fun set_name name th = th |> renamed_prop (prop_of th |> map_abs_vars (fn s =>
      if s = "\<n>\<a>\<m>\<e>" then name else s))
fun new_reg ctx name meta = 
  apply_proc_naive
    (@{print} (mapper_index_of meta 1 RS set_name name (@{print} @{thm new_reg}) |> @{print})) meta
  |> NuSys.accept_proc ctx
fun new_regs ctx = fold (new_reg ctx)
fun delete_locale ctx meta =
  NuSys.apply_proc ctx
    (mapper_index_of meta 0 RS @{thm delete_reg}) meta
  |> NuSys.accept_proc ctx

val store_reg_thm = @{thm store_reg}
val load_reg_thm = @{thm load_reg}
fun store_reg_at path = NuPath.mapper path RS store_reg_thm
fun load_reg_at path = NuPath.getter path RS load_reg_thm
fun move_reg_at path = NuPath.mapper path RS @{thm move_reg}

fun store_reg ctx name meta =
  NuSys.apply_proc ctx (store_reg_at (find_path2 name
    (dest_current_nu meta |> NuHelp.dest_binop @{const_name Stack_Delimiter} |> #1))) meta
fun load_reg ctx name meta =
  NuSys.apply_proc ctx (load_reg_at (find_path2 name (dest_current_nu meta))) meta
fun move_reg ctx name meta =
  NuSys.apply_proc ctx (move_reg_at (find_path2 name (dest_current_nu meta))) meta

fun perhaps' f x = (f x) handle NameConfliction _ => x
fun assign_reg ctx name meta =
  perhaps' (new_reg ctx name) meta |> store_reg ctx name
end
