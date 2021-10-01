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

fun find_path_i name (Const ("NuPrim.AndTy", _) $ t1 $ t2)
      = (case find_path_i name t1 of SOME x => SOME (NuPath.L :: x)
           | NONE => case find_path_i name t2 of SOME x => SOME (NuPath.R :: x)
           | NONE => NONE)
  | find_path_i name (Const ("NuPrim.RegisterTy",_) $ name' $ _)
      = if dest_name_tag name' = name then SOME [] else NONE
  | find_path_i name _ = NONE
fun find_path2 name regs =
  case find_path_i name regs of SOME x => x | _ => raise NoSuchRegister name
fun exists_name name regs = Option.isSome (find_path_i name regs)
fun chk_confliction name regs =
  if exists_name name regs then raise NameConfliction name else ()

fun bit1_num_i ret n =
  if n <= 1 then ret else
    bit1_num_i (if n mod 2 = 1 then ret+1 else ret) (n div 2)
val bit1_num = bit1_num_i 0
val address_left_mapper = @{thm address_left_mapper}
val address_here_mapper = @{thm address_here_mapper}
fun top_mapper depth delta = (* the address-mapper at top layer *)
  funpow (delta + bit1_num (depth - 1))
    (fn th => th RS address_left_mapper) address_here_mapper
fun tree_size ret ((Const ("NuPrim.AndTy", _) $ t1 $ t2)::r) =
      tree_size ret (t1::t2::r)
  | tree_size ret (_::r) = tree_size (ret + 1) r
  | tree_size ret [] = ret

val new_reg_locale_th = @{thm new_reg_locale}
val delete_reg_locale_th = @{thm delete_reg_locale}
fun new_locale_i ctx meta =
  apply_proc_naive (top_mapper (current_block_depth (meta |> @{print})) 0 RS new_reg_locale_th) meta
  |> NuSys.accept_proc ctx
fun new_locale ctx meta = new_locale_i (NuSys.load_specthm meta ctx) meta
fun delete_locale_i ctx meta =
  NuSys.apply_proc ctx
    (top_mapper (current_block_depth meta) 0 RS delete_reg_locale_th) meta
  |> NuSys.accept_proc ctx
fun delete_locale ctx meta = delete_locale_i (NuSys.load_specthm meta ctx) meta

fun set_name name th = th |> renamed_prop (prop_of th |> map_abs_vars (fn s =>
      if s = "\<n>\<a>\<m>\<e>" then name else s))
fun new_reg ctx name meta =
  let val bdep = current_block_depth meta
    val regs = registers_of_specthm meta
    val _ = chk_confliction name regs
    fun bit1_num' x = if x <= 1 then 0 else bit1_num (x - 1) + 1
    val delta = bit1_num' bdep
    val local_num = funpow delta (dest_andTy #> fst) regs |> (tree_size 0 o single)
    val new_reg = top_mapper local_num delta RS set_name name @{thm new_reg}
  in apply_proc_naive new_reg meta |> NuSys.accept_proc ctx end
fun new_regs ctx = fold (new_reg ctx)

val store_reg_thm = @{thm store_reg}
val load_reg_thm = @{thm load_reg}
fun store_reg_at path = NuPath.mapper path RS store_reg_thm
fun load_reg_at path = NuPath.mapper path RS load_reg_thm
fun move_reg_at path = NuPath.mapper path RS @{thm remove_reg}

fun store_reg_i ctx name meta =
  NuSys.apply_proc ctx (store_reg_at (find_path2 name (registers_of_specthm meta))) meta
fun load_reg_i ctx name meta =
  NuSys.apply_proc ctx (load_reg_at (find_path2 name (registers_of_specthm meta))) meta
fun move_reg ctx name meta =
  NuSys.apply_proc ctx (move_reg_at (find_path2 name (registers_of_specthm meta))) meta
fun load_reg ctx name meta =
  load_reg_i (NuSys.load_specthm meta ctx) name meta
fun store_reg ctx name meta =
  store_reg_i (NuSys.load_specthm meta ctx) name meta

fun perhaps' f x = (f x) handle NameConfliction _ => x
fun assign_reg_i ctx name meta =
  perhaps' (new_reg ctx name) meta |> store_reg ctx name
fun assign_reg ctx name meta =
  assign_reg_i (NuSys.load_specthm meta ctx) name meta
end
