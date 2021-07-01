signature NU_REGISTERS = sig
  exception NameConfliction of string
  exception NoSuchRegister of string
  val new_reg_at : string (*name*) -> NuPath.T list -> thm
  val new_reg : string (*name*) -> term (*register collection*) -> thm
  val store_reg_at : NuPath.T list -> thm
  val store_reg : string (*name*) -> term (*register collection*) -> thm
  (* store to an existing register or create a new one *)
  val assign_reg : string (*name*) -> term (*register collection*) -> thm
  val load_reg : string (*name*) -> term (*register collection*) -> thm
end
structure NuRegisters : NU_REGISTERS = struct
open NuGeneral NuBasics Term Thm
exception NameConfliction of string
exception NoSuchRegister of string

fun set_name name th = th |> renamed_prop (prop_of th |> map_abs_vars (fn s =>
      if s = "\<n>\<a>\<m>\<e>" then name else s))

val new_reg_0_thm = @{thm new_reg_0}
val new_reg_L_thm = @{thm new_reg_L}
val new_reg_R_thm = @{thm new_reg_R}
fun new_reg_thm NuPath.L = new_reg_L_thm
  | new_reg_thm NuPath.R = new_reg_R_thm
fun new_reg_at name [] = new_reg_0_thm |> set_name name
  | new_reg_at name (lr::path) = NuPath.mapper path RS (new_reg_thm lr) |> set_name name
val store_reg_thm = @{thm store_reg}
val load_reg_thm = @{thm load_reg}
fun store_reg_at path = NuPath.mapper path RS store_reg_thm
fun load_reg_at path = NuPath.mapper path RS load_reg_thm

fun prepend_bitlst_impl (bits,n) =
  ((if Word8.andb (0wx01, n) = 0wx01 then true else false)::bits, Word8.>> (n,0wx01))
fun prepend_bitlst bits c = repeat_n 7 prepend_bitlst_impl (bits, Byte.charToByte c) |> fst
fun to_bitlst_impl bits [] = bits
  | to_bitlst_impl bits (c::r) = prepend_bitlst (to_bitlst_impl bits r) c
fun to_bitlst s = to_bitlst_impl [] (String.explode s)

fun common_header_impl (ret,[],r2) = (rev ret,[],r2)
  | common_header_impl (ret,r1,[]) = (rev ret,r1,[])
  | common_header_impl (ret,(h1::r1),(h2::r2)) =
      if h1 = h2 then common_header_impl (h1::ret, r1, r2) else (rev ret, h1::r1, h2::r2)
fun common_header (a,b) = common_header_impl ([],a,b)
fun starts_with [] s = SOME s
  | starts_with _ [] = NONE
  | starts_with (h::l) (hs::ls) = if h = hs then starts_with l ls else NONE

fun mk_node (l,r) = (case common_header (BiTree.get_tag l, BiTree.get_tag r)
                       of (s,sl,sr) => BiTree.Node (s, BiTree.set_tag sl l, BiTree.set_tag sr r))
fun mk_trie (BiTree.Leaf (_, s)) = BiTree.Leaf (to_bitlst s, ())
  | mk_trie (BiTree.Node (_, l, r)) = mk_node (mk_trie l, mk_trie r)

local
exception NameConflictionInternal
fun find_path_impl ret s (BiTree.Node (seq,l,r)) =
      (case common_header (seq,s) of (_,seq',s') =>
        (case (seq',s') of ([],[]) => raise NameConflictionInternal
            | (_,[]) => NuPath.L::ret
            | ([],s' as true::_) => find_path_impl (NuPath.R::ret) s' r
            | ([],s' as false::_) => find_path_impl (NuPath.L::ret) s' l
            | (true::_,false::_) => NuPath.L::ret
            | (false::_,true::_) => NuPath.R::ret
            | _ => raise Fail "unreachable"))
  | find_path_impl ret s (BiTree.Leaf (seq,_)) =
      (case common_header (seq,s) of (_,seq',s') =>
        (case (seq',s') of ([],[]) => raise NameConflictionInternal
            | (_,[]) => NuPath.L::ret
            | ([],_) => NuPath.R::ret
            | (true::_,false::_) => NuPath.L::ret
            | (false::_,true::_) => NuPath.R::ret
            | _ => raise Fail "unreachable"))
fun find_path regs name =
      (case dest_registerTys regs
         of NONE => []
          | SOME tree => mk_trie tree |> find_path_impl [] (to_bitlst name))
in
fun new_reg name regs = new_reg_at name (find_path regs name)
      handle NameConflictionInternal => raise NameConfliction name
end

local
fun find_path_impl name [] = raise NoSuchRegister name
  | find_path_impl name ((BiTree.Leaf (_, name'), ret)::rs) =
      if name' = name then ret else find_path_impl name rs
  | find_path_impl name ((BiTree.Node (_, l,r), ret)::rs) =
      find_path_impl name ((l,NuPath.L::ret) :: (r,NuPath.R::ret) :: rs)
fun find_path name regs =
      (case dest_registerTys regs
         of NONE => raise NoSuchRegister name
          | SOME tree => find_path_impl name [(tree,[])])

fun find_path2_impl name [] = raise NoSuchRegister name
  | find_path2_impl name (((Const ("NuPrim.AndTy", _) $ t1 $ t2),path)::r)
      = find_path2_impl name ((t1,NuPath.L::path)::(t2,NuPath.R::path)::r)
  | find_path2_impl name (((Const ("NuPrim.RegisterTy",_) $ name' $ _),path)::r)
      = if dest_name_tag name' = name then path else find_path2_impl name r
  | find_path2_impl name ((t,_)::r) = raise TERM ("register_path",[t])
fun find_path2 name regs =
  if same_const Void_name regs
  then raise NoSuchRegister name
  else find_path2_impl name [(regs,[])]

fun find_path3_impl name [] = false
  | find_path3_impl name ((Const ("NuPrim.AndTy", _) $ t1 $ t2)::r)
      = find_path3_impl name (t1::t2::r)
  | find_path3_impl name ((Const ("NuPrim.RegisterTy",_) $ name' $ _)::r)
      = if dest_name_tag name' = name then true else find_path3_impl name r
  | find_path3_impl name (t::r) = raise TERM ("register_path",[t])
fun find_path3 name regs =
  if same_const Void_name regs then false else find_path3_impl name [regs]
 
in
fun store_reg name regs = store_reg_at (find_path2 name regs)
fun load_reg name regs = load_reg_at (find_path2 name regs)
fun assign_reg name regs =
  if find_path3 name regs then store_reg name regs else new_reg name regs
end
end
