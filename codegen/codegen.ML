(* Map from logic types to printer types
* 
* numeral itself    :  int
* lrep itself       :  llty
* func              :  ctxt -> string * ctxt,  generating the function and
*                      returning the name to be called of that function.
*                      See printer of the `call` instruction (NuCG_NuSys.op_call).
* index             :  int list, see `NuCG.put_idx` and `NuCG_NuSys.index_here`
*)
signature NU_CG = sig
  datatype llty = T_int of int | T_ptr | T_tup of llty
                | T_array of llty | <%> of (llty*llty) | T_nil | T_PTR of llty
  datatype ssa = Reg of int | Literal of string | <*> of (ssa*ssa) (*pair*) | Nil
  type ctxt

  val ssa_num : ssa -> int
  val to_s : ssa -> string
  val tystr : llty -> string

  val print : (string list -> unit) -> ctxt -> unit
  val get_output : (string list -> ctxt -> 'a) -> ctxt -> 'a
  val map_output : (string list -> string list) -> ctxt -> ctxt
  val put : string -> ctxt -> ctxt (*output string*)
  val puti: int -> ctxt -> ctxt (*output integer*)
  val putt : llty -> ctxt -> ctxt
  val putT : llty -> ctxt -> ctxt
  val putv  : ssa -> ctxt -> ctxt
  val putv' : llty -> ssa -> ctxt -> ctxt
  val putL : int -> ctxt -> ctxt (*output label*)

  val basic_block : (int -> int) -> (int -> ctxt -> ctxt) -> ctxt -> ctxt
  val get_bb : (int -> ctxt -> ctxt) -> ctxt -> ctxt
  val put_bb : int -> ctxt -> ctxt (*begin a basic block, outputing `Label:\n`*)

  val size_t : int
  val SizeT : llty

  val get_ssa : (ssa -> ctxt -> ctxt) -> ctxt -> ctxt
  val map_ssa : (ssa -> ssa) -> ctxt -> ctxt
  val counter : (int -> int) -> (int -> ctxt -> ctxt) -> ctxt -> ctxt
    (*counter :       ^ mapper    ^ origin    ^ accssor *)
  val label_counter : (int -> int) -> (int -> ctxt -> ctxt) -> ctxt -> ctxt
  val assign : (int -> ctxt -> ctxt) -> ctxt -> ctxt
  val assign_label : (int -> ctxt -> ctxt) -> ctxt -> ctxt
  val pop : (ssa -> ctxt -> ctxt) -> ctxt -> ctxt
  val pop_put  : ctxt -> ctxt
  val pop_put' : llty -> ctxt -> ctxt
  val push : ssa -> ctxt -> ctxt
  val expr : (ctxt -> ctxt) -> ctxt -> ctxt

  val fusion  : (ctxt -> ctxt) -> ctxt -> ctxt
  val fusion2 : (ctxt -> ctxt) -> ctxt -> ctxt
  val fusion'   : (llty -> ctxt -> ctxt) -> llty -> ctxt -> ctxt
  val fusion2'  : (llty -> llty -> ctxt -> ctxt) -> llty -> llty -> ctxt -> ctxt

  val monop : ((ctxt -> ctxt) -> ctxt -> ctxt) -> string -> ctxt -> ctxt
  val binop : ((ctxt -> ctxt) -> ctxt -> ctxt) -> string -> ctxt -> ctxt
  val monop' : ((ctxt -> ctxt) -> ctxt -> ctxt) -> string -> llty -> ctxt -> ctxt
  val binop' : ((ctxt -> ctxt) -> ctxt -> ctxt) -> string -> llty -> llty -> ctxt -> ctxt
  val binop'1: ((ctxt -> ctxt) -> ctxt -> ctxt) -> string -> llty -> ctxt -> ctxt

  val trunc_tail : ctxt -> ctxt
  val mk_tail : ctxt -> ctxt

  val op_pair_gen : ctxt -> ctxt
  val op_depair_gen : ctxt -> ctxt

  val cast : string -> llty -> llty -> ctxt -> ctxt
  val bitcast : llty -> llty -> ctxt -> ctxt
  val ptr2size_t : llty -> ctxt -> ctxt

  val put_idx  : int list -> ctxt -> ctxt
  val put_idx' : int list -> ctxt -> ctxt
  val expr_idx  : int list -> (ctxt -> ctxt) -> ctxt -> ctxt
  val expr_idx' : int list -> (ctxt -> ctxt) -> ctxt -> ctxt
  val op_get_tuple_gen : int list -> llty -> ctxt -> ctxt
  val op_set_tuple_gen : int list -> llty -> llty -> ctxt -> ctxt
  val op_cons_tup_gen : llty -> ctxt -> ctxt
  val op_dest_tup_gen : llty -> ctxt -> ctxt

  val br  : int -> ctxt -> ctxt (*unconditional*)
  val br' : int -> int -> ctxt -> ctxt (*conditional*)
  val phi : llty -> int -> int -> ctxt -> ctxt

  val def_func : string -> llty -> llty -> (ctxt -> ctxt) -> ctxt -> string * ctxt

  val codegen : (ctxt -> ctxt) -> Path.T -> unit

  val debug : string -> ctxt -> ctxt
  (* val fake : ctxt *)
end

structure NuCG : NU_CG = struct infixr 6 <*> <%>

datatype llty = T_int of int | T_ptr | T_tup of llty | T_array of llty | <%> of (llty*llty) | T_nil
              | T_PTR of llty
      (*T_PTR is typed pointer type while T_ptr is always `i8*`*)
datatype ssa = Reg of int | Literal of string | <*> of (ssa*ssa) (*pair*) | Nil
type ctxt = ssa * string list * (int * int * int * string list Symtab.table)
  (*ssa, output, (ssa counter, label counter, label of current basic block,
  *               functions table)*)

fun ssa_num (Reg _) = 1 | ssa_num (Literal _) = 1 | ssa_num Nil = 0
  | ssa_num (A <*> B) = ssa_num A + ssa_num B

fun to_s (Reg i) = "%" ^ string_of_int i | to_s (Literal s) = s
  | to_s x = (@{print} x; raise Fail "")
fun tystr (T_int i) = "i" ^ string_of_int i
  | tystr T_ptr = "i8*"             | tystr (T_PTR t) = tystr t ^ "*"
  | tystr (T_tup t) = "{" ^ tystr t ^ "}"
  | tystr (t <%> T_nil) = tystr t   |  tystr (a <%> b) = tystr a ^ ", " ^ tystr b
  | tystr T_nil = "void"

fun get_output f (c as (_,out,_)) = f out c   ;   fun map_output f (ssa,out,c) = (ssa,f out,c)

fun put s (ssa,out,c) = (ssa,s::out,c);   val putv = put o to_s;    val puti = put o string_of_int
val putt = put o tystr
(* 
fun putv' (t <%> T_nil) (v <*> Nil) = putv' t v
  | putv' (t1 <%> t2) (v1 <*> v2) = putv' t2 v2 #> put ", " #> putv' t1 v1
  | putv' t v = putt t #> put " " #> putv v *)
fun putv' t v = putt t #> put " " #> putv v


fun putL i = put (if i <= 0 then "%" ^ string_of_int (~i) else "%L" ^ string_of_int i)
fun basic_block m f (s,out,(cnt,lcnt,bb,ftab)) = f bb (s,out,(cnt,lcnt,m bb,ftab))
val get_bb = basic_block I;   fun set_bb i = basic_block (K i) (K I)
fun put_bb i = put ("L" ^ string_of_int i ^ ":\n") #> set_bb i

val size_t = 32; val SizeT = T_int size_t

fun print f (_,out,(_,_,_,ftab)) = (List.app (f o rev o snd) (Symtab.dest ftab); f (rev out))
fun debug s (c:ctxt) = (tracing s; print (tracing o String.concat) c; @{print} c)

fun get_ssa f (s,ot,c) = f s (s,ot,c)       ;  fun map_ssa f (s,ot,c) = (f s,ot,c)
fun counter f g (ssa,out,(cnt,lcnt,bb,ftab)) = g cnt (ssa,out,(f cnt,lcnt,bb,ftab))
fun label_counter f g (ssa,out,(cnt,lcnt,bb,ftab)) = g lcnt (ssa,out,(cnt,f lcnt,bb,ftab))
val assign = counter (fn i => i + 1)        ;   val assign_label = label_counter (fn i => i + 1)
fun pop f (X <*> ssa,ot,c) = f X (ssa,ot,c) ;   fun push X (ssa, ot,c) = (X <*> ssa, ot,c)
val pop_put = pop putv                      ;   fun pop_put' ty = pop (putv' ty)
val pop_put2 = pop (fn A => pop_put #> put ", " #> putv A)
fun pop_put2' t1 t2 = pop (fn A => pop_put' t1 #> put ", " #> putv' t2 A)
fun pop_put2'1 ty = pop (fn A => pop_put' ty #> put ", " #> putv A)
fun expr f = assign (fn i => put ("%" ^ string_of_int i ^ " = ") #> f #> push (Reg i))


(*Monop & Binop*)
fun fusion f ((A <*> B) <*> R, ot,c) =
      let val (B' <*> R', ot',c')  = fusion f (B <*> R, ot,c)
          val (A' <*> R'', ot'',c'') = fusion f (A <*> R', ot',c')
      in ((A' <*> B') <*> R'', ot'',c'') end
  | fusion f (Nil <*> R, ot,c) = (Nil <*> R, ot,c)
  | fusion f sc = f sc

fun fusion2 f ((A1 <*> B1) <*> (A2 <*> B2) <*> R, ot,c) =
      let val (B' <*> R', ot',c')  = fusion2 f (B1 <*> B2 <*> R, ot,c)
          val (A' <*> R'', ot'',c'') = fusion2 f (A1 <*> A2 <*> R', ot',c')
      in ((A' <*> B') <*> R'', ot'',c'') end
  | fusion2 f (Nil <*> Nil <*> R, ot,c) = (Nil <*> R, ot,c)
  | fusion2 f sc = f sc

fun fusion' f (S <%> T) ((A <*> B) <*> R, ot,c) =
      let val (B' <*> R', ot',c')  = fusion' f T (B <*> R, ot,c)
          val (A' <*> R'', ot'',c'') = fusion' f S (A <*> R', ot',c')
      in ((A' <*> B') <*> R'', ot'',c'') end
  | fusion' f _ (Nil <*> R, ot,c) = (Nil <*> R, ot,c)
  | fusion' f t sc = f t sc

fun fusion2' f (S1 <%> T1) (S2 <%> T2) ((A1 <*> B1) <*> (A2 <*> B2) <*> R, ot,c) =
      let val (B' <*> R', ot',c')  = fusion2' f T1 T2 (B1 <*> B2 <*> R, ot,c)
          val (A' <*> R'', ot'',c'') = fusion2' f S1 S2 (A1 <*> A2 <*> R', ot',c')
      in ((A' <*> B') <*> R'', ot'',c'') end
  | fusion2' f _ _ (Nil <*> Nil <*> R, ot,c) = (Nil <*> R, ot,c)
  | fusion2' f t1 t2 sc = f t1 t2 sc

fun monop head opr = fusion  (head (put opr #> pop_put)  #> put "\n")
fun binop head opr = fusion2 (head (put opr #> pop_put2) #> put "\n")
fun monop' head opr = fusion' (fn ty => head (put opr #> pop_put' ty) #> put "\n")
fun binop' head opr = fusion2' (fn t1 => fn t2 => head (put opr #> pop_put2' t1 t2) #> put "\n")
fun binop'1 head opr ty = fusion2'(fn ty=> fn _=> head (put opr #> pop_put2'1 ty) #> put "\n") ty ty


(*Branch*)
fun br  L = put "br label " #> putL L #> put "\n"
fun br' Lt Lf = pop (fn C => put "br i1 " #> putv C #> put ", label " #> putL Lt
                                                    #> put ", label " #> putL Lf #> put "\n")

fun phi ty L1 L2 = fusion2' (fn ty => fn _ => expr (
      put "phi " #> putt ty #> put " [" #> pop_put #> put ", " #> putL L1
                          #> put "], [" #> pop_put #> put ", " #> putL L2 #> put "]\n")) ty ty


(*Pair*)
val op_pair_gen   = pop (fn A => pop (fn B => push (B <*> A)))
val op_depair_gen = pop (fn (A <*> B) => push B #> push A)
val trunc_tail = map_ssa (fn (A <*> R) => A)  ;  val mk_tail = map_ssa (fn S => S <*> Nil)


(*Tuple & Index*)
val put_idx  = fold_rev (fn i => put ", "     #> put (string_of_int i))
val put_idx' = fold_rev (fn i => put ", i32 " #> put (string_of_int i))
fun expr_idx idx G = expr (G #> put_idx idx);    fun expr_idx' idx G = G #> put_idx idx

fun op_get_tuple_gen idx T = monop' (expr_idx idx) "extractvalue " (T_tup T)
fun op_set_tuple_gen idx T = binop' (expr_idx idx) "insertvalue "  (T_tup T)

fun cons_tup gen i (T_nil <%> TR) (_ <*> SR) = cons_tup gen i TR SR
  | cons_tup gen i (T <%> TR)     (S <*> SR) = push S #> cons_tup gen (i+1) TR SR #> gen i T
  | cons_tup gen i T_nil          _ = push (Literal "undef")
  | cons_tup gen i T              S = push S #> push (Literal "undef") #> gen i T
fun dest_tup gen i (T_nil <%> TR) S = push Nil #> dest_tup gen i TR S #> op_pair_gen
  | dest_tup gen i (T <%> TR)     S = push S #> gen i #> dest_tup gen (i+1) TR S #> op_pair_gen
  | dest_tup gen i T_nil          S = push Nil
  | dest_tup gen i T              S = push S #> gen i

fun op_cons_tup_gen T = pop (cons_tup (fn i => binop' (expr_idx [i]) "insertvalue "  (T_tup T)) 0 T)
fun op_dest_tup_gen T = pop (dest_tup (fn i => monop' (expr_idx [i]) "extractvalue " (T_tup T)) 0 T)


(*Cast*)
fun cast opr T T' = expr (put opr #> pop_put' T #> put " to " #> putt T' #> put "\n")
val bitcast = cast "bitcast "
fun ptr2size_t T = cast "ptrtoint " (T_PTR T) SizeT


(*Def func*)
fun arguments T_nil = push Nil
  | arguments (t1 <%> t2) = arguments t1 #> arguments t2 #> op_pair_gen
  | arguments _ = assign (push o Reg)
fun returns T_nil = put "ret void"  |  returns (ty <%> T_nil) = put "ret " #> pop_put' ty
  | returns ty = mk_tail #> op_cons_tup_gen ty #> put "ret " #> pop_put' (T_tup ty)
fun putT (t <%> T_nil) = putt t | putT (t as (_ <%> _)) = putt (T_tup t) | putT t = putt t

fun funtab M G (ssa,out,(cnt,lcnt,bb,ftab)) = G ftab (ssa,out,(cnt,lcnt,bb,M ftab))
fun gen_func name arg ret gen ftab = (Nil,[],(0,1,0,ftab))
  |> (put "define " #> putT ret #> put " @" #> put name #> put "(" #> putt arg #> put ") nounwind {\n"
        #> arguments arg #> trunc_tail #> assign (set_bb o ~) #> gen #> returns ret #> put "\n}\n\n")
  |> funtab I (fn ftab' => get_output (fn O => fn _ => Symtab.update_new (name, O) ftab'))

fun def_func name arg ret gen (c as (_,_,(_,_,_,ftab))) =
  if Symtab.defined ftab name then (name,c) else (name, funtab (gen_func name arg ret gen) (K I) c)


fun output_list file txts = List.app (fn txt => BinIO.output (file, Byte.stringToBytes txt)) txts
fun print_file c = File.open_output (fn F => print (output_list F) c)
fun codegen gen = print_file (gen (Nil,[],(0,1,0,Symtab.empty)))

(*Debug*)
(* val fake = (Reg 21 <*> Nil, [], (4,1,0,Symtab.empty)) *)

end
