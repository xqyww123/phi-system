structure TyCG_NuSys = struct val void = NuCG.T_nil end

structure NuCG_NuSys = struct open NuCG infixr 6 <*> <%>

(* Structural *)
val op_dup_gen = pop (fn X => push X #> push X)
val op_drop_gen = pop (K I)
val op_let_gen = pop
val op_local_value_gen = push
fun op_sel_gen ty = pop (fn C => binop' expr ("select i1 " ^ to_s C ^ ", ") ty ty)

fun op_if_gen ty brT brF = assign_label (fn Lt => assign_label (fn Lf => assign_label (fn Lx =>
  br' Lt Lf #> put_bb Lt #> get_ssa (fn s0 => brT #> get_bb (fn Lt' => br Lx #> get_ssa (fn sT => 
               put_bb Lf #> map_ssa (K s0) #> brF #> get_bb (fn Lf' => br Lx #> get_ssa (fn sF =>
               put_bb Lx #> map_ssa (K (sT <*> sF <*> Nil)) #> phi ty Lt' Lf' #> trunc_tail))))))))

val swap = pop (fn A => pop (fn B => push A #> push B))
fun subst Nil = push Nil  |  subst (a <*> b) = subst b #> subst a #> swap #> op_pair_gen
  | subst s = assign (push o Reg)
fun op_do_while_gen ty body = assign_label (fn L1 => assign_label (fn Lx => get_bb (fn L0 =>
  (*L0: the previous block before the loop; L1: main loop body; Lx: exit of the loop *)
  br L1 #> put_bb L1 #> get_ssa (fn S0 => get_output (fn O0 => map_output (K [])
  (*The phi nodes merge initial registers and results of the loop. Because the results are currently
  * unavailable, we count the number of phi nodes and reserve the indecies, and remembering
  * the initial registers S0, index count N0, output O0, enter the printing of body firstly. *)
  #> counter I (fn N0 => subst S0 #> trunc_tail #> body #> br' L1 Lx #> get_bb (fn L1' => put_bb Lx
  (*After the body is printed, acquiring the final registers S1, index count N1, output O1,
  * we by resuming back to the initial state S0, N0, O0, generate those absent phi nodes. *)
  #> get_ssa (fn S1 => get_output (fn O1 => map_output (K O0)
       #> counter (K N0) (fn N1 => map_ssa (K (S0 <*> S1 <*> Nil)) #> phi ty L0 L1' #> trunc_tail
  (*At last replenish the output of loop body O1 and return to final state N1, S1*)
  #> map_output (fn O0' => O1 @ O0') #> counter (K N1) (K I) #> map_ssa (K S1)))))))))))

fun op_recursion_gen name arg ret gen = def_func name arg ret (gen (pair name))

(* Arithmetics *)
fun pow x n y = if n = 0 then y else pow x (n-1) (x*y)
val size_cap = pow 2 size_t 1
fun op_const_int_gen b x = push (Literal (string_of_int x))
fun op_const_size_t_gen x = if x >= size_cap then raise Fail "size_t: overflow"
                            else push (Literal (string_of_int x))
fun op_add_gen b = binop expr ("add i" ^ string_of_int b ^ " ")
fun op_sub_gen b = binop expr ("sub i" ^ string_of_int b ^ " ")
fun op_mul_gen b = binop expr ("mul i" ^ string_of_int b ^ " ")
fun op_udiv_gen b= binop expr ("udiv i"^ string_of_int b ^ " ")
fun op_xor_gen b = binop expr ("xor i" ^ string_of_int b ^ " ")
fun op_not_gen b = op_const_int_gen b (pow 2 b 1 - 1) #> op_xor_gen b
fun op_lt_gen  b = binop expr ("icmp ult i" ^ string_of_int b ^ " ")
fun op_le_gen  b = binop expr ("icmp ule i" ^ string_of_int b ^ " ")
fun op_equal_gen (T as T_int _) = binop expr ("icmp eq " ^ tystr T ^ " ")
  | op_equal_gen (T_tup T) = pop (fn X => op_dest_tup_gen T #> push X #> op_dest_tup_gen T)
        #> binop'1 expr ("icmp eq ") T
  | op_equal_gen T = binop'1 expr ("icmp eq ") T


(* Tuple & Index *)
val index_here_gen = []
fun index_right_gen (i::r) = (i+1 :: r) | index_right_gen [] = [1]
fun index_left_gen r = 0::r


(* Call *)
val no_argument_gen = T_nil;    fun and_argument_gen l ty = ty <%> l

fun pop_arg T_nil = I             | pop_arg (T <%> T_nil) = pop_put' T
  | pop_arg (h <%> l) = pop_put' h #> put ", " #> pop_arg l

fun catS Nil s' = s' | catS (s <*> r) s' = s <*> (catS r s')

fun op_call_gen arg ret func =
  (if ret = T_nil then I else expr) 
    (put "call " #> putT ret #> put " @" #> func #-> put #> put "(" #> pop_arg arg #> put ")\n")
  #> (case ret of (_ <%> _ <%> _) => op_dest_tup_gen ret #> pop (map_ssa o catS) | _ => I)

val func_wrap_gen = op_call_gen

(* Memory *)
fun GEP T idx = binop' (expr_idx idx) ("getelementptr " ^ tystr T ^ ", ") (T_PTR T) SizeT
fun ptrcast T = bitcast T_ptr (T_PTR T)   ;   fun ptrcast' T = bitcast (T_PTR T) T_ptr
fun op_shift_pointer_gen T = pop (fn Sd => ptrcast T #> push Sd #> GEP T [] #> ptrcast' T)

fun size_of_gen T = expr (put "getelementptr " #> putt T #> put "* null, i32 1\n") #> ptr2size_t T

fun op_alloc_gen T = pop (fn A0 => size_of_gen T #> push A0)
      #> op_call_gen (SizeT <%> SizeT <%> T_nil) T_ptr (pair "calloc")

(*U: type of the element to be loaded; T: type of the aggregate.*)
fun op_load_gen  U T idx = ptrcast T #> monop' (expr_idx idx) ("load " ^ tystr U ^ ", ") (T_PTR T)
fun op_store_gen U T idx = swap #> ptrcast T #> binop' (expr_idx' idx) "store " U (T_PTR T)

fun Prog_Interface_gen name X Y G = def_func name X Y G #> snd


end
