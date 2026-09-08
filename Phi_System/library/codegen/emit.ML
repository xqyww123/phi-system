structure Phi_CG_Emit = struct

type cfg = {lang: string}

fun tr_name #"\\" = "" | tr_name #"<" = "" | tr_name #">" = "_" | tr_name c = str c
val tr_str = String.translate tr_name

fun w s buffer = s :: buffer
val wi = w o string_of_int
val w' = w o tr_str
val ws = w o ML_Syntax.print_string
fun wstr ss buffer = "\"" :: (ss @ ("\"" :: buffer))
fun w_ty name = w' (String.substring (name, 1, String.size name - 1))

(* fun uniq_id (c:cfg') b = wstr [string_of_int (length b), ".", (#1 c)] b *)

fun w_const (c:string * cfg) name =
  case String.fields (fn c => c = #".") name of (h::l) =>
    if h = #1 c then w' (String.concatWith "_'_" l) #> w "_"
    else w (#lang (#2 c)) #> w "'G_" #> w' name #> w "_"

fun gen_typ (c:string * cfg) (Type (name, tys)) =
      w (#lang (#2 c)) #> w "'G_" #> w' name #> w "_T" #> fold (fn ty => w " (" #> gen_typ c ty #> w ")") tys
  | gen_typ _ (TFree (name, _))   = w_ty name #> w "_t"
  | gen_typ _ (TVar ((name,i),_)) = w_ty name #> w "_t" #> wi i

(*A symbol term is a per-process numeral (Performant_Isabelle_HOL.SSymb) whose only
  sanctioned exit is Phi_Tool_Symbol.dest_symbol; the emitter wants the identifier it
  stands for, as a string literal, so symbols are caught before the generic clauses.*)
fun gen_tm bi c tm =
  (case Phi_Tool_Symbol.dest_symbol tm
     of SOME s => wstr [s]
      | NONE => gen_tm' bi c tm)
and gen_tm' bi c (Const ("Pure.type", Type ("itself", [ty]))) = gen_typ c ty
  | gen_tm' bi c (Const (@{const_name LABEL_TAG}, _) $ (Abs (s,_,_))) = wstr [s]
  (* | compile_body bi c (Const (@{const_name UNIQ_ID}, _)) = uniq_id c *)
  | gen_tm' bi c (Const (name,_)) = w_const c name
  | gen_tm' bi c (Free (name,_)) = w' name #> w "_v"
  | gen_tm' bi c (Var ((name,i),_)) = w' name #> w "_v" #> wi i
  | gen_tm' bi c (Bound i) = w "b" #> wi (bi - i)
  | gen_tm' bi c (Abs (_,T,body))
      = w "(fn " #> binder c bi T #> w " => " #> gen_tm (bi+1) c body #> w ")"
  | gen_tm' bi c (A $ B) = gen_tm bi c A #> w " (" #> gen_tm bi c B #> w ")"
(*the ML name of the variable bound at depth bi+1: a TYPE binder is named after its type, which is
  how the body spells it, any other binder by its depth*)
and binder c _  (Type ("itself", [ty])) = gen_typ c ty
  | binder _ bi _ = w "b" #> wi (bi+1)

(*The _K hook of a parameter type, named from its head constructor like the _T hook of a type
  (its arguments ignored); a TYPE parameter by the sort of its variable, len or FIX_ARITY_VALs;
  NONE for a bare type variable, which has no text.*)
fun gen_key thy c T =
  let fun hook name = w (#lang (#2 c)) #> w "'G_" #> w' name #> w "_K"
      fun by_sort S =
        if Sign.subsort thy (S, ["Type_Length.len"]) then SOME (hook "Type_Length.len")
        else if Sign.subsort thy (S, [@{class FIX_ARITY_VALs}]) then SOME (hook @{class FIX_ARITY_VALs})
        else NONE
   in case T of Type ("itself", [TFree (_, S)]) => by_sort S
              | Type ("itself", [TVar (_, S)]) => by_sort S
              | Type (name, _) => SOME (hook name)
              | _ => NONE
  end

(*A definition made inside a context is \<open>c x\<^sub>1 \<dots> x\<^sub>n \<equiv> \<lambda>y\<^sub>1 \<dots> y\<^sub>m. body\<close>: the x\<^sub>i are the
  context's parameters (schematic variables), the y\<^sub>j the closure's, the last of them being the
  run-time argument when the procedure's binder record says so.  It is emitted as the ML function
  of all of them; when the body is a procedure, the body is wrapped by Phi_CG.frame so that its
  instance name, made of the parameters' texts, names the C function.*)
fun gen_proc ctxt c thm =
  let val thy = Context.theory_of ctxt
      fun err () = raise THM ("the code emitter needs a definition of the form \<open>c x\<^sub>1 \<dots> x\<^sub>n \<equiv> body\<close>", 0, [thm])
      fun ctxt_param (Var ((name,i),T)) = (w' name #> w "_v" #> wi i, T)
        | ctxt_param (Free (name,T))    = (w' name #> w "_v", T)
        | ctxt_param _ = err ()
      fun strip bi (Abs (_, T, B)) = strip (bi+1) B |> (fn (ps, bi', B') => ((binder c bi T, T) :: ps, bi', B'))
        | strip bi t = ([], bi, t)
      fun key (v, T) = case gen_key thy c T of SOME h => h #> w " (" #> v #> w ")" | NONE => w "Phi_CG.pair NONE"
      fun keys [] = I | keys (k::ks) = k #> fold (fn k' => w "," #> k') ks
      fun lambda (v, _) body = w "(fn " #> v #> w " => " #> body #> w ")"
   in case Thm.concl_of thm
   of Const ("Pure.eq",_) $ LHS $ B =>
        (case Term.strip_comb LHS
           of (Const (name, _), args) =>
                let val (bs, bi, body) = strip ~1 B
                    val has_arg = Phi_Procedure.has_runtime_arg ctxt name
                    val (params, arg) =
                      if has_arg = SOME true andalso not (null bs)
                      then (map ctxt_param args @ take (length bs - 1) bs, SOME (List.last bs))
                      else (map ctxt_param args @ bs, NONE)
                    val rest = (case arg of SOME a => lambda a (gen_tm bi c body) | NONE => gen_tm bi c body)
                    val wrapper =
                      case (has_arg, try (Phi_Syntax.dest_procT_params o Term.fastype_of1) (rev (map snd bs), body))
                        of (SOME true,  SOME [])  => SOME "Phi_CG.frame'"
                         | (SOME false, SOME [_]) => SOME "Phi_CG.frame'"
                         | (SOME false, SOME [])  => SOME "Phi_CG.frame"
                         | _ => NONE
                    val wrapped = (case wrapper of NONE => rest
                      | SOME f => w f #> w " (Phi_CG.mangle " #> ws name #> w " [" #> keys (map key params) #> w "]) (" #> rest #> w ")")
                 in w "val " #> w_const c name #> w " = " #> fold_rev lambda params wrapped #> w "\n" end
            | _ => err ())
    | _ => err ()
  end

fun gen_extractor ctxt (c:cfg) open_self path intrfs procs thyname =
  let val c' = (thyname, c)
      val CG = w "val _ = Phi_" #> w (#lang c) #> w "'G.codegen " #> ws (path ^ "." ^ #lang c) #> w " (I"
        #> fold (fn (eN,tm) => w" #> Phi_CG.interf " #> wstr[eN] #> w" (" #> gen_tm ~1 c' tm #> w")") intrfs #> w")\n"
      val gen = w "structure " #> w (#lang c) #> w "'G_" #> w thyname #> w " = struct\n"
        #> open_self ? (w "open " #> w (#lang c) #> w "'G_" #> w thyname #> w "\n")
        #> fold (gen_proc ctxt c') procs
        #> not (null intrfs) ? CG #> w "end\n"
  in String.concat (rev (gen [])) end

fun codegen c os p i ps t ctxt = ML_Context.expression Position.none (ML_Lex.read (gen_extractor ctxt c os p i ps t)) ctxt

end
