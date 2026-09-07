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
  | gen_tm' bi c (Abs (_,Type ("itself", [ty]),body))
      = w "(fn " #> gen_typ c ty #> w " => " #> gen_tm (bi+1) c body #> w ")"
  | gen_tm' bi c (Abs (_,_,body))
      = w "(fn b" #> wi (bi+1) #> w " => " #> gen_tm (bi+1) c body #> w ")"
  | gen_tm' bi c (A $ B) = gen_tm bi c A #> w " (" #> gen_tm bi c B #> w ")"

(*A definition made inside a context is \<open>c x\<^sub>1 \<dots> x\<^sub>n \<equiv> body\<close> with the context's parameters
  x\<^sub>i as schematic variables; it is emitted as the ML function of those parameters.*)
fun gen_proc c thm =
  let fun param (Var ((name,i),_)) = w "(fn " #> w' name #> w "_v" #> wi i #> w " => "
        | param (Free (name,_))    = w "(fn " #> w' name #> w "_v" #> w " => "
        | param _ = raise THM ("the code emitter needs a definition of the form \<open>c x\<^sub>1 \<dots> x\<^sub>n \<equiv> body\<close>", 0, [thm])
   in case Thm.concl_of thm
   of Const ("Pure.eq",_) $ LHS $ B =>
        (case Term.strip_comb LHS
           of (Const (name, _), args) =>
                w "val " #> w_const c name #> w " = " #> fold param args #> gen_tm ~1 c B
                #> fold (fn _ => w ")") args #> w "\n"
            | _ => raise THM ("the code emitter needs a definition of the form \<open>c x\<^sub>1 \<dots> x\<^sub>n \<equiv> body\<close>", 0, [thm]))
    | _ => raise THM ("the code emitter needs a definition of the form \<open>c x\<^sub>1 \<dots> x\<^sub>n \<equiv> body\<close>", 0, [thm])
  end

fun gen_extractor (c:cfg) open_self path intrfs procs thyname =
  let val c' = (thyname, c)
      val CG = w "val _ = Phi_" #> w (#lang c) #> w "'G.codegen " #> ws (path ^ "." ^ #lang c) #> w " (I"
        #> Symtab.fold (fn (eN,tm) => w" #> Phi_CG.interf " #> wstr[eN] #> w" (" #> gen_tm ~1 c' tm #> w")") intrfs #> w")\n"
      val gen = w "structure " #> w (#lang c) #> w "'G_" #> w thyname #> w " = struct\n"
        #> open_self ? (w "open " #> w (#lang c) #> w "'G_" #> w thyname #> w "\n")
        #> fold (gen_proc c') procs
        #> not (Symtab.is_empty intrfs) ? CG #> w "end\n"
  in String.concat (rev (gen [])) end

fun codegen c os p i ps t = ML_Context.expression Position.none (ML_Lex.read (gen_extractor c os p i ps t))

end
