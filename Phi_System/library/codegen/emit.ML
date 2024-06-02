structure Phi_CG_Emit = struct

type config = {name_space: string}
fun w s buffer = s :: buffer  ;  fun wi i = w (string_of_int i)
fun tr_name #"\\" = "" | tr_name #"<" = "" | tr_name #">" = "_" | tr_name c = str c
val w' = w o String.translate tr_name
fun wstr ss buffer = "\"" :: (ss @ ("\"" :: buffer))
fun w_ty name = w' (String.substring (name, 1, String.size name - 1))
fun uniq_id (c:config) b = wstr [string_of_int (length b), ".", (#name_space c)] b

fun w_const (c:config) name =
  case String.fields (fn c => c = #".") name of (h::l) =>
    if h = #name_space c then w' (String.concatWith "_'_" l) #> w "_gen"
    else w "CG_" #> w' name #> w "_gen"

fun gen_typ (Type (name, tys))
      = w' name #> w "_gen" #> fold (fn ty => w " (" #> gen_typ ty #> w ")") tys
  | gen_typ (TFree (name, _))   = w_ty name #> w "_t"
  | gen_typ (TVar ((name,i),_)) = w_ty name #> w "_t" #> wi i

fun gen_body bi c (Const ("Pure.type", Type ("itself", [ty]))) = gen_typ ty
  | gen_body bi c (Const (@{const_name LABEL_TAG}, _) $ (Abs (s,_,_))) = wstr [s]
  (* | compile_body bi c (Const (@{const_name UNIQ_ID}, _)) = uniq_id c *)
  | gen_body bi c (Const (name,_)) = w_const c name
  | gen_body bi c (Free (name,_)) = w' name #> w "_v"
  | gen_body bi c (Var ((name,i),_)) = w' name #> w "_v" #> wi i
  | gen_body bi c (Bound i) = w "b" #> wi (bi - i)
  | gen_body bi c (Abs (_,Type ("itself", [ty]),body))
      = w "(fn " #> gen_typ ty #> w " => " #> gen_body (bi+1) c body #> w ")"
  | gen_body bi c (Abs (_,_,body))
      = w "(fn b" #> wi (bi+1) #> w " => " #> gen_body (bi+1) c body #> w ")"
  | gen_body bi c (A $ B) = gen_body bi c A #> w " (" #> gen_body bi c B #> w ")"

fun gen_proc' c (Const ("Pure.eq",_) $ Const (name, _) $ B)
      = w "val " #> w_const c name #> w " = " #> gen_body 0 c B #> w "\n"

fun gen_proc c = gen_proc' c o Thm.prop_of

fun gen_extractor thy =
  let val c = {name_space = Context.theory_name {long=false} thy}
      val gen = w "structure CG_" #> w (Context.theory_name {long=false} thy) #> w " = struct\n"
        #> fold (gen_proc c o Phi_Procedure.compilation_thm_of thy)
              (Phi_Procedure.procedures_of (Context.Theory thy) |> rev)
        #> w "val gen = I"
        #> Symtab.fold (fn (eN, pN) => w " #> CGSys.F " #> wstr [eN] #> w " " #> w_const c pN)
                       (Phi_Procedure.interfaces_of thy)
        #> w "\nend"
  in String.concat (rev (gen [])) end



end
