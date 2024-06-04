structure Phi_CG_Emit = struct

type config = {name_space: string}
fun w s buffer = s :: buffer  ;  fun wi i = w (string_of_int i)
fun tr_name #"\\" = "" | tr_name #"<" = "" | tr_name #">" = "_" | tr_name c = str c
val tr_str = String.translate tr_name; val w' = w o tr_str
fun wstr ss buffer = "\"" :: (ss @ ("\"" :: buffer))
fun w_ty name = w' (String.substring (name, 1, String.size name - 1))
fun uniq_id (c:config) b = wstr [string_of_int (length b), ".", (#name_space c)] b

fun w_const (c:config) name =
  case String.fields (fn c => c = #".") name of (h::l) =>
    if h = #name_space c then w' (String.concatWith "_'_" l) #> w "_"
    else w "CG_" #> w' name #> w "_"

fun gen_typ (Type (name, tys))
      = w "CG_" #> w' name #> w "_T" #> fold (fn ty => w " (" #> gen_typ ty #> w ")") tys
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

fun gen_extractor oself thy =
  let val c = {name_space = Context.theory_name {long=false} thy}
      val tab = Phi_Procedure.interfaces_of thy
      val CG = w "val _ = Phi_CG.codegen \"" #> w (#name_space c) #> w "\" ("
        #> Symtab.fold (fn (eN,pN) => w " #> Phi_CG.interf " #> wstr[eN] #> w " " #> w_const c pN) tab #> w ")\n"
      val gen = w "structure CG_" #> w (Context.theory_name {long=false} thy) #> w " = struct\n"
        #> oself ? (w "open CG_" #> w (Context.theory_name {long=false} thy) #> w "\n")
        #> fold (gen_proc c) (Phi_Procedure.procedures_of (Context.Theory thy) |> rev)
        #> not (Symtab.is_empty tab) ? CG #> w "end\n"
      val src = String.concat (rev (gen []))
  in tracing src; src end

val export_code = Attrib.setup_config_bool \<^binding>\<open>\<phi>export_code\<close> (K false)

fun codegen oself thy = let val src = gen_extractor oself thy
      in ML_Context.expression Position.none (ML_Lex.read src) end

structure Generated = Theory_Data (
  type T = Symtab.set; val empty = Symtab.empty; val merge = Symtab.merge (K true) )

val _ = Theory.setup (Theory.at_end (fn thy =>
  let val name = Context.theory_name {long=false} thy
   in if Config.get_global thy export_code andalso Symtab.defined (Generated.get thy) name
   then SOME (Context.theory_map (codegen false thy) thy |> Generated.map (Symtab.insert_set name)) else NONE end))


end
