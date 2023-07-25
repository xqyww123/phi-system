(* Building Cache *)

signature PHI_CACHE_DB = sig

type proof_id = Phi_ID.encoded_ID
type proof_cache = Time.time * string
type cache = {proofs: proof_cache Symtab.table,
              async_tasks: Task_Queue.task list}

val get_cache : theory -> cache
val force_reload : theory -> cache
val register_async_task : Task_Queue.task -> theory -> unit

val store_cache : theory -> unit
val store_and_close_cache : theory -> unit
val invalidate_cache : theory -> unit
val invalidate_proof_cache : bool (*whether warn*) -> proof_id -> theory -> unit
(* val check_cache : string (*Document_ID*) -> Proof.context -> unit *)
val report_cache_is_outdated : bool (*whether warn*) -> theory -> unit

val get_cached_proof : theory -> proof_id -> (Time.time * string) option
val update_cached_proof : theory -> proof_id * (Time.time * string) -> unit

end


structure Phi_Cache_DB : PHI_CACHE_DB = struct

type proof_id = string
type proof_cache = Time.time * string
type cache = {proofs: (Time.time * string) Symtab.table,
              async_tasks: Task_Queue.task list}

val empty_cache = {proofs = Symtab.empty, async_tasks = []} : cache

fun cache_update_proof (id,s) ({proofs, async_tasks}:cache)
      = {proofs = Symtab.update (id,s) proofs,
         async_tasks = async_tasks} : cache

fun cache_invalidate_proof id ({proofs,async_tasks}:cache)
      = {proofs = Symtab.delete_safe id proofs (*Symtab.fold (fn (k,_) =>
                      if Phi_ID.dep id k
                      then Symtab.delete k
                      else I) proofs proofs*),
         async_tasks = []
        } : cache

fun cache_add_async task ({proofs,async_tasks}:cache)
      = {proofs = proofs, async_tasks = task :: async_tasks} : cache

local open XML in

fun encode_cache ({proofs, ...} : cache) =
  Elem (("cache", []), [
    Elem (("proofs",[]),
      Symtab.fold (fn (id,(t,prf)) => fn L =>
          Elem (("prf",[]),
                [Text (String.concatWith "|" [id,string_of_int (Time.toMilliseconds t),prf])])
          :: L)
        proofs [])
  ])

fun decode_cache (Elem (("cache", []), [
      Elem (("proofs",[]), entries)
    ]))
  = { proofs = fold (fn Elem (("prf",[]), [Text s]) =>
                  let val [id,t',prf] = String.fields (fn c => c = #"|") s
                   in Symtab.update (id, (Time.fromMilliseconds (Value.parse_nat t'), prf))
                  end)
               entries Symtab.empty,
      async_tasks = []
    } : cache

end

fun cache_path thy = 
      Path.append (Resources.master_directory thy) (Path.basic (Context.theory_name thy))
   |> Path.ext "phi-cache"

val openning_caches : (cache * bool) Symtab.table Synchronized.var
  = Synchronized.var "\<phi>-System.openning_caches" Symtab.empty

fun load_cache_raw thy =
  let val path = cache_path thy
   in if File.is_file path
      then decode_cache (XML.parse (Bytes.read path |> XZ.uncompress |> Bytes.content))
           handle er => (
             warning ("corrupted cache : " ^ Context.theory_name thy ^ "\n" ^
                      Runtime.exn_message er);
             empty_cache)
      else empty_cache
  end

fun force_reload thy =
  Synchronized.change_result openning_caches (fn tab =>
    let val c = load_cache_raw thy
     in (c, Symtab.update (Context.theory_name thy, (c, false)) tab) end )

fun get_cache_i thy tab =
  case Symtab.lookup tab (Context.theory_name thy)
      of SOME (x, _) => (x, tab)
       | _ => let val c = load_cache_raw thy
               in (c, Symtab.update_new (Context.theory_name thy, (c, false)) tab) end

fun get_cache thy =
  Synchronized.change_result openning_caches (get_cache_i thy)

fun register_async_task task thy =
  let val name = Context.theory_name thy
   in Synchronized.change openning_caches (fn tab =>
      case Symtab.lookup tab name
        of SOME (c, flag) => Symtab.update (name, (cache_add_async task c, flag)) tab
         | _ => let val c = cache_add_async task (load_cache_raw thy)
                 in Symtab.update_new (name, (c, false)) tab end )
  end

fun store_cache' tab thy =
  case Symtab.lookup tab (Context.theory_name thy)
    of SOME (c, changed) =>
        if changed
        then Bytes.write (cache_path thy) (XZ.compress (Bytes.string (
              XML.string_of (encode_cache c))))
        else ()
     | _ => ()


fun store_cache thy = store_cache' (Synchronized.value openning_caches) thy

fun store_and_close_cache thy =
  Synchronized.change openning_caches (fn tab =>
    (store_cache' tab thy;
     Symtab.delete_safe (Context.theory_name thy) tab))

fun invalidate_cache thy =
  Synchronized.change openning_caches (Symtab.update (Context.theory_name thy, (empty_cache, true)))

fun get_cached_proof thy = Symtab.lookup (#proofs (get_cache thy))

fun update_cached_proof thy (id,s) =
  Synchronized.change openning_caches (fn tab => (
    get_cache_i thy tab;
    Symtab.map_entry (Context.theory_name thy)
                     (fn (c, _) => (cache_update_proof (id,s) c, true)) tab
  ))

fun report_cache_is_outdated warn thy =
  if Phi_Envir.runtime_mode () = Phi_Envir.PRODUCTION
  then error   ("Proof cache for theory " ^ Context.theory_name thy ^ " is outdated!")
  else if warn
       then warning ("Proof cache for theory " ^ Context.theory_name thy ^ " is outdated!")
       else ()

fun invalidate_proof_cache warn id thy =
 (report_cache_is_outdated warn thy;
  Synchronized.change openning_caches (fn tab => (
    get_cache_i thy tab;
    Symtab.map_entry (Context.theory_name thy) (fn (c, _) => (cache_invalidate_proof id c, true)) tab
 )))

(** Document_ID of each construct to detect if caches are invalid **)
(*
val doc_ids : string Phi_ID.Tab.table Synchronized.var
      = Synchronized.var "\<phi>-System.doc_ids" Phi_ID.Tab.empty

fun check_cache' construct doc_id thy =
  let fun clean_tab tab =
            Phi_ID.Tab.fold (fn (k,_) =>
              if Phi_ID.dep' construct k
              then Phi_ID.Tab.delete k
              else I) tab tab
   in if null (snd construct)
         orelse (Synchronized.change_result doc_ids (fn tab =>
            case Phi_ID.Tab.lookup tab construct
              of SOME id' =>
                  if id' = doc_id
                  then (true , tab)
                  else (false, Phi_ID.Tab.update (construct, doc_id) (clean_tab tab))
               | _ =>  (true , Phi_ID.Tab.update (construct, doc_id) tab)))
      then ()
      else invalidate_proof_cache (Phi_ID.encode construct) thy
  end

fun check_cache doc_id ctxt =
  case Phi_ID.get ctxt
    of SOME phid => check_cache' phid doc_id (Proof_Context.theory_of ctxt)
     | _ => () *)

(*TODO: maybe we need some way to clean up unused cache entries.*)


val _ = Theory.setup (Theory.at_end (fn thy => (
  if Phi_Envir.runtime_mode () = Phi_Envir.PRODUCTION then ()
  else let val tasks = #async_tasks (get_cache thy)
        in if null tasks then store_and_close_cache thy
           else (tracing "There are asynchronous proof tasks. The proof cache will be written \
                         \once they are finished." ;
                 Future.forks {name="\<phi>System.store_cache", group=NONE, deps = tasks, pri=1, interrupts=false}
                  [(fn _ => (store_and_close_cache thy;
                             tracing "The proof cache has been written."))] ;
                ())
        end
  ; NONE)))

end