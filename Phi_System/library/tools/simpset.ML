signature SIMPSET_CONFIGURE = sig

datatype initial_ss_configure = Empty_SS (*containing nothing*)
                              | Minimal_SS (*containing necessary elements to enable minimal usage*)
                              | Give_SS of simpset

val initial_ss_of : initial_ss_configure -> simpset

end

signature SIMPSET = sig

val get : Context.generic -> simpset
val get': Proof.context -> simpset
val equip : Proof.context -> Proof.context
val map : (Proof.context -> Proof.context) -> Context.generic -> Context.generic
val print : Proof.context -> bool -> unit

end

structure Simpset_Configure : SIMPSET_CONFIGURE = struct
datatype initial_ss_configure = Empty_SS (*containing nothing*)
                              | Minimal_SS (*containing necessary elements to enable minimal usage*)
                              | Give_SS of simpset
fun initial_ss_of Empty_SS =
      let val ctxt = Context.the_local_context ()
          val mksimps = Raw_Simplifier.mksimps ctxt
       in Raw_Simplifier.simpset_map ctxt (Raw_Simplifier.set_mksimps (K mksimps))
                                          Raw_Simplifier.empty_ss
      end
  | initial_ss_of Minimal_SS =
      Raw_Simplifier.simpset_of (Raw_Simplifier.clear_simpset (Context.the_local_context ()))
  | initial_ss_of (Give_SS ss) = ss
end

functor Simpset(Config : sig
  val initial_ss : Simpset_Configure.initial_ss_configure
  val binding : binding
  val comment : string
end) : SIMPSET = struct

structure Data = Generic_Data (
  type T = simpset
  val empty = Simpset_Configure.initial_ss_of Config.initial_ss
  val merge = Raw_Simplifier.merge_ss
)

val get = Data.get
val get' = get o Context.Proof
fun equip ctxt = Raw_Simplifier.put_simpset (get' ctxt) ctxt

fun map f generic = Data.map (Raw_Simplifier.simpset_map (Context.proof_of generic) f) generic

val add = Thm.declaration_attribute (fn th => map (fn ctxt => ctxt addsimps [th]))
val del = Thm.declaration_attribute (fn th => map (fn ctxt => ctxt delsimps [th]))

val _ = Theory.setup (Attrib.setup Config.binding (Attrib.add_del add del) Config.comment)

fun print ctxt verbose =
  writeln (Pretty.string_of (Simplifier.pretty_simpset verbose (equip ctxt)))

end

