signature SIMPSET_CONFIGURE = sig

datatype initial_ss_configure = Empty_SS (*containing nothing*)
                              | Empty_SS_configure of (Proof.context -> Proof.context)
                              | Minimal_SS (*containing necessary elements to enable minimal usage*)
                              | Minimal_SS_configure of (Proof.context -> Proof.context)
                              | Give_SS of simpset

val initial_ss_of : initial_ss_configure -> simpset

end

signature SIMPSET = sig

val get : Context.generic -> simpset
val get': Proof.context -> simpset
val equip : Proof.context -> Proof.context
(*merge the current simpset by this simpet*)
val enhance : Proof.context -> Proof.context

val map : (Proof.context -> Proof.context) -> Context.generic -> Context.generic
val map' : (Proof.context -> Proof.context) -> Proof.context -> Proof.context
val print : Proof.context -> bool -> unit
val simp_rules: Proof.context -> thm list

val add_simps: thm list -> Context.generic -> Context.generic
val add_simps': thm list -> Proof.context -> Proof.context
val del_simps: thm list -> Context.generic -> Context.generic

end

structure Simpset_Configure : SIMPSET_CONFIGURE = struct
datatype initial_ss_configure = Empty_SS (*containing nothing*)
                              | Empty_SS_configure of (Proof.context -> Proof.context)
                              | Minimal_SS (*containing necessary elements to enable minimal usage*)
                              | Minimal_SS_configure of (Proof.context -> Proof.context)
                              | Give_SS of simpset
fun initial_ss_of Empty_SS =
      let val ctxt = Context.the_local_context ()
       in Simplifier.simpset_map ctxt (Simplifier.set_mksimps (Simpdata.mksimps Simpdata.mksimps_pairs))
                                       Simplifier.empty_ss
      end
  | initial_ss_of (Empty_SS_configure cfg) =
      Simplifier.simpset_map (Context.the_local_context ()) cfg Simplifier.empty_ss
  | initial_ss_of Minimal_SS =
      Raw_Simplifier.simpset_of (Raw_Simplifier.clear_simpset (Context.the_local_context ()))
  | initial_ss_of (Minimal_SS_configure cfg) =
      Simplifier.simpset_map (Context.the_local_context ()) cfg
          (Raw_Simplifier.simpset_of (Raw_Simplifier.clear_simpset (Context.the_local_context ())))
  | initial_ss_of (Give_SS ss) = ss
end

functor Simpset(Config : sig
  val initial_ss : Simpset_Configure.initial_ss_configure
  val binding : binding option
  val comment : string
  val attribute : (attribute -> attribute -> attribute context_parser) option (*a way extending the default attribute*)
  val post_merging : Proof.context -> Proof.context (*A way to override existing settings like removing a congruence rule.*)
end) : SIMPSET = struct

structure Data = Generic_Data (
  type T = simpset
  val empty = Simpset_Configure.initial_ss_of Config.initial_ss
  val merge = Raw_Simplifier.merge_ss
)

val get = Data.get
val get' = get o Context.Proof

fun equip ctxt = Raw_Simplifier.put_simpset (get' ctxt) ctxt
fun enhance ctxt =
  Simplifier.put_simpset (Simplifier.merge_ss (Simplifier.simpset_of ctxt, get' ctxt)) ctxt
    |> Config.post_merging

fun map f generic = Data.map (Raw_Simplifier.simpset_map (Context.proof_of generic) f) generic
fun map' f = Context.proof_map (map f)
fun map_with_result f generic =
  let val ss = Data.get generic
      val (result,ctxt') = Simplifier.put_simpset ss (Context.proof_of generic) |> f
   in (result, Data.put (Simplifier.simpset_of ctxt') generic) end

structure Thms = Named_Thms (
  val name = the_default Binding.empty Config.binding
  val description = Config.comment
)

val simp_rules = Thms.get

fun add_simps thms = map_with_result (fn ctxt =>
          (maps (Simplifier.mksimps ctxt) thms, ctxt addsimps thms)
        ) #-> fold Thms.add_thm
val add_simps' = Context.proof_map o add_simps
fun del_simps thms = map_with_result (fn ctxt =>
          (maps (Simplifier.mksimps ctxt) thms, ctxt delsimps thms)
        ) #-> fold Thms.del_thm

val add = Thm.declaration_attribute (fn th => add_simps [th])
val del = Thm.declaration_attribute (fn th => del_simps [th])

val _ = (
  case Config.binding of SOME B =>
    Theory.setup ( Attrib.setup B (the_default Attrib.add_del Config.attribute add del) Config.comment
                #> Global_Theory.add_thms_dynamic (B, Thms.get o Context.proof_of))
    | _ => ())

fun print ctxt verbose =
  writeln (Pretty.string_of (Simplifier.pretty_simpset verbose (equip ctxt)))

end

(***Predefined Simpsets***)

structure Phi_Safe_Simps = Simpset (
  val initial_ss = Simpset_Configure.Empty_SS
  val binding = SOME \<^binding>\<open>\<phi>safe_simp\<close>
  val comment = "Safe simpification rules for evaluation or simple goals"
  val attribute = NONE
  val post_merging = I
)
