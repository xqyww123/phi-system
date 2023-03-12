signature NAMED_PREMISES = sig

(*register the attributes (and also let bindings) of the given bindings directly*)
val add_bindings : (Attrib.binding * term list) list -> Proof.context -> Proof.context

(*bind leading assumptions of the subgoal with the given attributes and let bindings,
  up to the number of the given attributes*)
val bind_sequent_assms : (Attrib.binding * term list (*let bindings*)) list -> int (*goal*)
                      -> context_state -> context_state
val bindings_of : Proof.context -> term -> (Attrib.binding * term list (*let bindings*)) option list
val remove_assm_bindings : Proof.context -> int -> thm
                        -> (Attrib.binding * term list) option list * thm
val update_binding : string
                  -> (   (Attrib.binding * term list (*let bindings*))
                      -> (Attrib.binding * term list (*let bindings*)))
                  -> Proof.context -> Proof.context
val remove_bindings : string list -> Proof.context -> Proof.context

val registered : Proof.context -> string -> bool

end

structure Named_Premises : NAMED_PREMISES = struct

structure Data = Proof_Data (
  type T = (Attrib.binding * term list (*let bindings*)) Symtab.table * string (*anonymous id*)
  val init = K (Symtab.empty, "\<p>\<r>\<e>\<m>_a")
)

fun registered ctxt = Symtab.defined (fst (Data.get ctxt))

fun add_bindings bindings =
      Data.map (apfst (fold (fn X as ((B,attrs),pats) =>
        if Binding.is_empty B
        then if null attrs andalso null pats
             then I
             else error "empty binding!"
        else Symtab.update_new (Binding.name_of B, X)) bindings))

fun update_binding name f = Data.map (apfst (Symtab.map_entry name f))

fun remove_bindings names = Data.map (apfst (fold Symtab.delete_safe names))

fun default_name bindings ctxt =
  let val anonymous = snd (Data.get ctxt)
      val (bindings', anonymous') =
            fold_map (fn X as ((B,attrs),pats) => fn a =>
                if Binding.is_empty B andalso (not (null attrs) orelse not (null pats))
                then (((Binding.prefix_name a B, attrs), pats), Symbol.bump_string a)
                else (X,a)) bindings anonymous
  in (bindings', Data.map (apsnd (K anonymous')) ctxt)  end

fun bind_sequent_assms' bindings goal (ctxt,sequent) =
  (add_bindings bindings ctxt,
   Conv.gconv_rule (fold_rev (fn ((B,_),_) =>
          Conv.implies_conv (if Binding.is_empty B then Conv.all_conv
                             else Phi_Syntax.intro_labelled (Binding.name_of B)))
          bindings Conv.all_conv)
        goal
        sequent)

fun bind_sequent_assms bindings goal (ctxt,sequent) =
  case default_name bindings ctxt of (bindings', ctxt') =>
          bind_sequent_assms' bindings' goal (ctxt', sequent)

fun bindings_of' tab (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ X $ Y)
      = (try Phi_Syntax.dest_labelled X |> Option.map (fn (k,_) =>
                case Symtab.lookup tab k of SOME x => x
                   | NONE => ((Binding.name k,[]),[])))
          :: bindings_of' tab Y
  | bindings_of' tab (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_,_,X))
      = bindings_of' tab X
  | bindings_of' _ _ = []

val bindings_of = bindings_of' o fst o Data.get

fun remove_assm_bindings' ctxt X =
  (Conv.forall_conv (remove_assm_bindings' o snd) ctxt
   else_conv (Conv.try_conv (Conv.implies_conv
          (Conv.try_conv (HOLogic.Trueprop_conv Phi_Syntax.elim_labelled
                                else_conv Phi_Syntax.elim_labelled))
          (remove_assm_bindings' ctxt)))) X

fun remove_assm_bindings ctxt goal sequent =
  (bindings_of ctxt (Logic.nth_prem (goal, Thm.prop_of sequent)),
   Conv.gconv_rule (remove_assm_bindings' ctxt) goal sequent)


end