(* FILE: library/additions/local_value.ML
   AUTHOR: Qiyuan XU

   Access and assignment for local value.
*)

signature PHI_LOCAL_VALUE = sig

(* Tools *)

val valname_prefix : string
val get_raw_val_in_rule : thm -> term

(* Access of Local Value *)

val has_val : string (*external name*) -> Proof.context -> bool
val delete_val : string (*external name*) -> Proof.context -> Proof.context
val update_val : binding -> thm (*rule*) -> Proof.context -> Proof.context
      (*a rule in form \<open>(\<phi>arg.dest (v <val-of> (name::valname)) \<Turnstile> (x \<Ztypecolon> T)\<close>*)


end

structure Phi_Local_Value : PHI_LOCAL_VALUE = struct

structure Values = Proof_Data (
  type T = (thm * string) Symtab.table
              (*rules in form \<open>(\<phi>arg.dest (v <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)\<close>,
                internal value name*)
  val init = K Symtab.empty
)

fun has_val xname ctxt = Symtab.defined (Values.get ctxt) xname
fun get_internal_val_name xname ctxt =
  Symtab.lookup (Values.get ctxt) xname |> Option.map snd

fun internal_name_of ctxt xname =
  case get_internal_val_name xname ctxt
    of SOME x => x | _ => raise Fail "not a known local value"

fun get_raw_val_in_rule rule =
   case Thm.prop_of rule
     of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Satisfaction\<close>, _)
            $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _) $ V)
            $ _)
           => V
       | _ => raise THM ("Bad Rule", 0, [rule])

fun pattern_of' mk_var rule =
  let val i = 1 + Thm.maxidx_of rule
  in case Thm.prop_of rule
       of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Satisfaction\<close>, (T1 as 
Type ("fun", [_, Type ("fun", [T,_])])))
              $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2) $ V)
              $ _)
             => \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Satisfaction\<close>, T1)
                  $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2) $ mk_var (i,V))
                  $ Var (("out", i), T))
         | _ => raise THM ("Bad Rule", 0, [rule])
  end

fun pattern_of__value_of ctxt xname rule =
      pattern_of' (fn (i,rawval) =>
        case rawval of Const (\<^const_name>\<open>Value_of\<close>, T3)
                        $ V1 $ Free (vname, T4) $ (path as Const (\<^const_name>\<open>Nil\<close>, _))
              => if vname = internal_name_of ctxt xname
                 then Const (\<^const_name>\<open>Value_of\<close>, T3)
                        $ Var (("val", i), fastype_of V1)
                        $ Free (vname, T4)
                        $ path
                 else raise THM ("Bad Rule", 0, [rule])
           | _ => raise THM ("Bad Rule", 0, [rule])) rule

fun pattern_of rule =
      pattern_of' (fn (i,rawval) => Var (("val",i), fastype_of rawval)) rule


fun delete_val' pred xname ctxt =
  case Symtab.lookup (Values.get ctxt) xname
    of SOME (rule, _) =>
          if pred rule
          then ctxt
          else Context.proof_map (
                  Phi_Reasoner.del_reasoners [pattern_of__value_of ctxt xname rule]
                      (fn r => #name r aconv Thm.prop_of rule)
                  ) ctxt
     | NONE => ctxt

val delete_val = delete_val' (K false)


fun extract_x_T th =
      let val ctm = Thm.cprop_of th |> Thm.dest_arg |> Thm.dest_arg
       in (Thm.dest_arg1 ctm, Thm.dest_arg ctm)
      end



fun dest_rule rule =
  case Thm.prop_of rule
    of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Satisfaction\<close>, _)
          $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _)
                       $ (Const (\<^const_name>\<open>Value_of\<close>, _)
                            $ _ $ Free (vname, T) $ Const (\<^const_name>\<open>Nil\<close>, _)))
          $ Spec)
         => (vname,T,
             (case Spec of \<^Const>\<open>\<phi>Type _ _\<close> $ _ $ _ => SOME (extract_x_T rule)
                         | _ => NONE))
     | _ => raise THM ("Bad Rule", 0, [rule])

fun update_val b rule ctxt = 
  let val (vname,T,V) = dest_rule rule
      val ctxt' = ctxt
                |> delete_val' (fn rule' => Thm.eq_thm_prop (rule',rule)) (Binding.name_of b)
                |> Values.map (Symtab.update ((Binding.name_of b), (rule, vname)))
      val pattern = pattern_of__value_of ctxt' (Binding.name_of b) rule
      val thy = Proof_Context.theory_of ctxt
   in ctxt'
     |> Context.proof_map (
          Phi_Reasoner.del_reasoners [pattern] (fn r => Pattern.matches thy (pattern, #name r))
       #> Phi_Reasoner.add_rule (Binding.pos_of b) Phi_Reasoner.NORMAL_LOCAL_CUT'
                                (SOME @{reasoner_group %local_value})
                                ([(pattern, NONE)],[]) NONE [rule])
     |> Generic_Variable_Access.bind_generic_vars
            [(Binding.name_of b, (Thm.cterm_of ctxt (Free (vname, T)), K V))]
     |> Proof_Context.maybe_bind_term ((Binding.name_of b,0),
                                       Option.map (Thm.term_of o fst) V)
  end

val value_assigner_id = "val"
val valname_prefix = "\<v>\<a>\<l>_"

fun value_assigner (b,eleidx) (ctxt,_) =
let
  val _ = if Generic_Element_Access.is_empty_input (Thm.term_of eleidx)
          then ()
          else error "Cannot assign to a member field of a local value"
  val xname = Binding.name_of b
  val (vname, ctxt) =
        case get_internal_val_name xname ctxt
          of SOME vname => (vname, ctxt)
           | _ => Proof_Context.add_fixes [(Binding.prefix_name valname_prefix b,
                                            SOME \<^typ>\<open>valname\<close>, NoSyn)] ctxt
                    |> apfst hd
  val vterm = Thm.cterm_of ctxt (Free (vname, \<^typ>\<open>valname\<close>))
  val rule = @{thm "__set_value_rule__"}
        |> Thm.instantiate (TVars.empty, Vars.make [((("name",0), \<^typ>\<open>valname\<close>), vterm)])
in (rule, ctxt, [], [update_val b]) end


(*An optimization if all assignments are to values*)
fun optimized_value_assign bs stat =
  let
    fun fast_assign bs (ctxt, sequent) =
      let
        val _ = if forall (fn ((_,eleidx),_) =>
                      Generic_Element_Access.is_empty_input (Thm.term_of eleidx)) bs
                then ()
                else error "Cannot assign to a member field of a local value"
        val (vnames, ctxt) = fold_map (fn ((b,_),_) => fn ctxt =>
              case get_internal_val_name (Binding.name_of b) ctxt
                of SOME vname => (vname, ctxt)
                 | NONE => Proof_Context.add_fixes [(Binding.prefix_name valname_prefix b,
                                                     SOME \<^typ>\<open>valname\<close>, NoSyn)] ctxt
                              |> apfst hd) bs ctxt
        val vterms = map (fn V => Thm.cterm_of ctxt (Free (V, \<^typ>\<open>valname\<close>))) vnames
        val rule = Thm.trivial (Thm.var (("init",0),\<^ctyp>\<open>prop\<close>))
              |> fold (fn V => fn rule =>
                    Thm.instantiate (TVars.empty, Vars.make [((("name",0),\<^typ>\<open>valname\<close>),V)])
                                    @{thm "__fast_assign_val__"}
                    RS rule) vterms
              |> (fn rule => @{thm "__fast_assign_val_0__"} RS rule)
        val sequent = Phi_Apply.apply [rule] ctxt sequent
              |> Phi_Reasoners.safer_obligation_solver1 {can_inst=false} ctxt
        val (sequent, vals) = PLPR_Syntax.elim_ant_seq_or_HOL_conj sequent
        val vals = PLPR_Syntax.elim_ant_sequence_or_HOL_conj vals
              |> Phi_Help.front
      in fold2 (fn ((x,_),_) => update_val x) bs vals ctxt
      |> rpair sequent
      end
  in if forall (fn (_,(id,_)) => id = value_assigner_id) bs
     then raise Generic_Variable_Access.Assignment_Hooks.Success (fast_assign bs stat)
     else stat
  end

(*** Setup ***)

val _ = Theory.setup (
   Generic_Variable_Access.register_assigner
      ("val", \<^type_name>\<open>valname\<close>, "to declare a new local value", (value_assigner_id, value_assigner))
#> Context.theory_map (Generic_Variable_Access.Assignment_Hooks.add 100 optimized_value_assign)
)

end