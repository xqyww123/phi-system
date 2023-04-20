(* FILE: library/additions/local_value.ML
   AUTHOR: Qiyuan XU

   Access and assignment for local value.
*)

signature PHI_VALUE = sig

val has_val : string (*external name*) -> Proof.context -> bool
val delete_val : string (*external name*) -> Proof.context -> Proof.context
val update_val : binding -> thm (*rule*) -> Proof.context -> Proof.context
      (*a rule in form \<open>(\<phi>arg.dest (v <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)\<close>*)

val valname_prefix : string

end

structure Phi_Value : PHI_VALUE = struct

structure Values = Proof_Data (
  type T = (thm * string) Symtab.table
              (*rules in form \<open>(\<phi>arg.dest (v <val-of> (name::valname)) \<in> (x \<Ztypecolon> T)\<close>,
                internal value name*)
  val init = K Symtab.empty
)

fun has_val xname ctxt = Symtab.defined (Values.get ctxt) xname
fun get_internal_val_name xname ctxt =
  Symtab.lookup (Values.get ctxt) xname |> Option.map snd

fun pattern_of ctxt xname rule =
  let
    val iname = case get_internal_val_name xname ctxt
                  of SOME x => x | _ => raise Fail "not a known local value"
    val i = 1 + Thm.maxidx_of rule
  in case Thm.prop_of rule
       of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>,
                                (T1 as Type ("fun", [_, Type ("fun", [T,_])])))
              $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2)
                              $ (Const (\<^const_name>\<open>Value_of\<close>, T3) $ V1 $ Free (vname, T4)))
              $ _)
             => if vname = iname
                then
                  \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, T1)
                    $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, T2)
                          $ (Const (\<^const_name>\<open>Value_of\<close>, T3) $ Var (("val", i), fastype_of V1)
                                                              $ Free (vname, T4)))
                    $ Var (("out", i), T))
                else raise THM ("Bad Rule", 0, [rule])
         | _ => raise THM ("Bad Rule", 0, [rule])
  end

fun delete_val' pred xname ctxt =
  case Symtab.lookup (Values.get ctxt) xname
    of SOME (rule, _) =>
          if pred rule
          then ctxt
          else Context.proof_map (
                  Phi_Reasoner.del_reasoners
                      (pattern_of ctxt xname rule)
                      (fn r => #name r aconv Thm.prop_of rule)
                  ) ctxt
     | NONE => ctxt

val delete_val = delete_val' (K false)


fun dest_rule rule =
  case Thm.prop_of rule
    of \<^const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>Set.member\<close>, _)
          $ (Const (\<^const_name>\<open>\<phi>arg.dest\<close>, _)
                       $ (Const (\<^const_name>\<open>Value_of\<close>, _) $ _ $ Free (vname, T)))
          $ Spec)
         => (vname,T,
             (case Spec of \<^Const>\<open>\<phi>Type _ _\<close> $ V $ _ => SOME V
                         | _ => NONE))
     | _ => raise THM ("Bad Rule", 0, [rule])

fun update_val b rule ctxt = 
  let val (vname,T,V) = dest_rule rule
   in ctxt
     |> delete_val' (fn rule' => Thm.eq_thm_prop (rule',rule)) (Binding.name_of b)
     |> Values.map (Symtab.update ((Binding.name_of b), (rule, vname)))
     |> (fn ctxt' =>
        Context.proof_map (Phi_Reasoner.add_intro_rule
                              (Binding.pos_of b) 1000
                              ([(pattern_of ctxt' (Binding.name_of b) rule, NONE)],[]) NONE
                              [rule]) ctxt')
     |> Generic_Variable_Access.bind_local_vals
            [(Binding.name_of b, (Free (vname, T), K V))]
     |> Proof_Context.maybe_bind_term ((Binding.name_of b,0), V)
  end


val value_assigner_id = "val"
val valname_prefix = "\<v>\<a>\<l>_"

fun value_assigner b (ctxt,_) =
  let
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
        val (vnames, ctxt) = fold_map (fn (b,_) => fn ctxt =>
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
        val (ctxt,sequent) = Phi_Apply.apply [rule] (ctxt,sequent)
              |> Phi_Reasoners.safer_obligation_solver1
        val (sequent, vals) = HOLogic.conj_elim ctxt sequent
        val vals = HOLogic.conj_elims ctxt vals
              |> Phi_Help.front
      in fold2 (update_val o fst) bs vals ctxt
      |> rpair sequent
      end
  in if forall (fn (_,(id,_)) => id = value_assigner_id) bs
     then raise Generic_Variable_Access.Assignment_Hooks.Success (fast_assign bs stat)
     else stat
  end


val _ = Theory.setup (
   Generic_Variable_Access.register_assigner
      ("val", \<^type_name>\<open>valname\<close>, "to declare a new local value", (value_assigner_id, value_assigner))
#> Context.theory_map (Generic_Variable_Access.Assignment_Hooks.add 100 optimized_value_assign)
)

end