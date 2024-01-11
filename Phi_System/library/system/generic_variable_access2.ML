signature GENERIC_VARIABLE_ACCESS = sig
include GENERIC_VARIABLE_ACCESS

(** Get **)

val get_value : string -> cterm -> Proof.context -> thm -> thm

(** Assignment **)

type element_index_input = cterm
type assigner = string (*identifier (kind) of the assigner*)
              * ( binding (*name of the value or variable*)
                * element_index_input
               -> context_state
               -> ( thm (*rule*)
                  * Proof.context
                  * cterm list (*fixed quantified variables in the rule*)
                  * (thm -> Proof.context -> Proof.context) list)
                      (*declare the condition, coinciding with the order of the conditions*))

val assignment : ((binding * element_index_input) * assigner) list
              -> context_state -> context_state
val assignment_cmd : (string (*keyword*) option * (binding (*of generic variables*) * element_index_input)) list
              -> context_state -> context_state

val register_assigner : string (*keyword that the assigner binds*)
                      * string (*type name of the generic variable*)
                      * string (*description for display*)
                      * assigner -> theory -> theory

structure Assignment_Hooks : HOOKS

end

structure Generic_Variable_Access : GENERIC_VARIABLE_ACCESS = struct
open Generic_Variable_Access

(*** Get Value ***)

fun get_value name element_index ctxt sequent =
  let val vname = dereference_generic_var1 ctxt (Free (name, dummyT))
      val idx = Int.max (Thm.maxidx_of_cterm vname, Thm.maxidx_of_cterm element_index) + 1
      val Ty = TVar(("'x",idx), \<^sort>\<open>type\<close>)
      (*val Ty = lookup_bindings ctxt name
            |> Option.mapPartial (fn (_, get) => get (ctxt, Phi_Envir.the_construction ctxt))
            |> Option.map (fastype_of o Thm.term_of o fst)
            |> (fn SOME T => T
                 | NONE => TVar (("'x", idx), \<^sort>\<open>type\<close>))*)
      val target =
            Thm.apply (
            Thm.apply (
              Thm.cterm_of ctxt (\<^Const>\<open>Value_of \<open>Ty\<close> \<open>Thm.typ_of_cterm vname\<close>\<close>
                                    $ Var (("x",idx), Ty)))
              vname)
              element_index
   in Phi_Sys.synthesis target ctxt sequent
  end

(*** Assignment ***)

type element_index_input = cterm
type assigner = string (*identifier of the assigner*)
             * ( binding (*name of the value or variable*)
               * element_index_input
               -> context_state
               -> ( thm (*rule*)
                  * Proof.context
                  * cterm list (*fixed quantified variables in the rule*)
                  * (thm -> Proof.context -> Proof.context) list)
                      (*declare the condition, coinciding with the order of the conditions*))

structure Assigner = Theory_Data (
  type T = (
             ( string (*description*)
             * assigner) Symtab.table (*key: kind, also the keyword used in the programming*)
           * string Symtab.table (*from full name of the type of the generic variable to its kind*)
           )
  val empty = (Symtab.empty, Symtab.empty)
  fun merge ((a1,b1),(a2,b2)) =
        (Symtab.merge (K true) (a1,a2), Symtab.merge (op =) (b1,b2))
)

fun register_assigner (keyword, typ_const, descr, assigner) =
  Assigner.map (fn (A,K) => (Symtab.update_new (keyword, (descr, assigner)) A,
                             Symtab.update_new (typ_const, keyword) K))

fun parse_assigner ctxt assgm =
  let
    val (assigner, type_map) = Assigner.get (Proof_Context.theory_of ctxt)
    fun not_found name = let open Pretty in
        error (string_of (chunks (
          block [Binding.pretty name, str " is not an existing local value or variable."] ::
          str "Use the following syntax:" ::
          (map (fn (key, (descr,_)) =>
                    item [keyword1 key, str " ", Binding.pretty name, str ", ", str descr])
               (Symtab.dest assigner))
        )))
      end
    fun find name =
      case Generic_Variable_Access.lookup_bindings ctxt (Binding.name_of name)
        of SOME (X,_) => (
            case Thm.typ_of_cterm X
              of Type (T, _) =>
                  (case Symtab.lookup type_map T
                     of SOME key => key
                      | NONE => not_found name)
               | _ => not_found name)
         | _ => not_found name
    fun parse (NONE, name) = parse (SOME (find (fst name)), name)
      | parse (SOME key, name) =
          case Symtab.lookup assigner key
            of SOME (_, A) => (name, A)
             | _ => let open Pretty
                     in error (string_of (block [
                          keyword1 key, str " is not a kind of assignment target."
                     ])) end
  in map parse assgm
  end



fun strip_imp_prems_rev ret ct =
  let val (cA, cB) = Thm.dest_implies ct
  in strip_imp_prems_rev (cA :: ret) cB end
  handle TERM _ => (ret, ct)



fun default_assignment (name_assigner:((binding * element_index_input) * assigner) list) (ctxt,sequent) =
  let
  (*make the assignment procedure*)
  val (rule', ctxt, vterms', decl') = (Thm.trivial (Thm.var (("init",0),\<^ctyp>\<open>prop\<close>)),ctxt,[],[])
        |> fold (fn (name_idx,(_,f)) => fn (proc, ctxt, vterms, Asm) =>
              let val (rule, ctxt', vterms', Asm') = f name_idx  (ctxt,sequent)
               in (rule RS proc, ctxt', rev vterms' @ vterms, rev Asm' @ Asm) end
           ) name_assigner
  val rule = @{thm "__value_access_0__"} RS rule'
  val vterms = rev vterms'
  val decl = rev decl'

  (*apply the assignment procedure*)
  val proc'2 = Phi_Apply.apply [rule] ctxt sequent
  fun is_prem_of P (Abs (_,_,X)) = is_prem_of P X
    | is_prem_of P (\<^const>\<open>Trueprop\<close> $ X) = is_prem_of P X
    | is_prem_of P (Const (\<^const_name>\<open>Pure.all\<close>,_) $ X) = is_prem_of P X
    | is_prem_of P (\<^const>\<open>Pure.imp\<close> $ _ $ X) = is_prem_of P X
    | is_prem_of P X = P X
  val prems = Thm.prems_of proc'2
  val i_body = find_index (is_prem_of (fn (Const (\<^const_name>\<open>\<phi>Procedure\<close>, _) $ _ $ _ $ _ $ _) => true
                                        | _ => false)) prems
  val i_oblg = find_index (is_prem_of (fn (Const (\<^const_name>\<open>Premise\<close>, _) $ Const (\<^const_name>\<open>MODE_COLLECT\<close>, _) $ _ ) => true
                                        | _ => false)) prems
  val _ = if i_body = ~1 orelse i_oblg = ~1
          then error "Internal Bug: Some assignment rule is wrong!" else ()
  val proc'3 = proc'2
            |> Thm.permute_prems 0 i_oblg
            |> Thm.permute_prems 1 (if i_body < i_oblg then i_body else i_body - 1)
            |> Thm.permute_prems 0 2


  val proc =
           Phi_Reasoner.reason1 (fn _ =>
            "Fail to assign variable(s). Typically, it is due to unsolved semantic types."
           ) NONE (SOME (Thm.nprems_of proc'3 - 2)) ctxt proc'3
        |> Phi_Reasoners.weak_obligation_solver' {can_inst=true} (fn _ =>
            error "Fail to solve proof obligations in the assignment automatically. \
                  \It is a limitation for now that it cannot be proven manually. \
                  \We are improving this soon.") ctxt
        |> (fn th => th RS @{thm conjunct1})

  in if null vterms andalso null decl'
     then (ctxt, @{thm "\<phi>__Return_rule__"[OF view_shift_refl]} RS proc)
     else let

      val (rev_hyps, proc_cterm) = Thm.cprem_of proc 1
               |> fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) vterms
               |> strip_imp_prems_rev []

      (*insert a callback frame for concatenating sequents*)
      fun concact_sequent sequent' =
            Phi_Help.comp_rule_incr_left ctxt (Drule.forall_intr_list vterms sequent') proc
      val (_, ctxt) = Assumption.add_assms (fn _ => fn _ => (concact_sequent, I)) [] ctxt

      (*Now we change the goal of the programming context to add the newly generated items if any *)
      val (_,arg_spec,ret_spec,E_spec) = Phi_Syntax.dest_procedure_c proc_cterm
      val ctxt =
        if is_Var (Term.head_of (Thm.term_of ret_spec)) andalso
                   is_Var (Term.head_of (Thm.term_of E_spec))
                   (*change log: I added Term.head_of. if no bug, remove this comment*)
        then ctxt
        else let  
          val goal = Phi_Envir.get_thesis ctxt
          val (trueprop, goal_term) = Thm.dest_comb goal
          val ((goal_Pending, goal_ret), goal_E) = Thm.dest_comb goal_term |> apfst Thm.dest_comb
          fun instantiate_R inst spec =
            let
              fun left_most (Const (\<^const_name>\<open>times\<close>, _) $ A $ _) = left_most A
                | left_most X = X
              val spec' = Thm.incr_indexes_cterm (Thm.maxidx_of_cterm goal) spec
              fun err () = error "At least one of the assignment rules is not configured properly."
              val inst_ty = case Thm.typ_of_cterm inst
                              of \<^Type>\<open>fun \<^Type>\<open>\<phi>arg _\<close> _\<close> =>
                                      SOME (Thm.dest_ctyp0 (Thm.dest_ctyp0 (Thm.ctyp_of_cterm inst)))
                               | \<^Type>\<open>fun \<^typ>\<open>ABNM\<close> _\<close> => NONE
                               | _ => err ()
              val (R, tv) = case (case Thm.term_of spec'
                                    of Abs (_,_,X) => left_most X |> dest_comb |> fst
                                     | X => left_most X)
                              of Var (R, \<^Type>\<open>fun \<^Type>\<open>\<phi>arg \<open>TVar tv\<close>\<close> _\<close>) => (R, SOME tv)
                               | Var (R, \<^Type>\<open>fun \<^typ>\<open>ABNM\<close> _\<close>) => (R, NONE)
                               | _ => err ()
              val tyinsts = case (tv, inst_ty)
                              of (SOME a, SOME b) => TVars.make [(a,b)]
                               | (NONE, NONE) => TVars.empty
                               | _ => err ()
            in spec'
            |> Thm.instantiate_cterm (tyinsts, Vars.make [((R, Thm.typ_of_cterm inst), inst)])
            end                        
          val goal_ret' = instantiate_R goal_ret ret_spec
          val goal_E'   = instantiate_R goal_E E_spec
          val goal' = Thm.apply trueprop (Thm.apply (Thm.apply goal_Pending goal_ret') goal_E')
          in Phi_Envir.put_thesis goal' ctxt end

      (*declare every hypothesis*)
      val (Hs,ctxt) =
        if null rev_hyps
        then ([], ctxt)
        else Assumption.add_assms Assumption.presume_export (rev rev_hyps) ctxt
      val ctxt = fold2 (fn H => fn D => D H) Hs decl ctxt

      (*make the new initial sequent*)
      val (ctxt, sequent') = Phi_Working_Mode.initialize_sequent_procedure arg_spec ctxt

      (*insert a normalization of the abnormal spec before any exporting*)
      val (_, ctxt) =
        if is_Var (Term.head_of (Thm.term_of E_spec))
                  (*change log: I added Term.head_of. if no bug, remove this comment*)
        then ([], ctxt)
        else Assumption.add_assms (fn _ => fn _ =>
                ((fn sequentx =>
                    let val (_,_,_,Y,_) = Phi_Syntax.dest_PendingConstruction (Thm.prop_of sequentx)
                        val thy = Proof_Context.theory_of ctxt
                        val sequentx1 = if Pattern.matches thy (Thm.term_of ret_spec, Y)
                                        then sequentx
                                        else Phi_Sys.cast ret_spec ctxt sequentx
                        val sequentx2 =
                              #cast_exception Phi_Working_Mode.programming E_spec ctxt sequentx1
                                    |> Phi_Reasoners.weak_obligation_solver1 {can_inst=true} ctxt
                         in sequentx2
                        end),
                 I)) [] ctxt
      in (ctxt, sequent')
      end
  end

structure Assignment_Hooks = Hooks (type arg = ((binding * element_index_input) * assigner) list
                                    type state = context_state)

fun assignment assgns (ctxt,sequent)
      = Assignment_Hooks.invoke_until_success (Context.Proof ctxt)
                                              default_assignment assgns (ctxt,sequent)

fun assignment_cmd binds (ctxt,sequent) =
      assignment (parse_assigner ctxt binds) (ctxt,sequent)


end