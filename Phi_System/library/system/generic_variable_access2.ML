signature GENERIC_VARIABLE_ACCESS = sig
include GENERIC_VARIABLE_ACCESS

(** Assignment **)

type assigner = string (*identifier of the assigner*)
             * (binding (*name of the value or variable*)
               -> context_state
               -> ( thm (*rule*)
                  * Proof.context
                  * cterm list (*fixed quantified variables in the rule*)
                  * (thm -> Proof.context -> Proof.context) list)
                      (*declare the condition, coinciding with the order of the conditions*))

val assignment : (binding * assigner) list
              -> Proof.context * thm -> Proof.context * thm
val assignment_cmd : (string (*keyword*) option * binding (*of generic variables*)) list
      -> Proof.context * thm -> Proof.context * thm

val register_assigner : string (*keyword that the assigner binds*)
                      * string (*type name of the generic variable*)
                      * string (*description for display*)
                      * assigner -> theory -> theory

structure Assignment_Hooks : HOOKS

end

structure Generic_Variable_Access : GENERIC_VARIABLE_ACCESS = struct
open Generic_Variable_Access

(*** Assignment ***)

type assigner = string (*identifier of the assigner*)
             * (binding (*name of the value or variable*)
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

fun parse_assigner ctxt =
  let
    val (assigner, type_map) = Assigner.get (Proof_Context.theory_of ctxt)
    fun not_defined name = let open Pretty in
        error (string_of (chunks (
          block [Binding.pretty name, str " is not an existing local value or variable."] ::
          str "Use the following syntax:" ::
          (map (fn (key, (descr,_)) =>
                    item [keyword1 key, str " ", Binding.pretty name, str ", ", str descr])
               (Symtab.dest assigner))
        )))
      end
    fun find name =
      case Variable.lookup_fixed ctxt (Binding.name_of name)
            |> Option.mapPartial (Variable.default_type ctxt)
        of SOME (Type ("dummy", [])) => not_defined name
         | SOME (Type (T, _)) =>
            (case Symtab.lookup type_map T
               of SOME key => key
                | NONE => not_defined name)
         | _ => not_defined name
    fun parse (NONE, name) = parse (SOME (find name), name)
      | parse (SOME key, name) =
          case Symtab.lookup assigner key
            of SOME (_, A) => (name, A)
             | _ => let open Pretty
                     in error (string_of (block [
                          keyword1 key, str " is not associated with any assignment rule."
                     ])) end
  in map parse
  end
  


fun strip_imp_prems_rev ret ct =
  let val (cA, cB) = Thm.dest_implies ct
  in strip_imp_prems_rev (cA :: ret) cB end
  handle TERM _ => (ret, ct)


(*TODO*)
fun concact_sequent ctxt rule vars sequent =
  Phi_Help.comp_rule_incr_left ctxt (Drule.forall_intr_list vars sequent) rule

fun default_assignment (name_assigner:(binding * assigner) list) (ctxt,sequent) =
  let
  (*make the assignment procedure*)
  val (rule', ctxt', vterms', decl') = (Thm.trivial (Thm.var (("init",0),\<^ctyp>\<open>prop\<close>)),ctxt,[],[])
        |> fold (fn (name,(_,f)) => fn (proc, ctxt, vterms, Asm) =>
              let val (rule, ctxt', vterms', Asm') = f name (ctxt,sequent)
               in (rule RS proc, ctxt', rev vterms' @ vterms, rev Asm' @ Asm) end
           ) name_assigner
  val rule = @{thm "__value_access_0__"} RS rule'
  val vterms = rev vterms'
  val decl = rev decl'

  (*apply the assignment procedure*)
  val (ctxt, proc) = NuApply.apply [rule] (ctxt',sequent)
        |> apsnd (fn th =>
            (*find where is the procedural parameter, and permute it to the end*)
            let
              fun is_body (Abs (_,_,X)) = is_body X
                | is_body (\<^const>\<open>Trueprop\<close> $ X) = is_body X
                | is_body (Const (\<^const_name>\<open>Pure.all\<close>,_) $ X) = is_body X
                | is_body (\<^const>\<open>Pure.imp\<close> $ _ $ X) = is_body X
                | is_body (X $ _) = is_body X
                | is_body (Const (\<^const_name>\<open>\<phi>Procedure\<close>, _)) = true
                | is_body _ = false
              val delt = 1 + find_index is_body (Thm.prems_of th)
              val _ = if delt = 0 then error "Internal Bug: Some assignment rule is wrong!" else ()
            in Thm.permute_prems 0 delt th end)
        |> Phi_Reasoner.reason1 (fn _ => 
            "Fail to assign variable(s). Typically, it is due to unsolved semantic types."
           ) (SOME ~1)
        |> apsnd (fn th => th RS @{thm conjunct1})
  
  in if null vterms
     then (ctxt, @{thm "\<phi>__Return_rule__"[OF view_shift_id]} RS proc)
              |> Phi_Sys.accept_proc
     else let
      (*insert a callback frame for concatenating sequents*)
      val (_, ctxt) = Assumption.add_assms
                            (fn _ => fn _ => (concact_sequent ctxt proc vterms, I)) [] ctxt
      
      val (rev_hyps, proc_cterm) = Thm.cprem_of proc 1
               |> fold (fn v => fn prem => Drule.beta_conv (Thm.dest_arg prem) v) vterms
               |> strip_imp_prems_rev []
      
      (*Now we change the goal of the programming context to add the *)
      val (_,arg_spec,ret_spec,E_spec) = Phi_Syntax.dest_procedure_c proc_cterm
      val goal = Phi_Envir.get_thesis ctxt
      val (trueprop, goal_term) = Thm.dest_comb goal
      val ((goal_F_arg,goal_ret), goal_E) = Thm.dest_comb goal_term |> apfst Thm.dest_comb
      fun instantiate_R inst spec =
        let
          fun left_most (Const (\<^const_name>\<open>times\<close>, _) $ A $ _) = left_most A
            | left_most X = X
          val spec' = Thm.incr_indexes_cterm (Thm.maxidx_of_cterm goal) spec
          val R = case (case Thm.term_of spec'
                          of Abs (_,_,X) => left_most X |> dest_comb |> fst
                           | X => left_most X)
                    of Var (R, _) => R
                     | _ => error "At least one of the assignment rules is not configured properly."
        in spec'
        |> Drule.mk_term
        |> Drule.infer_instantiate ctxt [(R,inst)]
        |> Drule.dest_term
        end
      val goal_ret' = instantiate_R goal_ret ret_spec
      (*  val goal_E'   = instantiate_R goal_E   E_spec *)
      val goal' = Thm.apply trueprop (Thm.apply (Thm.apply goal_F_arg goal_ret') goal_E)
      val ctxt = Phi_Envir.put_thesis goal' ctxt
      
      (*declare every hypothesis*)
      val (Hs,ctxt) = Assumption.add_assms Assumption.presume_export (rev rev_hyps) ctxt
      val ctxt = fold2 (fn H => fn D => D H) Hs decl ctxt
      
      (*make the new initial sequent*)
      val blk_name = Variable.revert_fixed ctxt (Term.term_name (Phi_Syntax.current_block_var sequent))
      val (ctxt, sequent') = #initial_sequent Phi_Working_Mode.procedure blk_name arg_spec ctxt
      
      val (_, ctxt) = Assumption.add_assms (fn _ => fn _ =>
                ((fn sequentx => #cast_exception Phi_Working_Mode.procedure E_spec (ctxt, sequentx)
                                    |> Phi_Reasoners.safer_obligation_solver1
                                    |> snd),
                 I)) [] ctxt
      in (ctxt, sequent')
      end
  end

structure Assignment_Hooks = Hooks(type arg = (binding * assigner) list)

val assignment = Assignment_Hooks.invoke_until_success default_assignment

fun assignment_cmd binds (ctxt,sequent) =
      assignment (parse_assigner ctxt binds) (ctxt,sequent)


end