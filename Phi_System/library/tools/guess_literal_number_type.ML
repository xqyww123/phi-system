signature PHI_TYPE_OF_LITERAL = sig

type time = int

val is_numeral : term -> bool
val is_literal : term -> bool

val collect_statistics : Phi_Working_Mode.working_mode -> time -> thm -> Proof.context -> Proof.context
val guess : Proof.context -> PLPR_Pattern.bv_typs -> time -> term -> cterm option

val synthesisable_literals : Symtab.set Synchronized.var

end

signature GENERIC_VARIABLE_ACCESS = sig
val parse_phi_type_of_generic_var : (term -> term option) Symtab.table Unsynchronized.ref
end

structure Generic_Variable_Access : GENERIC_VARIABLE_ACCESS = struct
val parse_phi_type_of_generic_var = Unsynchronized.ref (Symtab.make [(\<^const_name>\<open>Val\<close>, fn _ $ T => SOME T)])
end

structure Phi_Type_of_Literal : PHI_TYPE_OF_LITERAL = struct

type time = int

val unknown_num_ty = Type("!unknown_num", [])

structure Recent_Types_of_Literal = Proof_Data (
  type T = (time * real * cterm) Termtab.table Typtab.table
           (*key: (type name of the abstract object) $ phi-type*)
  val init = K Typtab.empty
)

fun update_weight time0 time weight =
      if time0 <= time then weight else weight * Math.pow (0.9, Real.fromInt (time0 - time))

fun update_statistics ctxt time0 abst_ty term =
  Typtab.map_default (abst_ty, Termtab.empty) (fn tab =>
    case Termtab.lookup tab term
      of SOME (time, weight, cterm) =>
          let val weight' = update_weight time0 time weight + 1.0
           in Termtab.update (term, (time0, weight', cterm)) tab
          end
       | NONE => Termtab.update (term, (time0, 1.0, Thm.cterm_of ctxt term)) tab )

fun is_numeral term = can HOLogic.dest_numeral term orelse
                      can HOLogic.dest_number  term orelse
                      can HOLogic.dest_nat     term

fun is_literal term = is_numeral term orelse can HOLogic.dest_literal term

fun is_num_ty (Type(\<^type_name>\<open>nat\<close>, _)) = true
  | is_num_ty (Type(\<^type_name>\<open>int\<close>, _)) = true
  | is_num_ty _ = false

val synthesisable_literals = Synchronized.var "Phi_Type_of_Literal.synthesisable_literals" Symtab.empty

fun scan ctxt time0 =
  Phi_Syntax.fold_items_of_assertion' (fn bvs =>
    fn Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ x $ T =>
        (case Term.head_of (Phi_Help.beta_eta_contract_term T)
           of Const(N, _) => (
             (case Symtab.lookup (!Generic_Variable_Access.parse_phi_type_of_generic_var) N
                of SOME parser => (
                    case parser T
                      of SOME T' =>
                         (case Term.head_of T'
                            of Const(NT', _) =>
                                if Symtab.defined (Synchronized.value synthesisable_literals) NT'
                                then let val ty = Term.fastype_of1 (bvs,x)
                                      in update_statistics ctxt time0 ty T'
                                      #> is_num_ty ty ? update_statistics ctxt time0 unknown_num_ty T'
                                     end
                                else I
                             | _ => I)
                       | _ => I)
                 | _ => I)
               handle Match => I)
            | _ => I )
     | _ => I)

fun collect_statistics mode time construction_sequent ctxt =
  Recent_Types_of_Literal.map (
      scan ctxt time [] (#spec_of mode (Thm.prop_of construction_sequent))) ctxt

fun guess ctxt bvtys time literal =
  let val records = Recent_Types_of_Literal.get ctxt
      val ty0 = Term.fastype_of1 (bvtys, literal)
      val ty  = case ty0 of TVar _ => if is_numeral literal
                                      then unknown_num_ty
                                      else raise Fail ""
                          | _ => ty0
   in Typtab.lookup records ty
   |> Option.mapPartial (fn tmtab =>
        Termtab.fold (fn (_, (time', weight, ans)) =>
          let val weight' = update_weight time time' weight
              val thy = Proof_Context.theory_of ctxt
           in fn NONE => SOME (weight', ans)
               | SOME (another_weight, another_ans) =>
                  if another_weight < weight' andalso
                     can (Sign.typ_match thy
                               (ty0, snd (Phi_Syntax.dest_phi_type_ty (Thm.typ_of_cterm ans))))
                         Vartab.empty
                  then SOME (weight', ans)
                  else SOME (another_weight, another_ans)
          end ) tmtab NONE)
   |> Option.map snd
  end
  handle Fail _ => NONE

val _ = Theory.setup (Context.theory_map (
    Phi_Envir.On_Updating_State_Sequent.add 100 (fn arg => fn (ctxt, sequent) =>
      case #latest_ready_construction arg
        of SOME constr => (collect_statistics (#mode arg) (#time arg) constr ctxt, sequent)
         | NONE => (ctxt, sequent))
 #> Phi_Envir.Enter_Programming_Environ.add 0 (fn _ => fn (ctxt, sequent) => 
      (collect_statistics (Phi_Working_Mode.mode1 ctxt) 0 sequent ctxt, sequent))
 ))

end