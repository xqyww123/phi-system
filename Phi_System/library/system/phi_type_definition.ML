signature PHI_TYPE_DEF = sig

datatype def = DIRECT_DEF    of (term (*lhs*) * (string (*def_name*) * thm (*def*)))
             | RECURSIVE_DEF of Function.info

type phi_type = {
        def: def,
        algebras: thm list
}

type algebra_hints = term list
type declaration = phi_type * algebra_hints -> local_theory -> phi_type * local_theory

val leading_const_name : thm -> string
val def_eq : def * def -> bool
val add_phi_type : algebra_hints -> def -> Proof.context -> phi_type * local_theory
val constants_name_of : phi_type -> string list
val add_algebraic_declaration : priority * declaration -> theory -> theory

end

structure Phi_Type_Def : PHI_TYPE_DEF = struct

fun leading_const_name thm =
  Term.term_name (Term.head_of (HOLogic.dest_Trueprop (Thm.concl_of thm)))

datatype def = DIRECT_DEF    of (term (*lhs*) * (string (*def_name*) * thm (*def*)))
             | RECURSIVE_DEF of Function.info

fun def_eq (DIRECT_DEF (_,(_,th1)), DIRECT_DEF (_,(_,th2)))
      = (leading_const_name th1 = leading_const_name th2)
  | def_eq (RECURSIVE_DEF info1, RECURSIVE_DEF info2)
      = (#fnames info1 = #fnames info2)
  | def_eq _ = false

type algebra_hints = term list

type phi_type = {
        def: def,
        algebras: thm list
}

fun constants_name_of ({def,...} : phi_type) =
      case def of DIRECT_DEF (_,(_,th)) => [leading_const_name th]
                | RECURSIVE_DEF info => map Binding.name_of (#fnames info)

type declaration = phi_type * algebra_hints -> local_theory -> phi_type * local_theory

structure Alg_Decls = Theory_Data (
  type T = declaration PriorityTab.table
  val empty = PriorityTab.empty
  val merge = PriorityTab.merge (K true)
)

structure Phi_Types = Generic_Data (
  type T = phi_type Symtab.table (*key: constant name of the phi-type*)
  val empty = Symtab.empty
  val merge = Symtab.merge (def_eq o apply2 #def)
)

(*fun algebraic_declarfations_of lthy algebra =
  the_default [] (Symtab.lookup (Alg_Decls.get (Proof_Context.theory_of lthy)) algebra) *)

fun add_algebraic_declaration (priority, decl) thy =
      Alg_Decls.map (PriorityTab.update_new ((priority, Context.theory_name thy), decl))   thy

fun invoke_algebraic_declarations hints def lthy =
      PriorityTab.fold (fn (_, decl) => fn (phity', lthy') =>
          decl (phity', hints) lthy'
      ) (Alg_Decls.get (Proof_Context.theory_of lthy))
        ({def=def,algebras=[]}, lthy)

fun add_phi_type hints def lthy =
  let val (phity',lthy') = invoke_algebraic_declarations hints def lthy
   in (phity',
       Local_Theory.declaration {syntax=false,pervasive=false}
         (K (Phi_Types.map (
              fold (fn name => Symtab.update_new (name,phity')) (constants_name_of phity')
         ))) lthy')
  end

fun check_algebra_hints ctxt terms =
  let val ctxt' = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
      val terms' = Syntax.check_terms ctxt' terms
      fun pad_term term =
            case Term.fastype_of term
              of \<^Type>\<open>fun T _\<close> => pad_term (term $ Var (("uu", maxidx_of_term term + 1), T))
               | \<^Type>\<open>bool\<close> => HOLogic.Trueprop $ term
               | \<^Type>\<open>prop\<close> => term
               | _ => raise TERM("BAD Algebra Instantiation", [term])
   in map pad_term terms' end

(*** Definition Command ***)

(** Recursive **)

(*Stolen from *)
local open Function_Lib
open Function_Common
open Function_Fun

fun gen_add_fun hints add lthy =
  let
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
    fun prove_termination lthy =
      Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy) lthy
    val lthy1 = lthy |> add pat_completeness_auto |> snd
    val (info, lthy2) = prove_termination lthy1
        handle ERROR s => raise (ERROR (s ^ "\n\
                            \Fail to show the termination automatically. \
                            \May use command \<open>\<phi>type_definition\<close> to prove the termination manually"))
   in lthy2
   |> add_phi_type hints (RECURSIVE_DEF info) |> snd
  end

in

(* fun add_fun a b c = gen_add_fun (Function.add_function a b c) *)
fun add_fun_cmd a b c hints int lthy =
      gen_add_fun (check_algebra_hints lthy (map (Syntax.parse_term lthy) hints))
                  (fn tac => Function.add_function_cmd a b c  tac int) lthy

end

val algebra_hints = Scan.repeat (\<^keyword>\<open>is\<close> |-- Parse.term)

val def_by_fun = (Function_Common.function_parser Function_Fun.fun_config -- algebra_hints
      >> (fn ((config, (fixes, specs)), algebras) => add_fun_cmd fixes specs config algebras))

val def_by_function = (Function_Common.function_parser Function_Common.default_config
      >> (fn (config, (fixes, specs)) => Function.function_cmd fixes specs config))

val def_direct = (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes -- algebra_hints
   >> (fn ((((decl, spec), prems), params), hints) => fn int =>
        Specification.definition_cmd decl params prems spec int
           #> (fn (def, lthy') =>
                add_phi_type (check_algebra_hints lthy' (map (Syntax.parse_term lthy') hints))
                             (DIRECT_DEF def) lthy'
                  |> snd)
        ))

val _ = Outer_Syntax.local_theory' \<^command_keyword>\<open>\<phi>type_def\<close>
    "define \<phi>-types" (def_direct || def_by_fun)


(***  ***)


end