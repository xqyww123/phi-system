(* FILE: library/system/procedure.ML
   AUTHOR: Qiyuan Xu

   Defining procedures in IDE-CP.
*)

signature PHI_PROCEDURE = sig
  val procedure_kind : string
  val cast_kind : string
  val app_suffix : string
  val compilation_suffix : string

  val simp_monads : Proof.context -> thm -> thm
  val define : bool (*whether to define a new constant*)
        -> Attrib.binding -> local_theory * thm -> local_theory * thm

  type export_name = string
  (*interfaces introduced in this given theory, excluding others inherited from parent theories*)
  val interfaces_of : theory -> term Symtab.table
  (*procedures introduced in this given theory, excluding others inherited from parent theories*)
  val procedures_of : Context.generic -> thm list (*definitions*)
  val add_interface : export_name * term -> theory -> theory
  (* val add_interface_command : (Binding.binding * string) * (string * string)
  * option -> theory -> theory *)
  val add_procedure : thm -> Context.generic -> Context.generic


end

structure Phi_Procedure : PHI_PROCEDURE = struct
open Phi_Envir

val app_suffix = "_\<phi>app"
val compilation_suffix = "_def"
val procedure_kind = "\<phi>procedure"
val cast_kind = "\<phi>cast"
(* val compilation_thm = gen_get_thm compilation_suffix
fun compilation_thm_of ctx tm = compilation_thm ctx (term_name tm,
  Position.none) *)

type export_name = string


(*All procedures to be exported in one theory*)
structure Procedures = Generic_Data(
  type T = thm list Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true)
)

val thy_name_of_ctxt = Context.theory_long_name o Context.theory_of

fun procedures_of ctxt =
  the_default [] (Symtab.lookup (Procedures.get ctxt) (thy_name_of_ctxt ctxt))

fun add_procedure thm ctxt =
  Procedures.map (Symtab.map_default (thy_name_of_ctxt ctxt, [])
    (fn l => thm :: l)) ctxt





fun norm_def ctxt (m,n,instance) def = let
  val vars = strip_abs_vars (Logic.dest_equals (Thm.concl_of def) |> #2)
  val ty_vars = take m vars
        |> map (fn (_, ty) => Thm.cterm_of ctxt (Const ("Pure.type", ty)))
  val normal_vars = take n (drop m vars)
        |> map (fn (name,ty) => Thm.var ((name,0), Thm.ctyp_of ctxt ty))
  val insts = ty_vars @ normal_vars @ (map (Thm.cterm_of ctxt) instance)
  in
    fold (fn a => fn b => Thm.combination b a) (map Thm.reflexive insts) def
      |> Raw_Simplifier.rewrite_rule ctxt @{thms \<phi>V_simps[folded atomize_eq]}
      |> Drule.eta_contraction_rule
  end

fun closure precond substT f =
  let
  (*val tvars = Term.add_tvars f []
    val (subst,_) = Term.fold_types Term.declare_typ_names f Name.context
                    |> pair []
                    |> fold_rev (fn ((name,idx),sort) => fn (L,ctxt) =>
                          Name.variant name ctxt
                            |> apfst (fn name' =>
                                  (((name,idx),sort), TFree (name',sort))::L)
                     ) tvars
    val f' = Term_Subst.instantiate (TVars.make subst, Vars.empty) f *)

    fun trim ((i as \<^term>\<open>\<phi>V_none\<close>), (x as Abs (_, \<^typ>\<open>unit \<phi>arg\<close>, X)))
          = if Term.is_open X then ([i], x) else ([], X)
      | trim (i,x) = ([i],x)

    val vals = Procedure_Syntax.collect_vals false precond
    fun sort [] _ = []
      | sort (v::vs) xs = if member (op =) xs v then v :: sort vs xs else sort vs xs
    fun sort' vs xs = let val ret = sort vs xs
                       in if length ret = length xs then ret else error "BUG 8fd43cf2"
                      end

    val (instance,f'') = Procedure_Syntax.package_values "\<a>\<r>\<g>" false (sort' vals) NONE f |> trim
    val vars = fold_aterms (fn Var (name, T) => insert (op =) (name, T)
                             | _ => I) f'' []
    fun abst i (Var v) =
         (case find_index (fn x => x = v) vars
            of ~1 => raise Fail "bug!"
             |  j => Bound (j + i))
      | abst i (A $ B) = abst i A $ abst i B
      | abst i (Abs (name,ty,X)) = Abs (name,ty,abst (i+1) X)
      | abst _ X = X

  in abst 0 f''
      |> fold (fn ((name,_), T) => fn X => Abs (name, T, X)) vars
      |> TVars.fold (fn (_,tfree) => fn x => Abs ("_", Type ("itself", [Thm.typ_of tfree]), x)) substT
      |> pair (TVars.size substT, length vars, instance)
  end

fun rule_proc_F C ctxt =
      Conv.fconv_rule (Phi_Conv.hhf_concl_conv (K
              (  Phi_Syntax.proc_monad_conv C
       else_conv Phi_Syntax.pending_construction_monad_conv C)) ctxt)

fun simp_monads ctxt sequent =
  let val sctxt = Proc_Monad_SS.equip ctxt
      val sequent' = rule_proc_F (Simplifier.rewrite sctxt) ctxt sequent
   in sequent'
  end

fun importT_proc th ctxt =
  let
    val (f,_,_,_) = Thm.concl_of th |> Phi_Syntax.dest_procedure
    val (instT, ctxt') = Variable.importT_inst [f] ctxt;
    val instT' = TVars.map (K (Thm.ctyp_of ctxt')) instT;
    val th' = Thm.instantiate (instT', Vars.empty) th;
  in ((instT', th'), ctxt') end;


fun gen_define def_const (binding,attrs) (lthy0,sequent0) =
  let
    val ((substT, sequent), lthy) = importT_proc sequent0 lthy0

    val (f,precond,_,_) = Thm.concl_of sequent |> Phi_Syntax.dest_procedure

    (*all variables are in the procedure body*)
    (*then f' is the standard form of a definition*)
    val (arity_ins,f') = closure precond substT f
                      |> apsnd (Raw_Simplifier.rewrite_term (Proof_Context.theory_of lthy)
                                @{thms \<phi>V_simps[folded atomize_eq]} [])

    val (def_binding,proc_binding) = if Binding.is_empty binding
                                     then (binding,binding)
                                     else (Binding.suffix_name compilation_suffix binding
                                          ,Binding.suffix_name app_suffix binding)

    (*replace the procedure body in the procedural theorem to the newly defined constant*)
    fun rename ctxt def =
          rule_proc_F (fn ctm => Conv.rewr_conv (Thm.symmetric def) ctm) ctxt

    val (lthy, sequent'') =
      if Binding.is_empty binding orelse not def_const
      then (lthy, sequent)
      else lthy
            |> Local_Theory.define ((binding, NoSyn), ((def_binding,[]), f'))
            |-> (fn (tm,(_,def)) => fn lthy_x =>
                lthy_x
                  |> Local_Theory.declaration {syntax=false, pervasive=false, pos=Binding.pos_of binding}
                        (fn m => add_procedure (Morphism.thm m def))
                  |> rpair (rename lthy_x (norm_def lthy_x arity_ins def) sequent)
                )

  in lthy |> Local_Theory.notes_kind procedure_kind
                [((proc_binding,attrs), [([sequent''],[])])]
          |> apfst (fn [(_,[sequent'4])] => sequent'4)
          |> swap
  end

fun define' def_const binding stat =
  if Binding.is_empty_atts binding then stat else gen_define def_const binding stat

fun define def_const binding (lthy,sequent) =
  define' def_const binding (lthy, simp_monads lthy sequent)


(*All interfaces to be exported in *a* theory*)
structure Interfaces = Theory_Data(
  type T = term Symtab.table Symtab.table
              (*key: name of exported interface, value: procedure constant name*)
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun interfaces_of thy =
  the_default Symtab.empty (Symtab.lookup (Interfaces.get thy) (Context.theory_long_name thy))

fun add_interface intrf thy =
  Interfaces.map (Symtab.map_default
    (Context.theory_long_name thy, Symtab.empty)
    (Symtab.insert (K false) intrf)) thy

fun chk_interf_thm thm =
  let fun chk LHS =
        case Term.head_of LHS
          of C as Const(N,_) => C
           | _ => raise THM ("Phi_Procedure.add_interface", 0, [thm])
   in case Thm.concl_of thm
   of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ LHS $ _ => chk LHS
    | X => chk (#1 (Phi_Syntax.dest_procedure X))
  end

(* raise THM ("Phi_Procedure.add_interface", 0, [thm]) *)

val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>export\<close> (
  Scan.lift (Scan.option Parse.name) --
  Scan.optional (Scan.lift (\<^keyword>\<open>for\<close>) |-- Scan.repeat1 (Args.term)) []
  >> (fn (name, args) =>
    Thm.declaration_attribute (fn thm =>
      Context.mapping (fn thy => 
        let val const = chk_interf_thm thm
            val term = fold (fn arg => fn X => X $ arg) args const
            val ctm = Thm.global_cterm_of thy term
            val targs  = Phi_Syntax.dest_procT_params (Thm.typ_of_cterm ctm)
            val term = case targs
                         of []  => Abs ("_", \<^Type>\<open>unit\<close>, term)
                          | [_] => term
                          |  _  => raise CTERM("require parameters", [ctm])
            val bname = case name of SOME X => X | _ => Term.term_name const
         in add_interface (bname, term) thy
        end) I ))
) "declare that a \<phi>-procedure shall be exported")


end
