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
  (*names of the parameters of a procedure constant, outermost first; "" for an unnamed one*)
  val param_names_of : Context.generic -> string -> string list option
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

structure Param_Names = Generic_Data(
  type T = string list Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true)
)

fun add_param_names (c, names) = Param_Names.map (Symtab.update (c, names))
fun param_names_of ctxt c = Symtab.lookup (Param_Names.get ctxt) c


fun norm_def ctxt (m,normal_insts,instance) def = let
  val vars = strip_abs_vars (Logic.dest_equals (Thm.concl_of def) |> #2)
  val ty_vars = take m vars
        |> map (fn (_, ty) => Thm.cterm_of ctxt (Const ("Pure.type", ty)))
  val insts = ty_vars @ map (Thm.cterm_of ctxt) (normal_insts @ instance)
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

    (*A \<phi>-type parameter T -- schematic, or fixed by the context -- may occur in the body only as
      \<open>\<typeof> T\<close>; each such subterm becomes its own TY parameter, so a definition is parameterized
      by semantic types, never by \<phi>-types.*)
    fun phi_param_name (Var ((name,_), T)) = if can Phi_Syntax.dest_phi_type_ty' T then SOME name else NONE
      | phi_param_name (Free (name, T))    = if can Phi_Syntax.dest_phi_type_ty' T then SOME name else NONE
      | phi_param_name _ = NONE
    fun typeofs (t as Const (\<^const_name>\<open>SType_Of\<close>, _) $ T) =
          (case phi_param_name T of SOME name => insert (op =) (name, t) | NONE => I)
      | typeofs (A $ B) = typeofs A #> typeofs B
      | typeofs (Abs (_,_,X)) = typeofs X
      | typeofs _ = I
    val used = Name.make_context (fold_aterms (fn Var ((name,_),_) => insert (op =) name
                                                | Free (name,_) => insert (op =) name | _ => I) f'' [])
    val (gen, _) = fold_map (fn (name, t) =>
                        Name.variant (if name = "T" then "TY" else "TY_" ^ name)
                        #>> (fn name' => (t, Var ((name',0), \<^Type>\<open>TY\<close>))))
                     (typeofs f'' []) used
    fun generalize (t as Const (\<^const_name>\<open>SType_Of\<close>, _) $ _) = the_default t (AList.lookup (op aconv) gen t)
      | generalize (A $ B) = generalize A $ generalize B
      | generalize (Abs (name,ty,X)) = Abs (name,ty,generalize X)
      | generalize t = t
    val f'' = generalize f''
    val _ = case fold_aterms (fn v => is_some (phi_param_name v) ? cons v) f'' []
              of [] => ()
               | vs => raise TERM ("\<phi>-type parameters may occur in a procedure body only as \<open>\<typeof> T\<close>", vs @ [f''])

    val vars = fold_aterms (fn Var (name, T) => insert (op =) (name, T)
                             | _ => I) f'' []
    val insts = map (fn v => the_default (Var v) (AList.lookup (op =) (map swap gen) (Var v))) vars
    fun abst i (Var v) =
         (case find_index (fn x => x = v) vars
            of ~1 => raise Fail "bug!"
             |  j => Bound (j + i))
      | abst i (A $ B) = abst i A $ abst i B
      | abst i (Abs (name,ty,X)) = Abs (name,ty,abst (i+1) X)
      | abst _ X = X

    (*type variables no longer occurring in the body (typically the abstract type of a
      generalized \<phi>-type parameter) get no TYPE parameter*)
    val tfrees = Term.add_tfrees f'' []
    val ty_params = TVars.fold (fn (_, ctyp) => fn L =>
                        case Thm.typ_of ctyp
                          of T as TFree v => if member (op =) tfrees v then T :: L else L
                           | T => T :: L) substT []
                 |> rev

    val names = map (K "") ty_params @ map (fn ((name,_),_) => name) (rev vars)

  in abst 0 f''
      |> fold (fn ((name,_), T) => fn X => Abs (name, T, X)) vars
      |> fold (fn T => fn x => Abs ("_", Type ("itself", [T]), x)) ty_params
      |> pair ((length ty_params, rev insts (*outermost binder first*), instance), names)
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
      else let
        (*all variables are in the procedure body, then f' is the standard form of a definition*)
        val ((arity_ins, names), f') =
              closure precond substT f
                |> apsnd (Raw_Simplifier.rewrite_term (Proof_Context.theory_of lthy)
                                                      @{thms \<phi>V_simps[folded atomize_eq]} [])
        val (_, _, instance) = arity_ins
       in lthy
            |> Local_Theory.define ((binding, NoSyn), ((def_binding,[]), f'))
            |-> (fn (tm,(_,def)) => fn lthy_x =>
                let val const_name = Local_Theory.full_name lthy_x binding
                    (*the exported definition applies the constant to the parameters fixed by the
                      context, if any; their names come first*)
                    fun ctxt_params def' =
                          map (fn Var ((n,_),_) => n | Free (n,_) => n | _ => "")
                              (snd (Term.strip_comb (fst (Logic.dest_equals (Thm.concl_of def')))))
                 in lthy_x
                  |> Local_Theory.declaration {syntax=false, pervasive=false, pos=Binding.pos_of binding}
                        (fn m => let val def' = Morphism.thm m def
                                  in add_procedure def'
                                  #> add_param_names (const_name, ctxt_params def' @ names @ map (K "") instance)
                                 end)
                  |> rpair (rename lthy_x (norm_def lthy_x arity_ins def) sequent)
                end)
      end

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

(*An instance argument is given either by the parameter's name (\<open>K = \<int'>\<close>) or positionally;
  named arguments take their parameter, positional ones fill the remaining parameters in order.*)
fun assign_instance_args thy c items =
  let val params = Phi_Syntax.dest_procT_params (Sign.the_const_type thy c)
      val names = case param_names_of (Context.Theory thy) c
                    of SOME ns => if length ns = length params then ns else map (K "") params
                     | NONE => map (K "") params
      val named = map_filter (fn (SOME n, t) => SOME (n, t) | _ => NONE) items
      val positional = map_filter (fn (NONE, t) => SOME t | _ => NONE) items
      val _ = List.app (fn (n, _) => if member (op =) names n then ()
                                    else error ("Unknown parameter " ^ quote n ^ " of procedure " ^ quote c ^
                                                "; its named parameters are " ^ commas_quote (filter (fn s => s <> "") names))) named
      fun go [] pos acc = (rev acc, pos)
        | go (n :: ns) pos acc =
            (case AList.lookup (op =) named n
               of SOME t => go ns pos (t :: acc)
                | NONE => (case pos of t :: pos' => go ns pos' (t :: acc)
                                     | [] => (rev acc, [])))
      val (args, rest) = go names positional []
      val _ = null rest orelse error ("Too many instance arguments for procedure " ^ quote c)
   in args end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>\<phi>export\<close> (
  Scan.lift (Scan.option Parse.name) --
  Scan.optional (Scan.lift (\<^keyword>\<open>for\<close>) |--
      (let val item = Scan.lift (Parse.name --| Parse.$$$ "=") -- Args.term >> (fn (n, t) => (SOME n, t))
                   || Args.term >> pair NONE
        in item -- Scan.repeat (Scan.option (Scan.lift (Parse.$$$ "and")) |-- item) >> op :: end)) []
  >> (fn (name, items) =>
    Thm.declaration_attribute (fn thm =>
      Context.mapping (fn thy =>
        let val const = chk_interf_thm thm
            val c = Term.dest_Const_name const
            val args = assign_instance_args thy c items
            (*instantiate the constant's type by unifying its parameter types with the arguments;
              type inference would leave pre-existing schematic type variables of the arguments alone*)
            val maxidx = fold (Integer.max o Term.maxidx_of_term) args ~1
            val T = Logic.incr_tvar (maxidx + 1) (Sign.the_const_type thy c)
            val (tye, _) = fold2 (fn arg => fn pT => Sign.typ_unify thy (pT, Term.fastype_of arg))
                                 args (take (length args) (Phi_Syntax.dest_procT_params T))
                                 (Vartab.empty, maxidx + 1 + Term.maxidx_of_typ T)
            val term = Term.list_comb (Const (c, Envir.subst_type tye T), map (Envir.subst_term_types tye) args)
            val ctm = Thm.global_cterm_of thy term
            val targs  = Phi_Syntax.dest_procT_params (Thm.typ_of_cterm ctm)
            val term = case targs
                         of []  => Abs ("_", \<^Type>\<open>unit\<close>, term)
                          | [_] => term
                          |  _  => let val names = the_default [] (param_names_of (Context.Theory thy) c)
                                       val given = length args
                                       val missing = drop given (names ~~ Phi_Syntax.dest_procT_params (Sign.the_const_type thy c))
                                                     handle ListPair.UnequalLengths => []
                                    in error ("The exported procedure " ^ quote c ^ " still has " ^
                                              string_of_int (length targs - 1) ^ " uninstantiated parameter(s)" ^
                                              (if null missing then "" else ": " ^
                                                 commas (map (fn (n, T) => (if n = "" then "_" else n) ^ " :: " ^
                                                                            Syntax.string_of_typ_global thy T) missing)))
                                   end
            val bname = case name of SOME X => X | _ => Term.term_name const
            val _ = if Term.exists_Const (fn (N, _) => N = \<^const_name>\<open>sem_poison_T\<close>) term
                    then error ("The type signature of the exported procedure " ^ quote bname ^
                                " involves the poison type: " ^ Syntax.string_of_term_global thy term)
                    else ()
         in add_interface (bname, term) thy
        end) I ))
) "declare that a \<phi>-procedure shall be exported")

end
