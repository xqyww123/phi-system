signature PHI_TYPECLASS = sig

datatype 'a element = Require of 'a | Routine of 'a

type typeclass = {
    const: cterm,
    elements : (Attrib.binding * thm (*elim*)) element list,
    def  : thm,
    intro: thm (*,
    programming: thm *)
  }

(* Basic Oprs *)

val burrow_elements : 'a list -> 'b element list -> 'a element list
val burrow_elements2 : 'c list -> ('a * 'b) element list -> ('a * 'c) element list
val map_element : ('a -> 'b) -> 'a element -> 'b element

val map_typeclass : (cterm -> cterm)
                 -> (thm -> thm)
                 -> (Attrib.binding * thm -> Attrib.binding * thm)
                 -> typeclass -> typeclass
val morphism_typeclass : morphism -> typeclass -> typeclass

val trim_context : typeclass -> typeclass
val transfer : theory -> typeclass -> typeclass

(* Commands *)

val define_typeclass : (binding * (binding * string option * mixfix) list) *
                       (Attrib.binding * string) element list
                    -> local_theory -> local_theory

end

structure Phi_Typeclass : PHI_TYPECLASS = struct

datatype 'a element = Require of 'a | Routine of 'a

fun burrow_elements [] [] = []
  | burrow_elements (x::L) (Require _ :: Eles) = Require x :: burrow_elements L Eles
  | burrow_elements (x::L) (Routine _ :: Eles) = Routine x :: burrow_elements L Eles
  | burrow_elements _ _ = raise ListPair.UnequalLengths

fun burrow_elements2 [] [] = []
  | burrow_elements2 (x::L) (Require (attr,_) :: Eles) = Require (attr,x) :: burrow_elements2 L Eles
  | burrow_elements2 (x::L) (Routine (attr,_) :: Eles) = Routine (attr,x) :: burrow_elements2 L Eles
  | burrow_elements2 _ _ = raise ListPair.UnequalLengths

fun map_element f (Require x) = Require (f x)
  | map_element f (Routine x) = Routine (f x)

type typeclass = {
    const: cterm,
    elements : (Attrib.binding * thm) element list,
    def  : thm,
    intro: thm (*,
    programming: thm *)
  }


fun map_typeclass mctm mthm mele ({const, elements, def, intro} : typeclass) = {
      const = mctm const,
      elements = map (map_element mele) elements,
      def = mthm def,
      intro = mthm intro
  } : typeclass

fun morphism_typeclass m =
      map_typeclass (Morphism.cterm m) (Morphism.thm m)
                    (fn ((b,attrs),thm) =>
                        ((Morphism.binding m b, map (map (Token.transform m)) attrs), Morphism.thm m thm))

val trim_context =
      map_typeclass Thm.trim_context_cterm Thm.trim_context
                    (fn ((b,attrs),thm) => ((b, map (map Token.trim_context) attrs), Thm.trim_context thm))

fun transfer thy =
      map_typeclass (Thm.transfer_cterm thy) (Thm.transfer thy)
                    (fn ((b,attrs),thm) => ((b, map (map (Token.transfer thy)) attrs), Thm.transfer thy thm))

fun short_name_of (cls : typeclass) =
      Term.term_name (head_of (Thm.term_of (#const cls)))

structure Class = Generic_Data (
  type T = typeclass Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge pointer_eq
)

structure Instances = Generic_Data (
  type T = thm iNet.net
  val empty = iNet.empty
  val merge = iNet.merge Thm.eq_thm_prop
)

fun lookup_class' ctxt =
  let val cls = Class.get ctxt
   in fn bvs => fn term =>
        Symtab.lookup cls (
             case head_of (snd (PLPR_Syntax.concl_of_antecedent bvs term))
               of Const(N,_) => N
                | _ => error "BUG")
  end

fun lookup_class ctxt =
  let val lookup = lookup_class' ctxt
   in fn bvs => fn term =>
        Option.map (transfer (Context.theory_of ctxt)) (lookup bvs term)
  end

fun unknown_class ctxt term =
      let open Pretty in error (string_of (
          block ([Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt term, brk 1] @
                 text "is not a known \<phi>typeclass.")
      )) end

fun register_instance thm ctxt  =
  let val _ = case Thm.prop_of thm
                of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
                    (case lookup_class' ctxt [] X
                       of SOME _ => ()
                        | NONE => unknown_class ctxt X )
                 | _ => error "The \<phi>-class instance theorm must be condition-less"
      val thm = Drule.zero_var_indexes thm
   in Instances.map (
        iNet.insert_term Thm.eq_thm_prop (Thm.prop_of thm, thm)) ctxt
  end

fun proc_of tm =
      case try Phi_Syntax.dest_procedure (snd (PLPR_Syntax.concl_of_antecedent [] tm))
        of SOME (proc, _, _, _) => SOME (Term.head_of proc)
         | NONE => NONE

fun define_typeclass ((binding,vars),elements) lthy =
  let (*parse*)
      val pos = Binding.pos_of binding
      val terms = map (fn Require (_,term) => term
                        | Routine (_,term) => term) elements
      val (stmt, parse_ctxt) = Proof_Context.read_stmt vars (map (fn x => [(x,[])]) terms) lthy
      val proc_vars = map_filter (Option.map Term.dest_Free o proc_of o hd) (#propss stmt)
      val param_frees = map (Term.dest_Free o #2 o #2) (#vars stmt) @ proc_vars
      fun close tm =
            Logic.close_prop (subtract (op =) param_frees (Term.add_frees tm [])
                                |> map (fn (N,Ty) => (N, Free (N,Ty)))) [] tm
      val terms' = map (close o hd) (#propss stmt)
      val elements' = burrow_elements2 terms' elements

      (* check *)
      fun chk_element (Require (attr,_)) = (*TODO*) Require (attr,"")
        | chk_element (Routine (attr,tm)) =
            case proc_of tm
              of SOME tm => Routine (apsnd (map (Attrib.check_src lthy)) attr,
                                     fst (Term.dest_Free tm))
               | NONE => error (let open Pretty in string_of (
                     chunks [block (text "Bad specification:"),
                             Syntax.pretty_term lthy tm,
                             block ([str "Clause", brk 1, keyword2 "fix"] @
                                    text "must be followed with a procedure specification.")]
                 ) end)
      val proc_names = List.map chk_element elements'


      (* mk def *)
      val params = map Free param_frees
      val const_typ = \<^Type>\<open>bool\<close>
                   |> fold_rev (fn param => fn T =>
                        \<^Type>\<open>fun \<open>fastype_of param\<close> T\<close>
                      ) params
      val def_term = \<^Const>\<open>Pure.eq \<open>dummyT\<close>\<close>
            $ (fold (fn param => fn X => X $ param) params (Free(Binding.name_of binding, dummyT)))
            $ (foldl1 HOLogic.mk_conj (map (Phi_Conv.atomize_term parse_ctxt) terms'))
         |> Syntax.check_prop lthy
   in lthy
   |> Specification.definition (SOME (binding, SOME const_typ, NoSyn)) [] []
                               ((binding, []), def_term)
   |-> (fn (const,(_,def)) => fn lthy =>
  let (* make *)
      val const' = Thm.cterm_of lthy const
      val elements'' = map (map_element (Thm.cterm_of lthy o snd)) elements'
      val def' = def RS' (lthy, @{thm Meson.TruepropI})
      val intro = rule_by_tactic lthy (REPEAT (resolve_tac lthy @{thms' conjI} 1))
                                      (def' RS' (lthy, @{thm' equal_elim_rule2}))

      fun next rule = rule RS' (lthy, @{thm' conjunct2}) handle THM _ => rule
      fun this rule = rule RS' (lthy, @{thm' conjunct1}) handle THM _ => rule
   (*  fun mkb name = Binding.make (name,pos) *)
      fun mkb name = Binding.qualify true (Binding.name_of binding) (Binding.make (name,pos))
      fun mk_interface (attr,name) rule =
            (if Binding.is_empty_atts attr
             then (mkb name, [])
             else if Binding.is_empty (fst attr)
             then (mkb name, snd attr)
             else apfst (Binding.qualify true (Binding.name_of binding)) attr,
             [([Phi_Conv.rulify lthy rule], [])])
      fun mk_subclass (attr,_) rule =
            (attr, [([Phi_Conv.rulify lthy rule], [])])
      fun mk_elim [] _ = []
        | mk_elim (Require _ :: L) rule = mk_elim L (next rule)
        | mk_elim (Routine name :: L) rule =
            mk_interface name (this rule) :: mk_elim L (next rule)
      val procs = mk_elim proc_names (def' RS' (lthy, @{thm' equal_elim_rule1}))

      fun mk_interface (attr,name) rule =
            (if Binding.is_empty_atts attr
             then (mkb name, [])
             else if Binding.is_empty (fst attr)
             then (mkb name, snd attr)
             else attr
               (* apfst (Binding.qualify true (Binding.name_of binding)) attr *),
             Phi_Conv.rulify lthy rule)
      fun mk_subclass (attr,_) rule = (attr, Phi_Conv.rulify lthy rule) 
      fun mk_elim [] _ = []
        | mk_elim (Require name :: L) rule =
            Require (mk_subclass name (this rule)) :: mk_elim L (next rule)
        | mk_elim (Routine name :: L) rule =
            Routine (mk_interface name (this rule)) :: mk_elim L (next rule)
      val elims = mk_elim proc_names (def' RS' (lthy, @{thm' equal_elim_rule1}))

      (* assemble *)
      val typeclass = {
          const = const',
          elements = elims,
          def = def,
          intro = intro
        }
   in lthy
   |> Local_Theory.declaration {syntax=false, pervasive=false, pos=Binding.pos_of binding} (fn m => 
        case Term.head_of (Morphism.term m const)
          of Const (N, _) =>
              Class.map (Symtab.update_new (N, morphism_typeclass m typeclass))
           | _ => I)
   |> Local_Theory.notes procs |> snd
   |> Local_Theory.note ((Binding.suffix_name "_def" binding, []), [def]) |> snd
   |> Local_Theory.note ((mkb "intro", []), [intro]) |> snd
  end)
  end

fun match_instances ctxt =
  let val net = Instances.get ctxt
      val thy = Context.theory_of ctxt
   in fn pattern => iNet.match_term net pattern
                 |> filter (fn rule => PLPR_Pattern.does_smatch thy (K false) [] (pattern, Thm.concl_of rule))
  end

fun unify_instances ctxt =
  let val net = Instances.get ctxt
      val thy = Context.theory_of ctxt
   in fn pattern => 
        let val pattern = Logic.incr_indexes ([], [], 1) pattern
            val env = Envir.empty (maxidx_of_term pattern + 1)
         in iNet.unify_term net pattern
         |> filter (fn rule => 
              is_some (Seq.pull (Unify.unifiers (ctxt, env, [(pattern, Thm.concl_of rule)]))) )
        end
  end

fun unify_instances1 ctxt =
  let val unify = unify_instances ctxt
   in fn pattern =>
        case unify pattern
          of [] => NONE
           | [th] => SOME th
           | L => error (let open Pretty in string_of (
                    chunks (
                        block (text "Multiple possible instantiation of class" @
                              [brk 1, Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt pattern])
                        :: map (fn th =>
                            item [Context.cases Syntax.pretty_term_global Syntax.pretty_term ctxt (Thm.prop_of th)]) L)
                 ) end)
  end

fun prefix_of_instance instance_thm =
  let val (_, args) = case Thm.prop_of instance_thm
                        of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
                              Term.strip_comb X
                         | _ => error "BUG"
   in case find_first (Phi_Syntax.is_phi_type_ty o fastype_of) args
        of SOME tm => tm
                   |> Term.head_of
                   |> Term.term_name
         | NONE => error "The typeclass is not even about a \<phi>-type?!"
  end

(*
fun install_instance prefix (class : typeclass, instance_thm) lthy =
  let val qualify = case prefix
                      of SOME p => Binding.qualify true p
                       | _ => I
      val procs = map_filter (
            fn Require _ => NONE
             | Routine (b,th) =>
                  SOME (apfst qualify b, [([instance_thm RS' (lthy,th)],[])])
        ) (#elements class) 
   in lthy
   |> Local_Theory.notes procs
  end
*)

fun build_instance topmost pos class prop procs lthy =
  let val param_num = length (filter (fn Require _ => true | _ => false) (#elements class)) + 1
      val (head,params) = Term.strip_comb prop

      val rule0 = #intro class
      val (_, schemas) = Term.strip_comb (HOLogic.dest_Trueprop (Thm.concl_of rule0))
      val rule1 = Drule.infer_instantiate lthy
                      (map2 (fn Var (N,_) => (fn X => (N, Thm.cterm_of lthy X))
                              | _ => error "BUG: Bad rule")
                            (take param_num schemas)
                            (take param_num params))
                      rule0

      val unify_instances1 = unify_instances1 (Context.Proof lthy)
      val lookup_class = lookup_class (Context.Proof lthy)

      fun allI th = allI (@{thm' allI} RS th) handle THM _ => th

      fun reason [] sequent lthy =
            if Thm.no_prems sequent then (sequent, lthy)
            else error "BUG: Bad rule"
        | reason (Require _ :: eles) sequent lthy =
            let val ant = hd (Thm.prems_of sequent)
                val target = head_of (snd (PLPR_Syntax.concl_of_antecedent [] ant))
             in case lookup_class [] ant
             of SOME class => (
                    case unify_instances1 target
                      of NONE => build_instance false pos class target procs lthy
                              |> (fn (clsthm, lthy) =>
                                    reason eles (clsthm RS' (lthy, sequent)) lthy)
                       | SOME clsthm =>
                                    reason eles (clsthm RS' (lthy, sequent)) lthy
                  )
              | NONE =>
                    Phi_Reasoner.reason1 (fn () => let open Pretty in string_of (
                        chunks [block (text "Fail to derive a requirement of the class"),
                                Syntax.pretty_term lthy (hd (Thm.prems_of sequent))]
                      ) end) NONE (SOME 1) lthy sequent
                    |> rpair lthy
            end
        | reason (Routine ((b,_),_) :: eles) sequent lthy =
            (case find_first (fn (N,_) => N = Binding.name_of b) procs
               of SOME (name, proc) =>
                    (proc RS' (lthy, Phi_Apply.app_conv RS' (lthy, allI sequent)))
                      |> Phi_Reasoner.reason1 (fn () => let open Pretty in string_of (
                            chunks [block (text "Fail to transform the given procedure"),
                                    Syntax.pretty_term lthy (Thm.prop_of proc),
                                    block (text "to the desired specification in typeclass" @
                                           [brk 1, str (short_name_of class)]),
                                    Syntax.pretty_term lthy (hd (Thm.prems_of sequent))]
                          ) end)
                          NONE (SOME 1) lthy
                      |> (fn th => reason eles th lthy)
                | NONE => error (let open Pretty in string_of (
                        block [str "Procedure", brk 1, Binding.pretty b, brk 1, str "in typeclass",
                               brk 1, str (short_name_of class), brk 1, str "is not given."]
                    ) end))
      val (sequent, lthy) = reason (#elements class) rule1 lthy
   in lthy
   |> Local_Theory.declaration {syntax=false, pervasive=false, pos=pos} (fn _ =>
          register_instance sequent)
   |> pair sequent
  end

fun instantiate_i add_fixes chk_procs chk_term
                  (((raw_half_prop, pos), raw_fixes), raw_procs) lthy =
  let val (_, ctxt) = add_fixes raw_fixes lthy
      val procs = chk_procs lthy raw_procs

      val half_prop = chk_term ctxt raw_half_prop
      val (head,params) = Term.strip_comb half_prop
      val class = case head
                    of Const(N, _) => (
                       case Symtab.lookup (Class.get (Context.Proof ctxt)) N
                         of SOME cls => cls
                          | NONE => unknown_class (Context.Proof ctxt) head )
                     | _ => unknown_class (Context.Proof ctxt) head

      val param_num = length (filter (fn Require _ => true | _ => false) (#elements class)) + 1
      val _ = if length params = param_num then ()
              else error (let open Pretty in string_of (
                  block (text "Incorrect number of arguments:" @
                         [str "class", brk 1, str "requires", brk 1,
                          str (string_of_int param_num), brk 1] @
                         text "parameters, whereas it is given" @
                         [brk 1, str (string_of_int (length params)), brk 1, str "parameters."])
              ) end)
      
     (* | reason (Routine ) *)
   in lthy
   |> build_instance true pos class half_prop procs
  end

val instantiate = instantiate_i Proof_Context.add_fixes (K I) Syntax.check_term
val instantiate_cmd = instantiate_i Proof_Context.add_fixes_cmd (fn ctxt => map (fn (name,th) =>
                                (name, case Phi_App_Rules.app_rules ctxt [th]
                                         of [] => error ("The " ^ name ^ " is provided with no procedure!")
                                          | [th] => th
                                          | _ => error ("The " ^ name ^ " is provided with more than one procedures!") )))
                        Syntax.read_term


(*
fun global_instantiate (raw_half_prop, raw_fixes) ctxt =
  let val half_prop = Syntax.check_term
   in ctxt
  end
*)

(** Commands **)

val opt_fact_binding =
  Scan.optional ((Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty) --| \<^keyword>\<open>:\<close>)
    Binding.empty_atts

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>typeclass\<close>
          "declare typeclass in \<phi>-programming lang"
       ((Parse.binding
         -- (\<^keyword>\<open>(\<close> |-- Parse.vars --| \<^keyword>\<open>)\<close>)
         -- (Scan.repeat1 (
              (\<^keyword>\<open>requires\<close> |-- Parse.and_list1 Parse.term >> map (Require o pair Binding.empty_atts))
           || (\<^keyword>\<open>fixes\<close> |-- Parse.and_list1 (opt_fact_binding -- Parse.term) >> map Routine)) >> flat))
     >> define_typeclass)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>instance\<close>
          "declare typeclass in \<phi>-programming lang"
        ((Parse.position Parse.term -- Parse.for_fixes
         -- Scan.optional (\<^keyword>\<open>where\<close> |--
           Scan.repeat1 (Parse.name --| \<^keyword>\<open>=\<close> -- Parse.thm)) [])
          >> (snd oo instantiate_cmd))
        

(*

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>instance\<close>
          "declare typeclass in \<phi>-programming lang"
        (Parse.term -- Parse.for_fixes --| \<^keyword>\<open>begin\<close>)
*)

end