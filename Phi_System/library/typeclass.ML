signature PHI_TYPECLASS = sig

datatype 'a element = Require of 'a | Routine of 'a

type typeclass = {
    const: cterm,
    elements : cterm element list,
    def  : thm,
    intro: thm (*,
    programming: thm *)
  }

(* Basic Oprs *)

val burrow_elements : 'a list -> 'b element list -> 'a element list
val burrow_elements2 : 'c list -> ('a * 'b) element list -> ('a * 'c) element list
val map_element : ('a -> 'b) -> 'a element -> 'b element

val map_typeclass : (cterm -> cterm) -> (thm -> thm) -> typeclass -> typeclass
val morphism_typeclass : morphism -> typeclass -> typeclass

(* Commands *)

val define_typeclass : (binding * (binding * string option * mixfix) list) *
                       ((binding * Token.src list) * string) element list
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
    elements : cterm element list,
    def  : thm,
    intro: thm (*,
    programming: thm *)
  }

fun map_typeclass mctm mthm ({const, elements, def, intro} : typeclass) = {
      const = mctm const,
      elements = map (map_element mctm) elements,
      def = mthm def,
      intro = mthm intro
  } : typeclass

fun morphism_typeclass m =
      map_typeclass (Morphism.cterm m) (Morphism.thm m)

structure Data = Generic_Data (
  type T = typeclass Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge pointer_eq
)

fun define_typeclass ((binding,vars),elements) lthy =
  let (*parse*)
      val pos = Binding.pos_of binding
      val terms = map (fn Require (_,term) => term
                        | Routine (_,term) => term) elements
      val (stmt, parse_ctxt) = Proof_Context.read_stmt vars (map (fn x => [(x,[])]) terms) lthy
      fun proc_of tm =
            case try Phi_Syntax.dest_procedure (snd (PLPR_Syntax.concl_of_antecedent [] tm))
              of SOME (proc, _, _, _) => SOME (Term.head_of proc)
               | NONE => NONE
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
      fun mk_interface (attr,name) rule =
            (if Binding.is_empty_atts attr
             then (Binding.qualify true (Binding.name_of binding)
                                        (Binding.make (name,pos)), [])
             else apfst (Binding.qualify true (Binding.name_of binding)) attr,
             [([Phi_Conv.rulify lthy rule], [])])
      fun mk_interface' [] _ = []
        | mk_interface' (Require _ :: L) rule = mk_interface' L (next rule)
        | mk_interface' (Routine name :: L) rule =
            mk_interface name (this rule) :: mk_interface' L (next rule)
      val procs = mk_interface' proc_names (def' RS' (lthy, @{thm' equal_elim_rule1}))

      (* assemble *)
      val typeclass = {
          const = const',
          elements = elements'',
          def = def,
          intro = intro
        }
   in lthy
   |> Local_Theory.declaration {syntax=false, pervasive=false, pos=Binding.pos_of binding} (fn m => 
        case Term.head_of (Morphism.term m const)
          of Const (N, _) =>
              Data.map (Symtab.update_new (N, morphism_typeclass m typeclass))
           | _ => I)
   |> Local_Theory.notes procs |> snd
   |> Local_Theory.note ((Binding.suffix_name "_def" binding, []), [def]) |> snd
   |> Local_Theory.note ((Binding.suffix_name "_intro" binding, []), [intro]) |> snd
  end)
  end

val opt_fact_binding =
  Scan.optional ((Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty) --| \<^keyword>\<open>:\<close>)
    Binding.empty_atts


(** Commands **)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>\<phi>typeclass\<close>
          "declare typeclass in \<phi>-programming lang"
       ((Parse.binding
         -- (\<^keyword>\<open>(\<close> |-- Parse.vars --| \<^keyword>\<open>)\<close>)
         -- (Scan.repeat1 (
              (\<^keyword>\<open>requires\<close> |-- Parse.and_list1 Parse.term >> map (Require o pair Binding.empty_atts))
           || (\<^keyword>\<open>fixes\<close> |-- Parse.and_list1 (opt_fact_binding -- Parse.term) >> map Routine)) >> flat))
     >> define_typeclass)

end