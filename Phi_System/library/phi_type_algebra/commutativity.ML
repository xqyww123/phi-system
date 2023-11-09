signature PHI_TYPE = sig
include PHI_TYPE

(** distinguish commutative \<phi>-type operators from its lambda application **)

type arity = int list (*Gs, its length is the arity of F, its elements are the arities of each G*) *
             int list (*Fs, its length is the arity of G', its elements are the arities of each F'*)

val parse_comm_F_Gs_from_appl : Context.generic ->
        Pattern_Translation.bvs * term (*lambda combination of F(G(T))*) ->
        ((term (*F*) * term list (*Gs*)) * (term (*G'*) * term list (*Fs'*))) list

val register_comm_tyoprs : (arity * Pattern_Translation.redex_residues) list ->
        Context.generic -> Context.generic
     (*redex: F (G\<^sub>1 T\<^sub>1\<^sub>,\<^sub>1 \<dots> T\<^sub>1\<^sub>,\<^sub>a\<^sub>(\<^sub>1\<^sub>)) \<dots> (G\<^sub>m T\<^sub>m\<^sub>,\<^sub>1 \<dots> T\<^sub>m\<^sub>,\<^sub>a\<^sub>(\<^sub>m\<^sub>))
       residues: F,   G\<^sub>1, T\<^sub>1\<^sub>,\<^sub>1, \<dots>, T\<^sub>1\<^sub>,\<^sub>a\<^sub>(\<^sub>1\<^sub>),       \<dots>,  G\<^sub>m, T\<^sub>m\<^sub>,\<^sub>1, \<dots>, T\<^sub>m\<^sub>,\<^sub>a\<^sub>(\<^sub>m\<^sub>),       a(i) gives the arity of G\<^sub>i
                 G',  F\<^sub>1',T\<^sub>f\<^sub>(\<^sub>1\<^sub>,\<^sub>1\<^sub>), \<dots>, T\<^sub>f\<^sub>(\<^sub>1\<^sub>,\<^sub>b\<^sub>(\<^sub>1\<^sub>)\<^sub>),   \<dots>,  F\<^sub>n', T\<^sub>f\<^sub>(\<^sub>n\<^sub>,\<^sub>1\<^sub>), \<dots>, T\<^sub>f\<^sub>(\<^sub>n\<^sub>,\<^sub>b\<^sub>(\<^sub>n\<^sub>)\<^sub>)  b(j) gives the arity of F'\<^sub>j
       where the commutativity transforms F (G\<^sub>1 T\<^sub>1\<^sub>,\<^sub>1 \<dots> T\<^sub>1\<^sub>,\<^sub>a\<^sub>(\<^sub>1\<^sub>)) \<dots> (G\<^sub>m T\<^sub>m\<^sub>,\<^sub>1 \<dots> T\<^sub>m\<^sub>,\<^sub>a\<^sub>(\<^sub>m\<^sub>)) to
                                          G' (F'\<^sub>1 T\<^sub>f\<^sub>(\<^sub>1\<^sub>,\<^sub>1\<^sub>) \<dots> T\<^sub>f\<^sub>(\<^sub>1\<^sub>,\<^sub>b\<^sub>(\<^sub>1\<^sub>)\<^sub>)) \<dots> (F\<^sub>n' T\<^sub>f\<^sub>(\<^sub>n\<^sub>,\<^sub>1\<^sub>) \<dots> T\<^sub>f\<^sub>(\<^sub>n\<^sub>,\<^sub>b\<^sub>(\<^sub>n\<^sub>)\<^sub>))*)
     (*automatically invoked when any \<phi>-LPR rule is registered*)

val register_comm_tyoprs_rule_pass : arity * term -> Context.generic -> Context.generic
      (*see the examples below*)


(** Control of Swap Normalization **)

type whether_swap_norm = term (*F*) * term list (*Gs*) -> bool option
      (*whether to invoke the normalization swapping \<open>F\<close> into \<open>Gs\<close>,
        return None to leave the control to the settings of lower priority*)

datatype swap_direction = S_In | S_Out
val control_swap_normalizations_on : (swap_direction * (term (*F*) * term list (*Gs*)) * whether_swap_norm * Reasoner_Group.group) list
                                 -> Context.generic -> Context.generic
    (*if S_In, swap \<open>F\<close> into all of the operands \<open>Gs\<close>, \<open>F(Gs(T)) \<rightarrow> G(Fs(T))\<close>
      if S_Out, \<open>Gs\<close> can only have 1 element, and it swaps \<open>F\<close> out of the \<open>G\<close>, \<open>G(F(T)) \<rightarrow> F(G(T))\<close>*)

val whether_to_swap_normalize : Context.generic -> PLPR_Pattern.bvs -> term -> bool

(*
val commutative_rules : Context.generic -> term (*F*) * term list (*Gs*) -> (Position.T * thm) list

val are_commutative : Context.generic -> term * term list -> bool
val is_commutative : Context.generic -> term (*F*) -> int list (*available arities of F. empty means non-commutative*)

val comm_patterns : ((term (*pattern*) * term (*F*) * term list (*Gs*)) * int (*arity of F*)) list Unsynchronized.ref
*)

val whether_swap_norm__sender : whether_swap_norm option Unsynchronized.ref
val phi_simp_trigger_id : serial

end

structure Phi_Type : PHI_TYPE = struct
open Phi_Type


type arity = int list (*Gs, its length is the arity of F, its elements are the arity of each G*) *
             int list (*Fs, its length is the arity of G', its elements are the arities of each F'*)

val comm_tyoprs_eq = eq_pair (op =) (eq_pair (op aconv) (eq_list (op aconv)))
fun comm_tyoprs_eq' thy = eq_pair (op =) (eq_pair (Pattern.equiv thy) (eq_list (Pattern.equiv thy)))

structure Comm_Tyoprs = Generic_Data (
  type T = (arity * Pattern_Translation.redex_residues) iNet.net
           (*redex: F (G\<^sub>1 T\<^sub>1\<^sub>1 \<dots> T\<^sub>1\<^sub>n) \<dots> (G\<^sub>m T\<^sub>m\<^sub>1 \<dots> T\<^sub>m\<^sub>n) \<longrightarrow>
             residues: F, G\<^sub>1, T\<^sub>1\<^sub>1, \<dots>, T\<^sub>1\<^sub>n, \<dots>, G\<^sub>m, T\<^sub>m\<^sub>1, \<dots>, T\<^sub>m\<^sub>n*)
  val empty = iNet.empty
  val merge = iNet.merge comm_tyoprs_eq
)

(*fun sum L = fold (fn x => fn y => x + y) L 0*)
fun sum_1 L = fold (fn x => fn y => x + y + 1) L 0

fun parse_comm_F_Gs_from_appl ctxt =
  let val rewrites = Comm_Tyoprs.get ctxt
      val thy = Context.theory_of ctxt
      fun split [] [] = []
        | split (n::N) (G::Lg) = G :: split N (drop n Lg)
        | split _ _ = error "BUG: bad patterns"
      fun split' arity (F::L) = (F, split arity L)
   in fn (bvs, F_G_T) =>
      iNet.match_term rewrites F_G_T
   |> map_filter (fn ((arities_F, arities_G'), redex_residues) =>
        Pattern_Translation.rewrites thy (K true) bvs redex_residues F_G_T
     |> Option.map (fn L =>
          let val len = sum_1 arities_F + 1
           in (split' arities_F (List.take (L, len)), split' arities_G' (List.drop (L, len)))
          end))
   |> distinct (eq_pair (eq_pair (op aconv) (eq_list (op aconv)))
                        (eq_pair (op aconv) (eq_list (op aconv))))
  end

fun register_comm_tyoprs arity_redex_residues ctxt =
  Comm_Tyoprs.map (fold (fn a_r_r as (_,(comb,_)) =>
    iNet.insert_term_safe (comm_tyoprs_eq' (Context.theory_of ctxt)) (comb,a_r_r)
  ) arity_redex_residues) ctxt

val pass_id_head = Const("tyopr_comm_pass", dummyT)
fun register_comm_tyoprs_rule_pass (arity,rewr) =
  let val (property::redex_residues) = Logic.dest_conjunction_list rewr
      val redex_residues' = map Logic.dest_term redex_residues
      val _ = if length redex_residues' = sum_1 (#1 arity) + 3 + sum_1 (#2 arity)
              then () else error "Bad redex_residues'"
   in Phi_Reasoner.add_pass (pass_id_head $ rewr, property,
        fn _ => fn (rules, prio, pats, guard, ctxt) =>
          let val rewr = map (fn rule =>
                    let val env = Pattern.match (Context.theory_of ctxt) (property, Thm.concl_of rule) (Vartab.empty, Vartab.empty)
                        val (redex::residues) = map (Envir.subst_term env) redex_residues'
                     in (arity, (redex, residues))
                    end) rules
              val ctxt' = register_comm_tyoprs rewr ctxt
           in (rules, prio, pats, guard, ctxt')
          end)
  end

val _ = Theory.setup (Context.theory_map (
  fold register_comm_tyoprs_rule_pass
    [(([1], [1]), \<^pattern_prop>\<open>Tyops_Commute ?F ?F' ?G ?G' ?T ?D ?r &&&
              TERM(?F (?G ?T)) &&& TERM(?F) &&& TERM(?G) &&& TERM(?T)
                               &&& TERM(?G') &&& TERM(?F') &&& TERM(?T)\<close>),
     (([2], [1,1]), \<^pattern_prop>\<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&&
              TERM(?F (?G ?T ?U)) &&& TERM(?F) &&& TERM(?G) &&& TERM(?T) &&& TERM(?U)
                                  &&& TERM(?G') &&& TERM(?F'\<^sub>T) &&& TERM(?T) &&& TERM(?F'\<^sub>U) &&& TERM(?U) \<close>),
     (([1,1], [2]), \<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&&
              TERM(?G' (?F'\<^sub>T ?T) (?F'\<^sub>U ?U)) &&& TERM(?G') &&& TERM(?F'\<^sub>T) &&& TERM(?T) &&& TERM(?F'\<^sub>U) &&& TERM(?U)
                                           &&& TERM(?F) &&& TERM(?G) &&& TERM(?T) &&& TERM(?U) \<close>)]
))



type whether_swap_norm = term (*F*) * term list (*Gs*) -> bool option
      (*whether to invoke the normalization swapping \<open>F\<close> into \<open>Gs\<close>*)
type F_Gs_encoding = term
type G_F_encoding = term
type encoding = term (*either F_Gs_encoding or G_F_encoding*)

datatype swap_direction = S_In | S_Out

fun encoding_F_Gs (F,Gs) =
  let fun is_dddot (Var (N, _)) = N = Auto_Bind.dddot
        | is_dddot _ = false
      fun pass_dddot [] = [] (*disabled: (*with the tailing unit, dddot can match zero or any terms*)*)
        | pass_dddot [X] =
            if is_dddot X then [Var (Auto_Bind.dddot, \<^typ>\<open>prop\<close>)] else [X]
        | pass_dddot (X::L) =
            if is_dddot X then error "\<open>\<dots>\<close> should only be seen at the last"
                          else Logic.mk_term X :: pass_dddot L
   in Logic.mk_conjunction_list (Logic.mk_term F :: pass_dddot Gs)
  end

fun encoding_G_F (G,F) = HOLogic.mk_prod (G,F)

fun encoding S_In  F_Gs = encoding_F_Gs F_Gs
  | encoding S_Out (F,[G]) = encoding_G_F (G,F)
  | encoding S_Out (_,Gs) = raise TERM ("Gs must be of single element in S_Out mode", Gs)

val NS_eq = eq_pair4 (op =) (op aconv) pointer_eq (op =)

structure Norm_Swaps = Generic_Data (
  type T = (swap_direction * encoding * whether_swap_norm * Reasoner_Group.group) Net.net
  val empty = Net.empty
  val merge = Net.merge NS_eq
)

fun control_swap_normalizations_on settings =
  Norm_Swaps.map (fold (fn (direction,terms,chk,prio) =>
      let val enc = encoding direction terms
       in Net.insert_term NS_eq (enc, (direction,enc,chk,prio))
      end
    ) settings)

fun whether_to_swap_normalize_internal ctxt =
  let val norm_swaps = Norm_Swaps.get ctxt
      val thy = Context.theory_of ctxt
   in fn bvs => fn (F_Gs, G_Fs') =>
  let fun chk_enc enc = Net.match_term norm_swaps enc
           |> filter (fn (_,enc',_,_) => PLPR_Pattern.matches thy (K true) bvs (enc', enc))
           |> sort (int_ord o apply2 (#1 o #4))
           |> get_first (fn (_,_,chk,(prio,_)) => Option.map (pair prio) (chk F_Gs))
      val check_In = chk_enc o encoding_F_Gs
      val check_Out1 = chk_enc o encoding_G_F
      fun chk_oprs F_Gs =
            Phi_Help.max_of' (int_ord o apply2 fst)
                             (check_In F_Gs :: map (check_Out1 o pair (fst F_Gs)) (snd F_Gs))

      val chk_F_Gs = chk_oprs F_Gs
      val chk_G_Fs'= chk_oprs G_Fs'

   in case (chk_F_Gs, chk_G_Fs')
   of (SOME (prio_a, result_a), SOME (prio_b, result_b)) =>
        if prio_a >= prio_b then result_a else not result_b
    | (SOME (_, result), NONE) => result
    | (NONE, SOME (_, result)) => not result
    | (NONE, NONE) => false
  end
  end

fun whether_to_swap_normalize ctxt =
  let val internal_check = whether_to_swap_normalize_internal ctxt
      val parse_comm = parse_comm_F_Gs_from_appl ctxt
   in fn bvs => fn F_G_T_term =>
      exists (internal_check bvs) (parse_comm (bvs, F_G_T_term))
  end

fun swap_normalization_guard (ctxt, sequent) =
  let val (bvs, goal) = Phi_Help.strip_meta_hhf_bvs (Phi_Help.leading_antecedent' sequent)
      val (ToA, direction) =
          case PLPR_Syntax.dest_action_of' (fn Const(\<^const_name>\<open>\<A>simp'\<close>, _) $ _ $ _ => true
                                             | _ => false) goal
            of (ToA, _ $ direction $ _) =>
               (ToA, 
                case direction of Const(\<^const_name>\<open>True\<close>, _) => true
                                | Const(\<^const_name>\<open>False\<close>, _) => false
                                | _ => raise THM ("the direction must be a literal", 1, [sequent]))
             | _ => error "BUG"

      val F_G_T = case Phi_Syntax.dest_transformation ToA
                    of (X, Y, _) =>
                        if direction
                        then snd (Phi_Syntax.dest_phi_type_assertion X)
                        else case Y
                          of Const(\<^const_name>\<open>ExSet\<close>, _) $ Abs (_, _,
                                Const(\<^const_name>\<open>Subjection\<close>, _) $ Y' $ _)
                               => snd (Phi_Syntax.dest_phi_type_assertion Y')
                           | _ => snd (Phi_Syntax.dest_phi_type_assertion Y )
                     | _ => raise THM("swap_normalization_guard: BUG", 1, [sequent])

   in (*(Config.get ctxt enable_swap_normalization_in_CoP_simp orelse
       Config.get ctxt under_NToA_ctxt) andalso*)
      whether_to_swap_normalize (Context.Proof ctxt) bvs F_G_T
  end


datatype whether_swap_norm_synt =
            Literal of whether_swap_norm | ML_Code of Input.source

val direction_synt = Args.$$$ "into" >> K S_In
                  || Args.$$$ "from" >> K S_Out

val to_normalize_synt =
      Scan.optional (\<^keyword>\<open>is\<close> |-- (  Args.$$$ "false" >> K (Literal (K (SOME false)))
                                     || Args.$$$ "true"  >> K (Literal (K (SOME true)))
                                     || Parse.ML_source  >> ML_Code ))
                    (Literal (K (SOME true)))
         

val whether_swap_norm__sender = Unsynchronized.ref (NONE : whether_swap_norm option)
val whether_swap_norm__parse_locker = Synchronized.var "to_normalize__parse_locker" ()

fun check_whether_swap_norm_synt ctxt (ML_Code src) = 
      Synchronized.change_result whether_swap_norm__parse_locker (fn () =>
        let val _ = ML_Context.expression (Input.pos_of src)
                      (ML_Lex.read "Phi_Type.to_normalize__sender := SOME ((" @
                       ML_Lex.read_source src @
                       ML_Lex.read ") : Phi_Type.to_normalize)") ctxt
            val ret = the (!whether_swap_norm__sender)
            val _ = whether_swap_norm__sender := NONE
         in (ret, ())
        end)
  | check_whether_swap_norm_synt _ (Literal tn) = tn


val phi_simp_trigger_id' = Unsynchronized.ref 0
val phi_backward_simp_trigger_id' = Unsynchronized.ref 0

val _ = Theory.setup (

  Attrib.setup \<^binding>\<open>\<phi>ToA_swap_normalization\<close> (
    Parse.and_list1' (
      Args.term_pattern -- Scan.lift direction_synt -- Parse.and_list1' Args.term_pattern --
        Scan.lift (\<^keyword>\<open>(\<close> |-- Reasoner_Group.parser --| \<^keyword>\<open>)\<close>) --
        Scan.lift to_normalize_synt
        ) >> (
    fn raw_controls =>
      Thm.declaration_attribute (fn _ => fn ctxt =>
        let val controls = map (fn ((((F, direction), Gs), group), to_normalize_synt) =>
                                (direction, (F, Gs),
                                 check_whether_swap_norm_synt ctxt to_normalize_synt,
                                 Reasoner_Group.check_group true ctxt group)
                           ) raw_controls
         in control_swap_normalizations_on controls ctxt
        end)
  )) "controls whether the ToA nroamlziation swaps a \<phi>-type operator over certain operators or not"

#>Attrib.setup \<^binding>\<open>\<phi>ToA_swap_norm_simp\<close> (
  Phi_Reasoner.attr_syntax (Scan.succeed ()) (fn (pos, mode, group, (), pats, guard') =>
    Thm.declaration_attribute (fn rule => fn ctxt =>
      let val guard = the_default swap_normalization_guard guard'
       in ctxt
       |> Config.put_generic Phi_CoP_Simp.extract_pattern_trigger false
       |> Config.put_generic Phi_CoP_Backward_Simp.extract_pattern_trigger false

       |> Phi_Reasoner.add_rule pos mode (SOME (the_default @{reasoner_group %\<phi>ToA_swap_norm_derived} group))
                                pats (SOME guard) [rule]

       |> Config.restore_generic Phi_CoP_Simp.extract_pattern_trigger ctxt
       |> Config.restore_generic Phi_CoP_Backward_Simp.extract_pattern_trigger ctxt
      end
  )))
  "declaring a \<phi>simp rule which will be used in swapping normalization.\
  \ Note the swap still needs to be enabled by declaring \<phi>ToA_swap_normalization"

#> Context.theory_map (
    Phi_CoP_Simp.add_simp_trigger (\<^pattern>\<open>_ \<Ztypecolon> _\<close>, fn ctxt =>
      fn (bvs, Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) =>
        (*(Config.get_generic ctxt enable_swap_normalization_in_CoP_simp orelse
         Config.get_generic ctxt under_NToA_ctxt) andalso*)
        Phi_CoP_Simp.pass_recursively (whether_to_swap_normalize ctxt) bvs T
      ) #-> (fn id => fn ctxt => (
        phi_simp_trigger_id' := id ;
        ctxt
      ))
 #> Phi_CoP_Backward_Simp.add_simp_trigger (\<^pattern>\<open>_ \<Ztypecolon> _\<close>, fn ctxt =>
      fn (bvs, Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ T) =>
        (*(Config.get_generic ctxt enable_swap_normalization_in_CoP_simp orelse
         Config.get_generic ctxt under_NToA_ctxt) andalso*)
        Phi_CoP_Simp.pass_recursively (whether_to_swap_normalize ctxt) bvs T
      ) #-> (fn id => fn ctxt => (
        phi_backward_simp_trigger_id' := id ;
        ctxt
      ))
  )

)

val phi_simp_trigger_id = ! phi_simp_trigger_id'
val phi_backward_simp_trigger_id = ! phi_backward_simp_trigger_id'






(*
fun parse_raw_pattern raw =
  let val (pat::F::G) = Logic.dest_conjunction_list raw
   in (pat, F, G)
  end

val comm_patterns = Unsynchronized.ref (map (apfst parse_raw_pattern)
      [(\<^pattern_prop>\<open>Tyops_Commute ?F ?F' ?G ?G' ?T ?D ?r &&& TERM ?F &&& TERM ?G\<close>, 1),
       (\<^pattern_prop>\<open>Tyops_Commute\<^sub>1\<^sub>_\<^sub>2 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&& TERM ?F &&& TERM ?G\<close>, 1),
       (\<^pattern_prop>\<open>Tyops_Commute\<^sub>2\<^sub>_\<^sub>1 ?F ?F'\<^sub>T ?F'\<^sub>U ?G ?G' ?T ?U ?D ?r &&& TERM ?G' &&& TERM ?F'\<^sub>T &&& TERM ?F'\<^sub>U\<close>, 2)])

fun mk_comm_patterns thy (F,Gs) =
  map_filter (fn ((pat, F', Gs'),_) =>
    let val envir = fold (Pattern.match thy) ((F',F)::(Gs' ~~ Gs)) (Vartab.empty, Vartab.empty)
     in SOME (Envir.subst_term envir pat)
    end handle Pattern.MATCH => NONE
  ) (!comm_patterns)

fun mk_comm_patterns_F thy F =
  map_filter (fn ((pat, F', _), arity) =>
    let val envir = Pattern.match thy (F',F) (Vartab.empty, Vartab.empty)
     in SOME (Envir.subst_term envir pat, arity)
    end handle Pattern.MATCH => NONE
  ) (!comm_patterns)

fun commutative_rules ctxt =
  let val lookup = PLPR_Template_Properties.lookup_properties_match ctxt
      val chk_pat = PLPR_Template_Properties.assert_property_pattern (Context.theory_of ctxt)
   in fn (F,G) =>
  let val patterns = mk_comm_patterns (Context.theory_of ctxt) (F,G)
   in maps (lookup o chk_pat) patterns
  end
  end

fun commutative_rules_of_F ctxt =
  let val lookup = PLPR_Template_Properties.lookup_properties_match ctxt
      val chk_pat = PLPR_Template_Properties.assert_property_pattern (Context.theory_of ctxt)
   in fn F =>
  let val patterns = mk_comm_patterns_F (Context.theory_of ctxt) F
   in maps (fn (pat, arity) => lookup (chk_pat pat)
                            |> map (rpair arity)) patterns
  end
  end

fun are_commutative ctxt =
  let val rules = commutative_rules ctxt
   in fn (F,G) => not (null (rules (F,G)))
  end

fun is_commutative ctxt =
  let val rules = commutative_rules_of_F ctxt
   in fn F => distinct (op =) (map snd (rules F))
  end
*)

end
