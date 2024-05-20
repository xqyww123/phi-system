signature PHI_VARIABLE = sig

  include PHI_VARIABLE

  val variable_is_typed : bool Config.T

  datatype var_state = Uninitialized | Initialized of cterm * cterm | May_Initialized of cterm * cterm
  val dest_Var : cterm -> (string * var_state) option

  val varname_prefix : string

end

structure Phi_Variable : PHI_VARIABLE = struct

open Phi_Variable

val varname_prefix = "\<v>\<a>\<r>_"
val variable_is_typed = Attrib.setup_config_bool \<^binding>\<open>\<phi>variable_is_typed\<close> (K false)

datatype var_state = Uninitialized | Initialized of cterm * cterm | May_Initialized of cterm * cterm

fun dest_Var ctm =
  case Thm.term_of ctm
    of (Const (\<^const_name>\<open>\<phi>Type\<close>, _)
          $ x
          $ (Const (\<^const_name>\<open>Var\<close>,_)
              $ Free (name, \<^typ>\<open>varname\<close>)
              $ T))
         => (case T
               of Const (\<^const_name>\<open>\<phi>Some\<close>, _) $ T =>
                    SOME (name, Initialized (Thm.dest_arg1 ctm (*x*),
                            Thm.dest_arg (Thm.dest_arg (Thm.dest_arg ctm)) (*T*)))
                | Const (\<^const_name>\<open>\<phi>None\<close>, _) =>
                    SOME (name, Uninitialized)
                | Const (\<^const_name>\<open>\<phi>Option\<close>, _) $ T =>
                    SOME (name, May_Initialized (Thm.dest_arg1 ctm (*x*),
                            Thm.dest_arg (Thm.dest_arg (Thm.dest_arg ctm)) (*T*))))
     | _ => NONE

fun find_Var var ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>times\<close>, _) $ X $ R
        => (case dest_Var (Thm.dest_arg1 ctm)
              of SOME (name, xT) => if name = var then SOME xT else find_Var var (Thm.dest_arg ctm)
               | NONE => find_Var var (Thm.dest_arg ctm))
    | _ => (case dest_Var ctm
              of SOME (name, xT) => if name = var then SOME xT else NONE
               | NONE => NONE)

fun find_Var' var (_,sequent) =
  find_Var var (#4 (Phi_Syntax.dest_CurrentConstruction_c (Thm.cconcl_of sequent)))

fun evaluation var state =
      find_Var' var state
        |> Option.mapPartial (
              fn Initialized xT => SOME xT
               | May_Initialized xT => SOME xT
               | Uninitialized => NONE)

fun declare_rule pos rule =
  let val () = case Thm.prop_of rule
                 of _ (*Trueprop*) $ (Const(\<^const_name>\<open>LOCAL_VAR\<close>, _) $ _ $ _) => ()
                  | _ => raise THM ("Bad rule.", 0, [rule])
   in Context.proof_map (Phi_Reasoner.add_rule pos Phi_Reasoner.NORMAL_LOCAL_CUT'
                                               (SOME @{reasoner_group %local_var})
                                               ([], []) NONE [rule])
  end

fun chk_no_path_during_creating (b,idx) =
  if Generic_Element_Access.is_empty_input (Thm.term_of idx)
  then ()
  else error ("Variable " ^ Binding.name_of b ^ " has not been declared. \
              \Thus it is infeasible to assign its element partially. " ^
              Position.here (Binding.pos_of b))

fun variable_assigner' (b,idx) (ctxt,sequent) =
  let
  val vb = Binding.prefix_name varname_prefix b
  val iname = Variable.intern_fixed ctxt (Binding.name_of vb)
  val existed = is_some (find_Var' iname (ctxt,sequent))
  in if existed
     then (if Generic_Element_Access.is_empty_input (Thm.term_of idx)
           then Thm.instantiate
                   (TVars.empty,
                    Vars.make [((("vari",0),\<^typ>\<open>varname\<close>), Thm.cterm_of ctxt (Free(iname, \<^typ>\<open>varname\<close>)))])
                   @{thm "__set_var_rule_0__\<phi>app"}
           else Thm.instantiate
                   (TVars.empty,
                    Vars.make [((("vari",0),\<^typ>\<open>varname\<close>), Thm.cterm_of ctxt (Free(iname, \<^typ>\<open>varname\<close>))),
                               ((("input_index",0), \<^typ>\<open>element_index_input\<close>), idx)])
                   @{thm "__set_var_rule__\<phi>app"},
           ctxt, [], [])
     else let
          val _ = chk_no_path_during_creating (b,idx)
          val rule = if Config.get ctxt variable_is_typed
                     then @{thm "__set_new_var_rule__\<phi>app"}
                     else @{thm "__set_new_var_noty_rule__\<phi>app"}
          val ([vname],ctxt) = Proof_Context.add_fixes [(vb, SOME \<^typ>\<open>varname\<close>, NoSyn)] ctxt
          val ctxt = ctxt
                  |> Generic_Variable_Access.bind_generic_vars
                        [(Binding.name_of b, (Thm.cterm_of ctxt (Free (vname, @{typ varname})),
                                              evaluation vname))]
                  |> bind_variable (vname, Binding.name_of b)
          in (rule, ctxt,
              [Thm.cterm_of ctxt (Free (vname, @{typ varname}))],
              [declare_rule (Binding.pos_of b)])
          end
  end
val variable_assigner : Generic_Variable_Access.assigner = ("var", variable_assigner')

fun variable_declarer' TY (b,idx) (ctxt,sequent) =
  let
    val _ = chk_no_path_during_creating (b,idx)
    val vb = Binding.prefix_name varname_prefix b
    val ([vname],ctxt) = Proof_Context.add_fixes [(vb, SOME \<^typ>\<open>varname\<close>, NoSyn)] ctxt
    val ctxt = ctxt
            |> Generic_Variable_Access.bind_generic_vars
                        [(Binding.name_of b, (Thm.cterm_of ctxt (Free (vname, @{typ varname})),
                                              evaluation vname))]
            |> bind_variable (vname, Binding.name_of b)
    val idx = Thm.maxidx_of_cterm TY + 1
    val rule = @{thm "__new_var_rule__"}
          |> Thm.incr_indexes idx
          |> Thm.instantiate (TVars.empty, Vars.make [((("TY",idx),\<^typ>\<open>TY option\<close>),TY)])
  in (rule, ctxt,
      [Thm.cterm_of ctxt (Free (vname, @{typ varname}))],
      [declare_rule (Binding.pos_of b)])
  end

fun variable_declarer TY : Generic_Variable_Access.assigner = ("new_var", variable_declarer' TY)

val _ = Theory.setup (
   Generic_Variable_Access.register_assigner
     ("var", \<^type_name>\<open>varname\<close>, "to declare a new variable", variable_assigner)
#> Phi_CP_IDE.add_parser (["var"],
    { name = "declare_variable",
      pos = \<^here>,
      priorirty = @{priority %\<phi>parser_var_decl+50},
      precedence = 0,
      pattern = [\<^pattern_prop>\<open>\<c>\<u>\<r>\<r>\<e>\<n>\<t> ?blk [?H] \<r>\<e>\<s>\<u>\<l>\<t>\<s> \<i>\<n> ?S\<close>],
      proc = (fn opr_ctxt as (_,(ctxt,sequent)) =>
        \<^keyword>\<open>var\<close> |--
                Parse.list1 (Parse.list1 Parse.binding -- Scan.option (\<^keyword>\<open>::\<close> |-- Parse.term))
     >> (fn raw_vars => fn _ =>
      let
        val require_type = Config.get ctxt variable_is_typed
        val assigners = split_list raw_vars
            |> apsnd (burrow_options (map (Syntax.parse_term ctxt) #> Syntax.check_terms ctxt)
                   #> map (fn SOME TY => Thm.cterm_of ctxt (@{const Some (TY)} $ TY)
                            | NONE => if require_type
                                      then error "Semantic type of variables is required \
                                                 \in the current semantic formalization.\n\
                                                 \Please use syntax \<open>var name :: type\<close> to indicate\
                                                 \the semantic types of the variables."
                                      else Thm.cterm_of ctxt (@{const None (TY)})))
            |> uncurry (map2 (fn vs => fn TY =>
                    map (fn V => ((V, Generic_Element_Access.empty_input), variable_declarer TY)) vs))
            |> flat
      in apsnd (Generic_Variable_Access.assignment assigners) opr_ctxt end
   ))})
)


(*
fun process_arguments_to_variables (ctxt, sequent) =
  let
    val items = Phi_Syntax.strip_separations
                      (#4 (Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)))
         |> filter (fn (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ (Const (\<^const_name>\<open>Val\<close>, _) $ _ $ _))
                         => true
                     | _ => false)
         |> map_index I
         |> map_filter (fn (_, (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _
                                  $ (Const (\<^const_name>\<open>Val\<close>, _)
                                      $ (Const (\<^const_name>\<open>Value_of\<close>, _) $ _ $ Free (N, _) $ _ )
                                      $ _)))
                              => Variable.revert_fixed ctxt N
                         | (_, (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _
                                  $ (Const (\<^const_name>\<open>Val\<close>, _)
                                      $ (Const (\<^const_name>\<open>Value_of\<close>, _) $ _ $ Free (N, _) $ _ )
                                      $ _)))
  in ()
  end *)

(* ) *)

end

