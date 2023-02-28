signature PHI_VARIABLE = sig

  val variable_is_typed : bool Config.T
  val dest_Var : term -> (string * (term * term)) option

end

structure Phi_Variable : PHI_VARIABLE = struct

val variable_is_typed = Attrib.setup_config_bool \<^binding>\<open>\<phi>variable_is_typed\<close> (K false)

fun dest_Var (Const (\<^const_name>\<open>\<phi>Type\<close>, _)
                $ x
                $ (Const (\<^const_name>\<open>basic_fiction.\<phi>\<close>,_)
                    $ _
                    $ (Const (\<^const_name>\<open>\<phi>MapAt\<close>, _)
                        $ Free (name, \<^typ>\<open>varname\<close>)
                        $ (Const (\<^const_name>\<open>\<phi>Some\<close>, _) $ T))))
      = SOME (name, (x,T))
  | dest_Var _ = NONE

fun find_Var var (Const (\<^const_name>\<open>times\<close>, _) $ R $ X) =
     (case dest_Var X
        of SOME (name, xT) => if name = var then SOME xT else find_Var var R
         | NONE => find_Var var R)
  | find_Var var X =
      case dest_Var X
        of SOME (name, xT) => if name = var then SOME xT else NONE
         | NONE => NONE

fun declare_rule pos rule =
  let
  val pattern = case Thm.prop_of rule
                  of Const (\<^const_name>\<open>Pure.eq\<close>, (T1 as Type ("fun", [T,_]))) $ V1 $ _ =>
                      Const (\<^const_name>\<open>Pure.eq\<close>, T1)
                        $ V1 $ Var (("out", maxidx_of_term V1 + 1), T)
                   | _ => raise THM ("Bad rule.", 0, [rule])
   in Context.proof_map (Phi_Reasoner.add_intro_rule pos 1000 ([(pattern,NONE)], []) NONE [rule])
  end

fun variable_assigner' b (ctxt,sequent) =
  let
  val iname = Variable.intern_fixed ctxt (Binding.name_of b)
  val existed = find_Var iname (#4 (Phi_Syntax.dest_CurrentConstruction (Thm.concl_of sequent)))
                 |> is_some
  in if existed
     then (Thm.instantiate (TVars.empty, Vars.make [((("var",0),\<^typ>\<open>varname\<close>),
                                                    Thm.cterm_of ctxt (Free(iname, \<^typ>\<open>varname\<close>)))])
                           @{thm "__set_var_rule__"},
           ctxt, [], [])
     else let
          val rule = if Config.get ctxt variable_is_typed
                     then @{thm "__set_new_var_rule__"}
                     else @{thm "__set_new_var_noty_rule__"}
          val ([vname],ctxt) = Proof_Context.add_fixes [(b, SOME \<^typ>\<open>varname\<close>, NoSyn)] ctxt
          val ctxt = Generic_Variable_Access.bind_local_vals
                        [(Binding.name_of b, Free (Binding.name_of b, @{typ varname}))] ctxt
          in (rule, ctxt,
              [Thm.cterm_of ctxt (Free (vname, @{typ varname}))],
              [declare_rule (Binding.pos_of b)])
          end
  end
val variable_assigner : Generic_Variable_Access.assigner = ("var", variable_assigner')

fun variable_declarer' TY b (ctxt,sequent) =
  let
    val ([vname],ctxt) = Proof_Context.add_fixes [(b, SOME \<^typ>\<open>varname\<close>, NoSyn)] ctxt
    val ctxt = Generic_Variable_Access.bind_local_vals
                        [(Binding.name_of b, Free (Binding.name_of b, @{typ varname}))] ctxt
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
#> Phi_Processor.setup_global
    \<^binding>\<open>declare_variable\<close> 5000 [Phi_Processor.Whole_Prop
                                                \<^pattern_prop>\<open>\<^bold>c\<^bold>u\<^bold>r\<^bold>r\<^bold>e\<^bold>n\<^bold>t ?blk [?H] \<^bold>r\<^bold>e\<^bold>s\<^bold>u\<^bold>l\<^bold>t\<^bold>s \<^bold>i\<^bold>n ?S\<close>]
    (fn (ctxt,sequent) => \<^keyword>\<open>var\<close> |--
                Parse.list1 (Parse.list1 Parse.binding -- Scan.option (\<^keyword>\<open>::\<close> |-- Parse.term))
     >> (fn raw_vars => fn () =>
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
            |> uncurry (map2 (fn vs => fn TY => map (fn V => (V, variable_declarer TY)) vs))
            |> flat
      in Generic_Variable_Access.assignment assigners (ctxt,sequent) end
   )) ""
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
                                      $ (Const (\<^const_name>\<open>Value_of\<close>, _) $ _ $ Free (N, _))
                                      $ _)))
                              => Variable.revert_fixed ctxt N
                         | (_, (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _
                                  $ (Const (\<^const_name>\<open>Val\<close>, _)
                                      $ (Const (\<^const_name>\<open>Value_of\<close>, _) $ _ $ Free (N, _))
                                      $ _)))
  in ()
  end *)

(* ) *)

end

