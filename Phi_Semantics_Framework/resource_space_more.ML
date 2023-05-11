signature GENERIC_RESOURCE_SPACE = sig

structure Loc : RESOURCE_LOCALE

val declare_entries_i :
         binding -> (bstring * Position.T) list
      -> (binding * term * (string * (term Expression.map * term Expression.rewrites)) list) list
      -> theory -> Proof.state

val declare_entries :
         binding -> (bstring * Position.T) list
      -> (binding * string * ((xstring * Position.T)
                            * (string Expression.map * (Attrib.binding * string) list)) list) list
      -> theory -> Proof.state

val define_command : Outer_Syntax.command_keyword -> string -> unit

val lookup_entry : theory -> Symtab.key -> (term * term) option

end

signature GENERIC_RESOURCE_SPACE_ARGUMENT = sig

structure Loc : GENERIC_RESOURCE_LOCALE_ARGUMENT

val additional_data' : Loc.additional_data'
val prepare_map_rewr : binding -> term -> term
                    -> term Expression.map * term Expression.rewrites
                    -> term Expression.map * term Expression.rewrites
val prepare_space_name_binding : binding -> binding
val mandatory_path : string
val field_typ_of : term -> typ
val space_locale_exp : term list -> (term Expression.map * term Expression.rewrites)

end

functor Generic_Resource_Space (Config : GENERIC_RESOURCE_SPACE_ARGUMENT) : GENERIC_RESOURCE_SPACE =
struct

structure Loc = Generic_Resource_Locale(Config.Loc)

structure Entries = Theory_Data (
  type T = (term (*const*) * term (*domain or interp*)) Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (op =)
)

fun lookup_entry thy = Symtab.lookup (Entries.get thy)

fun read_expr_term thy term0 =
      let val term = Syntax.read_term_global thy term0
       in if null (Term.add_frees term []) andalso null (Term.add_tfrees term [])
             andalso null (Term.add_vars term []) andalso null (Term.add_tvars term [])
          then term
          else error (Pretty.string_of (Pretty.chunks [
                  Pretty.str "The term contains free (type) variables!",
                  Syntax.pretty_term_global thy term
              ]))
      end 

fun read_expr_maps thy (Expression.Positional terms)
      = Expression.Positional (map (Option.map (read_expr_term thy)) terms)
  | read_expr_maps thy (Expression.Named terms)
      = Expression.Named (map (apsnd (read_expr_term thy)) terms)

fun read_expr thy (xname, (m, rewr)) =
      (Locale.check thy xname, (read_expr_maps thy m, map (apsnd (read_expr_term thy)) rewr))

fun maps2 _ [] [] = []
  | maps2 f (x :: xs) (y :: ys) = f x y @ maps2 f xs ys
  | maps2 _ _ _ = raise ListPair.UnequalLengths;

fun gen_declare_entries prep_arg prep_expr
                        name_b parents entries0 thy =
  let val ctxt = Proof_Context.init_global thy
      val entries = map (fn (B,TM0,E) =>
            case prep_arg ctxt Config.additional_data' TM0 []
              of (TM, []) => (B, TM, map (prep_expr thy) E)
               | (_, tys) => error "Contains type variables!") entries0
      val space_xname = Config.prepare_space_name_binding name_b
      val space_name = Sign.full_name thy space_xname
      val space_entries = map (fn (B,TM,_) => (Binding.name_of B, TM)) entries
   in thy
   |> Loc.define_Resource_Locale_i (\<^sort>\<open>sep_algebra\<close>, (Config.Loc.field_locale, Position.none))
                            Config.additional_data' NONE [] space_xname
                            (map (fn p => (("",false), ([], p, []))) parents) space_entries
   |> "" <> Config.mandatory_path ? Sign.mandatory_path Config.mandatory_path
   |> (fn thy =>
      let val space_locale_info = case Symtab.lookup (Loc.locales (Context.Theory thy)) space_name
                                    of SOME x => x | NONE => raise Fail "internal bug #um90[3c"
          fun calc_field_terms thy =
                let val db = Entries.get thy
                    val field_terms = map (fn (name, TM) =>
                            case Symtab.lookup db name
                              of SOME (const, _) => const
                               | NONE => Free (name, Config.field_typ_of TM))
                          (#components space_locale_info)
                    val exp = ([(space_name, (("",false), Config.space_locale_exp field_terms))], [])
                 in (field_terms, exp)
                end
          val (field_terms, exp) = calc_field_terms thy
          val new_fields = map (fn (N,TM,_) => (N, SOME (Config.field_typ_of TM), NoSyn)) entries in
      if null new_fields andalso null parents
      then thy
       |> Named_Target.theory_init
       |> Interpretation.global_interpretation exp []
       |> Proof.global_terminal_proof
            ((Method.Basic (Method.METHOD o Classical.standard_tac), Position.no_range),
             SOME (Method.Basic (Method.SIMPLE_METHOD o Tactical.ALLGOALS o Simplifier.simp_tac),
                   Position.no_range))
       |> Local_Theory.exit_global
       |> pair ([],[])
      else
        let val goals = #goal (Proof.raw_goal (Interpretation.global_interpretation exp []
                                                                (Named_Target.theory_init thy)))
                     |> Thm.prems_of
            val num = length goals
            fun dest_conj_lift N X =
                  if N <= 1 then [X] else (case Conjunction.elim X of (A,B)
                                             => A :: dest_conj_lift (N-1) B)
         in thy
         |> Debt_Axiom.debt_axiomatization new_fields [] []
                [((Binding.suffix_name "_ax" space_xname, []), Logic.mk_conjunction_list goals)]
         |> (fn ((consts, [ax]), thy0) =>
        let val thy = thy0
                  |> Entries.map (fold2 (fn C => fn (N,item) =>
                            Symtab.update_new (N,(C,item))) consts space_entries)
            val axs = dest_conj_lift num ax
            val (field_terms2, exp2) = calc_field_terms thy
            val exp_properties : Expression.expression_i =
              (maps2 (fn (B,TM,Es) => fn C =>
                  map (fn (locale, map_rewr) =>
                      (locale, ((Config.mandatory_path^"."^Binding.name_of B,true),
                                Config.prepare_map_rewr B C TM map_rewr))) Es) entries consts
                  , [])
         in thy
         |> Named_Target.theory_init
         |> Interpretation.global_interpretation exp2 []
         |> Proof.global_terminal_proof ((Method.Basic (K (Method.SIMPLE_METHOD (fn thm =>
              Seq.single (fold (fn Ax => fn S => Thm.implies_elim S Ax) axs thm)
            ))) , Position.no_range), NONE)
         |> Local_Theory.exit_global
         |> pair exp_properties
        end)
        end
      end)
|> (fn x => x)
   |> "" <> Config.mandatory_path ? apsnd Sign.parent_path
   |> apsnd Named_Target.theory_init
   |-> Interpretation.isar_interpretation
  end

val declare_entries_i = gen_declare_entries Config.Loc.cert_arg (K I)
val declare_entries = gen_declare_entries Config.Loc.read_arg read_expr

val instance = Scan.optional (Parse.where_ |--
  Parse.and_list1 (Parse.name -- (Parse.$$$ "=" |-- Parse.term)) >> Expression.Named ||
  Scan.repeat1 (Parse.maybe Parse.term) >> Expression.Positional) (Expression.Named []) --
  (Scan.optional (Parse.$$$ "rewrites" |--
                      Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.prop)) []);

fun plus1_unless test scan =
  scan ::: Scan.repeat (Parse.$$$ "+" |-- Scan.unless test (Parse.!!! scan));

val locale_keyword' =
  Parse.$$$ "includes" || Parse_Spec.locale_keyword;

val locale_expression =
  let
    val expr2 = Parse.name_position;
    val expr1 = expr2 -- instance;
    val expr0 = plus1_unless locale_keyword' expr1;
  in expr0 end

val comp = Parse.binding --| \<^keyword>\<open>::\<close> -- Parse.!!! Parse.typ
              -- Scan.optional (\<^keyword>\<open>(\<close> |-- locale_expression --| \<^keyword>\<open>)\<close>) []
           >> (fn ((name,ty),expr) => (name,ty,expr))

val parent = Parse.name_position


fun define_command kwd comment = Outer_Syntax.command kwd comment
      (Parse.binding -- Scan.optional (\<^keyword>\<open>=\<close> |--
        ((Scan.repeat1 comp >> pair []) ||
          (plus1_unless comp parent --
            Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! (Scan.repeat1 comp)) []))) ([],[])
      >> (fn (name_b, (parents, entries)) =>
            Toplevel.local_theory_to_proof NONE NONE (fn lthy => lthy
                |> Local_Theory.exit_global
                |> declare_entries name_b parents entries)))

end


structure Resource_Space_Argument : GENERIC_RESOURCE_SPACE_ARGUMENT = struct

structure Loc = Resource_Locale_Argument

val additional_data' = ()
val prepare_space_name_binding = Binding.suffix_name "_res"
val mandatory_path = "RES"

fun prepare_map_rewr field_B field domain (Expression.Positional TMS, rw) =
      (Expression.Positional (SOME field :: TMS), rw)
  | prepare_map_rewr field_B field domain (Expression.Named TMS, rw) =
      (Expression.Named (("Res", field) :: TMS), rw)

fun field_typ_of tm =
  case type_of tm of \<^Type>\<open>sep_homo_set T\<close> => \<^Type>\<open>Resource_Space.kind \<^Type>\<open>RES_N\<close> \<^Type>\<open>RES\<close> T\<close>
                   | TY => raise TYPE ("Internal Bug #qcujm903", [TY], [])

fun space_locale_exp fields =
  (Expression.Positional ([SOME \<^term>\<open>RES.DOMAIN\<close>] @ map SOME fields
      @ [SOME \<^term>\<open>TYPE(RES_N)\<close>, SOME \<^term>\<open>TYPE(RES)\<close>]), [])

end

structure Resource_Space = Generic_Resource_Space(Resource_Space_Argument)

