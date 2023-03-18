(* Author: Norbert Schirmer, TU Muenchen, 2007
 * Author: Norbert Schirmer, Apple, 2021
 * Author: Qiyuan Xu, 2022, 2023
 * Modified from state_space.ML written by Norbert Schirmer. *)

signature RESOURCE_LOCALE = sig

val distinct_compsN : string
val namesN : string
val typeN : string
val fields_locale_N : string
val TVAR_N : string

type additional_data
type additional_data'

  val define_Resource_Locale_command : Outer_Syntax.command_keyword -> string -> unit

  val namespace_definition :
     binding ->
     typ ->
     (xstring, string) Expression.expr * (binding * string option * mixfix) list ->
     string list -> string list -> theory -> theory

  val define_Resource_Locale :
     string * (string * Position.T) ->
     additional_data ->
     (xstring * Position.T) option ->
     (string * string option) list ->
     binding ->
     ((string * bool) * (string list * (bstring * Position.T) * (string * string) list)) list ->
     (string * string) list -> theory -> theory
  val define_Resource_Locale_i :
     sort * (xstring * Position.T) ->
     additional_data' ->
     (xstring * Position.T) option ->
     (string * string option) list ->
     binding ->
     ((string * bool) * (typ list * (bstring * Position.T) * (string * string) list)) list ->
     (string * term) list -> theory -> theory

  val neq_x_y : Proof.context -> term -> term -> thm option
  val distinctNameSolver : Simplifier.solver
  val distinctTree_tac : Proof.context -> int -> tactic
  val distinct_simproc : Simplifier.simproc


  type Resource_Locale_info =
   {sort: sort, (* sort of representation *)
    args: (string * sort) list, (* type arguments *)
    parents: (typ list * string * string option list) list,
              (* type instantiation, Resource_Locale name, component renamings *)
    components: (string * term) list
   }

  val locales : Context.generic -> Resource_Locale_info Symtab.table

  val get_silent : Context.generic -> bool
  val set_silent : bool -> Context.generic -> Context.generic

  val trace_entry_data: Context.generic -> unit
  val trace_Resource_Locale_data: Context.generic -> unit

end

signature GENERIC_RESOURCE_LOCALE_ARGUMENT = sig

type additional_data
type additional_data'
type env = (string * sort) list

val entryT : typ -> typ -> typ -> typ
val prep_additional_data : Proof.context -> additional_data -> env -> additional_data' * env
val chk_additional_data : Proof.context -> additional_data' -> env -> additional_data' * env
val additional_data_parser : string * string -> (additional_data * (string * (string * Position.T))) parser

val repN : string
val repTN : string
val nameTN : string
val NAME_N : string

val read_arg : Proof.context -> additional_data' -> string -> (string * sort) list -> term * (string * sort) list
val cert_arg : Proof.context -> additional_data' -> term -> (string * sort) list -> term * (string * sort) list
val dest_typ : typ -> typ
val field_locale : string
val space_locale : string
val space_locale_args : additional_data' -> typ -> (string * typ) list

end


functor Generic_Resource_Locale (Config : GENERIC_RESOURCE_LOCALE_ARGUMENT) : RESOURCE_LOCALE = struct

(* Names *)

val distinct_compsN = "distinct_names"
val namesN = "_names"
val fields_locale_N = "_fields"
val typeN = "THE_TYPE"
val TVAR_N = "TYPE"

type additional_data  = Config.additional_data
type additional_data' = Config.additional_data'

(*** Library ***)

(* Misc *)

fun repT S = TFree (Config.repN, S)
fun dest_typ' TM = Config.dest_typ (Term.type_of TM)
      handle TYPE (msg, TYs, _) => raise TYPE (msg, TYs, [TM])

fun cons_name_of (Free (s,_)) = s
  | cons_name_of (Const (\<^const_name>\<open>kind.name\<close>, _) $ x) = Term.term_name x
  | cons_name_of t = raise TERM ("const_name_of", [t])

fun comps_of_distinct_thm thm = Thm.prop_of thm
  |> (fn (_$(_$t)) => DistinctTreeProver.dest_tree t) |> map cons_name_of |> sort_strings;

fun fold1 f xs = fold f (tl xs) (hd xs)
fun fold1' f [] x = x
  | fold1' f xs _ = fold1 f xs

fun sorted_subset eq [] ys = true
  | sorted_subset eq (x::xs) [] = false
  | sorted_subset eq (x::xs) (y::ys) = if eq (x,y) then sorted_subset eq xs ys
                                       else sorted_subset eq (x::xs) ys;

(* Locale *)

fun expression_no_pos (expr, fixes) : Expression.expression =
  (map (fn (name, inst) => ((name, Position.none), inst)) expr, fixes);


fun prove_interpretation_in ctxt_tac (name, expr) thy =
   thy
   |> Interpretation.global_sublocale_cmd (name, Position.none) (expression_no_pos expr) []
   |> Proof.global_terminal_proof
         ((Method.Basic (fn ctxt => SIMPLE_METHOD (ctxt_tac ctxt)), Position.no_range), NONE)
   |> Proof_Context.theory_of

fun add_locale name expr elems thy =
  thy
  |> Expression.add_locale name name [] expr elems
  |> snd
  |> Local_Theory.exit;

fun add_locale_cmd name expr elems thy =
  thy
  |> Expression.add_locale_cmd name Binding.empty [] (expression_no_pos expr) elems
  |> snd
  |> Local_Theory.exit;


(*** Persistent Data ***)

(** entry_info **)

(* distinct_thm *)

fun comps_of_distinct_thm thm = Thm.prop_of thm
  |> (fn (_$(_$t)) => DistinctTreeProver.dest_tree t) |> map cons_name_of |> sort_strings;

fun insert_tagged_distinct_thms tagged_thm tagged_thms =
 let
   fun ins t1 [] = [t1]
     | ins (t1 as (names1, _)) ((t2 as (names2, _))::thms) =
         if Ord_List.subset string_ord (names1, names2) then t2::thms
         else if Ord_List.subset string_ord (names2, names1) then ins t1 thms
         else t2 :: ins t1 thms
 in
   ins tagged_thm tagged_thms
 end

fun join_tagged_distinct_thms tagged_thms1 tagged_thms2 =
  tagged_thms1 |> fold insert_tagged_distinct_thms tagged_thms2

fun tag_distinct_thm thm = (comps_of_distinct_thm thm, thm)
val tag_distinct_thms = map tag_distinct_thm

fun join_distinct_thms thms1 thms2 =
  if pointer_eq (thms1, thms2) then thms1
  else join_tagged_distinct_thms (tag_distinct_thms thms1) (tag_distinct_thms thms2)
       |> map snd

fun insert_distinct_thm thm thms = join_distinct_thms thms [thm]

val join_distinctthm_tab = Symtab.join (fn name => fn (thms1, thms2) => join_distinct_thms thms1 thms2)

(* declinfo_entry *)

fun join_declinfo_entry name (T1:term, names1:string list) (T2, names2) =
  let
    fun typ_info T names = @{make_string} T ^ " "  ^ Pretty.string_of (Pretty.str_list "(" ")" names);
  in
    if T1 = T2 then (T1, distinct (op =) (names1 @ names2))
    else error ("entry '" ^ name ^ "' disagrees on interpretation:\n " ^
        typ_info T1 names1 ^ " vs. "  ^ typ_info T2 names2)
  end
fun guess_name (Free (x,_)) = x
  | guess_name _ = "unknown"

val join_declinfo = Termtab.join (fn trm => uncurry (join_declinfo_entry (guess_name trm)))

(* EntryData *)

type entry_info =
 {distinctthm: thm list Symtab.table, (* minimal list of maximal distinctness-assumptions
                                         for a component name *)
  silent: bool
 }


structure EntryData = Generic_Data
(
  type T = entry_info;
  val empty = {distinctthm = Symtab.empty, silent = false};
  fun merge
    ({distinctthm=distinctthm1, silent=silent1},
      {distinctthm=distinctthm2, silent=silent2}) : T =
    {distinctthm = join_distinctthm_tab (distinctthm1, distinctthm2),
     silent = silent1 andalso silent2 (* FIXME odd merge *)}
)

fun trace_entry_data context =
  tracing ("EntryData: " ^ @{make_string} (EntryData.get context))

fun make_entry_data distinctthm silent =
     {distinctthm=distinctthm,silent=silent}

fun set_silent silent ctxt =
  let val {distinctthm,...} = EntryData.get ctxt;
  in EntryData.put (make_entry_data distinctthm silent) ctxt
  end

val get_silent = #silent o EntryData.get


(** Resource_Locale **)

type Resource_Locale_info =
 {sort: sort, (* sort of representation *)
  args: (string * sort) list, (* type arguments *)
  parents: (typ list * string * string option list) list,
            (* type instantiation, Resource_Locale name, component renamings *)
  components: (string * term) list
 }

structure Resource_Locale_Data = Generic_Data
(
  type T = Resource_Locale_info Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
)

val locales = Resource_Locale_Data.get

fun trace_Resource_Locale_data context =
  tracing ("StateSpaceData: " ^ @{make_string} (Resource_Locale_Data.get context))

fun add_Resource_Locale name Sv args parents components ctxt =
      Resource_Locale_Data.put
        (Symtab.update_new (name, {sort=Sv,args=args,parents=parents,
                                   components=components})
                           (Resource_Locale_Data.get ctxt))
        ctxt;

fun get_Resource_Locale ctxt name =
      Symtab.lookup (Resource_Locale_Data.get ctxt) name;



(** Accessors of above two structure **)

fun mk_free ctxt name =
  if Variable.is_fixed ctxt name orelse Variable.is_declared ctxt name
  then
    let
      val n' = Variable.intern_fixed ctxt name |> perhaps Long_Name.dest_hidden;
      val free = Free (n', Proof_Context.infer_type ctxt (n', dummyT))
    in SOME (free) end
  else (tracing ("variable not fixed or declared: " ^ name); NONE)


fun get_dist_thm ctxt name = Symtab.lookup (#distinctthm (EntryData.get ctxt)) name

fun get_dist_thm2 ctxt x y =
 (let
    val dist_thms = [x, y] |> map cons_name_of
      |> map (these o get_dist_thm (Context.Proof ctxt)) |> flat;

    fun get_paths dist_thm =
      let
        val ctree = Thm.cprop_of dist_thm |> Thm.dest_comb |> #2 |> Thm.dest_comb |> #2;
        val tree = Thm.term_of ctree;
        val x_path = the (DistinctTreeProver.find_tree x tree);
        val y_path = the (DistinctTreeProver.find_tree y tree);
      in SOME (dist_thm, x_path, y_path) end
      handle Option.Option => NONE

    val result = get_first get_paths dist_thms
  in
    result
  end)


(*** Tactics ***)

fun neq_x_y ctxt x y =
  (let
    val (dist_thm, x_path, y_path) = the (get_dist_thm2 ctxt x y);
    val thm = DistinctTreeProver.distinctTreeProver ctxt dist_thm x_path y_path;
  in SOME thm
  end handle Option.Option => NONE)

fun distinctTree_tac ctxt = SUBGOAL (fn (goal, i) =>
  (case goal of
    Const (\<^const_name>\<open>Trueprop\<close>, _) $
      (Const (\<^const_name>\<open>Not\<close>, _) $
        (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ x $ y)) =>
      (case neq_x_y ctxt x y of
        SOME neq => resolve_tac ctxt [neq] i
      | NONE => no_tac)
  | _ => no_tac));

val distinctNameSolver = mk_solver "distinctNameSolver" distinctTree_tac;

val distinct_simproc =
  Simplifier.make_simproc \<^context> "StateSpace.distinct_simproc"
   {lhss = [\<^term>\<open>kind.name x = kind.name y\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>HOL.eq\<close>,_) $ x $ y =>
          Option.map (fn neq => DistinctTreeProver.neq_to_eq_False OF [neq])
              (neq_x_y ctxt x y)
      | _ => NONE)};

fun interprete_parent_entry name dist_thm_name parent_expr thy =
  let
    fun solve_tac ctxt = CSUBGOAL (fn (goal, i) =>
      let
        val distinct_thm = Proof_Context.get_thm ctxt dist_thm_name;
        val rule = DistinctTreeProver.distinct_implProver ctxt distinct_thm goal;
      in resolve_tac ctxt [rule] i end);

    fun tac ctxt =
      Locale.intro_locales_tac {strict = true, eager = true} ctxt [] THEN ALLGOALS (solve_tac ctxt);

  in
    thy |> prove_interpretation_in tac (name, parent_expr)
  end;


(*** Main Stuffs ***)

(** define cons **)

fun namespace_definition name nameT parent_expr parent_comps new_comps thy =
  let
    val pos = Binding.pos_of name
    val all_comps = parent_comps @ new_comps;
    val vars = (Binding.make (typeN,pos), SOME (Term.itselfT nameT), NoSyn)
          ::(map (fn n => (Binding.make (n,pos), NONE, NoSyn)) all_comps);
    val dist_thm_name = distinct_compsN;

    val dist_thm_full_name = dist_thm_name;

    fun type_attr phi = Thm.declaration_attribute (fn thm => fn context =>
      (case context of
        Context.Theory _ => context
      | Context.Proof ctxt =>
        let
          val {distinctthm=tt,silent} = EntryData.get context;
          val all_names = comps_of_distinct_thm thm;
          fun upd name = Symtab.map_default (name, [thm]) (fn thms => insert_distinct_thm thm thms)

          val tt' = tt |> fold upd all_names;
          val context' =
              Context_Position.set_visible false ctxt
              addsimprocs [distinct_simproc]
              |> Context_Position.restore_visible ctxt
              |> Context.Proof
              |> EntryData.put {distinctthm=tt',silent=silent};
        in context' end));

    val attr = Attrib.internal type_attr;

    val assume =
      ((Binding.name dist_thm_name, [attr]),
        [(HOLogic.Trueprop $
          (Const (\<^const_name>\<open>all_distinct\<close>, Type (\<^type_name>\<open>tree\<close>, [nameT]) --> HOLogic.boolT) $
            DistinctTreeProver.mk_tree (fn n => Free (n, nameT)) nameT
              (sort fast_string_ord all_comps)), [])]);
  in
    thy
    |> add_locale name ([], vars) [Element.Assumes [assume]]
    |> Proof_Context.theory_of
    |> interprete_parent_entry (Binding.name_of name) dist_thm_full_name parent_expr
  end;


(** define Resource_Locale **)

(* preliminary *)

fun encode_dot x = if x = #"." then #"_" else x;

fun encode_type (TFree (s, _)) = s
  | encode_type (TVar ((s,i),_)) = "?" ^ s ^ string_of_int i
  | encode_type (Type (n,Ts)) =
      let
        val Ts' = fold1' (fn x => fn y => x ^ "_" ^ y) (map encode_type Ts) "";
        val n' = String.map encode_dot n;
      in if Ts'="" then n' else Ts' ^ "_" ^ n' end;

fun parent_sort thy pname Sv =
  let
    val ctxt = Context.Theory thy;
    val {sort, parents, ...} = the (Symtab.lookup (Resource_Locale_Data.get ctxt) pname);
  in
    fold (parent_sort thy o #2) parents (Sign.inter_sort thy (Sv, sort))
  end

fun parent_components thy Sv (Ts, pname, renaming) =
  let
    val ctxt = Context.Theory thy;
    fun rename [] xs = xs
      | rename (NONE::rs)  (x::xs) = x::rename rs xs
      | rename (SOME r::rs) ((x,T)::xs) = (r,T)::rename rs xs;
    val {args, parents, components, ...} =
                  the (Symtab.lookup (Resource_Locale_Data.get ctxt) pname);
    val inst = (Config.repN, repT Sv) :: (map fst args ~~ Ts);
    val subst = Term.map_type_tfree (fn (N,S) =>
                    the_default (TFree (N,S)) (AList.lookup (op =) inst N));
    val parent_comps =
      maps (fn (Ts',n,rs) => parent_components thy Sv (map subst Ts', n, rs)) parents;
    val all_comps = rename renaming (parent_comps @ map (apsnd (Term.map_types subst)) components);
  in all_comps end;

(* main stuff *)

fun Resource_Locale_definition rep_sort project_injectL additional_data'
                   target args name_b parents parent_comps components thy =
  let
    val name = Binding.name_of name_b
    val pos = Binding.pos_of name_b
    val full_name = Sign.full_bname thy name;
    val all_comps = parent_comps @ components;

    val components' = map (fn (n,T) => (n, (T, full_name))) components;

    val repT = repT rep_sort
    val repTT = Term.itselfT repT
    val nameT = TFree (Config.NAME_N, \<^sort>\<open>type\<close>);
    val nameTT  = Term.itselfT nameT
    val entryT = Config.entryT nameT repT
    val NAME_TY = Free(Config.nameTN, nameTT)
    val VALUE_TY = Free(Config.repTN, repTT)
    val TVARS = map (fn (T,S) => (prefix TVAR_N T, Term.itselfT (TFree(T,S)))) args

    fun parent_expr (prefix, (_, n, rs)) =
      (suffix namesN n,
        (prefix,(Expression.Positional (SOME typeN :: rs),[])));
    val parents_expr = map parent_expr parents;

    val space_locale_args' = Config.space_locale_args additional_data' repT
    val space_locale_args  = map (SOME o Free) space_locale_args'

    val locinsts' =
          (Config.space_locale, (("",false),
                (Expression.Positional space_locale_args,[]))) ::
          map (fn (n,T) => (project_injectL,
                    ((n,false),(Expression.Positional
                         (space_locale_args @
                          [SOME (Free (n, entryT (dest_typ' T))),
                           SOME T])
                    ,[])))) all_comps;

    val locs' = (Binding.name Config.nameTN, SOME (Term.itselfT nameT), NoSyn) ::
                (Binding.name Config.repTN,  SOME (Term.itselfT repT),  NoSyn) ::
                (map (fn (N,T) => (Binding.name N, SOME T, NoSyn)) space_locale_args') @
                 maps (fn (n,T) => [(Binding.name n, NONE, NoSyn)]) all_comps @
                 map (fn (N,Ty) => (Binding.name N, SOME Ty, NoSyn) ) TVARS

    val (locinsts,locs) =
          case target of SOME t =>
              let
                val params = Locale.params_of thy (the target)
              in
                ((t,(("",false),(Expression.Positional (map (SOME o Free o fst) params),[])))
                 ::locinsts'
                ,locs' @
                 map_filter (fn ((N,T),M) => if exists (fn (N',_,_) => N = Binding.name_of N') locs'
                                             then NONE
                                             else SOME (Binding.name N, SOME T, M)) params)
              end
            | NONE => (locinsts',locs')

    val name_insts = map (fn (n,T) =>
          (n, Const (\<^const_name>\<open>kind.name\<close>, entryT (dest_typ' T) --> nameT)
                $ Free (n, entryT (dest_typ' T)))) all_comps

    fun interprete_parent_valuetypes (prefix, (Ts, pname, comps)) thyx =
      let
        val {components,...} =
             the (Symtab.lookup (Resource_Locale_Data.get (Context.Theory thyx)) pname);
        val components' = map (uncurry the_default) (map fst components ~~ comps)
        val pars = components';

        val expr = ([(suffix fields_locale_N pname,
                     (prefix, (Expression.Positional (map SOME (
                                  Config.nameTN::Config.repTN::(map fst space_locale_args')@pars)),
                               [])))],
                    []);

      in
        prove_interpretation_in (fn ctxt =>
            Locale.intro_locales_tac {strict = true, eager = false} ctxt [])
          (suffix fields_locale_N name, expr) thyx
      end;

    fun interprete_parent (prefix, (_, pname, rs)) =
      let
        val rs' = [NONE] @ rs
        val expr = ([(pname, (prefix, (Expression.Positional rs',[])))],[])
      in prove_interpretation_in
           (fn ctxt => Locale.intro_locales_tac {strict = true, eager = false} ctxt [])
           (full_name, expr) end;

  in thy
     |> namespace_definition
           (Binding.suffix_name namesN name_b) nameT (parents_expr,[])
           (map fst parent_comps) (map fst components)
     |> Context.theory_map
          (add_Resource_Locale full_name rep_sort args (map snd parents) all_comps)
     |> add_locale (Binding.suffix_name fields_locale_N name_b) (locinsts,locs) []
     |> Proof_Context.theory_of
     |> fold interprete_parent_valuetypes parents
     |> add_locale name_b
            (  [(suffix namesN full_name,
                  ((name ^ "_" ^ namesN, true),
                   (Expression.Named ((typeN, NAME_TY)::name_insts)
                   ,[]))),
                (suffix fields_locale_N full_name,
                  (("",false),(Expression.Named [(Config.nameTN, NAME_TY),(Config.repTN, VALUE_TY)], []))
                )],
               [(Binding.name Config.nameTN,  SOME nameTT,  NoSyn),
                (Binding.name Config.repTN, SOME repTT, NoSyn)])
            []
     |> Proof_Context.theory_of
     |> fold interprete_parent parents
  end;

(** preparation & wrapper for Resource_Locale **)

(* prepare arguments *)

fun read_typ ctxt raw_T env =
  let
    val ctxt' = fold (Variable.declare_typ o TFree) env ctxt;
    val T = Syntax.read_typ ctxt' raw_T;
    val env' = Term.add_tfreesT T env;
  in (T, env') end;

fun cert_typ ctxt raw_T env =
  let
    val thy = Proof_Context.theory_of ctxt;
    val T = Type.no_tvars (Sign.certify_typ thy raw_T)
      handle TYPE (msg, _, _) => error msg;
    val env' = Term.add_tfreesT T env;
  in (T, env') end;

fun gen_define_Resource_Locale prep_typ prep_term prep_sort prep_data
                   (sort,project_injectL) additional_data
                   target args name_b parents comps thy =
  let (* - args distinct
         - only args may occur in comps and parent-instantiations
         - number of insts must match parent args
         - no duplicate renamings
         - renaming should occur in entry
         -
         - self_sort: sort of the value type
      *)
    val _ = writeln ("Defining Resource_Locale " ^ Binding.print name_b ^ " ...");

    val target' = Option.map (Locale.check thy) target

    val ctxt = case target' of SOME t => Locale.init t thy
                             | NONE => Proof_Context.init_global thy

    fun add_parent (prefix, (Ts, pname, rs)) env =
      let
        val prefix' =
          (case prefix of
            ("", mandatory) => (fst pname, mandatory)
          | _ => prefix);

        val full_pname = Locale.check thy pname;
        val quote = quote o fst
        val {args,components,...} =
              (case get_Resource_Locale (Context.Theory thy) full_pname of
                SOME r => r
               | NONE => error ("Undefined Resource_Locale " ^ quote pname));


        val (Ts',env') = fold_map (prep_typ ctxt) Ts env
            handle ERROR msg => cat_error msg
                    ("The error(s) above occurred in parent Resource_Locale specification "
                    ^ quote pname);
        val err_insts = if length args <> length Ts' then
            ["number of type instantiation(s) does not match arguments of parent Resource_Locale "
              ^ quote pname]
            else [];

        val rnames = map fst rs
        val err_dup_renamings = (case duplicates (op =) rnames of
             [] => []
            | dups => ["Duplicate renaming(s) for " ^ commas dups])

        val cnames = map fst components;
        val err_rename_unknowns = (case subtract (op =) cnames rnames of
              [] => []
             | rs => ["Unknown components " ^ commas rs]);


        val rs' = map (AList.lookup (op =) rs o fst) components;
        val errs =err_insts @ err_dup_renamings @ err_rename_unknowns
      in
        if null errs then ((prefix', (Ts', full_pname, rs')), env')
        else error (cat_lines (errs @ ["in parent Resource_Locale " ^ quote pname]))
      end;

    val args' = map (apsnd (Option.map (Syntax.read_sort ctxt) #> the_default (Sign.defaultS thy))) args
    val (additional_data',env) = prep_data ctxt additional_data args'
    val (parents',env) = fold_map add_parent parents args';

    val sort' = fold (parent_sort thy o #2 o #2) parents' (prep_sort ctxt sort)
    val env = (Config.repN, sort')::env


    val err_dup_args =
         (case duplicates (op =) (map fst args) of
            [] => []
          | dups => ["Duplicate type argument(s) " ^ commas dups]);


    val err_dup_components =
         (case duplicates (op =) (map fst comps) of
           [] => []
          | dups => ["Duplicate state-space components " ^ commas dups]);

    fun prep_comp (n,T) env =
      let val (T', env') = prep_term ctxt additional_data' T env handle ERROR msg =>
       cat_error msg ("The error(s) above occurred in component " ^ quote n)
      in ((n,T'), env') end;

    val (comps',env') = fold_map prep_comp comps env;

    val err_value_keyword =
          if member (op =) (map fst args) Config.repN
          then ["'self is a reserved keyword and cannot be a type parameter"]
          else []


    (*TODO!!!*)
    val err_extra_frees = []

    val project_injectL = Locale.check thy project_injectL


    fun fst_eq ((x:string,_),(y,_)) = x = y;
    fun snd_eq ((_,t:term),(_,u)) = t = u;

    val raw_parent_comps = maps (parent_components thy sort' o snd) parents';
    fun check_type (n,T) =
          (case distinct (snd_eq) (filter (curry fst_eq (n,T)) raw_parent_comps) of
             []  => []
           | [_] => []
           | rs  => ["Different interpretation for component " ^ quote n ^ ": " ^
                commas (map (Syntax.string_of_term ctxt o snd) rs)])

    val err_dup_types = maps check_type (duplicates fst_eq raw_parent_comps)

    val parent_comps = distinct (fst_eq) raw_parent_comps;
    val all_comps = parent_comps @ comps';
    val err_comp_in_parent = (case duplicates (op =) (map fst all_comps) of
               [] => []
             | xs => ["Components already defined in parents: " ^ commas_quote xs]);
    val errs = err_dup_args @ err_dup_components @ err_extra_frees @
               err_dup_types @ err_comp_in_parent @ err_value_keyword;
  in if null errs
     then thy |> Resource_Locale_definition sort' project_injectL additional_data'
                                target' args' name_b parents' parent_comps comps'
     else error (cat_lines errs)
  end
  handle ERROR msg => cat_error msg ("Failed to define resource space " ^ Binding.print name_b);

val define_Resource_Locale =
      gen_define_Resource_Locale read_typ Config.read_arg
      (fn ctxt => fn S => if S = "" then \<^sort>\<open>sep_algebra\<close> else Syntax.read_sort ctxt S)
      Config.prep_additional_data
val define_Resource_Locale_i =
      gen_define_Resource_Locale cert_typ Config.cert_arg
      (fn ctxt => fn S => if null S then \<^sort>\<open>sep_algebra\<close> else Syntax.check_sort ctxt S)
      Config.chk_additional_data


(*** outer syntax ***)

local

val type_insts =
  Parse.typ >> single ||
  \<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 Parse.typ --| \<^keyword>\<open>)\<close>)

val comp = Parse.name -- (\<^keyword>\<open>::\<close> |-- Parse.!!! Parse.typ);
fun plus1_unless test scan =
  scan ::: Scan.repeat (\<^keyword>\<open>+\<close> |-- Scan.unless test (Parse.!!! scan));

val mapsto = \<^keyword>\<open>=\<close>;
val rename = Parse.name -- (mapsto |-- Parse.name);
val renames = Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.!!! (Parse.list1 rename --| \<^keyword>\<open>]\<close>)) [];

val parent =
  Parse_Spec.locale_prefix --
  ((type_insts -- Parse.name_position) || (Parse.name_position >> pair [])) -- renames
    >> (fn ((prefix, (insts, name)), renames) => (prefix, (insts, name, renames)));

in

fun Resource_Locale_decl' defaults =
  Parse.opt_target -- (Parse.type_args_constrained -- Parse.binding)
  -- Config.additional_data_parser defaults --
  (Scan.optional (\<^keyword>\<open>=\<close> |--
    ((Scan.repeat1 comp >> pair []) ||
      (plus1_unless comp parent --
        Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! (Scan.repeat1 comp)) []))) ([],[]));


fun define_Resource_Locale_command' defaults_setting kwd comment =
  Outer_Syntax.command kwd comment
    (Resource_Locale_decl' defaults_setting >> (
  fn (((target, (args, name)), (additional_data, sort_locale)), (parents, comps)) =>
      Toplevel.theory (define_Resource_Locale sort_locale additional_data target args name parents comps)));

val define_Resource_Locale_command = define_Resource_Locale_command' ("", Config.field_locale)

end

end




signature RESOURCE_LOCALE_ARGUMENT = sig

include GENERIC_RESOURCE_LOCALE_ARGUMENT

val DOMAIN_N : string

end

structure Resource_Locale_Argument : RESOURCE_LOCALE_ARGUMENT = struct

type additional_data  = unit
type additional_data' = unit
type env = (string * sort) list
val prep_additional_data = K pair
val chk_additional_data = K pair

fun entryT nameT repT T = \<^Type>\<open>kind nameT repT T\<close>
fun additional_data_parser (default_sort, default_locale) =
      Scan.optional (\<^keyword>\<open>::\<close> |-- (
        Parse.sort -- Scan.optional (\<^keyword>\<open>,\<close> |-- Parse.name_position) (default_locale, Position.none)
      )) (default_sort,(default_locale, Position.none))
      >> pair ()

val repN = "'REP"
val repTN = "TYPE'REP"
val nameTN = "TYPE'NAME"
val NAME_N = "'REP_N"
val DOMAIN_N = "DOMAIN"

fun read_arg ctxt _ raw_T env =
  let
    val ctxt' = fold (Variable.declare_typ o TFree) env ctxt;
    val TM0 = Syntax.parse_term ctxt' raw_T
    val chk = Syntax.check_term ctxt' o Type.constraint \<^Type>\<open>sep_homo_set dummyT\<close>
    val T = chk TM0
        handle err => (chk (\<^Const>\<open>sep_homo_set dummyT\<close> $ TM0)
        handle _ => raise err)
    val env' = Term.add_tfrees T env;
  in (T, env') end;

fun cert_arg ctxt _ raw_TM env =
  let
    val thy = Proof_Context.theory_of ctxt;
    val chk = Sign.certify_term thy
            o Syntax.check_term ctxt
            o Type.constraint \<^Type>\<open>sep_homo_set dummyT\<close>
    val (Tm,Ty,_) = chk raw_TM
         handle err => (chk (\<^Const>\<open>sep_homo_set dummyT\<close> $ raw_TM)
         handle _ => raise err)
    val _ = Type.no_tvars Ty
      handle TYPE (msg, _, _) => error msg;
    val Tm = Sign.no_vars ctxt Tm
    val env' = Term.add_tfrees Tm env;
  in (Tm, env') end;

fun dest_typ (\<^Type>\<open>sep_homo_set T\<close>) = T
  | dest_typ T = raise TYPE ("shoud be a sep_homo_set", [T], [])

val field_locale = \<^locale>\<open>resource_kind'\<close>
val space_locale = \<^locale>\<open>resource_space\<close>

val nameT = TFree (NAME_N, \<^sort>\<open>type\<close>);
val nameTT = Term.itselfT nameT

fun space_locale_args _ repT =
  let val domainT = nameT --> \<^Type>\<open>sep_homo_set repT\<close>
   in [(DOMAIN_N, domainT)]
  end

(* val space_locale_args : (term * typ) list *)

end

structure Resource_Locale = Generic_Resource_Locale(Resource_Locale_Argument)

