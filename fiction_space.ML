(* AUTHOR: Qiyuan Xu, 2022
 * Modified from state_space.ML written by Norbert Schirmer. *)

signature FICTION_SPACE = sig

val distinct_compsN : string
val namesN : string
val repN : string
val typeN : string
val repTN : string
val nameTN : string
val NAME_N : string
val INTERPRET_N : string
val fields_locale_N : string


  val define_FIS_command :
        Outer_Syntax.command_keyword ->
        string -> string * string -> unit


  val namespace_definition :
     binding ->
     typ ->
     (xstring, string) Expression.expr * (binding * string option * mixfix) list ->
     string list -> string list -> theory -> theory

  val define_FIS :
     string * (string * Position.T) ->
     (xstring * Position.T) option ->
     (string * string option) list ->
     binding -> string ->
     ((string * bool) * (string list * (bstring * Position.T) * (string * string) list)) list ->
     (string * string) list -> theory -> theory
  val define_FIS_i :
     string * (xstring * Position.T) ->
     (xstring * Position.T) option ->
     (string * string option) list ->
     binding -> typ ->
     ((string * bool) * (typ list * (bstring * Position.T) * (string * string) list)) list ->
     (string * term) list -> theory -> theory

  val FIS_decl :
     ((((xstring * Position.T) option * ((string * string option) list * binding)) *
          (string * (string * (bstring * Position.T)))) *
       (((string * bool) * (string list * (bstring * Position.T) * (bstring * bstring) list)) list *
        (bstring * string) list)) parser
  val FIS_decl' :
        string * string ->
        ((((string * Position.T) option *
           ((string * string option) list * binding)) *
          (string * (string * (string * Position.T)))) *
         (((string * bool) * (string list * (string * Position.T) * (string * string) list)) list *
        (string * string) list)) parser


  val neq_x_y : Proof.context -> term -> term -> thm option
  val distinctNameSolver : Simplifier.solver
  val distinctTree_tac : Proof.context -> int -> tactic
  val distinct_simproc : Simplifier.simproc


  val is_FIS : Context.generic -> xstring -> bool

  val get_comp' : Context.generic -> string -> (term * string list) option
  val get_comp : Context.generic -> string -> (term * string) option (* legacy wrapper, eventually replace by primed version *)
  val get_comps : Context.generic -> (term * string list) Termtab.table

  val get_silent : Context.generic -> bool
  val set_silent : bool -> Context.generic -> Context.generic

  val trace_entry_data: Context.generic -> unit
  val trace_FIS_data: Context.generic -> unit

end

structure Fiction_Space : FICTION_SPACE = struct

(* Names *)

val distinct_compsN = "distinct_names"
val namesN = "_names"
val fields_locale_N = "_fields"
val repN = "'FIC"
val typeN = "THE_TYPE"
val repTN = "TYPE'REP"
val nameTN = "TYPE'NAME"
val NAME_N = "'FIC_N"
val INTERPRET_N = "INTERPRET"
val TVAR_N = "TYPE"


val project_injectL_default = \<^locale>\<open>fictional_project_inject\<close>



(*** Library ***)

(* Misc *)

fun repT S = TFree (repN, S)
fun entryT nameT repT T = Type(\<^type_name>\<open>Entry\<close>, [nameT, repT, T])
fun fictionT T resT = Type(\<^type_name>\<open>fiction\<close>, [T,resT])
fun T_of_fic fic =
  case Term.type_of fic of Type(\<^type_name>\<open>fiction\<close>, [T,_]) => T
    | _ => raise TYPE ("shoud be fiction", [Term.type_of fic], [fic])

fun cons_name_of (Free (s,_)) = s
  | cons_name_of (Const (\<^const_name>\<open>Entry.name\<close>, _) $ x) = Term.term_name x
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
 {declinfo: (term * string list) Termtab.table, (* interpretation, names of component  *)
  distinctthm: thm list Symtab.table, (* minimal list of maximal distinctness-assumptions for a component name *)
  silent: bool
 };


structure EntryData = Generic_Data
(
  type T = entry_info;
  val empty = {declinfo = Termtab.empty, distinctthm = Symtab.empty, silent = false};
  fun merge
    ({declinfo=declinfo1, distinctthm=distinctthm1, silent=silent1},
      {declinfo=declinfo2, distinctthm=distinctthm2, silent=silent2}) : T =
    {declinfo = join_declinfo (declinfo1, declinfo2),
     distinctthm = join_distinctthm_tab (distinctthm1, distinctthm2),
     silent = silent1 andalso silent2 (* FIXME odd merge *)}
);

fun trace_entry_data context =  
  tracing ("EntryData: " ^ @{make_string} (EntryData.get context))

fun make_entry_data declinfo distinctthm silent =
     {declinfo=declinfo,distinctthm=distinctthm,silent=silent};


fun update_declinfo (n,v) ctxt =
  let       
    val {declinfo,distinctthm,silent} = EntryData.get ctxt;
    val v = apsnd single v
  in EntryData.put (make_entry_data
        (Termtab.map_default (n,v) (join_declinfo_entry (guess_name n) v) declinfo)
        distinctthm silent) ctxt
  end;

fun set_silent silent ctxt =
  let val {declinfo,distinctthm,...} = EntryData.get ctxt;
  in EntryData.put
      (make_entry_data declinfo distinctthm silent) ctxt
  end;

val get_silent = #silent o EntryData.get;


(** FIS **)

type FIS_info =
 {sort: sort, (* sort of representation *)
  args: (string * sort) list, (* type arguments *)
  parents: (typ list * string * string option list) list,
            (* type instantiation, FIS name, component renamings *)
  components: (string * term) list
 };

structure FIS_Data = Generic_Data
(
  type T = FIS_info Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

fun is_FIS context name =
  Symtab.defined (FIS_Data.get context) (Locale.intern (Context.theory_of context) name)

fun trace_FIS_data context =  
  tracing ("StateSpaceData: " ^ @{make_string} (FIS_Data.get context))

fun add_FIS name Sv args parents components ctxt =
      FIS_Data.put
        (Symtab.update_new (name, {sort=Sv,args=args,parents=parents,
                                   components=components})
                           (FIS_Data.get ctxt))
        ctxt;

fun get_FIS ctxt name =
      Symtab.lookup (FIS_Data.get ctxt) name;



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
    
       
fun get_comp' ctxt name =
  mk_free (Context.proof_of ctxt) name 
  |> Option.mapPartial (fn t => 
       let
         val declinfo = #declinfo (EntryData.get ctxt)
       in 
         case Termtab.lookup declinfo t of
           NONE => (* during syntax phase, types of fixes might not yet be constrained completely *) 
             AList.lookup (fn (x, Free (n,_)) => n = x | _ => false) (Termtab.dest declinfo) name
         | some => some
       end)

(* legacy wrapper *)
fun get_comp ctxt name =
 get_comp' ctxt name |> Option.map (apsnd (fn ns => if null ns then "" else hd ns)) 

fun get_comps ctxt = #declinfo (EntryData.get ctxt)

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
   {lhss = [\<^term>\<open>Entry.name x = Entry.name y\<close>],
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
          val {declinfo,distinctthm=tt,silent} = EntryData.get context;
          val all_names = comps_of_distinct_thm thm;
          fun upd name = Symtab.map_default (name, [thm]) (fn thms => insert_distinct_thm thm thms)

          val tt' = tt |> fold upd all_names;
          val context' =
              Context_Position.set_visible false ctxt
              addsimprocs [distinct_simproc]
              |> Context_Position.restore_visible ctxt
              |> Context.Proof
              |> EntryData.put {declinfo=declinfo,distinctthm=tt',silent=silent};
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


(** define FIS **)

(* preliminary *)

fun encode_dot x = if x = #"." then #"_" else x;

fun encode_type (TFree (s, _)) = s
  | encode_type (TVar ((s,i),_)) = "?" ^ s ^ string_of_int i
  | encode_type (Type (n,Ts)) =
      let
        val Ts' = fold1' (fn x => fn y => x ^ "_" ^ y) (map encode_type Ts) "";
        val n' = String.map encode_dot n;
      in if Ts'="" then n' else Ts' ^ "_" ^ n' end;


fun add_declaration name decl thy =
  thy
  |> Named_Target.init [] name
  |> (fn lthy => Local_Theory.declaration {syntax = true, pervasive = false} (decl lthy) lthy)
  |> Local_Theory.exit_global;

fun parent_sort thy pname Sv =
  let
    val ctxt = Context.Theory thy;
    val {sort, parents, ...} = the (Symtab.lookup (FIS_Data.get ctxt) pname);
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
                  the (Symtab.lookup (FIS_Data.get ctxt) pname);
    val inst = (repN, repT Sv) :: (map fst args ~~ Ts);
    val subst = Term.map_type_tfree (fn (N,S) =>
                    the_default (TFree (N,S)) (AList.lookup (op =) inst N));
    val parent_comps =
      maps (fn (Ts',n,rs) => parent_components thy Sv (map subst Ts', n, rs)) parents;
    val all_comps = rename renaming (parent_comps @ map (apsnd (Term.map_types subst)) components);
  in all_comps end;

(* main stuff *)

fun FIS_definition rep_sort project_injectL
                   target args name_b resT parents parent_comps components thy =
  let
    val name = Binding.name_of name_b
    val pos = Binding.pos_of name_b
    val full_name = Sign.full_bname thy name;
    val all_comps = parent_comps @ components;

    val components' = map (fn (n,T) => (n,(T,full_name))) components;

    val arg_names = map fst args;
    (* 'self now is treated as a keyword so it doesn't need variant.*)
    (* val repN = singleton (Name.variant_list (repN :: arg_names)) "'self"; *)
    val nameN = singleton (Name.variant_list (repN :: arg_names)) "'name";
    val repT = repT rep_sort
    val repTT = Term.itselfT repT
    val resTT = Term.itselfT resT
    val nameT = TFree (NAME_N, Sign.defaultS thy);
    val nameTT  = Term.itselfT nameT
    val entryT = entryT nameT repT
    val domainT = nameT --> HOLogic.mk_setT repT
    val INTERP_T = nameT --> fictionT repT resT
    val INTERP = Free(INTERPRET_N, INTERP_T)
    val TYPE_TY = Free(nameTN, nameTT)
    val VALUE_TY = Free(repTN, repTT)
    val TVARS = map (fn (T,S) => (prefix TVAR_N T, Term.itselfT (TFree(T,S)))) args

    fun parent_expr (prefix, (_, n, rs)) =
      (suffix namesN n,
        (prefix,(Expression.Positional (SOME typeN :: rs),[])));
    val parents_expr = map parent_expr parents;

    val locinsts' =
          (\<^locale>\<open>fictional_space\<close>, (("",false),
                (Expression.Positional [SOME INTERP],[]))) ::
          map (fn (n,T) => (project_injectL,
                    ((n,false),(Expression.Positional
                         [SOME INTERP,
                          SOME (Free (n, entryT (T_of_fic T))),
                          SOME T]
                    ,[])))) all_comps;
    val locs' = (Binding.name typeN, SOME (Term.itselfT repT), NoSyn) ::
               (Binding.name INTERPRET_N, SOME INTERP_T, NoSyn) ::
                maps (fn (n,T) => [(Binding.name n, NONE, NoSyn)]) all_comps @
                map (fn (N,Ty) => (Binding.name N, SOME Ty, NoSyn) ) TVARS
    val (locinsts,locs) =
          case target of SOME t =>
              let
                val params = Locale.params_of thy (the target)
              in
                ((t,(("",false),(Expression.Positional (map (SOME o Free o fst) params),[])))::locinsts',
                  locs' @
                  map_filter (fn ((N,T),M) => if exists (fn (N',_,_) => N = Binding.name_of N') locs'
                                              then NONE
                                              else SOME (Binding.name N, SOME T, M)) params)
              end
            | NONE => (locinsts',locs')
    val name_insts = map (fn (n,T) =>
          (n, Const (\<^const_name>\<open>Entry.name\<close>, entryT (T_of_fic T) --> nameT)
                $ Free (n, entryT (T_of_fic T)))) all_comps

    fun interprete_parent_valuetypes (prefix, (Ts, pname, comps)) thyx =
      let
        val {components,...} =
             the (Symtab.lookup (FIS_Data.get (Context.Theory thyx)) pname);
        val components' = map (uncurry the_default) (map fst components ~~ comps)
        val pars = components';

        val expr = ([(suffix fields_locale_N pname,
                     (prefix, (Expression.Positional (map SOME (typeN::INTERPRET_N::pars)),[])))],[]);
(*        val (_, SOME intro) = Locale.intros_of thy (suffix fields_locale_N pname) |> @{print}
        val ax = Locale.axioms_of thy (suffix fields_locale_N full_name) |> @{print} *)
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

    fun declare_declinfo updates lthy phi ctxt =
      let
        fun upd_prf ctxt =
          let
            fun upd (n,(v:term * string)) =
              let
                val nT = Proof_Context.infer_type (Local_Theory.target_of lthy) (n, dummyT)
              in Context.proof_map
                  (update_declinfo (Morphism.term phi (Free (n,nT)),v))
              end;
            val ctxt' = ctxt |> fold upd updates 
          in ctxt' end;

      in Context.mapping I upd_prf ctxt end;

  in thy
     |> namespace_definition
           (Binding.suffix_name namesN name_b) nameT (parents_expr,[])
           (map fst parent_comps) (map fst components)
     |> Context.theory_map
          (add_FIS full_name rep_sort args (map snd parents) all_comps)
     |> add_locale (Binding.suffix_name fields_locale_N name_b) (locinsts,locs) []
     |> Proof_Context.theory_of
     |> fold interprete_parent_valuetypes parents
     |> add_locale name_b
            (  [(suffix namesN full_name,
                  (("",false),
                   (Expression.Named ((typeN, TYPE_TY)::name_insts)
                   ,[]))),
                (suffix fields_locale_N full_name,
                  (("",false),(Expression.Named [(typeN, VALUE_TY)], []))
                )],
               [(Binding.name nameTN,  SOME nameTT,  NoSyn),
                (Binding.name repTN, SOME repTT, NoSyn)])
            []
     |> Proof_Context.theory_of
     |> fold interprete_parent parents
     |> add_declaration full_name (declare_declinfo components')
  end;

(** preparation & wrapper for FIS **)

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

fun read_term ctxt ty raw_T env =
  let
    val ctxt' = fold (Variable.declare_typ o TFree) env ctxt;
    val T = Syntax.parse_term ctxt' raw_T
              |> Type.constraint ty
              |> Syntax.check_term ctxt'
    val env' = Term.add_tfrees T env;
  in (T, env') end;

fun cert_term ctxt ty raw_T env =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (Tm,Ty,_) = Sign.certify_term thy (Type.constraint ty raw_T)
    val _ = Type.no_tvars Ty
      handle TYPE (msg, _, _) => error msg;
    val Tm = Sign.no_vars ctxt Tm
    val env' = Term.add_tfrees Tm env;
  in (Tm, env') end;

fun gen_define_FIS prep_typ prep_term (sort,project_injectL)
                   target args name_b resT parents comps thy =
  let (* - args distinct
         - only args may occur in comps and parent-instantiations
         - number of insts must match parent args
         - no duplicate renamings
         - renaming should occur in entry
         -
         - self_sort: sort of the value type
      *)
    val _ = writeln ("Defining FIS " ^ Binding.print name_b ^ " ...");

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
              (case get_FIS (Context.Theory thy) full_pname of
                SOME r => r
               | NONE => error ("Undefined FIS " ^ quote pname));


        val (Ts',env') = fold_map (prep_typ ctxt) Ts env
            handle ERROR msg => cat_error msg
                    ("The error(s) above occurred in parent FIS specification "
                    ^ quote pname);
        val err_insts = if length args <> length Ts' then
            ["number of type instantiation(s) does not match arguments of parent FIS "
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
        else error (cat_lines (errs @ ["in parent FIS " ^ quote pname]))
      end;

    val args' = map (apsnd (Option.map (Syntax.read_sort ctxt) #> the_default (Sign.defaultS thy))) args
    val (resT',env) = prep_typ ctxt resT args'
    val (parents',env) = fold_map add_parent parents env;
    
    fun prep_sort S' S = if S = "" then S' else Syntax.read_sort ctxt S
    val sort' = fold (parent_sort thy o #2 o #2) parents'
                    (prep_sort \<^sort>\<open>{comm_monoid_mult,no_inverse}\<close> sort)
    val env = (repN, sort')::env
    
    val fictionT = Type(\<^type_name>\<open>fiction\<close>, [dummyT, resT'])


    val err_dup_args =
         (case duplicates (op =) (map fst args) of
            [] => []
          | dups => ["Duplicate type argument(s) " ^ commas dups]);


    val err_dup_components =
         (case duplicates (op =) (map fst comps) of
           [] => []
          | dups => ["Duplicate state-space components " ^ commas dups]);

    fun prep_comp (n,T) env =
      let val (T', env') = prep_term ctxt fictionT T env handle ERROR msg =>
       cat_error msg ("The error(s) above occurred in component " ^ quote n)
      in ((n,T'), env') end;

    val (comps',env') = fold_map prep_comp comps env;

    val err_value_keyword =
          if member (op =) (map fst args) repN
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
     then thy |> FIS_definition sort' project_injectL
                                target' args' name_b resT' parents' parent_comps comps'
     else error (cat_lines errs)
  end
  handle ERROR msg => cat_error msg ("Failed to define fiction space " ^ Binding.print name_b);

val define_FIS = gen_define_FIS read_typ read_term;
val define_FIS_i = gen_define_FIS cert_typ cert_term;


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

fun FIS_decl' (default_sort, default_locale) =
  Parse.opt_target -- (Parse.type_args_constrained -- Parse.binding) --|
  \<^keyword>\<open>::\<close> -- (
    Parse.typ --
    Scan.optional (Parse.sort --| \<^keyword>\<open>,\<close> -- Parse.name_position)
      (default_sort, (default_locale, Position.none))
  ) --
  (\<^keyword>\<open>=\<close> |--
    ((Scan.repeat1 comp >> pair []) ||
      (plus1_unless comp parent --
        Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! (Scan.repeat1 comp)) [])));


fun define_FIS_command kwd comment defaults_setting =
  Outer_Syntax.command kwd comment
    (FIS_decl' defaults_setting >> (fn (((target, (args, name)), (resT, sort_locale)), (parents, comps)) =>
      Toplevel.theory (define_FIS sort_locale target args name resT parents comps)));

val FIS_decl = FIS_decl' ("",project_injectL_default)
val _ = define_FIS_command
   \<^command_keyword>\<open>fiction_space\<close> "define fiction space by locale" ("",project_injectL_default)


end;

end
