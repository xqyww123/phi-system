(*  Title:      HOL/Statespace/state_space.ML
    
    
    Modified by Qiyuan Xu, 2022, to allow arbitray locale substituting for
    @{locale project_inject}. Resource State in Noe needs this feature to
    constrain the valuetype to be a resource algebra.
*)

signature STATE_SPACE =
sig
  val distinct_compsN : string
  val getN : string
  val putN : string
  val injectN : string
  val namespaceN : string
  val projectN : string
  val valuetypesN : string

  val define_statespace_command :
        Outer_Syntax.command_keyword ->
        string -> string * string -> unit
  val namespace_definition :
     binding ->
     typ ->
     (xstring, string) Expression.expr * (binding * string option * mixfix) list ->
     string list -> string list -> theory -> theory

  type gen_valuespace = (string -> typ -> typ -> (bstring * typ) list -> Expression.expression_i * Element.context_i list)
  type cap_hook = (string -> typ -> typ -> (bstring * typ) list ->
         Expression.expression_i * Element.context_i list -> Expression.expression_i * Element.context_i list)

  val define_statespace :
     string * string ->
     string list ->
     binding ->
     ((string * bool) * (string list * (bstring * Position.T) * (string * string) list)) list ->
     (string * string) list -> theory -> theory
  val define_statespace_ex :
     gen_valuespace ->
     cap_hook ->
     string * string ->
     string list ->
     binding ->
     ((string * bool) * (string list * (bstring * Position.T) * (string * string) list)) list ->
     (string * string) list -> theory -> theory
  val define_statespace_i : (*DEPRECIATED!*)
     string ->
     string * string ->
     string list ->
     binding ->
     ((string * bool) * (typ list * (bstring * Position.T) * (string * string) list)) list ->
     (string * typ) list -> theory -> theory

  val statespace_decl :
     (((string list * binding) * (string * string)) *
         (((string * bool) * (string list * (string * Position.T) * (string * string) list)) list *
          (string * string) list)) parser
  val statespace_decl' :
     (string * string) ->
     (((string list * binding) * (string * string)) *
         (((string * bool) * (string list * (string * Position.T) * (string * string) list)) list *
          (string * string) list)) parser


  val neq_x_y : Proof.context -> term -> term -> thm option
  val distinctNameSolver : Simplifier.solver
  val distinctTree_tac : Proof.context -> int -> tactic
  val distinct_simproc : Simplifier.simproc


  val is_statespace : Context.generic -> xstring -> bool

  val get_comp' : Context.generic -> string -> (typ * string * string list) option
  val get_comp : Context.generic -> string -> (typ * string * string) option (* legacy wrapper, eventually replace by primed version *)
  val get_comps : Context.generic -> (typ * string * string list) Termtab.table

  val get_silent : Context.generic -> bool
  val set_silent : bool -> Context.generic -> Context.generic


  val gen_lookup_tr : Proof.context -> term -> string -> term
  val lookup_swap_tr : Proof.context -> term list -> term
  val lookup_tr : Proof.context -> term list -> term
  val lookup_tr' : Proof.context -> term list -> term

  val gen'_update_tr :
     bool -> bool -> Proof.context -> string -> term -> term -> term
  val gen_update_tr : (* legacy wrapper, eventually replace by primed version *)
     bool ->  Proof.context -> string -> term -> term -> term

  val update_tr : Proof.context -> term list -> term
  val update_tr' : Proof.context -> term list -> term

  val trace_name_space_data: Context.generic -> unit
  val trace_state_space_data: Context.generic -> unit
end;

structure StateSpace : STATE_SPACE =
struct

type kind = string

type gen_valuespace = (string -> typ -> typ -> (bstring * typ) list -> Expression.expression_i * Element.context_i list)
type cap_hook = (string -> typ -> typ -> (bstring * typ) list ->
       Expression.expression_i * Element.context_i list -> Expression.expression_i * Element.context_i list)


(* Names *)

val distinct_compsN = "distinct_names"
val namespaceN = "_namespace"
val valuetypesN = "_valuetypes"
val projectN = "project"
val injectN = "inject"
val getN = "get"
val putN = "put"
val project_injectL_default = "StateSpaceLocale.project_inject"
val valueN = "'self"
val typeN = "THE_TYPE"
val valueTN = "VALUE_TYPE"
val nameTN = "NAME_TYPE"


(* Library *)

fun valueT S = TFree (valueN, S)
fun ap3_3 f (a,b,c) = (a,b,f c)

fun fold1 f xs = fold f (tl xs) (hd xs)
fun fold1' f [] x = x
  | fold1' f xs _ = fold1 f xs

fun sorted_subset eq [] ys = true
  | sorted_subset eq (x::xs) [] = false
  | sorted_subset eq (x::xs) (y::ys) = if eq (x,y) then sorted_subset eq xs ys
                                       else sorted_subset eq (x::xs) ys;

fun comps_of_distinct_thm thm = Thm.prop_of thm
  |> (fn (_$(_$t)) => DistinctTreeProver.dest_tree t) |> map (fst o dest_Free) |> sort_strings;

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


fun join_declinfo_entry name (T1:typ, K1:kind, names1:string list) (T2, K2, names2) =
  let
    fun typ_info T names = @{make_string} T ^ " "  ^ Pretty.string_of (Pretty.str_list "(" ")" names);
  in
    if T1 = T2 andalso K1 = K2 then (T1, K1, distinct (op =) (names1 @ names2))
    else if K1 <> K2 then
          error ("statespace component '" ^ name ^ "' disagrees on statespace-kind:\n " ^
        K1 ^ " vs. "  ^ K2)
    else  error ("statespace component '" ^ name ^ "' disagrees on type:\n " ^
        typ_info T1 names1 ^ " vs. "  ^ typ_info T2 names2)
  end
fun guess_name (Free (x,_)) = x
  | guess_name _ = "unknown"

val join_declinfo = Termtab.join (fn trm => uncurry (join_declinfo_entry (guess_name trm)))


(*
  A component might appear in *different* statespaces within the same context. However, it must
  be mapped to the same type. Note that this information is currently only properly maintained
  within contexts where all components are actually "fixes" and not arbitrary terms. Moreover, on
  the theory level the info stays empty.

  This means that on the theory level we do not make use of the syntax and the tree-based distinct simprocs.
  N.B: It might still make sense (from a performance perspective) to overcome this limitation
  and even use the simprocs when a statespace is interpreted for concrete names like HOL-strings.
  Once the distinct-theorem is proven by the interpretation the simproc can use the positions in
  the tree to derive distinctness of two strings vs. HOL-string comparison.
 *)
type namespace_info =
 {declinfo: (typ * kind * string list) Termtab.table, (* type, names of statespaces of component  *)
  distinctthm: thm list Symtab.table, (* minimal list of maximal distinctness-assumptions for a component name *)
  silent: bool
 };

structure NameSpaceData = Generic_Data
(
  type T = namespace_info;
  val empty = {declinfo = Termtab.empty, distinctthm = Symtab.empty, silent = false};
  fun merge
    ({declinfo=declinfo1, distinctthm=distinctthm1, silent=silent1},
      {declinfo=declinfo2, distinctthm=distinctthm2, silent=silent2}) : T =
    {declinfo = join_declinfo (declinfo1, declinfo2),
     distinctthm = join_distinctthm_tab (distinctthm1, distinctthm2),
     silent = silent1 andalso silent2 (* FIXME odd merge *)}
);

fun trace_name_space_data context =
  tracing ("NameSpaceData: " ^ @{make_string} (NameSpaceData.get context))

fun make_namespace_data declinfo distinctthm silent =
     {declinfo=declinfo,distinctthm=distinctthm,silent=silent};


fun update_declinfo (n,v) ctxt =
  let
    val {declinfo,distinctthm,silent} = NameSpaceData.get ctxt;
    val v = ap3_3 single v
  in NameSpaceData.put (make_namespace_data
        (Termtab.map_default (n,v) (join_declinfo_entry (guess_name n) v) declinfo)
        distinctthm silent) ctxt
  end;

fun set_silent silent ctxt =
  let val {declinfo,distinctthm,...} = NameSpaceData.get ctxt;
  in NameSpaceData.put
      (make_namespace_data declinfo distinctthm silent) ctxt
  end;

val get_silent = #silent o NameSpaceData.get;

fun expression_no_pos (expr, fixes) : Expression.expression =
  (map (fn (name, inst) => ((name, Position.none), inst)) expr, fixes);

fun prove_interpretation_in ctxt_tac (name, expr) thy =
   thy
   |> Interpretation.global_sublocale_cmd (name, Position.none) (expression_no_pos expr) []
   |> Proof.global_terminal_proof
         ((Method.Basic (fn ctxt => SIMPLE_METHOD (ctxt_tac ctxt)), Position.no_range), NONE)
   |> Proof_Context.theory_of

fun add_locale name (expr,elems) thy =
  thy
  |> Expression.add_locale name name [] expr elems
  |> snd
  |> Local_Theory.exit;

fun add_locale_cmd name (expr,elems) thy =
  thy
  |> Expression.add_locale_cmd name Binding.empty [] (expression_no_pos expr) elems
  |> snd
  |> Local_Theory.exit;

type statespace_info =
 {kind: string, (* a prefix for every projector and injector, so that statespaces
          of different kinds will not interfere with other kinds and can be imported together*)
  value_sort: sort, (* sort of value type *)
  args: (string * sort) list, (* type arguments *)
  parents: (typ list * string * string option list) list,
            (* type instantiation, state-space name, component renamings *)
  components: (string * typ) list,
  types: typ list (* range types of state space *)
 };

structure StateSpaceData = Generic_Data
(
  type T = statespace_info Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

fun is_statespace context name =
  Symtab.defined (StateSpaceData.get context) (Locale.intern (Context.theory_of context) name)

fun trace_state_space_data context =
  tracing ("StateSpaceData: " ^ @{make_string} (StateSpaceData.get context))

fun add_statespace name kind Sv args parents components types ctxt =
     StateSpaceData.put
      (Symtab.update_new (name, {kind=kind,value_sort=Sv,args=args,parents=parents,
                                components=components,types=types}) (StateSpaceData.get ctxt))
      ctxt;

fun get_statespace ctxt name =
      Symtab.lookup (StateSpaceData.get ctxt) name;


fun mk_free ctxt name =
  if Variable.is_fixed ctxt name orelse Variable.is_declared ctxt name
  then
    let
      val n' = Variable.intern_fixed ctxt name |> perhaps Long_Name.dest_hidden;
      val free = Free (n', Proof_Context.infer_type ctxt (n', dummyT))
    in SOME (free) end
  else (tracing ("variable not fixed or declared: " ^ name); NONE)


fun get_dist_thm ctxt name = Symtab.lookup (#distinctthm (NameSpaceData.get ctxt)) name;

fun get_dist_thm2 ctxt x y =
 (let
    val dist_thms = [x, y] |> map (#1 o dest_Free)
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
         val declinfo = #declinfo (NameSpaceData.get ctxt)
       in
         case Termtab.lookup declinfo t of
           NONE => (* during syntax phase, types of fixes might not yet be constrained completely *)
             AList.lookup (fn (x, Free (n,_)) => n = x | _ => false) (Termtab.dest declinfo) name
         | some => some
       end)

(* legacy wrapper *)
fun get_comp ctxt name =
 get_comp' ctxt name |> Option.map (ap3_3 (fn ns => if null ns then "" else hd ns))

fun get_comps ctxt = #declinfo (NameSpaceData.get ctxt)

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
        (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (x as Free _) $ (y as Free _))) =>
      (case neq_x_y ctxt x y of
        SOME neq => resolve_tac ctxt [neq] i
      | NONE => no_tac)
  | _ => no_tac));

val distinctNameSolver = mk_solver "distinctNameSolver" distinctTree_tac;

val distinct_simproc =
  Simplifier.make_simproc \<^context> "StateSpace.distinct_simproc"
   {lhss = [\<^term>\<open>x = y\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>HOL.eq\<close>,_) $ (x as Free _) $ (y as Free _) =>
          Option.map (fn neq => DistinctTreeProver.neq_to_eq_False OF [neq])
            (neq_x_y ctxt x y)
      | _ => NONE)};

fun interprete_parent_namespace name dist_thm_name parent_expr thy =
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
          val {declinfo,distinctthm=tt,silent} = NameSpaceData.get context;
          val all_names = comps_of_distinct_thm thm;
          fun upd name = Symtab.map_default (name, [thm]) (fn thms => insert_distinct_thm thm thms)

          val tt' = tt |> fold upd all_names;
          val context' =
              Context_Position.set_visible false ctxt
              addsimprocs [distinct_simproc]
              |> Context_Position.restore_visible ctxt
              |> Context.Proof
              |> NameSpaceData.put {declinfo=declinfo,distinctthm=tt',silent=silent};
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
    |> add_locale name (([], vars),[Element.Assumes [assume]])
    |> Proof_Context.theory_of
    |> interprete_parent_namespace (Binding.name_of name) dist_thm_full_name parent_expr
  end;

fun encode_dot x = if x = #"." then #"_" else x;

fun encode_type (TFree (s, _)) = s
  | encode_type (TVar ((s,i),_)) = "?" ^ s ^ string_of_int i
  | encode_type (Type (n,Ts)) =
      let
        val Ts' = fold1' (fn x => fn y => x ^ "_" ^ y) (map encode_type Ts) "";
        val n' = String.map encode_dot n;
      in if Ts'="" then n' else Ts' ^ "_" ^ n' end;

fun project_name k T = k^"_"^projectN ^"_"^encode_type T;
fun inject_name k T = k^"_"^injectN ^"_"^encode_type T;


fun add_declaration name decl thy =
  thy
  |> Named_Target.init [] name
  |> (fn lthy => Local_Theory.declaration {syntax = true, pervasive = false} (decl lthy) lthy)
  |> Local_Theory.exit_global;

fun parent_sort thy pname Sv =
  let
    val ctxt = Context.Theory thy;
    val {value_sort, parents, ...} = the (Symtab.lookup (StateSpaceData.get ctxt) pname);
  in
    fold (parent_sort thy o #2) parents (Sign.inter_sort thy (Sv,value_sort))
  end

fun parent_components thy Sv (Ts, pname, renaming) =
  let
    val ctxt = Context.Theory thy;
    fun rename [] xs = xs
      | rename (NONE::rs)  (x::xs) = x::rename rs xs
      | rename (SOME r::rs) ((x,T)::xs) = (r,T)::rename rs xs;
    val {value_sort, args, parents, components, ...} =
                  the (Symtab.lookup (StateSpaceData.get ctxt) pname);
    val inst = (valueN, valueT Sv) :: (map fst args ~~ Ts);
    val subst = Term.map_type_tfree (the o AList.lookup (op =) inst o fst);
    val parent_comps =
      maps (fn (Ts',n,rs) => parent_components thy Sv (map subst Ts', n, rs)) parents;
    val all_comps = rename renaming (parent_comps @ map (apsnd subst) components);
  in all_comps end;

fun distinct_types Ts =
      let val tab = fold (fn T => fn tab => Typtab.update (T,()) tab) Ts Typtab.empty;
      in map fst (Typtab.dest tab) end;

fun standard_valuespace Kd valueT nameT all_comps =
  let
    val Ts = distinct_types (map snd all_comps)
    fun projectT T = valueT --> T;
    fun injectT T = T --> valueT;
    val locinsts = map (fn T => (project_injectL_default,
          ((encode_type T,false),(Expression.Positional
              [SOME (Free (project_name Kd T,projectT T)),
               SOME (Free ((inject_name Kd T,injectT T)))],[])))) Ts
    val locs = (Binding.name typeN, SOME (Term.itselfT valueT), NoSyn)
                :: maps (fn T => [(Binding.name (project_name Kd T),NONE,NoSyn),
                                  (Binding.name (inject_name Kd T),NONE,NoSyn)]) Ts;
  in ((locinsts,locs),[])
  end

fun no_caphook Kd valueT nameT all_comps = I
fun fixstate_hook state_type Kd valueT nameT all_comps (expr,elms) =
  let
    fun projectT T = valueT --> T;
    fun injectT T = T --> valueT;
    val stateT = nameT --> valueT;
    val Ts = distinct_types (map snd all_comps)
    val constrains = maps (fn T =>
          [(project_name Kd T, projectT T),(inject_name Kd T,injectT T)]) Ts;
    val fx = Element.Fixes [(Binding.name state_type, SOME stateT, NoSyn)];
    val cs = Element.Constrains
              (map (fn (n,T) =>  (n, T))
                ((map (fn (n,_) => (n,nameT)) all_comps) @
                  constrains))
  in (expr, [fx,cs] @ elms)
  end

fun statespace_definition gen_valuespace hook_capL value_sort Kd
                          args name_b parents parent_comps components thy =
  let
    val name = Binding.name_of name_b
    val pos = Binding.pos_of name_b
    val full_name = Sign.full_bname thy name;
    val all_comps = parent_comps @ components;

    val components' = map (fn (n,T) => (n,(T,Kd,full_name))) components;

    val Ts = distinct_types (map snd all_comps);
    val arg_names = map fst args;
    (* 'self now is treated as a keyword so it doesn't need variant.*)
    (* val valueN = singleton (Name.variant_list (valueN :: arg_names)) "'self"; *)
    val nameN = singleton (Name.variant_list (valueN :: arg_names)) "'name";
    val valueT = valueT value_sort;
    val nameT = TFree (nameN, Sign.defaultS thy);
    val nameTT  = Term.itselfT nameT
    val valueTT = Term.itselfT (TFree("'value", value_sort))

    fun parent_expr (prefix, (_, n, rs)) =
      (suffix namespaceN n,
        (prefix,(Expression.Positional (SOME typeN :: rs),[])));
    val parents_expr = map parent_expr parents;

    val locV = gen_valuespace Kd valueT nameT all_comps;

    fun interprete_parent_valuetypes (prefix, (Ts, pname, _)) thy =
      let
        val {args,types,...} =
             the (Symtab.lookup (StateSpaceData.get (Context.Theory thy)) pname);
        val inst = map fst args ~~ Ts;
        val subst = Term.map_type_tfree (the o AList.lookup (op =) inst o fst);
        val pars = maps ((fn T => [project_name Kd T,inject_name Kd T]) o subst) types;

        val expr = ([(suffix valuetypesN name,
                     (prefix, (Expression.Positional (map SOME (typeN::pars)),[])))],[]);
      in
        prove_interpretation_in (fn ctxt => ALLGOALS (solve_tac ctxt (Assumption.all_prems_of ctxt)))
          (suffix valuetypesN name, expr) thy
      end;

    fun interprete_parent (prefix, (_, pname, rs)) =
      let
        val expr = ([(pname, (prefix, (Expression.Positional rs,[])))],[])
      in prove_interpretation_in
           (fn ctxt => Locale.intro_locales_tac {strict = true, eager = false} ctxt [])
           (full_name, expr) end;

    fun declare_declinfo updates lthy phi ctxt =
      let
        fun upd_prf ctxt =
          let
            fun upd (n,v) =
              let
                val nT = Proof_Context.infer_type (Local_Theory.target_of lthy) (n, dummyT)
              in Context.proof_map
                  (update_declinfo (Morphism.term phi (Free (n,nT)),v))
              end;
            val ctxt' = ctxt |> fold upd updates
          in ctxt' end;

      in Context.mapping I upd_prf ctxt end;

   (*fun string_of_typ T =
      Print_Mode.setmp []
        (Syntax.string_of_typ (Config.put show_sorts true (Syntax.init_pretty_global thy))) T;*)

  in thy
     |> namespace_definition
           (Binding.suffix_name namespaceN name_b) nameT (parents_expr,[])
           (map fst parent_comps) (map fst components)
     |> Context.theory_map
          (add_statespace full_name Kd value_sort args (map snd parents) components [])
     |> add_locale (Binding.suffix_name valuetypesN name_b) locV
     |> Proof_Context.theory_of
     |> fold interprete_parent_valuetypes parents
     |> add_locale name_b
          (hook_capL Kd valueT nameT all_comps
            (( [(suffix namespaceN full_name,
                  (("",false),(Expression.Named [(typeN, Free(nameTN, nameTT))],[]))),
                (suffix valuetypesN full_name,
                  (("",false),(Expression.Named [(typeN, Free(valueTN, valueTT))],[])))],
               [(Binding.name nameTN,  SOME nameTT,  NoSyn),
                (Binding.name valueTN, SOME valueTT, NoSyn)])
            ,[]))
     |> Proof_Context.theory_of
     |> fold interprete_parent parents
     |> add_declaration full_name (declare_declinfo components')
  end;


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

fun gen_define_statespace prep_typ (gen_valuespace:gen_valuespace) (hook_capL:cap_hook)
      (value_sort,Kd) args name_b parents comps thy =
  let (* - args distinct
         - only args may occur in comps and parent-instantiations
         - number of insts must match parent args
         - no duplicate renamings
         - renaming should occur in namespace
         -
         - self_sort: sort of the value type
      *)
    val _ = writeln ("Defining statespace " ^ Binding.print name_b ^ " ...");

    val ctxt = Proof_Context.init_global thy;

    fun add_parent (prefix, (Ts, pname, rs)) env =
      let
        val prefix' =
          (case prefix of
            ("", mandatory) => (fst pname, mandatory)
          | _ => prefix);

        val full_pname = Locale.check thy pname;
        val quote = quote o fst
        val {args,components,kind,...} =
              (case get_statespace (Context.Theory thy) full_pname of
                SOME r => r
               | NONE => error ("Undefined statespace " ^ quote pname));

        val _ = if kind = Kd then ()
                else error ("Kinds must be identical: "^Binding.print name_b^" is "^Kd
                            ^" but its parent "^fst prefix'^" is "^kind)

        val (Ts',env') = fold_map (prep_typ ctxt) Ts env
            handle ERROR msg => cat_error msg
                    ("The error(s) above occurred in parent statespace specification "
                    ^ quote pname);
        val err_insts = if length args <> length Ts' then
            ["number of type instantiation(s) does not match arguments of parent statespace "
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
        else error (cat_lines (errs @ ["in parent statespace " ^ quote pname]))
      end;

    val (parents',env) = fold_map add_parent parents [];
    val value_sort' = fold (parent_sort thy o #2 o #2) parents'
              (if value_sort = "" then Sign.defaultS thy else Syntax.read_sort ctxt value_sort)
    val env = (valueN, value_sort')::env

    val err_dup_args =
         (case duplicates (op =) args of
            [] => []
          | dups => ["Duplicate type argument(s) " ^ commas dups]);


    val err_dup_components =
         (case duplicates (op =) (map fst comps) of
           [] => []
          | dups => ["Duplicate state-space components " ^ commas dups]);

    fun prep_comp (n,T) env =
      let val (T', env') = prep_typ ctxt T env handle ERROR msg =>
       cat_error msg ("The error(s) above occurred in component " ^ quote n)
      in ((n,T'), env') end;

    val (comps',env') = fold_map prep_comp comps env;

    val err_value_keyword =
          if member (op =) args valueN
          then ["'self is a reserved keyword and cannot be a type parameter"]
          else []


    (*TODO!!!*)
    val err_extra_frees = []

    val args' = map (fn x => (x, AList.lookup (op =) env x |> the_default value_sort')) args;


    fun fst_eq ((x:string,_),(y,_)) = x = y;
    fun snd_eq ((_,t:typ),(_,u)) = t = u;

    val raw_parent_comps = maps (parent_components thy value_sort' o snd) parents';
    fun check_type (n,T) =
          (case distinct (snd_eq) (filter (curry fst_eq (n,T)) raw_parent_comps) of
             []  => []
           | [_] => []
           | rs  => ["Different types for component " ^ quote n ^ ": " ^
                commas (map (Syntax.string_of_typ ctxt o snd) rs)])

    val err_dup_types = maps check_type (duplicates fst_eq raw_parent_comps)

    val parent_comps = distinct (fst_eq) raw_parent_comps;
    val all_comps = parent_comps @ comps';
    val err_comp_in_parent = (case duplicates (op =) (map fst all_comps) of
               [] => []
             | xs => ["Components already defined in parents: " ^ commas_quote xs]);
    val errs = err_dup_args @ err_dup_components @ err_extra_frees @
               err_dup_types @ err_comp_in_parent @ err_value_keyword;
  in if null errs
     then thy |> statespace_definition gen_valuespace hook_capL
                                       value_sort' Kd
                                       args' name_b parents' parent_comps comps'
     else error (cat_lines errs)
  end
  handle ERROR msg => cat_error msg ("Failed to define statespace " ^ Binding.print name_b);

val define_statespace = gen_define_statespace read_typ standard_valuespace no_caphook;
val define_statespace_ex = gen_define_statespace read_typ;
val define_statespace_i = gen_define_statespace cert_typ standard_valuespace o fixstate_hook;



(*** parse/print - translations ***)


fun gen_lookup_tr ctxt s n =
  (case get_comp' (Context.Proof ctxt) n of
    SOME (T, Kd, _) =>
      Syntax.const \<^const_name>\<open>StateFun.lookup\<close> $
        Syntax.free (project_name Kd T) $ Syntax.free n $ s
  | NONE =>
      if get_silent (Context.Proof ctxt)
      then Syntax.const \<^const_name>\<open>StateFun.lookup\<close> $
        Syntax.const \<^const_syntax>\<open>undefined\<close> $ Syntax.free n $ s
      else raise TERM ("StateSpace.gen_lookup_tr: component " ^ quote n ^ " not defined", []));

fun lookup_tr ctxt [s, x] =
  (case Term_Position.strip_positions x of
    Free (n,_) => gen_lookup_tr ctxt s n
  | _ => raise Match);

fun lookup_swap_tr ctxt [Free (n,_),s] = gen_lookup_tr ctxt s n;

fun lookup_tr' ctxt [_ $ Free (prj, _), n as (_ $ Free (name, _)), s] =
      (case get_comp' (Context.Proof ctxt) name of
        SOME (T, Kd, _) =>
          if prj = project_name Kd T
          then Syntax.const "_statespace_lookup" $ s $ n
          else raise Match
      | NONE => raise Match)
  | lookup_tr' _ _ = raise Match;

fun gen'_update_tr const_val id ctxt n v s =
  let
    fun pname Kd T = if id then \<^const_name>\<open>Fun.id\<close> else project_name Kd T;
    fun iname Kd T = if id then \<^const_name>\<open>Fun.id\<close> else inject_name Kd T;
    val v = if const_val then (Syntax.const \<^const_name>\<open>K_statefun\<close> $ v) else v
  in
    (case get_comp' (Context.Proof ctxt) n of
      SOME (T, Kd, _) =>
        Syntax.const \<^const_name>\<open>StateFun.update\<close> $
          Syntax.free (pname Kd T) $ Syntax.free (iname Kd T) $
          Syntax.free n $ v $ s
    | NONE =>
        if get_silent (Context.Proof ctxt) then
          Syntax.const \<^const_name>\<open>StateFun.update\<close> $
            Syntax.const \<^const_syntax>\<open>undefined\<close> $ Syntax.const \<^const_syntax>\<open>undefined\<close> $
            Syntax.free n $ v $ s
       else raise TERM ("StateSpace.gen_update_tr: component " ^ n ^ " not defined", []))
   end;

val gen_update_tr = gen'_update_tr true

fun update_tr ctxt [s, x, v] =
  (case Term_Position.strip_positions x of
    Free (n, _) => gen'_update_tr true false ctxt n v s
  | _ => raise Match);

fun update_tr' ctxt
        [_ $ Free (prj, _), _ $ Free (inj, _), n as (_ $ Free (name, _)), (Const (k, _) $ v), s] =
      if Long_Name.base_name k = Long_Name.base_name \<^const_name>\<open>K_statefun\<close> then
        (case get_comp' (Context.Proof ctxt) name of
          SOME (T, Kd, _) =>
            if inj = inject_name Kd T andalso prj = project_name Kd T then
              Syntax.const "_statespace_update" $ s $ n $ v
            else raise Match
        | NONE => raise Match)
     else raise Match
  | update_tr' _ _ = raise Match;




(*** outer syntax *)

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

fun statespace_decl' (default_value_sort, default_kind) =
  Parse.type_args -- Parse.binding --
    Scan.optional (\<^keyword>\<open>::\<close> |-- (
         Parse.sort >> rpair default_kind
      || \<^keyword>\<open>(\<close> |-- Parse.sort --| \<^keyword>\<open>,\<close> -- Parse.string --| \<^keyword>\<open>)\<close>
    )) (default_value_sort, default_kind) --
  (\<^keyword>\<open>=\<close> |--
    ((Scan.repeat1 comp >> pair []) ||
      (plus1_unless comp parent --
        Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! (Scan.repeat1 comp)) [])));

fun define_statespace_command kwd comment defaults_setting =
  Outer_Syntax.command kwd comment
    (statespace_decl' defaults_setting >> (fn (((args, name), sort_locale), (parents, comps)) =>
      Toplevel.theory (define_statespace sort_locale args name parents comps)));

val statespace_decl = statespace_decl' ("","S")
val _ = define_statespace_command
   \<^command_keyword>\<open>statespace\<close> "define state-space as locale context" ("","S")

end;

end;
