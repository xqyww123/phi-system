(* Author: Norbert Schirmer, TU Muenchen, 2007
 * Author: Norbert Schirmer, Apple, 2021
 * Author: Qiyuan Xu, NTU Singapore, 2022
 * Modified from state_space.ML written by Norbert Schirmer. *)

signature VIRTUAL_DATATYPE = sig
  val distinct_compsN : string
  val valueN : string
  val typeN : string
  val valueTN : string
  val nameTN : string
  val CONS_N : string
  val CONS_OF_N : string
  val constructor_locale_N : string
  val fields_locale_N : string


  val define_VDT_command :
        Outer_Syntax.command_keyword ->
        string -> string * string -> unit


  val cons_definition :
     binding ->
     typ ->
     (xstring, string) Expression.expr * (binding * string option * mixfix) list ->
     string list -> string list -> theory -> theory

  val define_VDT :
     (string * (string * Position.T)) ->
     (xstring * Position.T) option ->
     (string * string option) list ->
     binding ->
     ((string * bool) * (string list * (bstring * Position.T) * (string * string) list)) list ->
     (string * string) list -> theory -> theory
  val define_VDT_i :
     (string * (string * Position.T)) ->
     (xstring * Position.T) option ->
     (string * string option) list ->
     binding ->
     ((string * bool) * (typ list * (bstring * Position.T) * (string * string) list)) list ->
     (string * typ) list -> theory -> theory

  val VDT_decl :
     ((((string * Position.T) option * ((string * string option) list * binding)) * (string * (bstring * Position.T))) *
       (((string * bool) * (string list * (bstring * Position.T) * (bstring * bstring) list)) list *
        (bstring * string) list)) parser
  val VDT_decl' :
     (string * string) ->
     ((((xstring * Position.T) option * ((string * string option) list * binding)) * (string * (bstring * Position.T))) *
       (((string * bool) * (string list * (bstring * Position.T) * (bstring * bstring) list)) list *
        (bstring * string) list)) parser


  val neq_x_y : Proof.context -> term -> term -> thm option
  val distinctNameSolver : Simplifier.solver
  val distinctTree_tac : Proof.context -> int -> tactic
  val distinct_simproc : Simplifier.simproc


  val is_VDT : Context.generic -> xstring -> bool

  val get_comp' : Context.generic -> string -> (typ * string list) option
  val get_comp : Context.generic -> string -> (typ * string) option (* legacy wrapper, eventually replace by primed version *)
  val get_comps : Context.generic -> (typ * string list) Termtab.table

  val get_silent : Context.generic -> bool
  val set_silent : bool -> Context.generic -> Context.generic

  val trace_constructor_data: Context.generic -> unit
  val trace_VDT_data: Context.generic -> unit

end

structure Virtual_DataType : VIRTUAL_DATATYPE = struct

(* Names *)

val distinct_compsN = "distinct_names"
val selfN = "'self"
val valueN = "'rep"
val typeN = "THE_TYPE"
val valueTN = "TYPE'REP"
val nameTN = "TYPE'NAME"
val CONS_N = "'CONS_NAME"
val CONS_OF_N = "CONS_OF"
val constructor_locale_N = "_names"
val fields_locale_N = "_prjs"
val TVAR_N = "TYPE"
val fieldN = "\<f>\<i>\<e>\<l>\<d>_"

val project_injectL_default = \<^locale>\<open>field_entry\<close>



(*** Library ***)

(* Misc *)

fun valueT S = TFree (valueN, S)
fun fieldT consT valueT T = Type(\<^type_name>\<open>Field\<close>, [consT, valueT, T])

fun cons_name_of (Free (s,_)) = s
  | cons_name_of (Const (\<^const_name>\<open>Field.name\<close>, _) $ x) = Term.term_name x
  | cons_name_of t = raise TERM ("const_name_of", [t])

val translate_self_to_rep = map_atyps (
      fn (ty as TFree (n,S)) => if n = selfN then TFree (valueN,S) else ty
       | ty => ty
)

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

(** constructor_info **)

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

fun join_declinfo_entry name (T1:typ, names1:string list) (T2, names2) =
  let
    fun typ_info T names = @{make_string} T ^ " "  ^ Pretty.string_of (Pretty.str_list "(" ")" names);
  in
    if T1 = T2 then (T1, distinct (op =) (names1 @ names2))
    else error ("constructor '" ^ name ^ "' disagrees on type:\n " ^ 
        typ_info T1 names1 ^ " vs. "  ^ typ_info T2 names2) 
  end
fun guess_name (Free (x,_)) = x
  | guess_name _ = "unknown"

val join_declinfo = Termtab.join (fn trm => uncurry (join_declinfo_entry (guess_name trm))) 

(* ConstructorData *)

type constructor_info =
 {declinfo: (typ * string list) Termtab.table, (* type, names of constructors of component  *)
  distinctthm: thm list Symtab.table, (* minimal list of maximal distinctness-assumptions for a component name *)
  silent: bool
 };


structure ConstructorData = Generic_Data
(
  type T = constructor_info;
  val empty = {declinfo = Termtab.empty, distinctthm = Symtab.empty, silent = false};
  fun merge
    ({declinfo=declinfo1, distinctthm=distinctthm1, silent=silent1},
      {declinfo=declinfo2, distinctthm=distinctthm2, silent=silent2}) : T =
    {declinfo = join_declinfo (declinfo1, declinfo2),
     distinctthm = join_distinctthm_tab (distinctthm1, distinctthm2),
     silent = silent1 andalso silent2 (* FIXME odd merge *)}
);

fun trace_constructor_data context =  
  tracing ("ConstructorData: " ^ @{make_string} (ConstructorData.get context))

fun make_constructor_data declinfo distinctthm silent =
     {declinfo=declinfo,distinctthm=distinctthm,silent=silent};


fun update_declinfo (n,v) ctxt =
  let       
    val {declinfo,distinctthm,silent} = ConstructorData.get ctxt;
    val v = apsnd single v
  in ConstructorData.put (make_constructor_data
        (Termtab.map_default (n,v) (join_declinfo_entry (guess_name n) v) declinfo)
        distinctthm silent) ctxt
  end;

fun set_silent silent ctxt =
  let val {declinfo,distinctthm,...} = ConstructorData.get ctxt;
  in ConstructorData.put
      (make_constructor_data declinfo distinctthm silent) ctxt
  end;

val get_silent = #silent o ConstructorData.get;


(** VDT **)

type VDT_info =
 {value_sort: sort, (* sort of value type *)
  args: (string * sort) list, (* type arguments *)
  parents: (typ list * string * string option list) list,
            (* type instantiation, VDT name, component renamings *)
  components: (string * typ) list
 };

structure VDT_Data = Generic_Data
(
  type T = VDT_info Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T = Symtab.merge (K true) data;
);

fun is_VDT context name =
  Symtab.defined (VDT_Data.get context) (Locale.intern (Context.theory_of context) name)

fun trace_VDT_data context =  
  tracing ("StateSpaceData: " ^ @{make_string} (VDT_Data.get context))

fun add_VDT name Sv args parents components ctxt =
      VDT_Data.put
        (Symtab.update_new (name, {value_sort=Sv,args=args,parents=parents,
                                   components=components})
                           (VDT_Data.get ctxt))
        ctxt;

fun get_VDT ctxt name =
      Symtab.lookup (VDT_Data.get ctxt) name;



(** Accessors of above two structure **)

fun mk_free ctxt name =
  if Variable.is_fixed ctxt name orelse Variable.is_declared ctxt name
  then
    let 
      val n' = Variable.intern_fixed ctxt name |> perhaps Long_Name.dest_hidden;
      val free = Free (n', Proof_Context.infer_type ctxt (n', dummyT))
    in SOME (free) end
  else (tracing ("variable not fixed or declared: " ^ name); NONE)


fun get_dist_thm ctxt name = Symtab.lookup (#distinctthm (ConstructorData.get ctxt)) name

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
  let val vname = fieldN ^ name in
  mk_free (Context.proof_of ctxt) vname
  |> Option.mapPartial (fn t => 
       let
         val declinfo = #declinfo (ConstructorData.get ctxt)
       in 
         case Termtab.lookup declinfo t of
           NONE => (* during syntax phase, types of fixes might not yet be constrained completely *) 
             AList.lookup (fn (x, Free (n,_)) => n = x | _ => false) (Termtab.dest declinfo) vname
         | some => some
       end)
  end

(* legacy wrapper *)
fun get_comp ctxt name =
 get_comp' ctxt name |> Option.map (apsnd (fn ns => if null ns then "" else hd ns)) 

fun get_comps ctxt = #declinfo (ConstructorData.get ctxt)

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
   {lhss = [\<^term>\<open>Field.name x = Field.name y\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>HOL.eq\<close>,_) $ x $ y =>
          Option.map (fn neq => DistinctTreeProver.neq_to_eq_False OF [neq])
              (neq_x_y ctxt x y)
      | _ => NONE)};

fun interprete_parent_constructor name dist_thm_name parent_expr thy =
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

fun cons_definition name nameT parent_expr parent_comps new_comps thy =
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
          val {declinfo,distinctthm=tt,silent} = ConstructorData.get context;
          val all_names = comps_of_distinct_thm thm;
          fun upd name = Symtab.map_default (name, [thm]) (fn thms => insert_distinct_thm thm thms)

          val tt' = tt |> fold upd all_names;
          val context' =
              Context_Position.set_visible false ctxt
              addsimprocs [distinct_simproc]
              |> Context_Position.restore_visible ctxt
              |> Context.Proof
              |> ConstructorData.put {declinfo=declinfo,distinctthm=tt',silent=silent};
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
    |> interprete_parent_constructor (Binding.name_of name) dist_thm_full_name parent_expr
  end;


(** define VDT **)

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
    val {value_sort, parents, ...} = the (Symtab.lookup (VDT_Data.get ctxt) pname);
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
                  the (Symtab.lookup (VDT_Data.get ctxt) pname);
    val inst = (valueN, valueT Sv) :: (map fst args ~~ Ts);
    val subst = Term.map_type_tfree (the o AList.lookup (op =) inst o fst);
    val parent_comps =
      maps (fn (Ts',n,rs) => parent_components thy Sv (map subst Ts', n, rs)) parents;
    val all_comps = rename renaming (parent_comps @ map (apsnd subst) components);
  in all_comps end;

(* main stuff *)

fun VDT_definition value_sort project_injectL
                   base args name_b parents parent_comps components thy =
  let
    val name = Binding.name_of name_b
    val pos = Binding.pos_of name_b
    val full_name = Sign.full_bname thy name;
    val all_comps = parent_comps @ components;

    val components' = map (fn (n,T) => (n,(T,full_name))) components;

    val arg_names = map fst args;
    (* 'self now is treated as a keyword so it doesn't need variant.*)
    (* val valueN = singleton (Name.variant_list (valueN :: arg_names)) "'self"; *)
    val nameN = singleton (Name.variant_list (valueN :: arg_names)) "'name";
    val valueT = valueT value_sort
    val valueTT = Term.itselfT valueT
    val nameT = TFree (CONS_N, Sign.defaultS thy);
    val nameTT  = Term.itselfT nameT
    val fieldT = fieldT nameT valueT
    val cons_of = Free(CONS_OF_N, valueT --> nameT)
    val TYPE_TY = Free(nameTN, nameTT)
    val VALUE_TY = Free(valueTN, valueTT)
    val TVARS = map (fn (T,S) => (prefix TVAR_N T, Term.itselfT (TFree(T,S)))) args

    fun parent_expr (prefix, (_, n, rs)) =
      (suffix constructor_locale_N n,
        (prefix,(Expression.Positional (SOME typeN :: rs),[])));
    val parents_expr = map parent_expr parents;

    val locinsts =
          (\<^locale>\<open>virtual_datatype\<close>, (("",false),
                (Expression.Positional [SOME cons_of],[]))) ::
          map (fn (n,T) => (project_injectL,
                    ((n,true),(Expression.Positional
                         [SOME cons_of,
                          SOME (Free (n, fieldT T))]
                    ,[])))) all_comps
    val locinsts =
          case base of SOME t => (t,(("",false),(Expression.Positional [],[])))::locinsts
                     | NONE => locinsts
    val locs = (Binding.name nameTN,  SOME (Term.itselfT nameT),  NoSyn) ::
               (Binding.name valueTN, SOME (Term.itselfT valueT), NoSyn) ::
               (Binding.name CONS_OF_N, SOME (valueT --> nameT), NoSyn) ::
               maps (fn (n,T) => [(Binding.name (n), NONE, NoSyn)]) all_comps @
               map (fn (N,Ty) => (Binding.name (N), SOME Ty, NoSyn) ) TVARS
    val name_insts = map (fn (n,T) =>
          (n, Const (\<^const_name>\<open>Field.name\<close>, fieldT T --> nameT)
                $ Free (fieldN^n, fieldT T))) all_comps
    val proj_insts = map (fn (n,T) =>
          (n, Free (fieldN^n, fieldT T))) all_comps
    val vars = (map (fn (n,T) => (Binding.make (fieldN^n,pos), NONE, NoSyn)) all_comps)

    fun interprete_parent_valuetypes (prefix, (Ts, pname, comps)) thy =
      let
        val {components,...} =
             the (Symtab.lookup (VDT_Data.get (Context.Theory thy)) pname);
        val components' = map (uncurry the_default) (map fst components ~~ comps)
        val pars = components';

        val expr = ([(suffix fields_locale_N pname,
                     (prefix, (Expression.Positional (map SOME (nameTN::valueTN::CONS_OF_N::pars)),[])))],[]);
(*        val (_, SOME intro) = Locale.intros_of thy (suffix fields_locale_N pname) |> @{print}
        val ax = Locale.axioms_of thy (suffix fields_locale_N full_name) |> @{print} *)
      in
        prove_interpretation_in (fn ctxt =>
            Locale.intro_locales_tac {strict = true, eager = false} ctxt [])
          (suffix fields_locale_N name, expr) thy
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
            fun upd (n,v) =
              let
                val nT = Proof_Context.infer_type (Local_Theory.target_of lthy) (n, dummyT)
              in Context.proof_map
                  (update_declinfo (Morphism.term phi (Free (n,nT)),v))
              end;
            val ctxt' = ctxt |> fold upd updates 
          in ctxt' end;

      in Context.mapping I upd_prf ctxt end;

  in thy
     |> cons_definition
           (Binding.suffix_name constructor_locale_N name_b) nameT (parents_expr,[])
           (map fst parent_comps) (map fst components)
     |> Context.theory_map
          (add_VDT full_name value_sort args (map snd parents) all_comps)
     |> add_locale (Binding.suffix_name fields_locale_N name_b) (locinsts,locs) []
     |> Proof_Context.theory_of
     |> fold interprete_parent_valuetypes parents
     |> add_locale name_b
            (  [(suffix constructor_locale_N full_name,
                  ((name ^ "_" ^ constructor_locale_N, true),
                   (Expression.Named ((typeN, TYPE_TY)::name_insts)
                   ,[]))),
                (suffix fields_locale_N full_name,
                  (("",false),(Expression.Named ([(nameTN, TYPE_TY),(valueTN, VALUE_TY)] @ proj_insts), []))
                )],
               [(Binding.name nameTN,  SOME nameTT,  NoSyn),
                (Binding.name valueTN, SOME valueTT, NoSyn)] @ vars)
            []
     |> Proof_Context.theory_of
     |> fold interprete_parent parents
     |> add_declaration full_name (declare_declinfo components')
  end;

(** preparation & wrapper for VDT **)

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

fun gen_define_VDT prep_typ' (value_sort,project_injectL)
                   base args name_b parents comps thy =
  let (* - args distinct
         - only args may occur in comps and parent-instantiations
         - number of insts must match parent args
         - no duplicate renamings
         - renaming should occur in constructor
         -
         - self_sort: sort of the value type
      *)
    val _ = writeln ("Defining VDT " ^ Binding.print name_b ^ " ...");

    val prep_typ = apfst translate_self_to_rep ooo prep_typ'

    val base' = Option.map (Locale.check thy) base

    val ctxt = case base' of SOME t => Locale.init t thy
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
              (case get_VDT (Context.Theory thy) full_pname of
                SOME r => r
               | NONE => error ("Undefined VDT " ^ quote pname));


        val (Ts',env') = fold_map (prep_typ ctxt) Ts env
            handle ERROR msg => cat_error msg
                    ("The error(s) above occurred in parent VDT specification "
                    ^ quote pname);
        val err_insts = if length args <> length Ts' then
            ["number of type instantiation(s) does not match arguments of parent VDT "
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
        else error (cat_lines (errs @ ["in parent VDT " ^ quote pname]))
      end;

    val args' = map (apsnd (Option.map (Syntax.read_sort ctxt) #> the_default (Sign.defaultS thy))) args

    val (parents',env) = fold_map add_parent parents args';
    val value_sort' = fold (parent_sort thy o #2 o #2) parents' 
              (if value_sort = "" then Sign.defaultS thy else Syntax.read_sort ctxt value_sort)
    val env = (selfN, value_sort')::env

    val err_dup_args =
         (case duplicates (op =) (map fst args) of
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
          if member (op =) (map fst args) selfN
          then [selfN ^ " is a reserved keyword and cannot be a type parameter"]
          else if member (op =) (map fst args) valueN
          then [valueN ^ " is a reserved keyword and cannot be a type parameter"]
          else []
      
      
    (*TODO!!!*)
    val err_extra_frees = []
      
    val project_injectL = Locale.check thy project_injectL


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
     then thy |> VDT_definition value_sort' project_injectL
                                base' args' name_b parents' parent_comps comps'
     else error (cat_lines errs)
  end
  handle ERROR msg => cat_error msg ("Failed to define VDT " ^ Binding.print name_b);

val define_VDT = gen_define_VDT read_typ;
val define_VDT_i = gen_define_VDT cert_typ;


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
  Parse_Spec.locale_prefix
  -- ((type_insts -- Parse.name_position) || (Parse.name_position >> pair []))
  -- renames
  >> (fn ((prefix, (insts, name)), renames) => (prefix, (insts, name, renames)));

in

fun VDT_decl' (default_value_sort, default_locale) =
  Parse.opt_target -- (Parse.type_args_constrained -- Parse.binding) --
    Scan.optional (\<^keyword>\<open>::\<close> |-- (
         Parse.sort >> rpair (default_locale, Position.none)
      || \<^keyword>\<open>(\<close> |-- Parse.sort --| \<^keyword>\<open>,\<close> -- Parse.name_position --| \<^keyword>\<open>)\<close>
    )) (default_value_sort,(default_locale, Position.none)) --
  (Scan.optional (\<^keyword>\<open>=\<close> |--
    ((Scan.repeat1 comp >> pair []) ||
      (plus1_unless comp parent --
        Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! (Scan.repeat1 comp)) []))) ([],[]));


fun define_VDT_command kwd comment defaults_setting =
  Outer_Syntax.command kwd comment
    (VDT_decl' defaults_setting >> (fn (((target, (args, name)), sort_locale), (parents, comps)) =>
      Toplevel.theory (define_VDT sort_locale target args name parents comps)));

val VDT_decl = VDT_decl' ("",project_injectL_default)
val _ = define_VDT_command
   \<^command_keyword>\<open>virtual_datatype\<close> "define virtual datatype as a locale context" ("",project_injectL_default)


end;

end
