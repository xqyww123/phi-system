exception REQUIRE_LAMBDA_NORMLAIZTION

signature PHI_HELP = sig

val warn_when_visible : Context.generic -> string -> unit

val take_last : int -> 'a list -> 'a list
val last : 'a list -> 'a
val front : 'a list -> 'a list
val split_last : 'a list -> 'a list * 'a
val repeat : ('a -> 'a) -> 'a -> 'a
val ntimes : int -> (int -> 'a -> 'a) -> 'a -> 'a

val max_of : ('a * 'a -> order) -> 'a list -> 'a option
val min_of : ('a * 'a -> order) -> 'a list -> 'a option


val leading_antecedent' : thm -> term

val LHS_of : term -> term
val RHS_of : term -> term

val pos_parser : string -> Position.T parser
val beta_eta_conversion : conv
val beta_eta_contract : thm -> thm
val beta_eta_contract_cterm : cterm -> cterm
val beta_eta_contract_term : term -> term
val beta_eta_contract_leading_antecedent : thm -> thm

val lambda_normalization_ctac : ('a * thm -> 'b) -> ('a * thm -> 'b)
val lambda_normalization_conv : conv -> conv
val lambda_normalization_rule : (thm -> thm) -> thm -> thm

val unique_flexflex : Proof.context -> thm -> thm

val list_mk_conj : term list -> term
val list_mk_disj : term list -> term
val conj_intros: Proof.context -> thm list -> thm
(*val conj_elim  : thm -> thm * thm
val conj_elims : thm -> thm list*)


(*For tyenv/tenv given from Pattern.match*)
val subst_tyenv : Type.tyenv -> typ TVars.table
val subst_tenv  : Type.tyenv -> Envir.tenv -> term Vars.table
val subst_env   : Type.tyenv * Envir.tenv -> typ TVars.table * term Vars.table
val subst_env'  : Envir.env -> typ TVars.table * term Vars.table

(*For tyenv/tenv given from Pattern.unify*)
val norm_tyenv : Type.tyenv -> typ TVars.table
val norm_tenv  : Type.tyenv -> Envir.tenv -> term Vars.table
val norm_env : Type.tyenv * Envir.tenv -> typ TVars.table * term Vars.table

val certify_tyvars : Context.generic -> typ TVars.table -> ctyp TVars.table
val certify_tmvars : Context.generic -> term Vars.table -> cterm Vars.table
val certify_vars : Context.generic -> typ TVars.table * term Vars.table -> ctyp TVars.table * cterm Vars.table
val uncertify_tyvars : ctyp TVars.table -> typ TVars.table
val uncertify_tmvars : cterm Vars.table -> term Vars.table
val uncertify_vars   : ctyp TVars.table * cterm Vars.table -> typ TVars.table * term Vars.table

(*val tvars_table_to_tyenv : ctyp TVars.table -> Type.tyenv
  val vars_table_to_tenv : cterm Vars.table -> Envir.tenv*)


val instantiate_higher_order_var : indexname list (*escape*) -> term list -> term Vars.table
(*Instantiate higher-order schematic variable whose all occurrences are applied to an argument
  containing no loose bound variable.*)

val instantiate_higher_order_var_in_antecedents' : int (*N*) -> Proof.context -> thm -> thm option (*returns none if no change*)
val instantiate_higher_order_var_in_antecedents : int (*N*) -> Proof.context -> thm -> thm
(*For the leading N antecedents only, if there is any higher-order schematic variable
which is applied to an argument containing no loose bound variable,
instantiate the schematic variable to the constant function on that parameter, \<open>\<lambda>_. ?var\<close>.

Different with instantiate_higher_order_var, the instantiation works successively for each leading
antecedent in order. `instantiate_higher_order_var` requires *all occurrences* of a HO
variable *in the whole proposition* have an argument containing no loose bound,
whereas `instantiate_higher_order_var_in_antecedents'` only checks the occurrences *in the leading
antecedent* one-by-one in order. Once a such HO variable is seen in the leading antecedent, it is instantiated,
no matter how it is applied in the subsequent antecedents nor the conclusion. This is identical to the
way of how \<phi>-LPR works, in the order of evaluating the antecedents.

N = ~1 means all antecedents

It assumes all variables can be instantiated arbitrarily.
However, for a reasoning rule, not all variables can be instantiated arbitrarily.
Some of them are IN-arguments which matches the input of a reasoning goal, so they should be considered
fixed, while others are OUT-arguments which assigns output to the reasoning goal, so they can be
instantiated arbitrarily.

Due to this issue, to simplify the higher order variables of a reasoning rule, the role of the
variables have to be given.

Also see Phi_Help.guess_IN_arguments_of_a_rule given latter
*)
val instantiate_higher_order_schematic_var_for_rule' :
        int (*N*) * indexname list (*IN-arguments to be fixed*) ->
        Proof.context -> thm -> thm option (*returns none if no change*)
val instantiate_higher_order_schematic_var_for_rule  :
        int (*N*) * indexname list (*IN-arguments to be fixed*) ->
        Proof.context -> thm -> thm



val has_head : string (* const name *) -> term -> bool

val strip_meta_hhf : term -> (string * typ) list (*quantified variables*)
                            * term list (*premises of the antecedent*)
                            * term (*conclusion containing loose bound*)
val strip_meta_hhf_bvtys : term -> PLPR_Pattern.bv_typs * term
val strip_meta_hhf_bvs : term -> PLPR_Pattern.bvs * term
val leading_antecedent : term -> (string * typ) list (*quantified variables*)
                               * term list (*premises of the antecedent*)
                               * term (*conclusion containing loose bound*)
val fix_leading_antecedent_meta_quantifiers : Proof.context -> term
                          -> term list (*quant vars*) * term list (*premises*) * term (*conclusion*) * Proof.context
                             (*where quantified variables are fixed*)
val strip_meta_hhf_c :
      cterm -> Proof.context -> cterm list (*quant vars*) * cterm list (*premises*) * cterm * Proof.context
val varified_leading_antecedent_meta_quantifiers : Proof.context -> term
                          -> term list (*premises*) * term (*conclusion*)
                             (*where quantified variables are varified (schematic variables)*)

end

structure Phi_Help : PHI_HELP = struct

fun warn_when_visible ctxt msg =
  if Context_Position.is_visible_generic ctxt
  then warning msg
  else ()

fun last [] = raise Fail "last"
  | last [x] = x
  | last (h::ls) = last ls
fun front [] = raise Fail "front"
  | front [x] = []
  | front (h::ls) = h :: front ls
fun split_last L = (front L, last L)
fun take_last n L = List.drop (L, length L - n)

fun repeat f x = repeat f (f x) handle TERM _ => x | CTERM _ => x | THM _ => x
fun ntimes_i i n f x = if i < n then ntimes_i (i+1) n f (f i x) else x
fun ntimes n f x = ntimes_i 0 n f x

fun max_of _ [] = NONE
  | max_of ord L = SOME (foldl1 (fn ab => if ord ab = LESS then snd ab else fst ab) L)

fun min_of _ [] = NONE
  | min_of ord L = SOME (foldl1 (fn ab => if ord ab = GREATER then snd ab else fst ab) L)


fun leading_antecedent' thm = fst (Logic.dest_implies (Thm.prop_of thm))

fun RHS_of (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ X) = X
  | RHS_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = RHS_of X
  | RHS_of (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ X) = X
  | RHS_of X = raise TERM ("LHS_of", [X])

fun LHS_of (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ X $ _) = X
  | LHS_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = LHS_of X
  | LHS_of (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ _) = X
  | LHS_of X = raise TERM ("LHS_of", [X])


fun pos_parser name =
  let val msg = name ^ " Fail to capture the position of your rule \
                  \when no argument is given to the attribute.\n\
                  \Please use \<open>" ^ name ^" add\<close> to address it.\n\
                  \The recorded position can be very helpful for debuging, albeit it \
                  \is not mandatory.\n\
                  \It is a technical limitation of Isar."
   in fn x => let val pos = Token.pos_of (hd x)
                  val _ = if pos = Position.none
                          then warning msg
                           else ()
               in (pos,x) end
  end

fun beta_eta_contract th =
  if Term.could_beta_eta_contract (Thm.prop_of th)
  then Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th
  else th

fun beta_eta_contract_cterm x =
  if Term.could_beta_eta_contract (Thm.term_of x)
  then Thm.dest_arg (Thm.cprop_of (Drule.beta_eta_conversion x))
  else x

fun beta_eta_contract_term x =
  if Term.could_beta_eta_contract x
  then Envir.beta_eta_contract x
  else x

fun beta_eta_conversion ctm =
  if Term.could_beta_eta_contract (Thm.term_of ctm)
  then Drule.beta_eta_conversion ctm
  else Conv.all_conv ctm

fun beta_eta_contract_leading_antecedent th =
  if Term.could_beta_eta_contract (leading_antecedent' th)
  then Thm.equal_elim (Conv.implies_conv Drule.beta_eta_conversion
                                         Conv.all_conv (Thm.cprop_of th)) th
  else th

fun lambda_normalization_ctac S s =
  let fun fallback exn =
        if Term.could_beta_eta_contract (Thm.prop_of (snd s))
        then S (apsnd beta_eta_contract s)
        else Exn.reraise exn
   in S s
      handle REQUIRE_LAMBDA_NORMLAIZTION => fallback (Fail "Internal Bug: is already normalized")
           | e as CTERM _ => fallback e
           | e as TERM _  => fallback e
           | e as THM _   => fallback e
  end

fun lambda_normalization_conv C ctm =
  let fun fallback exn =
        if Term.could_beta_eta_contract (Thm.term_of ctm)
        then (Drule.beta_eta_conversion then_conv C) ctm
        else Exn.reraise exn
   in C ctm
      handle REQUIRE_LAMBDA_NORMLAIZTION => fallback (Fail "Internal Bug: is already normalized")
           | e as CTERM _ => fallback e
           | e as TERM _  => fallback e
           | e as THM _   => fallback e
  end

fun lambda_normalization_rule R thm =
  let fun fallback exn =
        if Term.could_beta_eta_contract (Thm.prop_of thm)
        then R (beta_eta_contract thm)
        else Exn.reraise exn
   in R thm
      handle REQUIRE_LAMBDA_NORMLAIZTION => fallback (Fail "Internal Bug: is already normalized")
           | e as CTERM _ => fallback e
           | e as THM _   => fallback e
           | e as TERM _  => fallback e
  end

(*a naive but most general flex-flex solver, which works only when the structures are identical*)
fun flex_solver_for_type (Type (N, args), Type(N', args')) =
      if N = N' then maps flex_solver_for_type (args ~~ args')
      else raise TYPE("naive_flex_solver", [Type (N, args), Type(N', args')], [])
  | flex_solver_for_type (TFree A, TFree B) =
      if A = B then [] else raise TYPE("naive_flex_solver", [TFree A, TFree B], [])
  | flex_solver_for_type (TVar Va, TVar Vb) =
      if Va = Vb then [] else [(Va, TVar Vb)]
  | flex_solver_for_type (TVar Va, Tb) = [(Va, Tb)]

fun flex_solver (Abs (_,T,X), Abs (_,T',X')) (instT,inst) =
      flex_solver (X,X') (flex_solver_for_type (T,T') @ instT, inst)
  | flex_solver (A $ B, A' $ B') inst =
      flex_solver (A,A') (flex_solver (B,B') inst)
  | flex_solver (Free (Na,Ta), Free (Nb,Tb)) (instT,inst) =
      if Na = Nb then (flex_solver_for_type (Ta,Tb) @ instT, inst)
      else raise TERM ("naive_flex_solver", [Free (Na,Ta), Free (Nb,Tb)])
  | flex_solver (Bound a, Bound b) inst =
      if a = b then inst
      else raise TERM ("naive_flex_solver", [Bound a, Bound b])
  | flex_solver (Const (Na,Ta), Const (Nb,Tb)) (instT,inst) =
      if Na = Nb then (flex_solver_for_type (Ta,Tb) @ instT, inst)
      else raise TERM ("naive_flex_solver", [Const (Na,Ta), Const (Nb,Tb)])
  | flex_solver (Var (Na,Ta), Var (Nb,Tb)) (instT,inst) =
      if Na = Nb andalso Ta = Tb then (instT,inst)
      else (flex_solver_for_type (Ta, Tb) @ instT, (((Na,Ta), Var (Nb,Tb))) :: inst)
  | flex_solver (Var (Na,Ta), B) (instT,inst) =
      (flex_solver_for_type (Ta, Term.fastype_of B) @ instT, (((Na,Ta),B)) :: inst)

fun naive_flex_solver ctxt thm =
  let val tpairs = Thm.tpairs_of thm
   in if null tpairs then thm
  else let
      val inst = fold flex_solver tpairs ([],[])
      fun ty_add (k,v) tab = if TVars.defined tab k then raise TERM ("naive_flex_solver", [])
                             else TVars.add (k,v) tab
      fun tm_add (k,v) tab = if Vars.defined tab k then raise TERM ("naive_flex_solver", [])
                             else Vars.add (k,v) tab
      val instTy'= TVars.build (fold ty_add (fst inst))
      val instTy = TVars.build (fold (ty_add o apsnd (Thm.ctyp_of ctxt)) (fst inst))
      val instTm = Vars.build (fold (
                      tm_add o apsnd (Thm.cterm_of ctxt o Term_Subst.instantiate (instTy', Vars.empty))
                   ) (snd inst))
      val thm1 = Thm.instantiate (instTy, instTm) thm
      val frees = Term.declare_term_frees (Thm.prop_of thm) Name.context
      val vars = fold (fn (a,b) => Term.add_vars a o Term.add_vars b) (Thm.tpairs_of thm1) []
      val fix_names = Name.invent frees "\<x>" (length vars)
      val fixes = map2 (fn N => fn (_,T) => Thm.cterm_of ctxt (Free (N,T))) fix_names vars
   in Thm.instantiate (TVars.empty, Vars.make (vars ~~ fixes)) thm1
   |> Thm.flexflex_rule (SOME ctxt)
   |> Seq.pull
   |> (fn SOME (x, _) => x | NONE => error "BUG: naive_flex_solver")
   |> Thm.generalize (Names.empty, Names.make_set fix_names) (Thm.maxidx_of thm1)
  end
  end

fun unique_flexflex ctxt thm =
  if null (Thm.tpairs_of thm) then thm
  else (*case try (naive_flex_solver ctxt) thm (*disabled because of deficiencies in Isabelle kernel*)
    of SOME ret => ret
     | NONE =>*) Drule.flexflex_unique (SOME ctxt) thm

fun list_mk_conj [] = \<^const>\<open>True\<close>
  | list_mk_conj L = foldr1 HOLogic.mk_conj L

fun list_mk_disj [] = \<^const>\<open>True\<close>
  | list_mk_disj L = foldr1 HOLogic.mk_disj L

(*
fun conj_elim thPQ =
  let
    val _ = case Thm.prop_of thPQ
              of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) => ()
               | _ => raise THM ("conj_elim", 0, [thPQ])
    val (P, Q) = Thm.dest_binop (Thm.dest_arg (Thm.cprop_of thPQ))
      handle CTERM (msg, _) => raise THM (msg, 0, [thPQ]);
    val thP =
      Thm.implies_elim \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<and> Q \<Longrightarrow> P\<close> by (rule conjunct1)\<close> thPQ;
    val thQ =
      Thm.implies_elim \<^instantiate>\<open>P and Q in lemma (open) \<open>P \<and> Q \<Longrightarrow> Q\<close> by (rule conjunct2)\<close> thPQ;
  in (thP, thQ) end;

fun conj_elims th =
  case Thm.prop_of th
    of \<^Const>\<open>Trueprop\<close> $ \<^Const>\<open>True\<close> => []
     | _ => let fun elim th =
                  let val (th1, th2) = conj_elim th
                   in elim th1 @ elim th2
                  end handle THM _ => [th]
             in elim th
            end
*)

fun conj_intros _ [] = @{thm' TrueI}
  | conj_intros ctxt L = foldr1 (uncurry (HOLogic.conj_intr ctxt)) L


(* Substitution \& Instantiation *)

fun subst_tyenv tyenv
  = TVars.build (Vartab.fold (fn (N,(S,T)) => TVars.add ((N,S), T)) tyenv)

fun norm_tyenv tyenv
  = TVars.build (Vartab.fold (fn (N,(S,T)) => TVars.add ((N,S), Envir.norm_type tyenv T)) tyenv)

fun subst_tenv tyenv tenv =
  Vars.build (Vartab.fold (fn (N,(TY,TM)) =>
      Vars.add ((N, Envir.subst_type tyenv TY),
                (*Envir.subst_term_types tyenv*) (Envir.eta_contract TM))) tenv)

fun norm_tenv tyenv tenv =
  Vars.build (Vartab.fold (fn (N,(TY,TM)) =>
      Vars.add ((N, Envir.norm_type tyenv TY),
                    Envir.norm_term (Envir.Envir {maxidx = ~1, tenv=tenv,tyenv=tyenv}) TM
                                |> Envir.eta_contract)) tenv)

fun subst_env (TY,TM) = (subst_tyenv TY, subst_tenv TY TM)
fun subst_env' (Envir.Envir {tyenv, tenv, ...}) = subst_env (tyenv, tenv)
fun norm_env (TY,TM) = (norm_tyenv TY, norm_tenv TY TM)

fun certify_tyvars ctxt = TVars.map (K (Context.cases Thm.global_ctyp_of Thm.ctyp_of ctxt))
fun certify_tmvars ctxt = Vars.map (K (Context.cases Thm.global_cterm_of Thm.cterm_of ctxt))
fun certify_vars ctxt (ty, tm) = (certify_tyvars ctxt ty, certify_tmvars ctxt tm)
val uncertify_tyvars = TVars.map (K Thm.typ_of)
val uncertify_tmvars = Vars.map (K Thm.term_of)
fun uncertify_vars (ty, tm) = (uncertify_tyvars ty, uncertify_tmvars tm)


(* Instantiation of Higher Order Variables *)

fun mk_HO_ins terms (escape,ins0) =
  let
    fun count ret (X $ _) = count (ret + 1) X
      | count ret (Var v) = if member (op =) escape (fst v)
                            then (ret, NONE)
                            else (ret, SOME v)
      | count ret _ = (ret, NONE)
    val eq = ((op =) o apply2 fst)
    fun eq' ((a1,b1),(a2,b2)) = (fst a1 = fst a2 andalso b1 = b2)
    fun eqle ((a1,b1),(a2,b2)) = (fst a1 = fst a2 andalso b1 <= b2)
    fun sift (X as _ $ _) set =
         (case count 0 X
            of (N, SOME v) =>
                let fun subst (redex,residue) tm =
                          if redex aconv tm then residue
                          else (case tm of A $ B => subst (redex,residue) A $ subst (redex,residue) B
                                         | Abs (N,Ty,X) => Abs (N, Ty, subst (Term.incr_boundvars 1 redex, Term.incr_boundvars 1 residue) X)
                                         | X => X)
                    fun chk_dup A (X $ A') = chk_dup (subst (A', Term.dummy) A) X
                      | chk_dup A _ = Term.is_open A
                    fun visit (set,i) (X $ A) =
                          if Term.is_open A andalso chk_dup A X
                          then visit (sift A (insert eq' (v,N-i) set), i+1) X
                          else visit (sift A set, i+1) X
                      | visit (set,_) _ = set
                 in visit (insert eqle (v, ~1 - N) set,1) X end
             | _ =>
                let fun visit set (A $ B) = visit (sift B set) A
                      | visit set X = sift X set
                 in visit set X end)
      | sift (Abs(_,_,X)) set = sift X set
      | sift (Var v) set =
            if member (op =) escape (fst v)
            then set
            else insert eqle (v, ~1) set
      | sift _ set = set
    val set = fold sift terms []
    (*for elements in this set, if the second projection is negative 'n',
      '~1-n' is the number of arguments applied to an occurrence of the variable;
      else if is non-negative 'n', i.e., if (v,n) occurs in the set,
      the nth argument of the variable contains bound variable and therefore cannot be trimmed.

      calc_arity calculates the minimally number of occurred arguments applied to the variable*)
    fun calc_arity ret ((v,n)::L) =
          if n >= 0 orelse AList.defined eq ret v
          then calc_arity ret L
          else calc_arity ((v, fold (fn (v',m) => fn n' =>
                  if fst v' = fst v andalso m < 0 andalso ~1-m < n' then ~1-m else n') L (~1-n)) :: ret) L
      | calc_arity ret [] = ret
   val arity = calc_arity [] set
   fun forall_num n P = n < 0 orelse (P n andalso forall_num (n-1) P)
   val ins = map_filter (fn (v,n) =>
          if forall_num (n-1) (fn i => member eq' set (v,i))
          then NONE
          else let (*make the residue of the variable trimming upto the minimally number of
                     occurred arguments, leaving those argument containing loose bound untouched.*)
                   fun mk_term targs bs 0 T =
                          fold_rev (fn b => fn X => X $ b) bs
                            (Var (fst v, fold (fn a => fn T => \<^Type>\<open>fun a T\<close>) targs T))
                     | mk_term targs bs i \<^Type>\<open>fun a T\<close> =
                          if member (op =) set (v,n-i)
                          then Abs ("", a, mk_term (a::targs) (Bound (i-1) :: bs) (i-1) T)
                          else Abs ("", a, mk_term targs bs (i-1) T)
                     | mk_term _ _ _ _ = error "Internal bug #bb923326-bb1c-4ba6-9039-84963749ee92"
                   val term' = mk_term [] [] n (snd v)
                in SOME (v, term')
               end
       ) arity
    fun collect_var (Var (v,_)) ret = insert (op =) v ret
      | collect_var (A $ B) ret = collect_var B (collect_var A ret)
      | collect_var (Abs(_,_,X)) ret = collect_var X ret
      | collect_var _ ret = ret
   in (fold collect_var terms escape, ins@ins0)
  end

fun instantiate_higher_order_var escape terms = Vars.make (snd (mk_HO_ins terms (escape, [])))

fun instantiate_higher_order_var_in_antecedents' num ctxt thm =
  let fun get_concl (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs(_,_,X)) = get_concl X
        | get_concl (Const(\<^const_name>\<open>Pure.all\<close>, _) $ X) = get_concl (Term.incr_boundvars 1 X $ Bound 0)
        | get_concl (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = get_concl X
        | get_concl X = X
      val (_, ins) = fold (fn prem => mk_HO_ins [get_concl prem])
                          (case num of ~1 => Thm.prems_of thm
                                     | ~2 => Thm.prems_of thm @
                                             [snd (PLPR_Syntax.strip_embedded_patterns (Thm.concl_of thm))]
                                     | _  => List.take (Thm.prems_of thm, num))
                          ([],[])
  in if null ins then NONE
  else SOME (Thm.instantiate (TVars.empty, certify_tmvars (Context.Proof ctxt) (Vars.make ins)) thm)
 end

fun instantiate_higher_order_var_in_antecedents num ctxt thm =
  the_default thm (instantiate_higher_order_var_in_antecedents' num ctxt thm)

fun instantiate_higher_order_schematic_var_for_rule' (N, fixes) ctxt rule =
  let val (_, concl) = PLPR_Syntax.strip_embedded_patterns (Thm.concl_of rule)
      val vars0 = Term.add_vars concl []
      val typs = map (fn x => case AList.lookup (op =) vars0 x
                                of SOME ret => ret
                                 | _ => raise THM ("Not a variable occuring in the conclusion", 0, [rule])
                     ) fixes
      val (names, ctxt') = Variable.variant_fixes (map fst fixes) ctxt
      val frees = map (Thm.cterm_of ctxt' o Free) (names ~~ typs)
      val rule' = Thm.instantiate (TVars.empty, Vars.make ((fixes ~~ typs) ~~ frees)) rule
   in instantiate_higher_order_var_in_antecedents' N ctxt rule'
   |> Option.map (singleton (Variable.export ctxt' ctxt))
  end

fun instantiate_higher_order_schematic_var_for_rule num_fixes ctxt thm =
  the_default thm (instantiate_higher_order_schematic_var_for_rule' num_fixes ctxt thm)



fun has_head c (Const (c', _)) = (c = c')
  | has_head c (h $ _) = has_head c h
  | has_head _ _ = false

fun strip_meta_hhf term =
  let
    fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,H::P) B
      | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
      | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
          strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
      | strip (V,P) X = (rev V, rev P, X)
  in strip ([],[]) term end

fun strip_meta_hhf_bvtys term =
  let
    fun strip V (Const("Pure.imp", _) $ H $ B) = strip V B
      | strip V (Const("Pure.all", _) $ Abs (_, T, B)) = strip (T::V) B
      | strip V (Const("Pure.all", _) $ X) = strip V X
      | strip V X = (V, X)
  in strip [] term end

fun strip_meta_hhf_bvs term =
  let
    fun strip V (Const("Pure.imp", _) $ H $ B) = strip V B
      | strip V (Const("Pure.all", _) $ Abs (N, T, B)) = strip ((N,T)::V) B
      | strip V (Const("Pure.all", _) $ X) = strip V X
      | strip V X = (V, X)
  in strip [] term end

fun leading_antecedent (Const("Pure.imp", _) $ H $ _) = strip_meta_hhf H
  | leading_antecedent X = raise TERM ("has no antecedent", [X])

fun fix_leading_antecedent_meta_quantifiers ctxt0 sequent =
  let
    val (qvs, prems, ant01) = leading_antecedent sequent

    (* fix universally quantified variables *)
    val (qv_names, ctxt'01) = Variable.add_fixes (map fst qvs) ctxt0
    val qvars = map2 (fn N => fn (_,T) => Free (N,T)) qv_names qvs
    val ctxt = fold Variable.declare_term qvars ctxt'01
    val leading_ant = subst_bounds (rev qvars, ant01)
  in (qvars,prems,leading_ant,ctxt)
  end

fun strip_meta_hhf_c cterm ctxt =
  let
    fun strip (V,P) (Const("Pure.imp", _) $ H $ B) ctm ctxt
          = strip (V, Thm.dest_arg1 ctm :: P) B (Thm.dest_arg ctm) ctxt
      | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) ctm ctxt
          = let val ([name'],ctxt') = Variable.variant_fixes [a] ctxt
                val (v', B') = Thm.dest_abs_fresh name' (Thm.dest_arg ctm)
             in strip (v'::V,P) B B' ctxt'
            end
      | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ B) ctm ctxt
          = let val ([name'],ctxt') = Variable.variant_fixes ["_"] ctxt
                val v' = Thm.cterm_of ctxt (Free (name', ty))
                val B' = Thm.apply (Thm.dest_arg ctm) v'
             in strip (v' :: V, P) B B' ctxt'
            end
      | strip (V,P) X ctm ctxt = (rev V, rev P, ctm, ctxt)
  in strip ([],[]) (Thm.term_of cterm) cterm ctxt end

fun varified_leading_antecedent_meta_quantifiers ctxt sequent =
  let val (_,prems,leading_ant,ctxt') = fix_leading_antecedent_meta_quantifiers ctxt sequent
      val (leading_ant'::prems') = Variable.export_terms ctxt' ctxt (leading_ant::prems)
   in (prems',leading_ant')
  end



end

infix 0 RS' RSN'

fun tha RSN' (ctxt, i, thb) =
  (case Seq.chop 2 (Thm.biresolution (SOME ctxt) false [(false, tha)] i thb) of
    ([th], _) => Thm.solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", i, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", i, [tha, thb]));

(*Resolution: P \<Longrightarrow> Q, Q \<Longrightarrow> R gives P \<Longrightarrow> R*)
fun tha RS' (ctxt, thb) = tha RSN' (ctxt, 1,thb);

fun apply3 f (a,b,c) = (f a, f b, f c)
fun eq_pair3 f g h ((a,b,c),(a',b',c')) = f (a,a') andalso g (b,b') andalso h (c,c')

fun select P x = if P x then SOME x else NONE
