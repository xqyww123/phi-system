exception REQUIRE_LAMBDA_NORMLAIZTION

signature PHI_HELP = sig

val leading_antecedent' : thm -> term

val pos_parser : string -> Position.T parser
val beta_eta_conversion : conv
val beta_eta_contract : thm -> thm
val beta_eta_contract_cterm : cterm -> cterm
val beta_eta_contract_term : term -> term

val lambda_normalization_ctac : ('a * thm -> 'b) -> ('a * thm -> 'b)
val lambda_normalization_conv : conv -> conv
val lambda_normalization_rule : (thm -> thm) -> thm -> thm

val unique_flexflex : Proof.context -> thm -> thm

val list_mk_conj : term list -> term
val list_mk_disj : term list -> term
val conj_intros: Proof.context -> thm list -> thm
val conj_elim  : thm -> thm * thm
val conj_elims : thm -> thm list

val instantiate_higher_order_schematic_var' : int (*N*) -> Proof.context -> thm -> thm option (*returns none if no change*)
val instantiate_higher_order_schematic_var : int (*N*) -> Proof.context -> thm -> thm
(*For the leading N antecedents only, if there is any higher-order schematic variable
which is applied to a constant argument instead of a bound variable as usual,
instantiate the schematic variable to the constant function on that parameter, \<open>\<lambda>_. ?var\<close>.

N = ~1 means all antecedents, N = ~2 means to consider the conclusion of the thm in addition.*)


end

structure Phi_Help : PHI_HELP = struct

fun leading_antecedent' thm = fst (Logic.dest_implies (Thm.prop_of thm))

fun pos_parser name =
  let val msg = name ^ " cannot capture the position of your rule \
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

fun conj_intros _ [] = @{thm' TrueI}
  | conj_intros ctxt L = foldr1 (uncurry (HOLogic.conj_intr ctxt)) L


fun instantiate_higher_order_schematic_var' num ctxt thm =
  let fun get_concl (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs(_,_,X)) = get_concl X
        | get_concl (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = get_concl X
        | get_concl X = X
      fun mk_ins ant (escape,ins0) =
        let
          fun count ret (X $ _) = count (ret + 1) X
            | count ret (Var v) = if member (op =) escape (fst v)
                                  then (ret, NONE)
                                  else (ret, SOME v)
            | count ret _ = (ret, NONE)
          val eq = ((op =) o apply2 fst)
          fun eq' ((a1,b1),(a2,b2)) = (fst a1 = fst a2 andalso b1 = b2)
          fun eqle ((a1,b1),(a2,b2)) = (fst a1 = fst a2 andalso b1 <= b2)
          fun sift set (X as _ $ _) =
               (case count 0 X
                  of (N, SOME v) =>
                      let fun visit (set,i) (X $ A) =
                                if exists_subterm (fn Bound _ => true | _ => false) A
                                then visit (sift (insert eq' (v,N-i) set) A, i+1) X
                                else visit (sift set A, i+1) X
                            | visit (set,_) _ = set
                       in visit (insert eqle (v, ~1 - N) set,1) X end
                   | _ =>
                      let fun visit set (A $ B) = visit (sift set B) A
                            | visit set X = sift set X
                       in visit set X end)
            | sift set (Abs(_,_,X)) = sift set X
            | sift set (Var v) =
                  if member (op =) escape (fst v)
                  then set
                  else insert eqle (v, ~1) set
            | sift set _ = set
          val set = sift [] ant
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
                else let fun mk_term targs bs 0 T =
                                fold (fn b => fn X => X $ b) bs
                                  (Var (fst v, fold (fn a => fn T => \<^Type>\<open>fun a T\<close>) targs T))
                           | mk_term targs bs i \<^Type>\<open>fun a T\<close> =
                                if member (op =) set (v,n-i)
                                then Abs ("", a, mk_term (a::targs) (Bound (i-1) :: bs) (i-1) T)
                                else Abs ("", a, mk_term targs bs (i-1) T)
                           | mk_term _ _ _ _ = error "Internal bug #bb923326-bb1c-4ba6-9039-84963749ee92"
                         val term' = mk_term [] [] n (snd v)
                      in SOME (v, Thm.cterm_of ctxt term')
                     end
             ) arity
          fun collect_var ret (Var (v,_)) = insert (op =) v ret
            | collect_var ret (A $ B) = collect_var (collect_var ret A) B
            | collect_var ret (Abs(_,_,X)) = collect_var ret X
            | collect_var ret _ = ret
         in (collect_var escape ant, ins@ins0)
        end
      val (_, ins) = fold (fn prem => mk_ins (get_concl prem))
                          (if num = ~1 then Thm.prems_of thm
                           else if num = ~2 then Thm.prems_of thm @ [Thm.concl_of thm]
                           else List.take (Thm.prems_of thm, num))
                          ([],[])
  in if null ins then NONE
  else SOME (Thm.instantiate (TVars.empty, Vars.make ins) thm)
 end

fun instantiate_higher_order_schematic_var num ctxt thm =
  the_default thm (instantiate_higher_order_schematic_var' num ctxt thm)


end

signature PHI_CONV = sig

val may_Trueprop_conv : conv -> conv

val protect_conv : conv
val unprotect_conv : conv

val inverse_eta_conv : conv
val quant_conv : string -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_case_prod_conv : ((cterm * cterm) * Proof.context -> conv) -> conv -> Proof.context -> conv
val meta_ball_conv : conv -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_alls_conv : (Proof.context -> conv) -> Proof.context -> conv
val meta_all_body_conv : (Proof.context -> conv) -> Proof.context -> conv
val hol_ball_conv : conv -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val hol_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val hol_alls_to_meta_alls: (Proof.context -> conv) -> Proof.context -> conv
val exhausitively_expand_meta_and_hol_ball : (Proof.context -> conv) -> Proof.context -> conv

val hol_imp_conv : conv -> conv -> conv

val prod_case_split_in_all_conv : (Proof.context -> conv) -> Proof.context -> conv

val leading_antecedent_conv : conv -> conv
val hhf_concl_conv : (Proof.context -> conv) -> Proof.context -> conv
val hhf_conv : (Proof.context -> conv) (*premise conv*)
            -> (Proof.context -> conv) (*concl conv*)
            -> Proof.context -> conv
(*for any meta premise or HOL premise, meta quantification or HOL quantification*)
val premises_conv : (Proof.context -> conv) (*premise conv*)
                  -> (Proof.context -> conv) (*concl conv*)
                  -> Proof.context -> conv
val recursive_premises_conv : (Proof.context -> conv) -> Proof.context -> conv

val rewrite_leading_antecedent : Proof.context -> thm list -> thm -> thm
val simplify_leading_antecedent : Proof.context -> thm -> thm
val simplify_leading_antecedent_hhf_concl : Proof.context -> thm -> thm

val conj_sequence_conv : conv -> conv
      (*applies the conv to every element in a HOL.conj sequent (or a tree)*)

end

structure Phi_Conv : PHI_CONV = struct
open Conv

fun may_Trueprop_conv C ctm =
  case Thm.term_of ctm
    of \<^Const>\<open>Trueprop\<close> $ _ => Conv.arg_conv C ctm
     | _ => C ctm

val protect_conv = rewr_conv @{thm Pure.prop_def[symmetric]}
val unprotect_conv = rewr_conv @{thm Pure.prop_def}



val inverse_eta = Thm.eta_conversion \<^schematic_cterm>\<open>\<lambda>x. (?f::'a::{} \<Rightarrow> 'b::{}) x\<close>
               |> Thm.symmetric
               |> Thm.trim_context
fun inverse_eta_conv ctm =
  case Thm.typ_of_cterm ctm
    of Type (\<^type_name>\<open>fun\<close>, _) =>
          Thm.instantiate (TVars.make [((("'a",0),[]), Thm.dest_ctyp0 (Thm.ctyp_of_cterm ctm)),
                                       ((("'b",0),[]), Thm.dest_ctyp1(Thm.ctyp_of_cterm ctm))],
                           Vars.make [((("f",0), Thm.typ_of_cterm ctm), ctm)])
                          inverse_eta
     | _ => raise CTERM ("inverse_eta_conv: not a function", [ctm])

fun abs_conv cv ctxt ctm =
  case Thm.term_of ctm
    of Abs _ => Conv.abs_conv cv ctxt ctm
     | _ => (inverse_eta_conv then_conv Conv.abs_conv cv ctxt) ctm

fun meta_all_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const ("Pure.all", _) $ _ => arg_conv (abs_conv cv ctxt) ct
  | _ => raise CTERM ("meta_all_conv", [ct]))

fun meta_alls_conv cv ctxt ctm =
  case Thm.term_of ctm
    of Const ("Pure.all", _) $ _ => meta_all_conv (meta_alls_conv cv o snd) ctxt ctm
     | _ => cv ctxt ctm

fun meta_ball_conv cs cv ctxt ctm =
  (case Thm.term_of ctm of
    Const (\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
        combination_conv (arg_conv cs) (abs_conv cv ctxt) ctm
  | _ => raise CTERM ("meta_all_conv", [ctm]))

fun hol_ball_conv cs cv ctxt ctm =
  (case Thm.term_of ctm of
    Const (\<^const_name>\<open>Set.Ball\<close>, _) $ _ $ _ =>
        combination_conv (arg_conv cs) (abs_conv cv ctxt) ctm
  | _ => raise CTERM ("hol_ball_conv", [ctm]))

fun meta_case_prod_conv cv cx ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>meta_case_prod\<close>, _) $ _ $ _ =>
        combination_conv (arg_conv (abs_conv (fn (x,ctxt) =>
              abs_conv (fn (y,ctxt) => cv ((x,y), ctxt)) ctxt) ctxt)) cx ctm
     | _ => raise CTERM ("meta_case_prod_conv", [ctm])

fun is_strict_reflexive th = (op =) (Logic.dest_equals (Thm.prop_of th))
  handle TERM _ => false;

fun abs_conv cv ctxt ct =
  (case Thm.term_of ct of
    Abs (a, _, _) =>
      let
        val ((v, ct'), ctxt') = Variable.dest_abs_cterm ct ctxt;
        val eq = cv (v, ctxt') ct';
      in if is_strict_reflexive eq then all_conv ct else Thm.abstract_rule a v eq end
  | _ => raise CTERM ("abs_conv", [ct]));

fun quant_conv head cv ctxt ct =
  (case Thm.term_of ct
     of Const (N, _) $ Abs _ =>
          if N = head then Conv.arg_conv (abs_conv cv ctxt) ct
                      else raise CTERM ("quant_conv", [ct])
      | Const (N, _) $ _ =>
          if N = head then Conv.arg_conv (inverse_eta_conv then_conv abs_conv cv ctxt) ct
                      else raise CTERM ("quant_conv", [ct])
      | _ => raise CTERM ("quant_conv", [ct]))

val hol_all_conv = quant_conv \<^const_name>\<open>All\<close>

fun meta_all_body_conv C ctxt =
  meta_all_conv (fn (_, ctxt) => meta_all_body_conv C ctxt) ctxt
  else_conv C ctxt

fun hol_alls_to_meta_alls C ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>All\<close>, _) $ _) =>
         (Conv.rewr_conv @{thm' atomize_all[symmetric]} then_conv
          meta_all_conv (hol_alls_to_meta_alls C o snd) ctxt) ctm
     | _ => C ctxt ctm

fun hol_imp_conv cv1 cv2 ct =
  (case Thm.term_of ct
     of Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv cv1) cv2 ct
      | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (hol_imp_conv cv1 cv2) ct
      | _ => raise CTERM ("imp_conv", [ct]));



(*requires eta-beta normalization!*)
fun prod_case_split_in_all_conv C ctxt ctm =
  let fun get_bnames (Abs (N,_,Abs (N',_,_))) = SOME (N,N')
        | get_bnames _ = NONE
      fun rename_all2 NONE rule = rule
        | rename_all2 (SOME (N1, N2)) rule =
            let val (A1 $ Abs (_, T1, A2 $ Abs (_, T2, X))) = Thm.prop_of rule
             in Thm.renamed_prop (A1 $ Abs (N1, T1, A2 $ Abs (N2, T2, X))) rule
            end

      fun has_case_prod (Const (\<^const_name>\<open>meta_case_prod\<close>, _) $ f $ _)
            = SOME (get_bnames f, @{thm meta_case_prod_simp})
        | has_case_prod (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>case_prod\<close>, _) $ f $ _))
            = SOME (get_bnames f, @{thm prod.case[folded atomize_eq]})
        | has_case_prod _ = NONE

   in case Thm.term_of ctm
        of Const(\<^const_name>\<open>Pure.all\<close>, _) $ X =>
            (case has_case_prod X
               of SOME (bnames, rule) =>
                    ((rename_all2 bnames o Conv.rewr_conv @{thm split_paired_all}) then_conv
                     meta_all_conv (fn (_,ctxt') =>
                        meta_all_conv (K (Conv.rewr_conv rule)) ctxt' then_conv
                        prod_case_split_in_all_conv C ctxt') ctxt) ctm
                | NONE => C ctxt ctm)
         | _ => raise CTERM ("prod_case_split_in_all_conv: not a meta-all quantification", [ctm])
  end



fun exhausitively_expand_meta_and_hol_ball C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
         (Conv.rewr_conv @{thm meta_Ball_def} then_conv
          prod_case_split_in_all_conv (meta_all_conv (fn (_,ctxt') =>
              Conv.implies_concl_conv (exhausitively_expand_meta_and_hol_ball C ctxt'))) ctxt
         ) ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Ball\<close>, _) $ _ $ _ ) =>
         (Conv.rewr_conv @{thm Ball_for_reason} then_conv
          prod_case_split_in_all_conv (meta_all_conv (fn (_,ctxt') =>
              Conv.implies_concl_conv (exhausitively_expand_meta_and_hol_ball C ctxt'))) ctxt
         ) ctm
     | _ => C ctxt ctm




fun leading_antecedent_conv C = implies_conv C all_conv
fun hhf_concl_conv C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (hhf_concl_conv C o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.arg_conv (hhf_concl_conv C ctxt) ctm
     | _ => C ctxt ctm

fun hhf_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (hhf_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (hhf_conv Cp Cc ctxt) ctm
     | _ => Cc ctxt ctm

fun premises_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ => meta_all_conv (premises_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (Cp ctxt)) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.All\<close>, _) $ Abs _ =>
          Conv.arg_conv (Conv.abs_conv (premises_conv Cp Cc o snd) ctxt) ctm
     | _ => Cc ctxt ctm

fun recursive_premises_conv C ctxt ctm =
  premises_conv (fn ctxt => fn ctm =>
      case Thm.term_of ctm
        of Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.All\<close>, _) $ _ ) =>
              recursive_premises_conv C ctxt ctm
         | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ ) =>
              recursive_premises_conv C ctxt ctm
         | _ => C ctxt ctm)
    (K Conv.all_conv) ctxt ctm


fun rewrite_leading_antecedent ctxt rules =
  Conv.gconv_rule (Raw_Simplifier.rewrite ctxt true rules) 1

fun simplify_leading_antecedent ctxt =
  Conv.gconv_rule (Simplifier.rewrite ctxt) 1

fun simplify_leading_antecedent_hhf_concl ctxt =
  Conv.gconv_rule (hhf_concl_conv Simplifier.rewrite ctxt) 1

fun conj_sequence_conv C ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
       Conv.combination_conv (Conv.arg_conv (conj_sequence_conv C)) (conj_sequence_conv C) ctm
     | _ => C ctm


end

infix 0 RS' RSN'

fun tha RSN' (ctxt, i, thb) =
  (case Seq.chop 2 (Thm.biresolution (SOME ctxt) false [(false, tha)] i thb) of
    ([th], _) => Thm.solve_constraints th
  | ([], _) => raise THM ("RSN: no unifiers", i, [tha, thb])
  | _ => raise THM ("RSN: multiple unifiers", i, [tha, thb]));

(*Resolution: P \<Longrightarrow> Q, Q \<Longrightarrow> R gives P \<Longrightarrow> R*)
fun tha RS' (ctxt, thb) = tha RSN' (ctxt, 1,thb);


signature HOLOGIC = sig
include HOLOGIC

val imp_conv : conv -> conv -> conv
val All_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val Ex_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv

end

structure HOLogic : HOLOGIC = struct
open HOLogic

val imp_conv = Phi_Conv.hol_imp_conv
val All_conv = Phi_Conv.hol_all_conv
val Ex_conv = Phi_Conv.quant_conv \<^const_name>\<open>Ex\<close>

end

