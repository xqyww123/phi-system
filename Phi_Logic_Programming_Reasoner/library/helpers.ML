signature PHI_CONV = sig

val may_Trueprop_conv : conv -> conv

val protect_conv : conv
val unprotect_conv : conv

val LHS_conv : conv -> conv
val RHS_conv : conv -> conv

val inverse_eta_conv : conv
val quant_conv : string -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_case_prod_conv : ((cterm * cterm) * Proof.context -> conv) -> conv -> Proof.context -> conv
val meta_ball_conv : conv -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val meta_alls_conv : (Proof.context -> conv) -> Proof.context -> conv
val meta_all_body_conv : (Proof.context -> conv) -> Proof.context -> conv
val hol_ball_conv : conv -> (cterm * Proof.context -> conv) -> Proof.context -> conv
val rulify_Ball : (Proof.context -> conv) -> Proof.context -> conv
val hol_all_conv : (cterm * Proof.context -> conv) -> Proof.context -> conv
val hol_alls_to_meta_alls: (Proof.context -> conv) -> Proof.context -> conv

val prod_case_split_in_all_conv : (Proof.context -> conv) -> Proof.context -> conv
      (*converts \<open>\<And>x. meta_case_prod (meta_case_prod f) x\<close>, \<open>\<And>x. prem \<Longrightarrow>  meta_case_prod (meta_case_prod f) x\<close>
                 \<open>\<And>x. case_prod (case_prod f) x\<close>, \<open>\<And>x. prem \<longrightarrow> case_prod (case_prod f) x\<close>,
                 \<open>prem \<Longrightarrow> \<And>x. case_prod (case_prod f) x\<close>*)
val expand_meta_and_hol_ball : (Proof.context -> conv) (*converts the set*)
                            -> (Proof.context -> conv) (*converts the body*)
                            -> Proof.context -> conv
val exhausitively_expand_meta_and_hol_ball : (Proof.context -> conv) (*converts the set*)
                                          -> (Proof.context -> conv) (*converts the body*)
                                          -> Proof.context -> conv

val hol_imp_conv : conv -> conv -> conv

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

fun LHS_conv cv ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ =>
          Conv.arg1_conv cv ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) =>
          Conv.arg_conv (Conv.arg1_conv cv) ctm
     | _ => raise CTERM ("Not an equation", [ctm])

fun RHS_conv cv ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ =>
          Conv.arg_conv cv ctm
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) =>
          Conv.arg_conv (Conv.arg_conv cv) ctm
     | _ => raise CTERM ("Not an equation", [ctm])

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


fun rulify_case_prods cv ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Trueprop\<close>, _) $ X =>
      (case X
         of Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ _ =>
              (Conv.rewr_conv @{thm' atomize_case_prod[symmetric]} then_conv
               meta_case_prod_conv (rulify_case_prods cv o snd) Conv.all_conv ctxt then_conv
               Conv.try_conv (Conv.rewr_conv (Thm.transfer' ctxt
                    @{lemma' \<open>meta_case_prod (\<lambda>_ _. Trueprop True) x \<equiv> Trueprop True\<close>
                         by (unfold meta_case_prod_def)}))) ctm
          | _ => cv ctxt ctm
      )
     | _ => cv ctxt ctm

fun rulify_Ball C ctxt =
  Conv.rewr_conv @{thm' atomize_Ball[symmetric]} then_conv
  meta_ball_conv Conv.all_conv (rulify_case_prods C o snd) ctxt

(*requires eta-beta normalization!*)
fun prod_case_split_in_all_conv C ctxt =
  let fun get_bnames (Abs (N,_,Abs (N',_,_))) = SOME (N,N')
        | get_bnames _ = NONE
      fun rename_all2 NONE rule = rule
        | rename_all2 (SOME (N1, N2)) rule =
            case Thm.prop_of rule
              of Eq $ LHS $ (A1 $ Abs (_, T1, A2 $ Abs (_, T2, X))) =>
                  Thm.renamed_prop (Eq $ LHS $ (A1 $ Abs (N1, T1, A2 $ Abs (N2, T2, X)))) rule
               | _ => rule

      fun conv ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X) =>
              (case X
                 of Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const (\<^const_name>\<open>meta_case_prod\<close>, _) $ f $ _) =>
                      ((rename_all2 (get_bnames f) o Conv.rewr_conv @{thm split_paired_all}) then_conv
                        meta_all_conv (fn (_,ctxt') =>
                          meta_all_conv (K (Conv.arg_conv (Conv.rewr_conv @{thm meta_case_prod_simp}))) ctxt' then_conv
                          conv ctxt') ctxt) ctm
                  | Const (\<^const_name>\<open>meta_case_prod\<close>, _) $ f $ _ =>
                      ((rename_all2 (get_bnames f) o Conv.rewr_conv @{thm split_paired_all}) then_conv
                        meta_all_conv (fn (_,ctxt') =>
                          meta_all_conv (K (Conv.rewr_conv @{thm meta_case_prod_simp})) ctxt' then_conv
                          conv ctxt') ctxt) ctm
                  | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _
                      $ (Const (\<^const_name>\<open>case_prod\<close>, _) $ _ $ _)) =>
                      (Conv.rewr_conv @{thm' atomize_imp[symmetric]} then_conv
                       rulify_case_prods (K Conv.all_conv) ctxt then_conv
                       conv ctxt) ctm
                  | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>case_prod\<close>, _) $ _ $ _) =>
                      (rulify_case_prods (K Conv.all_conv) ctxt then_conv conv ctxt) ctm
                  | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $
                      (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>case_prod\<close>, _) $ _ $ _)) =>
                      (Conv.arg_conv (rulify_case_prods (K Conv.all_conv) ctxt) then_conv
                       conv ctxt) ctm
                  | _ => C ctxt ctm)
           | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ =>
                  (Conv.arg_conv inverse_eta_conv then_conv conv ctxt) ctm
           | _ => raise CTERM ("prod_case_split_in_all_conv: not a meta-all quantification", [ctm])
   in conv ctxt
  end

fun meta_ball_special_reduce on_fail on_success =
  let fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>meta_Ball\<close>, _)
              $ (Const(\<^const_name>\<open>Set.insert\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) $ Const(\<^const_name>\<open>bot\<close>, _))
              $ _ =>
                  (Conv.rewr_conv @{thm' meta_Ball_pair} then_conv conv) ctm
           | Const(\<^const_name>\<open>meta_Ball\<close>, _)
              $ (Const(\<^const_name>\<open>Set.insert\<close>, _) $ _ $ Const(\<^const_name>\<open>bot\<close>, _))
              $ _ =>
                  (Conv.rewr_conv @{thm' meta_Ball_sing} then_conv on_success) ctm
           | Const(\<^const_name>\<open>Ball\<close>, _)
              $ (Const(\<^const_name>\<open>Set.insert\<close>, _) $ (Const(\<^const_name>\<open>Pair\<close>, _) $ _ $ _) $ Const(\<^const_name>\<open>bot\<close>, _))
              $ _ =>
                  (Conv.rewr_conv @{thm' meta_Ball_pair} then_conv conv) ctm
           | _ => on_fail ctm
   in conv
  end

fun expand_meta_and_hol_ball Cs C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
        (Conv.arg1_conv (Cs ctxt) then_conv
         meta_ball_special_reduce
           (Conv.rewr_conv @{thm meta_Ball_def} then_conv
            prod_case_split_in_all_conv (meta_all_conv (fn (_,ctxt') =>
                Conv.implies_concl_conv (C ctxt'))) ctxt)
           (C ctxt))
         ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Ball\<close>, _) $ _ $ _ ) =>
         rulify_Ball C ctxt ctm
     | _ => C ctxt ctm

fun exhausitively_expand_meta_and_hol_ball Cs C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>meta_Ball\<close>, _) $ _ $ _ =>
            expand_meta_and_hol_ball Cs (exhausitively_expand_meta_and_hol_ball Cs C) ctxt ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Ball\<close>, _) $ _ $ _ ) =>
            expand_meta_and_hol_ball Cs (exhausitively_expand_meta_and_hol_ball Cs C) ctxt ctm
     | _ => C ctxt ctm


fun leading_antecedent_conv C = implies_conv C all_conv
fun hhf_concl_conv C ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => meta_all_conv (hhf_concl_conv C o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.arg_conv (hhf_concl_conv C ctxt) ctm
     | _ => C ctxt ctm

fun hhf_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => meta_all_conv (hhf_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (hhf_conv Cp Cc ctxt) ctm
     | _ => Cc ctxt ctm

fun premises_conv Cp Cc ctxt ctm =
  case Thm.term_of ctm
    of Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => meta_all_conv (premises_conv Cp Cc o snd) ctxt ctm
     | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => Conv.implies_conv (Cp ctxt) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.arg_conv (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
          Conv.combination_conv (Conv.arg_conv (Cp ctxt)) (premises_conv Cp Cc ctxt) ctm
     | Const (\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
          Conv.arg_conv (abs_conv (premises_conv Cp Cc o snd) ctxt) ctm
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

signature VARIABLE = sig
include VARIABLE

(*patched Variable.import and .export, as the original Variable.export only generalize fixed term variables
  but ignores fixed type variables of constants.*)

val export_generalization  :  typ TVars.table *  term Vars.table -> Names.set * Names.set
val export_generalization' : ctyp TVars.table * cterm Vars.table -> Names.set * Names.set

val export_inst : typ TVars.table * term Vars.table -> thm list -> thm list
val export_inst_to_original_idx : Proof.context -> typ TVars.table *  term Vars.table -> thm list -> thm list
  (*The usual 'export' varifies the fixed variables to fresh indexes instead of their original indexes.
    'export_inst_to_original_idx' improves this by fixing back to the original indexes, but slower.*)

end

structure Variable : VARIABLE = struct
open Variable

fun export_generalization (tyvars, tmvars) =
  (Names.build (TVars.fold (fn (_, TFree (N, _)) => Names.add_set N) tyvars),
   Names.build (Vars.fold (fn (_, tm) => Names.add_set (Term.term_name tm)) tmvars))

val export_generalization' = export_generalization o Phi_Help.uncertify_vars

fun export_inst inst ths =
  let val names = export_generalization inst
      val ids = map (fn th => Thm.maxidx_of th + 1) ths
   in map2 (Thm.generalize names) ids ths
  end

fun export_inst_to_original_idx ctxt inst ths =
  let val names = export_generalization inst
      val ids = map (fn th => Thm.maxidx_of th + 1) ths
      val ths' = map2 (Thm.generalize names) ids ths

      fun mk_inst_back i =
        (TVars.build (TVars.fold (fn (v, TFree (N,S)) => TVars.add (((N,i),S), Thm.ctyp_of ctxt (TVar v))) (fst inst)),
         Vars.build (Vars.fold (fn (v, Free (N,T)) => Vars.add (((N,i),T), Thm.cterm_of ctxt (Var v))) (snd inst)))
      fun inst_back i = Thm.instantiate (mk_inst_back i)

   in map2 inst_back ids ths'
  end

end

