signature PHI_REASONERS = sig
include PHI_REASONERS

val existential_obligation : int Config.T

end

structure Phi_Reasoners : PHI_REASONERS = struct
open Phi_Reasoners

val existential_obligation = Config.declare_int ("Phi_Reasoners.existential_obligation", \<^here>) (K 2)

val _ = Theory.setup (
  Attrib.setup \<^binding>\<open>\<phi>reason_mode_existential_obligation\<close> (
    Scan.lift (\<^keyword>\<open>=\<close> |--
      (Args.$$$ "yes" >> K 1 || Args.$$$ "no" >> K 0 || Args.$$$ "enhanced" >> K 2))
    >> (fn mode => Thm.declaration_attribute (K (Config.put_generic existential_obligation mode)))
  ) "set the mode how \<phi>-LPR generates existential quantificatino in the obligation.\n\
    \0: do not generate existence in obligations, leaving them schematic variables\n\
    \1: generate existence in obligations\n\
    \2: generate existence in obligations and apply a special patch on them to enhance the automation\
    \of Isabelle for solving them (using introduction rules)"
)

end

signature PHI_CONV = sig

include PHI_CONV

(* (P \<longrightarrow> Q1) \<and> (P \<longrightarrow> Q2) \<and> \<dots> \<and> (P --> Qn) *)
val zip_conjs : conv
(*recursively for each nested implication*)
val zip_conjs_recursively : conv

(* (* (\<forall>x. P1 x) \<and> (\<forall>x. P2 x) \<dots> \<and> (\<forall>x. Pn x) \<longrightarrow> (\<forall>x. P1 x \<and> P2 x \<and> \<dots> Pn x)) *)
val zip_Alls : conv
val zip_Alls_recursively : Proof.context -> conv *)

(*
val zip_All_conj_recursively : Proof.context -> conv
*)

val move_Ex_inside_All : Proof.context -> conv
val move_Ex_inside_All_recursive : (Proof.context -> conv) -> Proof.context -> conv

val move_sp_Ex_inside_All : Proof.context -> conv
val move_sp_Ex_inside_All_recursive : (Proof.context -> conv) -> Proof.context -> conv

val move_Ex_downto_Disj : conv
val move_Ex_downto_Disj_recursive : conv -> conv

val move_sp_Ex_downto_Disj : conv
val move_sp_Ex_downto_Disj_recursive : conv -> conv

(*move inside to \<forall> and \<or>, with zipping over \<and>*)
val move_Ex_inside : (Proof.context -> conv) -> Proof.context -> conv
val move_sp_Ex_inside : (Proof.context -> conv) -> Proof.context -> conv

(*
(*move to inside any \<forall> and \<or>, with zip over \<and> and \<forall>, exhaustively*)
val move_Ex_inside_exhaustively : Proof.context -> conv
val move_sp_Ex_inside_exhaustively : Proof.context -> conv*)

end

structure Phi_Conv : PHI_CONV = struct
open Phi_Conv

fun zip_conjs ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =>
        Conv.rewr_conv @{thm' imp_conjR[folded atomize_eq, symmetric]} ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Const(\<^const_name>\<open>True\<close>, _)) =>
        Conv.rewr_conv @{thm' HOL.simp_thms(21)[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>True\<close>, _)) $ _ =>
        Conv.rewr_conv @{thm' HOL.simp_thms(22)[folded atomize_eq]} ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) $ _ =>
        (Conv.arg1_conv zip_conjs then_conv zip_conjs) ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
        (Conv.arg_conv zip_conjs then_conv zip_conjs) ctm
     | _ => raise CTERM ("Phi_Conv.zip_conjs", [ctm])

fun zip_conjs_recursively ctm =
  (zip_conjs then_conv HOLogic.imp_conv Conv.all_conv zip_conjs_recursively) ctm
  handle CTERM _ => Conv.all_conv ctm

val zip_conjs_recursively1 = zip_conjs then_conv zip_conjs_recursively

fun bound_occurs i (Bound j) = i = j
  | bound_occurs i (Abs (_,_,X)) = bound_occurs (i+1) X
  | bound_occurs i (A $ B) = bound_occurs i A orelse bound_occurs i B
  | bound_occurs _ _ = false

(*mv_over_conj: (Qx. A \<and> B x) \<equiv> A \<and> (Qx. B)
  rm_trivial: (Qx. A) \<equiv> A *)
fun sink_quantifier_over_conjs (quant_name, mv_over_conj, rm_trivial, swap_rule) =
  let datatype part = All | No | Mix of thm
      (*given a conj-tree containing some leaves that are ex-quantified or not,
        this process sorts the tree such that all the quantified leaves are in the right child of the root
        and all the not-quantified are in the left child.
        All means the current subtree's leaves are all quantified,
        No means none of leaves are,
        Mix means all quantified leaves are in the right child and all that not are in the left,
            after the conversion given as the thm*)
      fun partition_conj var ctm =
        case Thm.term_of ctm
          of Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
               (case (partition_conj var (Thm.dest_arg1 ctm), partition_conj var (Thm.dest_arg ctm))
                  of (No, No) =>      No
                   | (No, All) =>     Mix (Conv.all_conv ctm)
                   | (No, Mix th) =>  Mix ((Conv.arg_conv (K th) then_conv
                                            Conv.rewr_conv @{thm' HOL.conj_assoc[folded atomize_eq, symmetric]}) ctm)
                   | (All, No) =>     Mix (Conv.rewr_conv @{thm' HOL.conj_commute[folded atomize_eq]} ctm)
                   | (All, All) =>    All
                   | (All, Mix th) => Mix ((Conv.arg_conv (K th) then_conv
                                           Conv.rewr_conv @{thm' HOL.conj_left_commute[folded atomize_eq]}) ctm)
                   | (Mix tha, No) => Mix ((Conv.arg1_conv (K tha) then_conv
                                            Conv.rewr_conv @{thm' partition_conj_MN}) ctm)
                   | (Mix tha, All) => Mix ((Conv.arg1_conv (K tha) then_conv
                                             Conv.rewr_conv @{thm' HOL.conj_assoc[folded atomize_eq]}) ctm)
                   | (Mix tha, Mix thb) => Mix ((Conv.arg1_conv (K tha) then_conv
                                                 Conv.arg_conv (K thb) then_conv
                                                 Conv.rewr_conv @{thm' partition_conj_MM}) ctm))
          | X => if exists_subterm (fn Free (N',_) => N' = var | _ => false) X
                 then All
                 else No

      fun quick_chk1 var (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) =
           (case (quick_chk1 var A, quick_chk1 var B)
              of (All, All) => All
               | (No, No) => No
               | _ => Mix Drule.dummy_thm)
        | quick_chk1 var X = if bound_occurs var X
                             then All
                             else No

      fun quick_chk lv (Y as (Const(N, _) $ X)) =
            if N = quant_name then quick_chk lv X else quick_chk1 lv Y
        | quick_chk lv (Abs (_, _, X)) = quick_chk (lv+1) X
        | quick_chk lv X = quick_chk1 lv X

      fun quick_chk0 ctm =
        case Thm.term_of ctm
          of Const(N, _) $ X =>
              if N = quant_name then quick_chk ~1 X else raise CTERM ("sink_quantifier_over_conjs", [ctm])
           | _ => raise CTERM ("sink_quantifier_over_conjs", [ctm])

      fun open_quant C ctm =
        case Thm.term_of ctm
          of Const(N, _) $ X =>
               if N = quant_name
               then (case X of Abs (_, _, X) => C X ctm
                             | _ => (Conv.arg_conv Phi_Conv.inverse_eta_conv then_conv
                                     open_quant C) ctm )
               else raise CTERM ("sink_quantifier_over_conjs", [ctm])
           | _ =>   raise CTERM ("sink_quantifier_over_conjs", [ctm])

   in fn ctxt => fn ctm => (
   case quick_chk0 ctm
     of All => raise CTERM ("sink_quantifier_over_conjs: unfeasible", [ctm])
      | No  => Conv.rewr_conv rm_trivial ctm
      | _ => let
        fun conv ctxt ctm = open_quant (fn tm => fn ctm =>
          case tm
            of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
                 (Phi_Conv.quant_conv quant_name (fn (cvar, ctxt) => fn ctm =>
                    let val Free (N, _) = Thm.term_of cvar
                     in case partition_conj N ctm
                          of Mix th => th
                           | _ => error "BUG sWz5mwYCSD2Wd08rPgFKEQ"
                    end
                  ) ctxt
                  then_conv Conv.rewr_conv mv_over_conj) ctm
             | Const(N,_) $ _ =>
                  if N = quant_name
                  then (Conv.rewr_conv swap_rule then_conv
                        Phi_Conv.quant_conv quant_name (conv o snd) ctxt) ctm
                  else raise CTERM ("sink_quantifier_over_conjs: no conj", [ctm])
             | _ => raise CTERM ("sink_quantifier_over_conjs: no conj", [ctm])
          ) ctm
        in conv ctxt ctm
       end)
  end

val sink_All_over_conjs = sink_quantifier_over_conjs
        (\<^const_name>\<open>HOL.All\<close>, @{thm' HOL.all_simps(2)[folded atomize_eq]},
                              @{thm' HOL.simp_thms(35)[folded atomize_eq]},
                              @{thm' HOL.all_comm[folded atomize_eq]})

(*
fun zip_Alls ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
        HOLogic.conj_conv zip_Alls zip_Alls ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
        HOLogic.conj_conv Conv.all_conv zip_Alls ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ ) =>
        Conv.rewr_conv @{thm' all_conj_distrib[folded atomize_eq, symmetric]} ctm
     | _ => raise CTERM ("Phi_Conv.zip_Alls", [ctm])

fun zip_Alls_recursively ctxt ctm =
  (zip_Alls then_conv HOLogic.All_conv (zip_Alls_recursively o snd) ctxt) ctm
  handle CTERM _ => Conv.all_conv ctm


fun zip_Alls__same_quantifier' (Name,cTy) =
  let val Ty = Thm.typ_of cTy
      val name = (Name, Ty)
      fun has_the_quantifier (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (N,Ty,X))
          (*It is not the strongest as it does not consider the quantifiers hidden down to conjunctions*)
            = name = (N,Ty) orelse has_the_quantifier X
        | has_the_quantifier (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = has_the_quantifier X
        | has_the_quantifier _ = false

      fun swap_the_quantifier ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (N,Ty,_) =>
              if name = (N,Ty) then Conv.all_conv ctm
              else (swap_the_quantifier then_conv Conv.rewr_conv @{thm' all_comm[folded atomize_eq]}) ctm
           | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
              (swap_the_quantifier then_conv Conv.rewr_conv @{thm' HOL.all_simps(6)[folded atomize_eq, symmetric]}) ctm
           | _ => raise CTERM ("Phi_Conv.swap_the_quantifier", [ctm])

      val rule0 = @{thm' HOL.simp_thms(35)[folded atomize_eq, symmetric]}
               |> Thm.instantiate (TVars.make [((("b",0),\<^sort>\<open>type\<close>),cTy)], Vars.empty)
      val P = Var (("P",0),\<^Type>\<open>bool\<close>)
      val prop = \<^Const>\<open>Pure.eq \<^Type>\<open>bool\<close>\<close> $ P $ (\<^Const>\<open>HOL.All Ty\<close> $ Abs (Name,Ty,P))
      val rule = Thm.renamed_prop prop rule0

      fun swap_the_quantifier_or_wear_the_hat ctm =
        if has_the_quantifier (Thm.term_of ctm)
        then swap_the_quantifier ctm
        else Conv.rewr_conv rule ctm (*wear a hat*)

      fun zip ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
                HOLogic.conj_conv zip zip ctm
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ XX)
                                            $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
                (case XX of Abs (N,Ty,_) =>
                    if name = (N,Ty) then HOLogic.conj_conv Conv.all_conv zip ctm
                    else (Conv.arg1_conv swap_the_quantifier_or_wear_the_hat then_conv zip) ctm
                  | _ => (Conv.arg1_conv (Conv.arg_conv Phi_Conv.inverse_eta_conv) then_conv zip) ctm)
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
                (Conv.arg1_conv swap_the_quantifier_or_wear_the_hat then_conv zip) ctm
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X1)
                                            $ (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X2) =>
               (case X1 of Abs (Na,Tya,_) =>
                 (case X2 of Abs (Nb,Tyb,_) =>
                      if name <> (Na,Tya)
                      then (Conv.arg1_conv swap_the_quantifier_or_wear_the_hat then_conv zip) ctm
                      else if name <> (Nb,Tyb)
                      then (Conv.arg_conv swap_the_quantifier_or_wear_the_hat then_conv zip) ctm
                      else Conv.rewr_conv @{thm' all_conj_distrib[folded atomize_eq, symmetric]} ctm
                    | _ => (Conv.arg_conv (Conv.arg_conv Phi_Conv.inverse_eta_conv) then_conv zip) ctm)
                 | _ => (Conv.arg1_conv (Conv.arg_conv Phi_Conv.inverse_eta_conv) then_conv zip) ctm)
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ Y =>
              ((case X of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ => Conv.all_conv
                        | _ => Conv.arg1_conv swap_the_quantifier_or_wear_the_hat) then_conv
               (case Y of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ => Conv.all_conv
                        | _ => Conv.arg_conv  swap_the_quantifier_or_wear_the_hat) then_conv
               zip) ctm
           | _ => raise CTERM ("Phi_Conv.zip_Alls__same_name", [ctm])

   in zip
  end

fun choose_zip_All_quantifier tm =
  let fun collect_quantifiers_one (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (N,Ty,X)) =
              (N,Ty) :: collect_quantifiers_one X
        | collect_quantifiers_one (Const(\<^const_name>\<open>HOL.All\<close>, _) $ X) = collect_quantifiers_one X
        | collect_quantifiers_one (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ X) = collect_quantifiers_one X
        | collect_quantifiers_one (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) =
            let val La = collect_quantifiers_one A
                val Lb = collect_quantifiers_one B
             in if length La >= length Lb then La else Lb
            end
        | collect_quantifiers_one _ = []
      fun collect_quantifiers (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ A $ B) =
            collect_quantifiers A @ collect_quantifiers B
        | collect_quantifiers X = [collect_quantifiers_one X]
      val quantifiers = collect_quantifiers tm
      fun is_leader quantifier = forall (fn (h::L) => h = quantifier orelse not (member (op =) L quantifier)
                                          | [] => true) quantifiers
   in get_first (fn [] => NONE
                  | (h::_) => if is_leader h then SOME h else NONE) quantifiers
  end

fun zip_Alls__same_quantifier ctxt ctm =
  case choose_zip_All_quantifier (Thm.term_of ctm)
    of NONE => raise CTERM ("zip_Alls__same_quantifier", [ctm])
     | SOME (Name,Ty) => zip_Alls__same_quantifier' (Name, Thm.ctyp_of ctxt Ty)
*)

(*
fun zip_All_conj_recursively ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
        HOLogic.All_conv (zip_All_conj_recursively o snd) ctxt ctm
     | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
        HOLogic.imp_conv Conv.all_conv (zip_All_conj_recursively ctxt) ctm
     | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ _ => let
            fun has_leading_All (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ Y) =
                  has_leading_All X andalso has_leading_All Y
              | has_leading_All (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) = true
              | has_leading_All _ = false
            fun has_leading_imp (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ Y) =
                  has_leading_imp X andalso has_leading_imp Y
              | has_leading_imp (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) = true
              | has_leading_imp _ = false
            val term = Thm.cterm_of ctm
            fun parse (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ X $ _) = parse X
              | parse (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) =
                  zip_Alls then_conv zip_All_conj_recursively ctxt
              | parse (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) =
                  zip_conjs then_conv zip_All_conj_recursively ctxt
              | parse _ = Conv.all_conv
         in if has_leading_All term then (zip_Alls__same_quantifier ctxt)
        end
     | _ => Conv.all_conv ctm
*)

(*requires beta eta normalized*)
fun gen_move_Ex_inside_All (Ex_name, rule) ctxt ctm =
  let fun err () = raise CTERM ("move_Ex_inside_All", [ctm])
      val _ = case Thm.term_of ctm of Const(Ex_name', \<^Type>\<open>fun \<^Type>\<open>fun \<^Type>\<open>fun _ _\<close> _\<close> _\<close>) $ _ =>
                     if Ex_name' = Ex_name then () else err ()
                 | _ => err ()
      val _ = case Thm.term_of ctm
                of _ $ Abs (_, _, Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) => ()
                 | _ => ()
      val cTy = Thm.ctyp_of_cterm (fst (Thm.dest_comb ctm)) (*the type of the Ex binder, (f \<Rightarrow> _) \<Rightarrow> _*)
             |> Thm.dest_ctyp0 |> Thm.dest_ctyp0 (*the type of the f*)
             |> Thm.dest_ctyp0 (*the type of the universally quantified variable*)

      val rule_of_hat = @{thm' HOL.simp_thms(35)[folded atomize_eq, symmetric]}
                     |> Thm.instantiate (TVars.make [((("'b",0),\<^sort>\<open>type\<close>),cTy)], Vars.empty)
      val wear_hat = Conv.rewr_conv rule_of_hat

      datatype ret = RFound of int | RNot_Occur
      exception Not_Occur
      exception Found of int
      exception Inconsistent

      fun find_All (lev, _) (Bound i $ Bound j) =
            if i = lev then RFound (lev - j) else RNot_Occur
        | find_All (lev, bounds) (Free (Ni, _) $ Bound j) =
            let val i = find_index (fn N => N = Ni) bounds
             in if i = lev then RFound (lev - j) else RNot_Occur 
            end
        | find_All (lev, bounds) (Free (Ni, _) $ Free (Nj, _)) =
            let val i = find_index (fn N => N = Ni) bounds
                val j = find_index (fn N => N = Nj) bounds
             in if i = lev then RFound (lev - j) else RNot_Occur 
            end
        | find_All lev (Const(\<^const_name>\<open>All\<close>, _) $ X) =
            find_All lev (case X of Abs _ => X
                                  | _ => Abs ("x", dummyT, Term.incr_boundvars 1 X $ Bound 0))
        | find_All (lev, bounds) (Abs (_, _, X)) = find_All (lev + 1, "" :: bounds) X
        | find_All lev (X $ Y) =
           (case (find_All lev X, find_All lev Y)
              of (RFound i, RFound j) => if i = j then RFound i else raise Inconsistent
               | (RFound i, RNot_Occur) => RFound i
               | (RNot_Occur, RFound i) => RFound i
               | (RNot_Occur, RNot_Occur) => RNot_Occur)
        | find_All _ _ = RNot_Occur

      datatype ret3 = TFound of int | TNot_Occur | TConv of thm
      fun try3 C ctm = TConv (C ctm) handle Not_Occur => TNot_Occur
                                          | Found i => TFound i

      fun move_All (lev,bounds) ctxt ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>All\<close>, _) $ _ =>
               (*((HOLogic.All_conv (fn (cv, ctxt) =>
                            move_All (lev+1, Term.term_name (Thm.term_of cv) :: bounds) ctxt) ctxt
                         then_conv Conv.rewr_conv @{thm' all_comm[folded atomize_eq]}) ctm
                        handle Found i => if i = lev+1 then Conv.all_conv ctm else raise Found i)*)

                (case try (sink_All_over_conjs ctxt) ctm
                   of SOME th => (K th then_conv move_All (lev,bounds) ctxt) ctm
                    | NONE => (
                        (HOLogic.All_conv (fn (cv, ctxt) =>
                            move_All (lev+1, Term.term_name (Thm.term_of cv) :: bounds) ctxt) ctxt
                         then_conv Conv.rewr_conv @{thm' all_comm[folded atomize_eq]}) ctm
                        handle Found i => if i = lev+1 then Conv.all_conv ctm else raise Found i))
                
           | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ X $ Y =>
                (case find_All (lev,bounds) X
                   of RFound i => (
                        case find_All (lev,bounds) Y
                          of RFound j => if i = j then raise Found i else raise Inconsistent
                           | RNot_Occur => raise Found i)
                    | RNot_Occur =>
                        (Conv.arg_conv (move_All (lev,bounds) ctxt) then_conv
                         Conv.rewr_conv @{thm' HOL.all_simps(6)[folded atomize_eq, symmetric]}) ctm)
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ Const(\<^const_name>\<open>True\<close>, _) $ _ =>
                (Conv.rewr_conv @{thm' HOL.simp_thms(22)[folded atomize_eq]} then_conv
                 move_All (lev,bounds) ctxt) ctm
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ Const(\<^const_name>\<open>True\<close>, _) =>
                (Conv.rewr_conv @{thm' HOL.simp_thms(21)[folded atomize_eq]} then_conv
                 move_All (lev,bounds) ctxt) ctm
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
                let fun conj_conv ctm =
                     (case (try3 (move_All (lev,bounds) ctxt) (Thm.dest_arg1 ctm),
                            try3 (move_All (lev,bounds) ctxt) (Thm.dest_arg ctm))
                        of (TFound i, TFound j) => if i = j then raise Found i else raise Inconsistent
                         | (TFound i, TNot_Occur) => raise Found i
                         | (TNot_Occur, TFound i) => raise Found i
                         | (TFound _, _) => raise Inconsistent
                         | (_, TFound _) => raise Inconsistent
                         | (TConv th1, TConv th2) => HOLogic.conj_conv (K th1) (K th2) ctm
                         | (TConv th1, TNot_Occur) => HOLogic.conj_conv (K th1) wear_hat ctm
                         | (TNot_Occur, TConv th2) => HOLogic.conj_conv wear_hat (K th2) ctm
                         | (TNot_Occur, TNot_Occur) => raise Not_Occur)
                 in (conj_conv then_conv
                     Conv.rewr_conv @{thm' all_conj_distrib[folded atomize_eq, symmetric]}) ctm
                end
           | _ => (case find_All (lev,bounds) (Thm.term_of ctm)
                     of RFound i => raise Found i
                      | RNot_Occur => raise Not_Occur)

      fun move_All_top (cv,ctxt) ctm =
        move_All (0,[Term.term_name (Thm.term_of cv)]) ctxt ctm

      fun the_move ctm =
        case Thm.term_of ctm
          of Const(Ex_name', _) $ (Abs(_, _, Const(\<^const_name>\<open>All\<close>, _) $ _)) =>
              let val _ = if Ex_name = Ex_name' then () else raise CTERM ("move_Ex_inside_All", [])
                  val (Ex, ctm1) = Thm.dest_comb ctm
                  val ( f, ctm2) = Thm.dest_abs_global ctm1
                  val (Al, ctm3) = Thm.dest_comb ctm2
                  val ( x, body) = Thm.dest_abs_global ctm3
                  val fx = Thm.apply f x
                  val Q = Thm.lambda x (Thm.lambda fx body)
                  val rule = Drule.infer_instantiate ctxt [(("Q",0),Q)] rule
               in Conv.rewr_conv rule ctm
              end
           | _ => error "BUG wXYN5fcXRhuYi/3CGR+zVQ" (*the previous move_All_top is not finished.*)

   in (Phi_Conv.quant_conv Ex_name move_All_top ctxt then_conv
       the_move) ctm
   handle Found _   => raise CTERM ("move_Ex_inside_All: fail to move the universal quantification to the top", [ctm])
        | Not_Occur => raise CTERM ("move_Ex_inside_All: the quantified variable does not occur at all", [ctm])
        | Inconsistent => raise CTERM ("move_Ex_inside_All: the quantified variable is applied to different terms", [ctm])
        | CTERM (msg, ctm) => (warning ("gen_move_Ex_inside_All fails\n" ^ msg);
                               raise CTERM (msg, ctm))
  end

val move_Ex_inside_All = gen_move_Ex_inside_All
      (\<^const_name>\<open>Ex\<close>, @{thm' choice_iff[folded atomize_eq, symmetric]})
val move_sp_Ex_inside_All = gen_move_Ex_inside_All
      (\<^const_name>\<open>special_Ex\<close>, @{thm' choice_iff[folded atomize_eq special_Ex_def, symmetric]})

fun move_Ex_inside_All_recursive C ctxt ctm =
  (move_Ex_inside_All ctxt then_conv
   hol_all_conv (move_Ex_inside_All_recursive C o snd) ctxt) ctm
  handle CTERM _ => C ctxt ctm

fun move_sp_Ex_inside_All_recursive C ctxt ctm =
  (move_sp_Ex_inside_All ctxt then_conv
   hol_all_conv (move_sp_Ex_inside_All_recursive C o snd) ctxt) ctm
  handle CTERM _ => C ctxt ctm

val move_Ex_downto_Disj = Conv.rewr_conv @{thm' HOL.ex_disj_distrib[folded atomize_eq]}
val move_sp_Ex_downto_Disj = Conv.rewr_conv @{thm' HOL.ex_disj_distrib[folded atomize_eq special_Ex_def]}

fun gen_move_Ex_downto_Disj_recursive move_Ex_downto_Disj =
let fun move_Ex_downto_Disj_recursive C ctm =
      (move_Ex_downto_Disj then_conv (fn ctm =>
         case Thm.term_of ctm
           of \<^Const>\<open>HOL.disj\<close> $ _ $ _ =>
                Conv.combination_conv (Conv.arg_conv (move_Ex_downto_Disj_recursive C))
                                      (move_Ex_downto_Disj_recursive C) ctm
            | _ => error "BUG MOPPI5TrSk6+fBN7oHwPbQ"
       )) ctm
      handle CTERM _ => C ctm
 in move_Ex_downto_Disj_recursive
end

val move_Ex_downto_Disj_recursive = gen_move_Ex_downto_Disj_recursive move_Ex_downto_Disj
val move_sp_Ex_downto_Disj_recursive = gen_move_Ex_downto_Disj_recursive move_sp_Ex_downto_Disj




fun gen_move_Ex_inside (ex_name, mv_all, mv_disj, mv_over_conj, rule_mv_imp, rm_trivial, swap_quant,
                        swap_ex, swap_sp_ex) C ctxt =
  let fun open_ex C ctm =
        case Thm.term_of ctm
          of Const(N, _) $ X =>
               if N = ex_name
               then (case X of Abs (_, _, X) => C X ctm
                             | _ => (Conv.arg_conv Phi_Conv.inverse_eta_conv then_conv
                                     open_ex C) ctm )
               else raise CTERM ("Phi_Conv.move_Ex_inside_exhaustively", [ctm])
           | _ =>   raise CTERM ("Phi_Conv.move_Ex_inside_exhaustively", [ctm])

      fun trivial_case_chk C =
        open_ex (fn tm => if bound_occurs 0 tm then C else Conv.rewr_conv rm_trivial)

      fun conv ctxt ctm = open_ex (fn tm => fn ctm =>
        case tm
          of Const(\<^const_name>\<open>HOL.All\<close>, _) $ _ =>
              (Phi_Conv.quant_conv ex_name (sink_All_over_conjs o snd) ctxt
               then_conv conv ctxt) ctm
           | Const(\<^const_name>\<open>HOL.disj\<close>, _) $ _ $ _ => mv_disj (conv ctxt) ctm 
           | Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _ =>
              if bound_occurs 0 tm
              then (case try (sink_quantifier_over_conjs (ex_name, mv_over_conj, rm_trivial, swap_quant) ctxt) ctm
                      of SOME th => (K th then_conv
                                     Conv.arg_conv (
                                       Phi_Conv.quant_conv ex_name (K zip_conjs_recursively) ctxt then_conv
                                       conv ctxt)) ctm
                       | NONE => (Phi_Conv.quant_conv ex_name (K zip_conjs_recursively1) ctxt then_conv
                                  conv ctxt) ctm)
              else Conv.rewr_conv rm_trivial ctm
           | Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _ =>
              (Conv.rewr_conv rule_mv_imp then_conv
               Conv.arg_conv (conv ctxt)) ctm
           | Const(\<^const_name>\<open>HOL.Ex\<close>, _) $ _ =>
              (Conv.rewr_conv swap_ex then_conv
               Phi_Conv.quant_conv \<^const_name>\<open>HOL.Ex\<close> (conv o snd) ctxt) ctm
           | Const(\<^const_name>\<open>special_Ex\<close>, _) $ _ =>
              (Conv.rewr_conv swap_sp_ex then_conv
               Phi_Conv.quant_conv \<^const_name>\<open>special_Ex\<close> (conv o snd) ctxt) ctm
           | _ => C ctxt ctm
        ) ctm
        handle CTERM _ =>
          (mv_all ctxt then_conv hol_all_conv (conv o snd) ctxt
           else_conv C ctxt) ctm
        
   in trivial_case_chk (
        Phi_Conv.quant_conv ex_name (fn (_, ctxt) =>
          Raw_Simplifier.rewrite ctxt true @{thms' HOL.simp_thms[folded atomize_eq]}) ctxt
        then_conv conv ctxt
      )
  end

val move_Ex_inside = gen_move_Ex_inside
      (\<^const_name>\<open>Ex\<close>, move_Ex_inside_All, move_Ex_downto_Disj_recursive,
       @{thm' HOL.ex_simps(2)[folded atomize_eq]},
       @{thm' HOL.ex_simps(6)[folded atomize_eq]},
       @{thm' HOL.simp_thms(36)[folded atomize_eq]},
       @{thm' HOL.ex_comm[folded atomize_eq]},
       @{thm' HOL.ex_comm[folded atomize_eq]},
       @{thm' sp_ex_ex_comm[symmetric]})

val move_sp_Ex_inside = gen_move_Ex_inside
      (\<^const_name>\<open>special_Ex\<close>,
       move_sp_Ex_inside_All,
       move_sp_Ex_downto_Disj_recursive,
       @{thm' HOL.ex_simps(2)[folded special_Ex_def atomize_eq]},
       @{thm' HOL.ex_simps(6)[folded special_Ex_def atomize_eq]},
       @{thm' HOL.simp_thms(36)[folded special_Ex_def atomize_eq]},
       @{thm' HOL.ex_comm[folded special_Ex_def atomize_eq]},
       @{thm' sp_ex_ex_comm},
       @{thm' HOL.ex_comm[folded special_Ex_def atomize_eq]})

end
