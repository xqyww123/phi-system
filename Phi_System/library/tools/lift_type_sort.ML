signature PHI_HELP = sig
include PHI_HELP

(*Find the most general 'good' instantiation of the given type to meet the given sort.
  Note, a 'good' most general instantiation means the result may not be the direct intersection
  of the sorts. Instead, what is expected is a smaller refinement having more assumptions and better
  algebraic properties.
  For example, the direct intersection {sep_magma, one} is usually unexpected but the smaller
  \<open>sep_magma_1\<close> is preferred.

  The file maintains a database giving a reduction to such better refinements.

  The operations prefixed by 'raw' will not apply such 'reduction to goodness'.
*)
  val raw_lift_type_sort : theory -> typ * sort -> Type.tyenv -> Type.tyenv
  val raw_lift_types_sort : theory -> (typ * sort) list -> typ TVars.table

  val lift_type_sort : theory -> typ * sort -> Type.tyenv -> Type.tyenv
  val lift_types_sort : theory -> (typ * sort) list -> typ TVars.table

  val add_expected_sort_red : (class (*A*) * class (*B*) * sort (*C*)) list -> theory -> theory
        (*register that C is the expected stronger intersection of A and B. *)

  (*lifts the sorts of the types to their good refinements.*)
  val refine_sorts_of_typs : theory -> typ list -> typ TVars.table
  val refine_sorts_of_tms  : theory -> term list -> typ TVars.table
  val refine_sorts_of_typ : theory -> typ -> typ
  val refine_sorts_of_tm  : theory -> term -> term

end

structure Phi_Help : PHI_HELP = struct
open Phi_Help

structure Sort_Expection_Red = Theory_Data (
  type T = sort (*C*) Symreltab.table (*key: A and B*)
  val empty = Symreltab.empty
  val merge = Symreltab.join (K (uncurry (inter (op =))))
)

fun add_expected_sort_red ABC thy =
  Sort_Expection_Red.map (
    fold (fn (A,B,C) =>
      if A <= B
      then Symreltab.map_default ((A,B), []) (curry (Sign.inter_sort thy) C)
      else Symreltab.map_default ((B,A), []) (curry (Sign.inter_sort thy) C)
    (*Symtab.map_default (B,[]) (AList.map_default (op =) (A,[]) (curry (Sign.inter_sort thy) C)) #>
      Symtab.map_default (A,[]) (AList.map_default (op =) (B,[]) (curry (Sign.inter_sort thy) C)) *)
    ) ABC
  ) thy

fun get_refined_sort_of_lifting_S thy =
  let val tsig = Sign.tsig_of thy
      val reds = Sort_Expection_Red.get thy
   in fn (A,B) =>
      Symreltab.fold (fn ((A',B'),C') => fn B =>
        if Type.subsort tsig (A,[A']) andalso Type.subsort tsig (B,[B']) then Type.inter_sort tsig (C', B)
        else if Type.subsort tsig (A,[B']) andalso Type.subsort tsig (B,[A']) then Type.inter_sort tsig (C', B)
        else B
      ) reds B
  end

fun get_refined_sort_of_lifting_T thy =
  let val tsig = Sign.tsig_of thy
      val reds = Sort_Expection_Red.get thy
   in fn (A,B) =>
      Symreltab.fold (fn ((A',B'),C') => fn B =>
        if Type.of_sort tsig (A,[A']) andalso Type.subsort tsig (B,[B']) then Type.inter_sort tsig (C', B)
        else if Type.of_sort tsig (A,[B']) andalso Type.subsort tsig (B,[A']) then Type.inter_sort tsig (C', B)
        else B
      ) reds B
  end

fun gen_lift_type_sort thy (ty,sort) (env00,idx) =
  if Sign.of_sort thy (ty, sort)
  then (env00,idx)
  else let val var_a = TVar(("a", idx+1), sort)
           val (env'1, idx'1) = Sign.typ_unify thy (ty, var_a) (env00, idx+1)
           val target = Envir.norm_type env'1 var_a
        in (Sign.typ_match thy (ty, target) env00, idx'1)
       end
       handle Type.TUNIFY => raise TYPE ("fail to unify the type to separation magma", [ty], [])

fun raw_lift_type_sort thy (ty,sort) env00 =
  let val idx = Vartab.fold (fn ((_,i1), (_,ty)) => Term.maxidx_typ ty o curry Int.max i1) env00
                            (Term.maxidx_of_typ ty) + 1
   in fst (gen_lift_type_sort thy (ty,sort) (env00, idx))
  end

fun lift_type_sort thy (ty,sort) =
      raw_lift_type_sort thy (ty, get_refined_sort_of_lifting_T thy (ty, sort))

fun raw_lift_types_sort thy ty_sorts =
  let val idx = Term.maxidx_of_typs (map fst ty_sorts)
   in fold (fn (T,S) => fn (env,idx) =>
        gen_lift_type_sort thy (Envir.subst_type env T, S) (env,idx)
      ) ty_sorts (Vartab.empty, idx)
        |> fst
        |> subst_tyenv
  end

fun lift_types_sort thy ty_sorts =
      raw_lift_types_sort thy (map (fn (ty,sort) =>
          (ty, get_refined_sort_of_lifting_T thy (ty, sort))) ty_sorts)

(** Refine types to their good refinements **)

fun refined_sort_of thy =
  let val tsig = Sign.tsig_of thy
      val reds = Sort_Expection_Red.get thy
   in fn S =>
      Symreltab.fold (fn ((A',B'),C') => fn S =>
        if Type.subsort tsig (S,[A']) andalso Type.subsort tsig (S,[B'])
        then Type.inter_sort tsig (C', S)
        else S
      ) reds S
  end

fun refine_sorts_of_vars thy vars =
  let val rsort = refined_sort_of thy
      val tsig = Sign.tsig_of thy
   in TVars.build (fold (fn (N,S) =>
        let val S' = rsort S
         in if Type.eq_sort tsig (S,S') then I
            else TVars.add ((N,S), TVar(N, S'))
        end) vars)
  end

fun refine_sorts_of_typs thy typs =
  refine_sorts_of_vars thy (fold Term.add_tvarsT typs [])

fun refine_sorts_of_tms thy tms =
  refine_sorts_of_vars thy (fold Term.add_tvars tms [])

fun refine_sorts_of_typ thy ty =
  let val inst = refine_sorts_of_typs thy [ty]
   in Term_Subst.instantiateT inst ty
  end

fun refine_sorts_of_tm thy tm =
  let val inst = refine_sorts_of_tms thy [tm]
   in Term_Subst.instantiate (inst, Vars.empty) tm
  end

(** Preset Reductions **)

val _ = Theory.setup (
  add_expected_sort_red [
    (\<^class>\<open>sep_disj\<close>, \<^class>\<open>times\<close>, \<^sort>\<open>sep_magma\<close>),
    (\<^class>\<open>sep_magma\<close>, \<^class>\<open>one\<close>, \<^sort>\<open>sep_magma_1\<close>),
    (\<^class>\<open>sep_magma\<close>, \<^class>\<open>share\<close>, \<^sort>\<open>share_nun_semimodule\<close>),
    (\<^class>\<open>share_nun_semimodule\<close>, \<^class>\<open>one\<close>, \<^sort>\<open>share_semimodule\<close>),
    (\<^class>\<open>share\<close>, \<^class>\<open>one\<close>, \<^sort>\<open>share_one\<close>),
    (\<^class>\<open>mul_carrier\<close>, \<^class>\<open>sep_magma\<close>, \<^sort>\<open>sep_carrier\<close>),
    (\<^class>\<open>sep_carrier\<close>, \<^class>\<open>one\<close>, \<^sort>\<open>sep_carrier_1\<close>)
  ]
)

end
