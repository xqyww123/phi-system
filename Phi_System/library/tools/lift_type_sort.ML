signature PHI_HELP = sig
include PHI_HELP

(*Find the most general instantiation of the given type to meet the given sort.
  Note, given a type of sort \<open>S\<close> and the lifting target \<open>S'\<close>, the expected sort
    may not be the most general intersection of \<open>S\<close> and \<open>S'\<close>, but the really meaningful
    one which can be smaller than this, such as expecting \<open>sep_magma_1\<close> instead of
    \<open>{sep_magma, one}\<close>.

  The operations prefixed by 'raw' will not apply the above 'expected reduction',
  but others will.
*)
  val raw_lift_type_sort : theory -> typ * sort -> Type.tyenv -> Type.tyenv
  val raw_lift_types_sort : theory -> (typ * sort) list -> typ TVars.table

  val lift_type_sort : theory -> typ * sort -> Type.tyenv -> Type.tyenv
  val lift_types_sort : theory -> (typ * sort) list -> typ TVars.table

  val add_expected_sort_red : (class (*A*) * class (*B*) * sort (*C*)) list -> theory -> theory
        (*register that C is the expected stronger intersection of A and B. *)

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

fun get_expected_sort_red_S thy =
  let val tsig = Sign.tsig_of thy
      val reds = Sort_Expection_Red.get thy
   in fn (A,B) =>
      Symreltab.fold (fn ((A',B'),C') => fn B =>
        if Type.subsort tsig (A,[A']) andalso Type.subsort tsig (B,[B']) then Type.inter_sort tsig (C', B)
        else if Type.subsort tsig (A,[B']) andalso Type.subsort tsig (B,[A']) then Type.inter_sort tsig (C', B)
        else B
      ) reds B
  end

fun get_expected_sort_red_T thy =
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
      raw_lift_type_sort thy (ty, get_expected_sort_red_T thy (ty, sort))

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
          (ty, get_expected_sort_red_T thy (ty, sort))) ty_sorts)

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
