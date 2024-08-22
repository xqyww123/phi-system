(* library/syntax/procedure.ML
   Author: Qiyuan Xu

   The syntax parser for procedure specification.

It is invoked once there are anonymous values in the argument specification,
or once the return specification is not given as an explicit lambda abstraction about the return values.
For translation in argument specification, all anonymous values are replaces by a free variable
  generated automatically.
For return specification, it collects all semantic values having \<^typ>\<open>'a \<phi>arg\<close> in the spec,
  and wrap the spec by a lambda abstraction over the semantic values, using the pair encoding
  of multi-return-values (rn, ...\<^bold>, r2 \<^bold>, r1).
*)

signature PROCEDURE_SYNTAX = sig
(*
Translate a term X containing values V (including anonymous values) into (\<lambda>vs. X\<theta>),
  where vs is a tuple aggregating values V,
  \<theta> is a substitution mapping the ith value in V to the ith projection of vs.

Values of identical name are considered identical. Any anonymous value is considered unique.
*)

val val_T : typ
val val_list_T : typ

val package_values :
       string (*name of the lambda variable*)
        -> bool (*the order for scanning and collecting the values.
                  true for Right-to-Left (the canonical order);
                  false for Left-to-Right*)
        -> (term list * term option) option (*values cache.
              If you run package_values by twice in the same context (of variables) and in the same scan order,
              this argument can be set to the return of the previous run to boost the performance.
              Set it to None by default*)
        -> term
        -> term (*value assemble*) * term (*lambda abstraction*)
         * (term list * term option) (*cache*)

val package_values0 :
       string (*name of the lambda variable*)
        -> bool (*the order for scanning and collecting the values.
                  true for Right-to-Left (the canonical order);
                  false for Left-to-Right*)
        -> (term list * term option) option (*values cache.
              If you run package_values by twice in the same context (of variables) and in the same scan order,
              this argument can be set to the return of the previous run to boost the performance.
              Set it to None by default*)
        -> term
        -> term (*value assemble*) * term (*lambda abstraction*)
         * (term list * term option) (*cache*)

val translate_arg : term -> term
val translate_ret : term -> term
(* Syntax translation during parse of the post-condition,
   roughly identical to (package_values "\<r>\<e>\<t>" false).
*)

val is_argT : typ -> bool
val dest_argT : typ -> typ
val mk_argT : typ -> typ
(*val dest_arg_prodT : typ -> typ * typ
val mk_arg_prodT   : typ * typ -> typ
val mk_arg_listT  : typ list -> typ*)
val mk_arg_list   : term list * term option -> term
val mk_arg_list'  : term list -> term
val dest_arg_list : term -> term list (*arguments*) * term option (*the argument of variable length*)
val map_argT  : (typ -> typ) -> typ -> typ


datatype quantify_mode = No_Quantify | HOL_Quantify
datatype parameterize_proc = No_Parameterize | Tuple_Pack | Lambda_Apps

val set_proc_parse_mode : quantify_mode * parameterize_proc -> Context.generic -> Context.generic
val restore_proc_parse_mode : Context.generic -> Context.generic -> Context.generic
val translate_proc_arg : Context.generic -> term -> term

end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct

(*** Parser ***)

fun is_argT (Type (\<^type_name>\<open>\<phi>arg\<close>, [_])) = true
  | is_argT _ = false
fun dest_argT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])) = T
  | dest_argT T = raise TYPE("Not a \<phi>arg type", [T], [])
fun mk_argT T = \<^Type>\<open>\<phi>arg \<open>T\<close>\<close>

val val_list_T = \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close>
val val_T = \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close>

(*
fun dest_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [Type (\<^type_name>\<open>prod\<close>, [A, B])]))
      = (Type (\<^type_name>\<open>\<phi>arg\<close>, [A]), Type (\<^type_name>\<open>\<phi>arg\<close>, [B]))
  | dest_arg_prodT (Type ("dummy", [])) = (dummyT,dummyT)
  | dest_arg_prodT T = raise TYPE("Not a \<phi>arg type", [T], [])

fun mk_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T1]), Type (\<^type_name>\<open>\<phi>arg\<close>, [T2]))
      = Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_prodT (T1,T2)])
  | mk_arg_prodT (T1,T2) = raise TYPE("Not a \<phi>arg type", [T1,T2], [])

fun mk_arg_listT Ts = mk_argT (HOLogic.mk_tupleT (map dest_argT Ts))
*)

fun map_argT f (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])) = Type (\<^type_name>\<open>\<phi>arg\<close>, [f T])
  | map_argT _ T = raise TYPE("Not a \<phi>arg type", [T], [])

fun mk_arg_list' [] = \<^Const>\<open>\<phi>V_nil\<close>
  | mk_arg_list' [tm] = tm
  | mk_arg_list' (tm::tms)
      = \<^Const>\<open>\<phi>V_cons\<close> $ tm $ mk_arg_list' tms

fun mk_arg_list ([], NONE) = \<^Const>\<open>\<phi>V_nil\<close>
  | mk_arg_list ([], SOME tm) = tm
  | mk_arg_list (tm::tms, tl)
      = \<^Const>\<open>\<phi>V_cons\<close> $ tm $ mk_arg_list (tms, tl)

fun dest_arg_list tm =
  let fun dest_args (Const (\<^const_name>\<open>\<phi>V_cons\<close>, _) $ A $ B) = A :: dest_args B
        | dest_args _ = []
      fun tailof (Const (\<^const_name>\<open>\<phi>V_cons\<close>, _) $ _ $ B) = tailof B
        | tailof (Const (\<^const_name>\<open>\<phi>V_nil\<close>, _)) = NONE
        | tailof X = SOME X
   in (dest_args tm, tailof tm)
  end


(*
Syntax translation during parsing of the pre-condition is simply replacing
all anonymous values by a name \<a>\<r>\<g>i for the ith value from left to right.
*)
fun need_translate_arg (Const (\<^const_name>\<open>anonymous\<close>, _)) = true
  | need_translate_arg (Const (\<^const_syntax>\<open>anonymous\<close>, _)) = true
  | need_translate_arg (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (Const (\<^const_syntax>\<open>\<phi>Type\<close>, _) $ _ $ X) = need_translate_arg X
  | need_translate_arg (A $ B) = need_translate_arg A orelse need_translate_arg B
  | need_translate_arg (Abs (_, _, X)) = need_translate_arg X
  | need_translate_arg _ = false

fun error_varlen_once () = error "the argument of variable length can only occur once"
fun set_VARLEN NONE vl = SOME vl
  | set_VARLEN (SOME _) _ = error_varlen_once ()

fun translate_arg' meet cnt s ns ( (C1 as Const (\<^const_name>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_name>\<open>Val\<close>, _))
                                       $ Const (\<^const_name>\<open>anonymous\<close>, _)
                                       $ X2))
      = let val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (meet, cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end
  | translate_arg' meet cnt s ns ( (C1 as Const (\<^const_syntax>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_syntax>\<open>Val\<close>, _))
                                       $ Const (\<^const_syntax>\<open>anonymous\<close>, _)
                                       $ X2))
      = let val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (meet, cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end

  | translate_arg' meet cnt s ns ( (C1 as Const (\<^const_name>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_name>\<open>Vals\<close>, _))
                                       $ Const (\<^const_name>\<open>anonymouss\<close>, _)
                                       $ X2))
      = let val _ = if meet then error_varlen_once () else ()
            val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (true, cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end
  | translate_arg' meet cnt s ns ( (C1 as Const (\<^const_syntax>\<open>\<phi>Type\<close>, _))
                              $ X $ ( (C2 as Const (\<^const_syntax>\<open>Vals\<close>, _))
                                       $ Const (\<^const_syntax>\<open>anonymouss\<close>, _)
                                       $ X2))
      = let val _ = if meet then error_varlen_once () else ()
            val name = "\<a>\<r>\<g>" ^ (string_of_int (cnt+1))
         in (true, cnt+1, s, name :: ns, C1 $ X $ (C2 $ Free (name, dummyT) $ X2))
        end

  | translate_arg' meet cnt s ns (Const (\<^const_name>\<open>anonymous\<close>, _))
      = let val s' = Symbol.bump_string s
         in (meet, cnt, s', s'::ns, Free ("\<a>\<r>\<g>" ^ s, dummyT))
        end
  | translate_arg' meet cnt s ns (Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = let val s' = Symbol.bump_string s
         in (meet, cnt, s', s'::ns, Free ("\<a>\<r>\<g>" ^ s, dummyT))
        end
  | translate_arg' meet cnt s ns (Const (\<^const_name>\<open>anonymouss\<close>, _))
      = let val _ = if meet then error_varlen_once () else ()
            val s' = Symbol.bump_string s
         in (true, cnt, s', s'::ns, Free ("\<a>\<r>\<g>" ^ s, dummyT))
        end
  | translate_arg' meet cnt s ns (Const (\<^const_syntax>\<open>anonymouss\<close>, _))
      = let val _ = if meet then error_varlen_once () else ()
            val s' = Symbol.bump_string s
         in (true, cnt, s', s'::ns, Free ("\<a>\<r>\<g>" ^ s, dummyT))
        end
  | translate_arg' meet cnt s ns (A $ B)
      = (case translate_arg' meet cnt  s  ns  A of (meet, cnt',s',ns',A') =>
         case translate_arg' meet cnt' s' ns' B of (meet, cnt'',s'',ns'',B') =>
          (meet, cnt'', s'', ns'', A' $ B'))
  | translate_arg' meet cnt s ns (Abs (name,ty, X))
      = (case translate_arg' meet cnt s ns X of (meet, cnt',s',ns',X') =>
           (meet, cnt', s', ns', Abs (name,ty,X')))
  | translate_arg' meet cnt s ns X = (meet, cnt,s,ns,X)

fun translate_arg X = #5 (translate_arg' false 0 "\<a>\<r>\<g>_a" [] X)

datatype quantify_mode = No_Quantify | HOL_Quantify
datatype parameterize_proc = No_Parameterize | Tuple_Pack | Lambda_Apps

structure Proc_Parse_Ctxt = Generic_Data (
  type T = (quantify_mode * parameterize_proc) option
  val empty = NONE
  val merge = merge_options
)

fun set_proc_parse_mode mode = Proc_Parse_Ctxt.put (SOME mode)
fun restore_proc_parse_mode ctxt = Proc_Parse_Ctxt.put (Proc_Parse_Ctxt.get ctxt)

fun dest_proc_synt ((H as Const(\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, _)) $ p $ A $ R) = (H,p,A,R,Term.dummy)
  | dest_proc_synt ((H as Const(\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, _)) $ p $ A $ R) = (H,p,A,R,Term.dummy)
  | dest_proc_synt ((H as Const(\<^const_syntax>\<open>\<phi>Procedure\<close>, _)) $ p $ A $ R $ E) = (H,p,A,R,E)
  | dest_proc_synt ((H as Const(\<^const_name>\<open>\<phi>Procedure\<close>, _)) $ p $ A $ R $ E) = (H,p,A,R,E)
  | dest_proc_synt TM = raise TERM("dest_proc_synt", [TM])

fun mk_proc_synt (H,p,A,R,E) =
      case H
        of Const(\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, _) => H $ p $ A $ R
         | Const(\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, _) => H $ p $ A $ R
         | Const(\<^const_syntax>\<open>\<phi>Procedure\<close>, _) => H $ p $ A $ R $ E
         | Const(\<^const_name>\<open>\<phi>Procedure\<close>, _)   => H $ p $ A $ R $ E
         | TM => raise TERM("mk_proc_synt", [TM])

fun translate_proc_arg' (qmode, pmode) tm =
  let val (Procedure, proc, Arg, Ret, Err) = dest_proc_synt tm
      val (_, _, _, names, Arg') = translate_arg' false 0 "\<a>\<r>\<g>_a" [] Arg
      val proc' = case pmode
                    of No_Parameterize => proc
                     | Tuple_Pack => proc $ mk_arg_list' (map (fn x => Free(x,dummyT)) (rev names))
                     | Lambda_Apps => fold_rev (fn N => fn X => X $ Free(N,dummyT) ) names proc
      val base = mk_proc_synt (Procedure, proc', Arg', Ret, Err)
      val ret = case qmode
                  of No_Quantify => base
                   | HOL_Quantify => base
                                  |> subst_atomic (map_index (fn (i,name) =>
                                                        (Free(name,dummyT), Bound i)) names)
                                  |> fold (fn name => fn X =>
                                        Const(\<^const_name>\<open>HOL.All\<close>, dummyT) $ Abs (name, dummyT, X)) names
   in ret
  end

fun translate_proc_arg ctxt tm =
  let val (_, _, Arg, _, _) = dest_proc_synt tm
   in if need_translate_arg Arg
      then case Proc_Parse_Ctxt.get ctxt
             of SOME mode => translate_proc_arg' mode tm
              | NONE => error (let open Pretty 
                  (*val pretty = Context.cases Syntax.pretty_term_global Syntax.pretty_term
                    fun show mode = let val tm' = translate_proc_arg' mode tm
                                     in try (Syntax.check_term (Context.proof_of ctxt)) tm'
                                     |> Option.map (fn tm'' => item [pretty ctxt tm''])
                                    end*)
                 in string_of (
                    chunks([block (text "Short syntax of \<open>\<v>\<a>\<l> T\<close> cannot be used here, because in this context\
                                       \ I cannot determine whether should the argument values be quantified,\
                                       \ or whether should I parameterize the procedure term using the argument values."),
                            block (text "You may clarify your formula by choosing one of the potential parses shown as follows")]
                         (*@ map_filter I
                             [show (No_Quantify, No_Parameterize),
                              show (HOL_Quantify, No_Parameterize),
                              show (No_Quantify, Tuple_Pack),
                              show (No_Quantify, Lambda_Apps),
                              show (HOL_Quantify, Lambda_Apps)]*) )
                 ) end)
      else tm
  end




(* fun mk_arg_prodT []  = \<^typ>\<open>unit \<phi>arg\<close>
  | mk_arg_prodT (Type ("dummy", []) :: _) = dummyT
  | mk_arg_prodT [T] = T
  | mk_arg_prodT (Type (\<^type_name>\<open>\<phi>arg\<close>, [T])::Ts) =
      (case mk_arg_prodT Ts of Type (\<^type_name>\<open>\<phi>arg\<close>, [Ts']) =>
          Type (\<^type_name>\<open>\<phi>arg\<close>, [HOLogic.mk_arg_prodT (T,Ts')]))
  | mk_arg_prodT T = raise TYPE("bug #g4389h", T, []) *)

fun nth_project 0 term = \<^Const>\<open>\<phi>V_hd\<close> $ term
  | nth_project i term = nth_project (i-1) (\<^Const>\<open>\<phi>V_tl\<close> $ term)
fun last_prj 0 term = term
  | last_prj i term = last_prj (i-1) (\<^Const>\<open>\<phi>V_tl\<close> $ term)


fun gen_collect_and_map R2L (*whether in an order from right to left or reversely*) =
let

fun collect_vals (Vs,VL) (v as Const (\<^const_name>\<open>anonymous\<close>, _)) = (v::Vs,VL)
  | collect_vals (Vs,VL) (v as Const (\<^const_syntax>\<open>anonymous\<close>, _)) = (v::Vs,VL)
  | collect_vals (Vs,VL) (v as Const (\<^const_name>\<open>anonymouss\<close>, _)) = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (v as Const (\<^const_syntax>\<open>anonymouss\<close>, _)) = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (v as Const (\<^const_name>\<open>\<phi>V_hd\<close>, _) $ _) = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (v as Const (\<^const_syntax>\<open>\<phi>V_hd\<close>, _) $ _) = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (v as Const (\<^const_name>\<open>\<phi>V_tl\<close>, _) $ _) = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (v as Const (\<^const_syntax>\<open>\<phi>V_tl\<close>, _) $ _) = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (v as Free (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close>)) = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (v as Free (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close>)) = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (v as Var (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close>)) = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (v as Var (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close>)) = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (v as Const ("_type_constraint_", \<^Type>\<open>fun \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close> _\<close>) $ _)
      = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (v as Const ("_type_constraint_", \<^Type>\<open>fun \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close> _\<close>) $ _)
      = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ Const(\<^type_syntax>\<open>VAL\<close>, _)))
      = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (v as Const ("_constrain", _) $ _ $ (Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $
                                  (Const(\<^type_syntax>\<open>list\<close>, _) $ Const(\<^type_syntax>\<open>VAL\<close>, _)) ))
      = (Vs, set_VARLEN VL v)
(*| collect_vals (Vs,VL) (Const (\<^const_name>\<open>Val\<close>, _) $ (v as Const (\<^const_name>\<open>anonymous\<close>, _)))
      = (v::Vs, VL)
  | collect_vals (Vs,VL) (Const (\<^const_syntax>\<open>Val\<close>, _) $ (v as Const (\<^const_syntax>\<open>anonymous\<close>, _)))
      = (v::Vs, VL)
  | collect_vals (Vs,VL) (Const (\<^const_name>\<open>Vals\<close>, _) $ (v as Const (\<^const_name>\<open>anonymouss\<close>, _)))
      = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (Const (\<^const_syntax>\<open>Vals\<close>, _) $ (v as Const (\<^const_syntax>\<open>anonymouss\<close>, _)))
      = (Vs, set_VARLEN VL v)*)
  | collect_vals (Vs,VL) (Const (\<^const_name>\<open>Val\<close>, _) $ v) = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (Const (\<^const_syntax>\<open>Val\<close>, _) $ v) = (insert (op = ) v Vs, VL)
  | collect_vals (Vs,VL) (Const (\<^const_name>\<open>Vals\<close>, _) $ v) = (Vs, set_VARLEN VL v)
  | collect_vals (Vs,VL) (Const (\<^const_syntax>\<open>Vals\<close>, _) $ v) = (Vs, set_VARLEN VL v)
  | collect_vals Vs (Const(\<^const_name>\<open>Subjection\<close>, _) $ A $ _) = collect_vals Vs A
  | collect_vals Vs (Const (\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ X) = collect_vals Vs X
  | collect_vals Vs (Abs (_,_,X)) = collect_vals Vs X
  | collect_vals Vs (X $ Y) =
      if R2L
      then collect_vals (collect_vals Vs X) Y
      else collect_vals (collect_vals Vs Y) X
  | collect_vals Vs _ = Vs

fun jth_index_of_annoy j ans (Const (\<^const_name>\<open>anonymous\<close>, _) :: L)
      = if j = 0 then ans else jth_index_of_annoy (j-1) (ans+1) L
  | jth_index_of_annoy j ans (Const (\<^const_syntax>\<open>anonymous\<close>, _) :: L)
      = if j = 0 then ans else jth_index_of_annoy (j-1) (ans+1) L
  | jth_index_of_annoy j ans (_ :: L)
      = jth_index_of_annoy j (ans+1) L
  | jth_index_of_annoy _ _ [] = raise Fail "Procedure_Syntax: Insufficient values"

fun mk_projection VS i v =
  let val ret = find_index (fn x => x = v) VS
   in if ret = ~1 then v
      else nth_project ret (Bound i)
  end

fun map_ret' VS term =
  let val j = Unsynchronized.ref 0
      fun incr () = let val ret = !j in j := ret + 1; ret end

fun map_ret i VS (Const (\<^const_name>\<open>anonymous\<close>, _))
      = SOME (nth_project (jth_index_of_annoy (incr()) 0 VS) (Bound i))
  | map_ret i VS (Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = SOME (nth_project (jth_index_of_annoy (incr()) 0 VS) (Bound i))
  | map_ret i VS (Const (\<^const_name>\<open>anonymouss\<close>, _))
      = SOME (last_prj (length VS) (Bound i))
  | map_ret i VS (Const (\<^const_syntax>\<open>anonymouss\<close>, _))
      = SOME (last_prj (length VS) (Bound i))

  | map_ret i VS (v as Const (\<^const_name>\<open>\<phi>V_hd\<close>, _) $ _)
      = SOME (mk_projection VS i v)
  | map_ret i VS (v as Const (\<^const_syntax>\<open>\<phi>V_hd\<close>, _) $ _)
      = SOME (mk_projection VS i v)
  | map_ret i VS (v as Const (\<^const_name>\<open>\<phi>V_tl\<close>, _) $ _)
      = SOME (mk_projection VS i v)
  | map_ret i VS (v as Const (\<^const_syntax>\<open>\<phi>V_tl\<close>, _) $ _)
      = SOME (mk_projection VS i v)

  | map_ret i VS (v as Free (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close>))
      = SOME (mk_projection VS i v)
  | map_ret i VS (v as Var (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close>))
      = SOME (mk_projection VS i v)
  | map_ret i VS (Free (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close>))
      = SOME (last_prj (length VS) (Bound i))
  | map_ret i VS (Var (_, \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close>))
      = SOME (last_prj (length VS) (Bound i))

  | map_ret i VS (v as Const ("_type_constraint_", \<^Type>\<open>fun \<^Type>\<open>\<phi>arg \<^Type>\<open>VAL\<close>\<close> _\<close>) $ _)
      = SOME (mk_projection VS i v)
  | map_ret i VS (Const ("_type_constraint_", \<^Type>\<open>fun \<^Type>\<open>\<phi>arg \<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close> _\<close>) $ _)
      = SOME (last_prj (length VS) (Bound i))
  | map_ret i VS (v as Const ("_constrain", _) $ _ $ (
          Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ Const(\<^type_syntax>\<open>VAL\<close>, _)))
      = SOME (mk_projection VS i v)
  | map_ret i VS (Const ("_constrain", _) $ _ $ (
          Const (\<^type_syntax>\<open>\<phi>arg\<close>, _) $ (Const (\<^type_syntax>\<open>list\<close>, _) $ Const(\<^type_syntax>\<open>VAL\<close>, _))))
      = SOME (last_prj (length VS) (Bound i))

  | map_ret i VS ((h as Const (\<^const_name>\<open>Val\<close>, _)) $ Const (\<^const_name>\<open>anonymous\<close>, _))
      = SOME (h $ nth_project (jth_index_of_annoy (incr()) 0 VS) (Bound i))
  | map_ret i VS ((h as Const (\<^const_syntax>\<open>Val\<close>, _)) $ Const (\<^const_syntax>\<open>anonymous\<close>, _))
      = SOME (h $ nth_project (jth_index_of_annoy (incr()) 0 VS) (Bound i))
  | map_ret i VS ((h as Const (\<^const_name>\<open>Vals\<close>, _)) $ Const (\<^const_name>\<open>anonymouss\<close>, _))
      = SOME (h $ last_prj (length VS) (Bound i))
  | map_ret i VS ((h as Const (\<^const_syntax>\<open>Vals\<close>, _)) $ Const (\<^const_syntax>\<open>anonymouss\<close>, _))
      = SOME (h $ last_prj (length VS) (Bound i))

  | map_ret i VS ((h as Const (\<^const_name>\<open>Val\<close>, _)) $ v)
      = SOME (h $ mk_projection VS i v)
  | map_ret i VS ((h as Const (\<^const_syntax>\<open>Val\<close>, _)) $ v)
      = SOME (h $ mk_projection VS i v)
  | map_ret i VS ((h as Const (\<^const_name>\<open>Vals\<close>, _)) $ _)
      = SOME (h $ last_prj (length VS) (Bound i))
  | map_ret i VS ((h as Const (\<^const_syntax>\<open>Vals\<close>, _)) $ _)
      = SOME (h $ last_prj (length VS) (Bound i))

  | map_ret i VS ((h as Const (\<^const_name>\<open>Subjection\<close>, _)) $ A $ B)
      = map_ret i VS A |> Option.map (fn A' => h $ A' $ B)
  | map_ret i VS ((h as Const (\<^const_name>\<open>\<phi>Type\<close>, _)) $ A $ B)
      = map_ret i VS B |> Option.map (fn B' => (h $ A $ B'))
  | map_ret i VS (Abs (name,ty,X))
      = map_ret (i+1) VS X |> Option.map (fn X' => Abs (name, ty,X'))
  | map_ret i VS (X $ Y)
      = (case if R2L
              then let val Y' =  map_ret i VS Y
                       val X' =  map_ret i VS X
                    in (X',Y')
                   end
              else let val X' =  map_ret i VS X
                       val Y' =  map_ret i VS Y
                    in (X',Y')
                   end
           of (NONE,NONE) => NONE
            | (X',Y') => SOME (the_default X X' $ the_default Y Y'))
  | map_ret i _ (Bound a) = if i <= a then SOME (Bound (a+1)) else NONE
  | map_ret _ _ _ = NONE
in the_default term (map_ret 0 VS term)
end
in (collect_vals, map_ret') end

(*val dummyT_sem = Type (\<^type_name>\<open>\<phi>arg\<close>, [dummyT])
fun ex_fastype_of TM =
  let val T = fastype_of TM in if T = dummyT then dummyT_sem else T end
  handle TERM _ => dummyT_sem*)

fun package_values name _ (SOME ([], NONE)) term =
      (\<^term>\<open>\<phi>V_nil\<close>, Abs(name, val_list_T, term), ([], NONE))
  | package_values name R2L Vs0 term =
  let
    val (collect_vals, map_ret) = gen_collect_and_map R2L
    val Vs = case Vs0 of SOME Vs => Vs | NONE => collect_vals ([],NONE) term
    (*val Tys = fold_rev (fn T => (fn [] => [T]
                                  | L as T'::_ => mk_arg_prodT (T,T') :: L))
              (map ex_fastype_of Vs) []
    val T = if null Tys then \<^typ>\<open>unit \<phi>arg\<close> else hd Tys*)
  in (mk_arg_list Vs,
      Abs(name, val_list_T,
          if null (#1 Vs) andalso #2 Vs = NONE
          then term else map_ret (#1 Vs) term),
      Vs)
  end

fun package_values0 name _ _ (term as Const (\<^const_name>\<open>Groups.zero_class.zero\<close>, _))
      = ( \<^Const>\<open>\<phi>arg \<open>\<^Type>\<open>list \<^Type>\<open>VAL\<close>\<close>\<close>\<close> $ \<^Const>\<open>unreachable\<close>,
          Abs (name, val_list_T, term),
          ([], NONE) )
  | package_values0 name R2L Vs0 term = package_values name R2L Vs0 term


fun translate_ret' (term as (Abs _)) = term
  | translate_ret' (term as (Var _)) = term
  | translate_ret' (term as (Free _)) = term
  | translate_ret' (tm as Const (\<^const_abbrev>\<open>Void\<close>, _))
      = Abs ("", val_list_T, tm)
  | translate_ret' (tm as Const (\<^const_name>\<open>one_class.one\<close>, _))
      = Abs ("", val_list_T, tm)
  | translate_ret' (term as (Const _)) = term
  | translate_ret' (Const ("_constrain", ty) $ X $ Y)
      =(case translate_ret' X of Abs (N,T,B) => Abs (N, T, Const ("_constrain", ty) $ B $ Y)
                              | B => Const ("_constrain", ty) $ B $ Y)
  | translate_ret' (Const ("_type_constraint_", ty) $ X)
      =(case translate_ret' X of Abs (N,T,B) => Abs (N, T, Const ("_type_constraint_", ty) $ B)
                              | B => Const ("_type_constraint_", ty) $ B)
  | translate_ret' (Const ("_constrainAbs", ty) $ X $ Y)
      =(case translate_ret' X of Abs (N,T,B) => Abs (N, T, Const ("_constrainAbs", ty) $ B $ Y)
                              | B => Const ("_constrainAbs", ty) $ B $ Y)
  | translate_ret' term =
      #2 (package_values0 "\<r>\<e>\<t>" false NONE term)


(* fun translate_num term =
      fold_aterms (
          fn Const (\<^const_name>\<open>val_syntax\<close>, _) => (fn n => n + 1)
           | _ => I) term 0 *)

fun need_translate_ret (Abs (_,_,_)) = false
  | need_translate_ret (Free _) = false
  | need_translate_ret (Var  _) = false
  | need_translate_ret (Const (\<^const_abbrev>\<open>Void\<close>, _)) = true
  | need_translate_ret (Const (\<^const_name>\<open>one_class.one\<close>, _)) = true
  | need_translate_ret (Const  _) = false
  | need_translate_ret (Const ("_constrain", _) $ X $ _)
      = need_translate_ret X
  | need_translate_ret (Const ("_type_constraint_", _) $ X)
      = need_translate_ret X
  | need_translate_ret (Const ("_constrainAbs", _) $ X $ _)
      = need_translate_ret X
  | need_translate_ret _ = true

fun translate_ret X = if need_translate_ret X then translate_ret' X else X

(*
The parse translation is invoked once there is an anonymous value in the argument specification,
or once the return specification is not a lambda abstraction nor an atom (a variable or a constant)
*)
val _ = Theory.setup (Sign.parse_translation [
    (\<^const_syntax>\<open>\<phi>Procedure\<close>, (fn ctxt => fn [f,Arg,Ret,E] =>
        (Const (\<^const_name>\<open>\<phi>Procedure\<close>, dummyT) $ f
          $ Arg
          $ (if need_translate_ret Ret then translate_ret' Ret else Ret)
          $ E)
        |> translate_proc_arg (Context.Proof ctxt))),
    (\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, (fn ctxt => fn [f,Arg,Ret] =>
        (Const (\<^const_abbrev>\<open>\<phi>Procedure_no_exception\<close>, dummyT) $ f
          $ Arg
          $ (if need_translate_ret Ret then translate_ret' Ret else Ret))
        |> translate_proc_arg (Context.Proof ctxt) ))
])


end