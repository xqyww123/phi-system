signature BNF_FP_SUGAR_MORE = sig

type fp_more = {
  deads: typ list,
  lives: typ list,
  lives': typ list,
  zip: term,
  unzip: term,
  zip_simps: thm list,
  unzip_simps: thm list
}

val add_fp_more : string * fp_more -> Context.generic -> Context.generic
val get_fp_more : Context.generic -> string -> fp_more option

val mk_zip : typ list -> typ list -> typ list -> fp_more -> term
val mk_unzip : typ list -> typ list -> typ list -> fp_more -> term

val export : Context.generic -> Context.generic -> Context.generic

val identity_element : typ -> Context.generic -> (ctyp TVars.table * thm) list * Context.generic
val identity_element_unify : typ -> Context.generic -> (ctyp TVars.table * thm) list * Context.generic

end

structure BNF_FP_Sugar_More : BNF_FP_SUGAR_MORE = struct
open BNF_Def

type fp_more = {
  deads: typ list,
  lives: typ list,
  lives': typ list,
  zip: term,
  unzip: term,
  zip_simps: thm list,
  unzip_simps: thm list
}

fun map_fp_more (fty, ftm, fth) (fp : fp_more) = {
  deads = fty (#deads fp),
  lives = fty (#lives fp),
  lives' = fty (#lives' fp),
  zip = ftm (#zip fp),
  unzip = ftm (#unzip fp),
  zip_simps = fth (#zip_simps fp),
  unzip_simps = fth (#unzip_simps fp)
} : fp_more

val trim_fp_more = map_fp_more (I, I, map Thm.trim_context)
fun transfer_fp_mode thy = map_fp_more (I, I, map (Thm.transfer thy))

fun fp_more_eq (fp1, fp2) =
  #zip fp1 = #zip fp2 andalso #unzip fp1 = #unzip fp2

structure Fp_Mores = Generic_Data (
  type T = fp_more Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge fp_more_eq
)

fun add_fp_more (ty_name, fp) = Fp_Mores.map (Symtab.update_new (ty_name, trim_fp_more fp))
fun get_fp_more generic ty_name =
      Option.map (transfer_fp_mode (Context.theory_of generic)) (Symtab.lookup (Fp_Mores.get generic) ty_name)

fun mk_zip Ds Ts Us fp_more =
      Term.subst_atomic_types
        ((#deads fp_more ~~ Ds) @ (#lives fp_more ~~ Ts) @ (#lives' fp_more ~~ Us)) (#zip fp_more)

fun mk_unzip Ds Ts Us fp_more =
      Term.subst_atomic_types
        ((#deads fp_more ~~ Ds) @ (#lives fp_more ~~ Ts) @ (#lives' fp_more ~~ Us)) (#unzip fp_more)


(*** Cache ***)

structure Properties = Generic_Data (
  type T = (typ * thm) list Symreltab.table
  val empty = Symreltab.empty
  val merge = Symreltab.merge (K true)
)

fun export from to = Properties.put (Properties.get from) to

fun gen_property match kind gen (typ0 as Type(Tname,_)) generic =
  let val ctxt = Context.proof_of generic
      val thy = Context.theory_of generic
      val typ = Term.map_atyps (fn TVar ((N,i),S) => TVar ((N,~i),S) | T => T) typ0
      val mpf = map_filter (fn (ty',ths) =>
                  let val i = Term.maxidx_of_typ ty'
                      val (env, _) = match thy (ty', typ) (Vartab.empty, i)
                      val inst = Phi_Help.tyenv_to_tvars_table ctxt env
                   in SOME (inst, Thm.instantiate (inst, Vars.empty) ths)
                  end handle TYPE_MATCH => NONE)
   in case Symreltab.lookup (Properties.get generic) (Tname,kind)
        of SOME ths =>
            (map (apsnd (Thm.transfer'' generic)) (mpf ths), generic)
         | NONE =>
            let val res = gen Tname generic
             in (mpf res, Properties.map (Symreltab.update_new (
                              (Tname,kind), res)) generic)
            end
  end
  | gen_property _ _ _ typ _ =
      raise TYPE ("Not a Type constant", [typ], [])



fun made_of_ctrs chk_ctrs (Const(N,_)) = chk_ctrs N
  | made_of_ctrs chk_ctrs (X $ Y) = made_of_ctrs chk_ctrs X andalso made_of_ctrs chk_ctrs Y
  | made_of_ctrs chk_ctrs (Abs(_,_,X)) = made_of_ctrs chk_ctrs X
  | made_of_ctrs _ _ = true

fun chk_search_result1 ctxt pattern [] =
      error ("No existing theorems found for " ^ Syntax.string_of_term ctxt pattern)
  | chk_search_result1 _ _ [x] = [x]
  | chk_search_result1 ctxt pattern L = let open Pretty in
        error (string_of (chunks (
            block [str "More than one existing theorems found for ", Syntax.pretty_term ctxt pattern] ::
            map (fn th => item [Syntax.pretty_term ctxt (Thm.prop_of th)]) L
          )))
      end

fun gen_unit_simps Tname generic =
  let val sorts = Sign.arity_sorts (Context.theory_of generic) Tname \<^sort>\<open>one\<close>
      val ctxt = Context.proof_of generic
      val ty_args = map_index (fn (i,S) => TVar(("x",i),S)) sorts
      val ty = Type(Tname, ty_args)
      val pattern = \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.eq ty\<close> $ \<^Const>\<open>one_class.one ty\<close> $ Var(("uu",0),ty))
      val ctrs =(case Context.cases Ctr_Sugar.ctr_sugar_of_global Ctr_Sugar.ctr_sugar_of generic Tname
                   of SOME c => fold (fn Const(N,_) => Symtab.insert_set N) (#ctrs c) Symtab.empty
                    | NONE => Symtab.empty)
              |> Symtab.defined
   in Find_Theorems.find_theorems ctxt NONE NONE true [(true, Find_Theorems.Pattern pattern)]
   |> snd
   |> map_filter (fn (_, th) => case Thm.prop_of th
                                  of _ (*Trueprop*) $ (_ (*eq*) $ _ $ RHS) =>
                                      if made_of_ctrs ctrs RHS
                                      then SOME th
                                      else NONE
                                   | _ => NONE)
   |> chk_search_result1 ctxt pattern
   |> map (fn th => case Thm.concl_of th
                      of _ (*Trueprop*) $ (_ (*eq*) $ LHS $ _) =>
                          (Term.fastype_of LHS, th))
  end

fun match' thy TU (tenv,i) = (Sign.typ_match thy TU tenv, i)
fun identity_element typ generic = gen_property match' "one" gen_unit_simps typ generic
fun identity_element_unify typ generic = gen_property Sign.typ_unify "one" gen_unit_simps typ generic

end