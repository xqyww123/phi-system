(*  Title:      NuSys.ML
    Author:     Qiyuan Xu

The toplevel structure of the ν-system.

`begin_proc (argument-statement, for-fixes, including bundles)`
    starts the block for procedure constrruction. The block is based on `notepad`. 

*)

signature NU_SYS = sig
  val register_label_head : string
  val show_proc_expression_attr : attribute context_parser
  val begin_proc_cmd : (string * Position.T) * (binding * string option * mixfix) list *
        (string * Position.T) list -> Proof.context -> Proof.state
  (* val end_proc : state -> state *)
end

structure NuSys : NU_SYS = struct
open NuHelp NuBasics Term HOLogic
type context = Proof.context
type state = Proof.state
val register_label_head = "\<upsilon>"

  fun ctx_parser_wrap f (ctx,tok) = case f tok of (x,tok') => (x,(ctx,tok'))
  val ctx_parser_wrap : 'a parser -> 'a context_parser = ctx_parser_wrap
  val bool_opt_parser = ctx_parser_wrap
        (Parse.$$$ "=" |-- ((Args.$$$ "false" >> K false) || (Args.$$$ "true" >> K true)))

  fun map_theory_total f = Context.mapping f (Proof_Context.background_theory f)

  (* val show_proc_expression = Config.declare_bool ("show_proc_expression", \<^here>) (K false) *)
  local
  val omitted = [Syntax.Print_Rule (("logic", "_codeblock_ x"),
        ("logic", "CONST CodeBlock x exp"))]
  val detailed = [Syntax.Print_Rule (("logic", "_codeblock_exp_ x exp"),
        ("logic", "CONST CodeBlock x exp"))]
  in
  val show_proc_expression_attr = let
    fun attr opt _ ctx = ctx |> map_theory_total
      (Isar_Cmd.no_translations (if opt then omitted else detailed)
      #> Isar_Cmd.translations  (if opt then detailed else omitted))
    in bool_opt_parser >> (Thm.declaration_attribute o attr) end
  end


val indTy = Type ("Nat.ind", [])
val stack_R = Free ("\<R>", Type ("Set.set", [TFree ("'\<R>", ["NuPrim.lrep"])]))
val arg_stat_term = Free ("\<ss>", dummyT)
val times_name = "Product_Type.Times"

(** proc command **)

val default_name = "v"
val auto_name = dest_nuTy #> fst #> Type.strip_constraints #> dest_Free #> fst
fun pass_name tm = 
      case dest_named tm of
         (SOME name, tm) => (name, tm)
       | (NONE, tm) => (tm |> try auto_name |> the_default default_name, tm)

(* "(a1 ⦂ N1 named n1) × ⋯ × (ak ⦂ Nk named nk)" -->
    ("(a1 ⦂ N1) × ⋯ × (ak ⦂ Nk) × ℛ ", [n1,...,nk]) with automatical naming for the anonymous *)
fun mk_argument arg : (term * string list) =
  let
    val (names,args) = arg |> strip_binop_r times_name |> map pass_name |> split_list
    val names = names |> Name.variant_list []
    val arg = list_mk_binop_r0 times_name stack_R args
    val arg = Trueprop $ (Const ("Set.member", dummyT) $ arg_stat_term $ arg)
  in
    (arg, names)
  end

fun begin_proc_cmd ((statement, pos), fixes, inc_bundles) stat =
  let
    val stat = stat
          |> Proof.begin_notepad
          |> Bundle.include_cmd inc_bundles
          |> Proof.begin_block
          |> NuHelp.fix_frees pos [stack_R, arg_stat_term]
          |> Proof.fix_cmd fixes
    val lthy = Proof.context_of stat
    val (arg,labels) = statement |> Syntax.parse_term lthy |> mk_argument 
    val arg = arg |> Syntax.check_term lthy
    val lthy = Proof.context_of stat
    val stat = stat |> NuHelp.fix_frees pos (Variable.add_frees lthy arg [] |> map Free)
    val lthy = Proof.context_of stat
    val _ = statement |> Syntax.parse_term lthy (* a dirty hack to fix the displayed color *)
    val arg = arg |> free_to_fix lthy
    val th = Thm.cterm_of lthy arg |> Thm.assume
    val _ = @{print} th
    val tm = writeln (Thm.string_of_thm lthy th)
    val stat = stat |> Proof.set_facts [th]
  in
    stat
  end

end
