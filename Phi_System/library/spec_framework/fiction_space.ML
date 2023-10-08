signature FICTION_LOCALE_ARGUMENT = sig

include GENERIC_RESOURCE_LOCALE_ARGUMENT

val DOMAIN_N : string
val INTERPRET_N : string

end

structure Fiction_Locale_Argument : FICTION_LOCALE_ARGUMENT = struct

type additional_data  = string
type additional_data' = typ
type env = (string * sort) list

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

fun entryT nameT repT T = \<^Type>\<open>Resource_Space.kind nameT repT T\<close>
val prep_additional_data = read_typ
val chk_additional_data = cert_typ

fun additional_data_parser (default_sort, default_locale) =
      \<^keyword>\<open>::\<close> |-- (
        Parse.typ --
        Scan.optional (Parse.sort --| \<^keyword>\<open>,\<close> -- Parse.name_position)
          (default_sort, (default_locale, Position.none))
      )

val repN = "'FREP"
val repTN = "TYPE'FREP"
val nameTN = "TYPE'NAME"
val NAME_N = "'FREP_N"
val DOMAIN_N = "DOMAIN"
val INTERPRET_N = "INTERPRET"

fun read_arg ctxt resT raw_T env =
  let
    val ctxt' = fold (Variable.declare_typ o TFree) env ctxt;
    val TM0 = Syntax.parse_term ctxt' raw_T
    val chk = Syntax.check_term ctxt' o Type.constraint \<^Type>\<open>fun dummyT \<^Type>\<open>set resT\<close>\<close>
    val T = chk TM0
    val env' = Term.add_tfrees T env;
  in (T, env') end;

fun cert_arg ctxt resT raw_TM env =
  let
    val thy = Proof_Context.theory_of ctxt;
    val chk = Sign.certify_term thy
            o Syntax.check_term ctxt
            o Type.constraint \<^Type>\<open>fun dummyT \<^Type>\<open>set resT\<close>\<close>
    val (Tm,Ty,_) = chk raw_TM
    val _ = Type.no_tvars Ty
      handle TYPE (msg, _, _) => error msg;
    val Tm = Sign.no_vars ctxt Tm
    val env' = Term.add_tfrees Tm env;
  in (Tm, env') end;

fun dest_typ (\<^Type>\<open>fun T _\<close>) = T
  | dest_typ T = raise TYPE ("shoud be a unital_homo", [T], [])

val field_locale = \<^locale>\<open>fiction_kind\<close>
val space_locale = \<^locale>\<open>fictional_space\<close>


val nameT = TFree (NAME_N, \<^sort>\<open>type\<close>);

fun space_locale_args resT repT =
  let val domainT = nameT --> \<^Type>\<open>sep_homo_set repT\<close>
      val INTERP_T = nameT --> \<^Type>\<open>unital_homo repT \<^Type>\<open>set resT\<close>\<close>
   in [(DOMAIN_N, domainT), (INTERPRET_N, INTERP_T)]
  end

end

structure Fiction_Locale = Generic_Resource_Locale(Fiction_Locale_Argument)
