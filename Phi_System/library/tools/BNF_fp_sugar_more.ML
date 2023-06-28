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



end