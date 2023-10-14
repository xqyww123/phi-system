signature PHI_PARSE = sig
  val $$$ : string -> string parser
  val auto_level : int parser
  val auto_level_force : int parser
end
structure Phi_Parse = struct
open Parse

fun $$$ key =
  group (fn () => "keyword " ^ quote key)
    ((short_ident || long_ident || sym_ident || keyword || string) >>
      (fn s => if s = key then s else Scan.fail ()))


fun iden_with pred = Scan.one (pred o Token.content_of) >> Token.content_of;
fun sym_iden_key x =
      group (fn () => Token.str_of_kind Token.Sym_Ident ^ " " ^ quote x)
            (Scan.ahead not_eof -- iden_with (fn y => x = y));

val auto_level =
  (sym_iden_key "!!" >> (K 1) || sym_iden_key "!!!" >> (K 0) || Scan.succeed 2)
val auto_level_force =
  (sym_iden_key "!!" >> (K 1) || sym_iden_key "!!!" >> (K 0))

end
