signature NU_PARSE = sig
  val $$$ : string -> string parser
  val auto_level : int parser
  val auto_level_force : int parser
  val repeat_N : int -> ('a -> 'b * 'a) -> 'a -> 'b list * 'a
end
structure NuParse = struct
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

fun repeat_N_i ret n scan a =
  if n <= 0 then (rev ret, a)
  else case scan a of (b,a') => repeat_N_i (b::ret) (n-1) scan a'
val repeat_N = repeat_N_i []
end
