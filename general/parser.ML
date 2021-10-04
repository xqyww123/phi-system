signature NU_PARSE = sig
  val auto_level : int parser
  val auto_level_force : int parser
  val repeate_N : int -> ('a -> 'b * 'a) -> 'a -> 'b list * 'a
end
structure NuParse = struct
open Parse
fun iden_with pred = Scan.one (pred o Token.content_of) >> Token.content_of;
fun sym_iden_key x =
      group (fn () => Token.str_of_kind Token.Sym_Ident ^ " " ^ quote x)
        (iden_with (fn y => x = y));
val auto_level =
  (sym_iden_key "!!" >> (K 1) || sym_iden_key "!!!" >> (K 0) || Scan.succeed 2)
val auto_level_force =
  (sym_iden_key "!!" >> (K 1) || sym_iden_key "!!!" >> (K 0))

fun repeate_N_i ret n scan a =
  if n <= 0 then (rev ret, a)
  else case scan a of (b,a') => repeate_N_i (b::ret) (n-1) scan a'
val repeate_N = repeate_N_i []
end
