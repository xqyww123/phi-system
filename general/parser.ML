signature NU_PARSE = sig
  val auto_level : int parser
end
structure NuParse = struct
local open Parse in
fun iden_with pred = Scan.one (pred o Token.content_of) >> Token.content_of;
fun sym_iden_key x =
      group (fn () => Token.str_of_kind Token.Sym_Ident ^ " " ^ quote x)
        (iden_with (fn y => x = y));
val auto_level =
  (sym_iden_key "!!" >> (K 1) || sym_iden_key "!!!" >> (K 0) || Scan.succeed 2)
end
end
