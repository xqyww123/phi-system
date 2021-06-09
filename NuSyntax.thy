theory NuSyntax
  imports NuPrim
begin

ML \<open>   \<close>

ML \<open>
signature NU_SYNTAX = sig
  type fixes = (binding * string option * mixfix) list
end

structure NuSyntax : NU_SYNTAX = struct
  type fixes = (binding * string option * mixfix) list
end

\<close>
end