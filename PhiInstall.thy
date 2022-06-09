theory PhiInstall
  imports Main HOL.Rat
begin

datatype SV = SV_1 rat nat | SV_0 | SV_L \<open>SV list\<close>

instantiation SV :: times begin
definition \<open>times_SV A B =
  (case (A,B) of (SV_1 sa na, SV_1 sb nb) \<Rightarrow>
      (if na = nb then SV_1 ))\<close>
end

end