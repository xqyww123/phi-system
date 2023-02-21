signature PATTERN_TRANSLATION = sig

val add : (int * term * term) list -> Context.generic -> Context.generic
val remove : int * term * term -> Context.generic -> Context.generic
val translate : Context.generic -> term -> term option
val setup_attribute : binding -> string -> theory -> theory

end

functor Pattern_Translation (Config : sig
  val multi_translation_err_msg : string
end) : PATTERN_TRANSLATION = struct

fun pat_pat_eq ((p1,a1,b1),(p2,a2,b2)) = p1 = p2 andalso a1 aconv a2 andalso b1 aconv b2

structure Data = Generic_Data (
  type T = (int (*priority*) * term (*pattern P*) * term (*the default pattern X*)) Net.net
  (*It gives the default pattern P of an introduction rule whose conclusion matches some pattern P.
    Larger priority is more prior.*)
  val empty = Net.empty
  val merge = Net.merge pat_pat_eq
)

fun add pat_pats ctxt =
      Data.map (fold (fn (n,p1,p2) =>
              Net.insert_term pat_pat_eq (p1,(n,p1,p2))) pat_pats) ctxt
      handle Net.INSERT => Exn.error ("Some pattern clashes with existing entries.")
fun remove (n,p1,p2) =
      Data.map (Net.delete_term_safe pat_pat_eq (p1,(n,p1,p2)))

fun calculate thy term (n, pat0, pat_ret0) =
  let val ind = Term.maxidx_of_term term + 1
      val pat = Logic.incr_indexes ([],[],ind) pat0
      val pat_ret = Logic.incr_indexes ([],[],ind) pat_ret0
      val s = Pattern.match thy (pat, term) (Vartab.empty, Vartab.empty)
   in (SOME (n, Envir.subst_term s pat_ret))
  end handle Pattern.MATCH => NONE

fun translate ctxt term =
  Net.match_term (Data.get ctxt) term
    |> sort (fn ((n1,_,_),(n2,_,_)) => int_ord (n2,n1))
    |> Seq.of_list
    |> Seq.map_filter (calculate (Context.theory_of ctxt) term)
    |> Seq.chop 2
    |> (fn ([], _) => NONE
         | ([(_,ret)], _) => SOME ret
         | ([(n1,ret),(n2,ret2)], _) =>
            if n1 = n2
            then error (Pretty.string_of (Pretty.chunks (
                    [Pretty.str "Multiple potential patterns are available:"] @
                    (map (Syntax.pretty_term (Context.proof_of ctxt)) [ret,ret2]) @
                    [Pretty.str Config.multi_translation_err_msg]
                 )))
            else SOME ret)


val pat2 = (Args.context -- Scan.lift (Parse.prop --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) -- Parse.prop
                                      --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (ctxt,((p1,p2),n)) =>
    let val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
        val [p1',p2'] = Syntax.check_props ctxt_p [Syntax.parse_prop ctxt_p p1,
                                                   Syntax.parse_prop ctxt_p p2]
     in (n,p1',p2')
     end)

fun setup_attribute binding comment = Attrib.setup binding
      (Parse.enum1' "and" pat2 >> (fn pats =>
              Thm.declaration_attribute (K (add pats)))) comment

end