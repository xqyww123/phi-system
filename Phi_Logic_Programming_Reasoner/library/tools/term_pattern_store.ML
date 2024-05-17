signature TERM_PATTERN_STORE_CFG = sig

type T

val eq : T * T -> bool

end

signature TERM_PATTERN_STORE = sig

(*priority : bigger value is of higher priority in execution*)

structure Config : TERM_PATTERN_STORE_CFG
type T = Config.T
type entry = priority * spattern * Position.T * T

val add : entry list -> Context.generic -> Context.generic
val remove : entry -> Context.generic -> Context.generic
val get : Context.generic -> term -> entry list
val list : Context.generic -> entry list

end

functor Term_Pattern_Store (Config : TERM_PATTERN_STORE_CFG) : TERM_PATTERN_STORE = struct

structure Config = Config
type T = Config.T
type entry = priority * spattern * Position.T * T

fun data_eq ((p1,a1,o1,x),(p2,a2,o2,y)) =
      p1 = p2 andalso a1 aconv a2 andalso o1 = o2 andalso
      Config.eq (x,y)

structure Data = Generic_Data (
  type T = (int (*priority*) * spattern (*pattern P*) * Position.T * Config.T) Net.net
  val empty = Net.empty
  val merge = Net.merge data_eq
)

fun add data ctxt =
      Data.map (fold (fn (n,p1,pos,x) =>
            let val p1' = PLPR_Pattern.mk_spattern p1
             in Net.insert_term data_eq (p1',(n,p1',pos,x))
            end
          ) data
        ) ctxt
      handle Net.INSERT => Exn.error ("Some pattern clashes with existing entries.")

fun remove (n,p,pos,x) =
      Data.map (Net.delete_term_safe data_eq (p,(n,p,pos,x)))

fun list ctxt = Net.content (Data.get ctxt)

fun get ctxt =
  let val data = Data.get ctxt
   in fn term => Net.match_term data term
              |> sort (fn ((n1,_,_,_),(n2,_,_,_)) => int_ord (n2,n1))
  end

(*
fun pat_synt T =
   ((Scan.lift (Parse.position Args.internal_term --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) --
     T --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (((p,pos),x),n) => (n,p,pos,x)))
|| ((Args.context -- Scan.lift (Parse.position (Parse.token Parse.embedded) --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
                  -- Scan.repeat1 (Parse.token Parse.embedded) --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (ctxt,(((tok_p,pos),x),n)) =>
    let val p = Token.inner_syntax_of tok_p
        val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
        val p' = Syntax.check_prop ctxt_p (Syntax.parse_prop ctxt_p p)
        val _ = Token.assign (SOME (Token.Term p')) tok_p
     in (n,p',pos,x)
     end))

fun setup_decl_attr binding =
  Attrib.setup binding
        (Args.context -- Parse.and_list' pat2 >> (fn (_,pats) =>
                Thm.declaration_attribute (K (fn ctxt' =>
                    add pats ctxt'
                    )))) comment
*)
end