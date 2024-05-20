signature PATTERN_STORE_CFG = sig

type T
val eq : T * T -> bool
val export : Proof.context -> Proof.context -> T -> T

end

signature TERM_PATTERN_STORE = sig

(*priority : bigger value is of higher priority in execution*)

structure Config : PATTERN_STORE_CFG
type T = Config.T
type entry = priority * spattern * Position.T * T

val add : entry list -> Context.generic -> Context.generic
val remove : entry -> Context.generic -> Context.generic
val get : Context.generic -> PLPR_Pattern.fixed_bounds -> bvs -> term -> entry list
val get_uniq : Context.generic -> PLPR_Pattern.fixed_bounds -> bvs -> term -> entry option
val list : Context.generic -> entry list
val export : Proof.context -> Proof.context -> entry -> entry

val setup_decl_attr : binding -> T parser -> 't parser
                   -> (Proof.context -> string * 't -> term * T)
                   -> string
                   -> theory -> theory
val setup_decl_ML_attr : binding -> string
                   -> (Proof.context -> string -> term) -> (Proof.context -> 'a -> T)
                   -> string
                   -> theory
                   -> 'a option Unsynchronized.ref * theory

end

functor Term_Pattern_Store (Config : PATTERN_STORE_CFG) : TERM_PATTERN_STORE = struct

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

fun export ctxt ctxt' (n, tm, pos, x)
      = (n, singleton (Variable.export_terms ctxt ctxt') tm, pos, Config.export ctxt ctxt' x)


fun get ctxt =
  let val data = Data.get ctxt
      val match = PLPR_Pattern.does_smatch (Context.theory_of ctxt)
   in fn fixed_bounds => fn bvs => fn term =>
          Net.match_term data term
              |> filter (fn (_,p,_,_) => match fixed_bounds bvs (p,term))
              |> sort (fn ((n1,_,_,_),(n2,_,_,_)) => int_ord (n2,n1))
  end

fun get_uniq ctxt =
  let val get = get ctxt
      fun uniq [] = NONE
        | uniq [x] = SOME x
        | uniq (x1::x2::L) =
            if #1 x1 = #1 x2
            then error (let open Pretty in
                  string_of (chunks [
                      str "Multiple potential patterns are available:",
                      Syntax.pretty_term (Context.proof_of ctxt) (#2 x1),
                      str "versus",
                      Syntax.pretty_term (Context.proof_of ctxt) (#2 x2)
                   ])
                 end)
            else SOME x1
   in fn fixed_bounds => fn bvs => fn term =>
         uniq (get fixed_bounds bvs term)
  end

fun decl_synt cached_parser parser parse_pattern =
   ((Scan.lift (Parse.position Args.internal_term --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>) --
     cached_parser --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (((p,pos),x),n) => (n,p,pos,x)))
|| ((Args.context -- Scan.lift (Parse.position (Parse.token Parse.embedded) --| (\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
                  -- parser --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
  >> (fn (ctxt,(((tok_p,pos),x),n)) =>
    let val p = Token.inner_syntax_of tok_p
        val ctxt_p = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
        val (p',x') = parse_pattern ctxt_p (p,x)
        val _ = Token.assign (SOME (Token.Term p')) tok_p
     in (n,p',pos,x')
     end))


fun setup_decl_attr binding cached_parser parser parse_pattern comment =
  Attrib.setup binding
        (Args.context -- Parse.and_list' (decl_synt cached_parser parser parse_pattern) >> (fn (_,pats) =>
                Thm.declaration_attribute (K (fn ctxt' =>
                    add pats ctxt'
                    )))) comment

fun setup_decl_ML_attr binding access_to_sender parse_pattern constructor comment =
  let val sender = Unsynchronized.ref NONE
      val locker = Synchronized.var (Binding.name_of binding) ()

      val term_pattern = Scan.peek (fn generic => Parse.position (Args.named_term (
            let val ctxt = Proof_Context.set_mode Proof_Context.mode_pattern (Context.proof_of generic)
             in parse_pattern ctxt end)))

      val decl_synt_ML =
          (Args.context -- term_pattern -- Scan.lift ((\<^keyword>\<open>=>\<close> || \<^keyword>\<open>\<Rightarrow>\<close>)
                       |-- Parse.ML_source --| \<^keyword>\<open>(\<close> -- Parse.nat --| \<^keyword>\<open>)\<close>))
        >> (fn ((ctxt,(p,pos)),(src,n)) =>
          let val ret = Synchronized.change_result locker (fn () =>
                          let val _ = ML_Context.expression (Input.pos_of src)
                                        (ML_Lex.read access_to_sender @
                                         ML_Lex.read ":= SOME (" @
                                         ML_Lex.read_source src @
                                         ML_Lex.read ")")
                                      (Context.Proof ctxt)
                              val ret = the (!sender)
                              val _ = sender := NONE
                           in (ret, ())
                          end)
           in (n,p,pos,constructor ctxt ret)
           end)
 
   in Attrib.setup binding
        (Args.context -- Parse.and_list' decl_synt_ML >> (fn (ctxt,pats) =>
                Thm.declaration_attribute (K (fn ctxt' =>
                    let val ctxt'' = Context.proof_of ctxt'
                     in add (map (export ctxt ctxt'') pats) ctxt' end)))) comment
   #> pair sender
  end


end