structure Phi_Pointer_Of = Pattern_Translation (
  val check_pattern = Syntax.check_terms
  val parse_pattern = Syntax.parse_term
  val multi_translation_err_msg =
        "Fail to infer the pointer \<phi>-type as there are different possible resolutions"
)

local

fun guess_pointer eqs =
  let fun scan_addr eq =
        let val (LHS,RHS) = Phi_Help.dest_HOL_eq (Thm.concl_of eq)
            val (_, args) = strip_comb LHS
            val addr = filter (fn (_,arg) => fastype_of arg = \<^typ>\<open>address\<close>) (map_index I args)
         in addr |> Option.map (fn addr =>
            xx
         )
        end
      fun guess_one (Const(\<^const_name>\<open>Trueprop\<close>, _)
            $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ RHS)) = scan RHS
        | guess_one X = raise TERM ("guess_pointer", [X])
   in ()
  end

fun pointer_of_deriver (_, pos) intrs phityp lthy =
  let open Phi_Type
      fun shouldn't_be_given name =
        raise Automation_Fail (fn () => let open Pretty in
            [block (text name @ [brk 1] @ text "is meaningless here in deriving \<open>Pointer_Of\<close>")]
          end)
      fun chk_intr (_, group, _, meth, notes, bundle) =
        if is_some group
        then shouldn't_be_given "Reasoner group or priority"
        else if is_some meth
        then shouldn't_be_given "Proof tactic"
        else if not (null notes)
        then shouldn't_be_given "Note"
        else if not (null notes)
        then shouldn't_be_given "Bundle"
        else ()
      val _ = List.app chk_intr intrs
      val hints = map_filter #1 intrs |> map fst
      val _ = if length hints > 1
              then raise Automation_Fail (fn () => let open Pretty in
                    [block (text "The deriver of \<open>Pointer_Of\<close> accepts at most one hint.")]
                  end)
              else ()
      
   in lthy
  end

in



end