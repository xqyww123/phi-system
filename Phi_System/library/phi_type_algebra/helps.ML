signature PHI_TYPE_ALGEBRA = sig

val conv_def_to_equaltion : Proof.context -> thm -> thm

end

structure Phi_Type_Algebra : PHI_TYPE_ALGEBRA = struct

fun conv_def_to_equaltion ctxt def =
  case Thm.concl_of def
    of Const(\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ =>
        conv_def_to_equaltion ctxt
          (Conv.fconv_rule (Phi_Conv.hhf_concl_conv Object_Logic.atomize ctxt) def)
     | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (
         Const(\<^const_name>\<open>HOL.eq\<close>, \<^Type>\<open>fun Ty _\<close>) $ LHS $ RHS) =>
       (case Ty
          of \<^Type>\<open>fun _ \<open>\<^Type>\<open>set _\<close>\<close>\<close> =>
              let val concl = Thm.dest_arg (Thm.cconcl_of def)
                  val T = Thm.dest_arg1 concl
                  val U = Thm.dest_arg  concl
                  val cty = Thm.ctyp_of_cterm T
                  val ty_a = Thm.dest_ctyp0 cty
                  val ty_b = Thm.dest_ctyp0 (Thm.dest_ctyp1 cty)
                  val rule = Thm.instantiate (TVars.make [((("'a",0),\<^sort>\<open>type\<close>),ty_a),
                                                          ((("'b",0),\<^sort>\<open>type\<close>),ty_b)],
                                              Vars.make [((("T",0),Thm.typ_of_cterm T),T),
                                                         ((("U",0),Thm.typ_of_cterm U),U)])
                             (case RHS of Abs _ => @{thm \<phi>Type_conv_eq_1}
                                        | Const(\<^const_name>\<open>case_prod\<close>, _) $ _ => @{thm \<phi>Type_conv_eq_1}
                                        | _ => @{thm \<phi>Type_conv_eq_2})
                  fun prod_beta ctm =
                    case Thm.term_of ctm
                      of Const(\<^const_name>\<open>case_prod\<close>, _) $ _ $ _ =>
                          (Conv.rewr_conv @{thm' case_prod_beta[folded atomize_eq]} then_conv prod_beta) ctm
                       | Abs _ $ _ $ _ =>
                          (Thm.beta_conversion true then_conv prod_beta) ctm
                       | _ => Conv.all_conv ctm

               in Thm.bicompose NONE {flatten=false,match=true,incremented=true}
                                     (false, def, Thm.nprems_of def) 1 rule
               |> Seq.hd
               |> Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.arg_conv prod_beta))
              end
           | \<^Type>\<open>set _\<close> => (
                case LHS of Const(\<^const_name>\<open>\<phi>Type\<close>, _) $ _ $ _ => def
                          | _ $ _ => Conv.fconv_rule (Phi_Conv.hhf_concl_conv (fn ctxt =>
                                        HOLogic.Trueprop_conv (HOLogic.eq_conv
                                          (fn ctm =>
                                            let val T = Thm.dest_fun ctm
                                                val x = Thm.dest_arg ctm
                                                val (b,a) = Phi_Syntax.dest_phi_type_ty_c (Thm.ctyp_of_cterm T)
                                                val rule = Thm.instantiate
                                                              (TVars.make [((("'b",0),\<^sort>\<open>type\<close>),b),
                                                                           ((("'a",0),\<^sort>\<open>type\<close>),a)],
                                                               Vars.make [((("T",0),Thm.typ_of_cterm T),T),
                                                                          ((("x",0),Thm.typ_of_cterm x),x)])
                                                              @{thm \<phi>Type_def[symmetric, folded atomize_eq]}
                                             in Conv.rewr_conv rule ctm
                                            end)
                                          Conv.all_conv)
                                     ) ctxt) def
                          | _ => raise THM ("Not a \<phi>-type definition", 0, [def]))
           | _ => raise THM ("Not a \<phi>-type definition", 0, [def]))
     | _ => raise THM ("Not a \<phi>-type definition", 0, [def])

end