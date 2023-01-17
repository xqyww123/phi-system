signature PROCEDURE_SYNTAX = sig
include PROCEDURE_SYNTAX

type item_printer = (Phi_Kind.T -> Proof.context -> term -> term option)

val add_item_printer :
      string (*name of the constant on which the printer binds*) * item_printer
      -> theory -> theory
val add_item_printer_lthy :
      string (*name of the constant on which the printer binds*) * (morphism -> item_printer)
      -> local_theory -> local_theory

end

structure Procedure_Syntax : PROCEDURE_SYNTAX = struct
open Procedure_Syntax



(*** Printer ***)

type item_printer = (Phi_Kind.T -> Proof.context -> term -> term option) (*translation*)
  (*returns NONE if the item is to be trimmed / hidden*)

structure Iterm_Printers = Generic_Data (
  type T = item_printer Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun add_item_printer name_P =
  Context.theory_map (Iterm_Printers.map (Symtab.update_new name_P))

fun add_item_printer_lthy (name, P) =
  Local_Theory.declaration {syntax=true, pervasive=false}
    (fn m => Iterm_Printers.map (Symtab.update_new (name, P m)))

fun head_of (X $ _) = head_of X
  | head_of (Const (N, _)) = SOME N
  | head_of _ = NONE

fun tr_item' _ _ _ NONE X = SOME X
  | tr_item' mode ctxt tab (SOME h) X =
     case Symtab.lookup tab h
        of SOME P => (P mode ctxt X handle Match => SOME X)
         | NONE => SOME X

fun tr_item mode ctxt tab (X as (\<^Const_>\<open>\<phi>Type _ _\<close> $ _ $ C)) = tr_item' mode ctxt tab (head_of C) X
  | tr_item mode ctxt tab (X as (Const (\<^const_syntax>\<open>\<phi>Type\<close>, _) $ _ $ C))
      = tr_item' mode ctxt tab (head_of C) X
  | tr_item mode ctxt tab X = tr_item' mode ctxt tab (head_of X) X

fun need_tr_item' ctxt tab mode (SOME h) X =
     (case Symtab.lookup tab h
        of SOME P => ((P mode ctxt X; true) handle Match => false)
         | NONE => false)
  | need_tr_item' _ _  _ NONE _ = false

fun need_tr_item ctxt tab mode (\<^Const_>\<open>\<phi>Type _ _\<close> $ _ $ C)
      = need_tr_item' ctxt tab mode (head_of C) C
  | need_tr_item ctxt tab mode (Const (\<^const_syntax>\<open>\<phi>Type\<close>, _) $ _ $ C)
      = need_tr_item' ctxt tab mode (head_of C) C
  | need_tr_item ctxt tab mode X
      = need_tr_item' ctxt tab mode (head_of X) X

fun strip_separations (Const (\<^const_name>\<open>times\<close>, _) $ A $ X) = A :: (strip_separations X)
  | strip_separations (Const (\<^const_syntax>\<open>COMMA\<close>, _) $ A $ X) = A :: (strip_separations X)
  | strip_separations X = [X]

fun mk_separations [] = Const (\<^const_syntax>\<open>Void\<close>, dummyT)
  | mk_separations L = foldr1 (fn (A,X) => Const (\<^const_syntax>\<open>COMMA\<close>, dummyT) $ A $ X) L


(*ctxt: the context to retrieve Item_Printers*)
fun printer_translation' ctxt tab mode (Abs (N,T,X))
      = Abs (N, T, printer_translation' ctxt tab mode X)
  | printer_translation' ctxt tab mode ((H as \<^Const_>\<open>Subjection _\<close>) $ S $ P)
      = H $ printer_translation' ctxt tab mode S $ P
  | printer_translation' ctxt tab mode ((H as Const (\<^const_syntax>\<open>Subjection\<close>, _)) $ S $ P)
      = H $ printer_translation' ctxt tab mode S $ P
  | printer_translation' ctxt tab mode ((H as \<^Const_>\<open>ExSet _ _\<close>) $ S)
      = H $ printer_translation' ctxt tab mode S
  | printer_translation' ctxt tab mode ((H as Const (\<^const_syntax>\<open>ExSet\<close>, _)) $ S)
      = H $ printer_translation' ctxt tab mode S
  | printer_translation' ctxt tab mode S =
      strip_separations S
        |> map_filter (tr_item mode ctxt tab)
        |> mk_separations

fun need_translation' ctxt tab mode (Abs (_,_,X)) = need_translation' ctxt tab mode  X
  | need_translation' ctxt tab mode (\<^Const_>\<open>Subjection _\<close> $ S $ _)
      = need_translation' ctxt tab mode S
  | need_translation' ctxt tab mode (Const (\<^const_syntax>\<open>Subjection\<close>, _) $ S $ _)
      = need_translation' ctxt tab mode S
  | need_translation' ctxt tab mode (\<^Const_>\<open>ExSet _ _\<close> $ S) = need_translation' ctxt tab mode S
  | need_translation' ctxt tab mode (Const (\<^const_syntax>\<open>ExSet\<close>, _) $ S) = need_translation' ctxt tab mode S
  | need_translation' ctxt tab mode (Const (\<^const_name>\<open>times\<close>, _) $ X $ Y)
      = need_tr_item ctxt tab mode  Y orelse need_translation' ctxt tab mode  X
  | need_translation' ctxt tab mode  (Const (\<^const_syntax>\<open>COMMA\<close>, _) $ X $ Y)
      = need_tr_item ctxt tab mode  Y orelse need_translation' ctxt tab mode  X
  | need_translation' ctxt tab mode X = need_tr_item ctxt tab mode  X


fun may_translation ctxt mode Xs F =
  let val tab = Iterm_Printers.get (Context.Proof ctxt)
   in if exists (need_translation' ctxt tab mode) Xs
      then F (map (printer_translation' ctxt tab mode) Xs)
      else raise Match
  end

val _ = Theory.setup (Sign.typed_print_translation [
    (\<^const_syntax>\<open>\<phi>Procedure\<close>, (fn ctxt => fn T => fn [f,A,R,E] =>
       if T = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Procedure [A,R,E] (fn [A',R',E'] =>
              Const (\<^const_syntax>\<open>\<phi>Procedure\<close>, Type("",[])) $ f $ A' $ R' $ E'))),
    (\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, (fn ctxt => fn T => fn [f,A,R] =>
       if T = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Procedure [A,R] (fn [A',R'] =>
              Const (\<^const_syntax>\<open>\<phi>Procedure_no_exception\<close>, Type("",[])) $ f $ A' $ R'))),
    (\<^const_syntax>\<open>View_Shift\<close>, (fn ctxt => fn TY => fn [S,T,P] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.View_Shift [S,T] (fn [S',T',P] =>
              Const (\<^const_syntax>\<open>View_Shift\<close>, Type("",[])) $ S' $ T' $ P))),
    (\<^const_syntax>\<open>Simple_View_Shift\<close>, (fn ctxt => fn TY => fn [S,T] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.View_Shift [S,T] (fn [S',T'] =>
              Const (\<^const_syntax>\<open>Simple_View_Shift\<close>, Type("",[])) $ S' $ T'))),
    (\<^const_syntax>\<open>Imply\<close>, (fn ctxt => fn TY => fn [S,T,P] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Implication [S,T] (fn [S',T'] =>
              Const (\<^const_syntax>\<open>Imply\<close>, Type("",[])) $ S' $ T' $ P))),
    (\<^const_syntax>\<open>SimpleImply\<close>, (fn ctxt => fn TY => fn [S,T] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Implication [S,T] (fn [S',T'] =>
              Const (\<^const_syntax>\<open>SimpleImply\<close>, Type("",[])) $ S' $ T'))),
    (\<^const_syntax>\<open>CurrentConstruction\<close>, (fn ctxt => fn TY => fn [m,s,R,S] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Construction [S] (fn [S'] =>
              Const (\<^const_syntax>\<open>CurrentConstruction\<close>, Type("",[])) $ m $ s $ R $ S'))),
    (\<^const_syntax>\<open>Programming_CurrentConstruction\<close>, (fn ctxt => fn TY => fn [s,R,S] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Construction [S] (fn [S'] =>
              Const (\<^const_syntax>\<open>Programming_CurrentConstruction\<close>, Type("",[])) $ s $ R $ S'))),
    (\<^const_syntax>\<open>View_Shift_CurrentConstruction\<close>, (fn ctxt => fn TY => fn [s,R,S] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Construction [S] (fn [S'] =>
              Const (\<^const_syntax>\<open>View_Shift_CurrentConstruction\<close>, Type("",[])) $ s $ R $ S'))),
    (\<^const_syntax>\<open>PendingConstruction\<close>, (fn ctxt => fn TY => fn [f,s,R,S,E] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Construction [S,E] (fn [S',E'] =>
              Const (\<^const_syntax>\<open>PendingConstruction\<close>, Type("",[])) $ f $ s $ R $ S' $ E'))),
    (\<^const_syntax>\<open>ToA_Construction\<close>, (fn ctxt => fn TY => fn [s,S] =>
       if TY = Type("",[]) then raise Match (*A trick to prevent infinite loop*)
       else may_translation ctxt Phi_Kind.Construction [S] (fn [S'] =>
              Const (\<^const_syntax>\<open>ToA_Construction\<close>, Type("",[])) $ s $ S')))
])

end