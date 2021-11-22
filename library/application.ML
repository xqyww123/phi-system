signature NU_APPLICATION = sig

  val apply_proc_naive : thm (*proc*) -> thm (*meta or major*) -> thm

  type application_thm = {
    thm : thm, (* the application theorem *)
    fee : int, (* cost of the application. the reasoner tries minimal cost first. *)
    applicant_idx : int (* index of the applicant (e.g. the procedure to be called)
                         * among premises of the application theorem. *)
  }

  val update : application_thm -> Context.generic -> Context.generic
  val apply : Proof.context -> thm list (*applicant*) -> thm (*major theorem*) -> thm Seq.seq

end

structure NuApply : NU_APPLICATION = struct
open NuHelp NuBasics

val expand_appliant = 
  repeate (fn th => th RS @{thm spec}) #>
  repeate (fn th => th RS @{thm mp}) #>
  repeate (fn th => th RS @{thm spec})

val thm_apply_proc = @{thm apply_proc}
fun apply_proc_naive proc =
  map_major (fn major => expand_appliant proc RS (major RS thm_apply_proc))

type application_thm = {
  thm : thm,
  fee : int,
  applicant_idx : int
}
type fee = int
type applicant_idx = int

val appl_ord = prod_ord int_ord thm_ord
structure Apptab = Table(type key = (fee * thm) val ord = appl_ord);

structure ApThms = Generic_Data
(
  type T = applicant_idx Apptab.table;
  val empty: T = Apptab.empty;
  val extend = I;
  val merge : T * T -> T = Apptab.merge (op =);
);

fun update {thm, fee, applicant_idx}
      = ApThms.map (Apptab.update ((fee,thm),applicant_idx))

fun biresolution_N thas thb i =
  biresolution NONE false (map (pair false) thas) i thb

fun apply ctx applicants major =
  let
    val applicants = map expand_appliant applicants
    fun apply' ((_,appl),idx) =
      Seq.make (fn () =>
        biresolution_N applicants (major RS appl) idx
          |> Seq.map (fn th =>
                Goal.protect (idx - 1) (solve_constraints th))
          |> Seq.pull)
  in
    (Apptab.dest (ApThms.get (Context.Proof ctx))
      |> map apply'
      |> fold_rev Seq.append
    ) Seq.empty
  end

end
