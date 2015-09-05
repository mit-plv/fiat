Require Import Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Import Coq.Strings.String.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.ADTNotation.BuildADT.
Require Import Fiat.ADTRefinement.
Require Import Fiat.Computation.Core.
Require Import Fiat.ADTNotation.BuildADTSig.

Lemma finish_Sharpening_SplitterADT'
      {repT fnew fto_string fis_char fget flength ftake fdrop fsplits}
(*      {repT}
      {fnew : string -> repT}
      {fto_string : repT -> repT * string}
      {fis_char : repT -> Ascii.ascii -> repT * bool}
      {fget : repT -> nat -> repT * option Ascii.ascii}
      {flength : repT -> repT * nat}
      {ftake fdrop : repT -> nat -> repT * ()}
      {fsplits : repT ->
                 item Ascii.ascii * production Ascii.ascii -> repT * list nat}*)
: { e : _
  & refineADT
   (ADTRep repT
    { Def Constructor "new" (s: string) : rep :=
        ret (fnew s),
      Def Method "to_string" (s : rep, _ : unit) : string :=
        ret (fto_string s),
      Def Method "is_char" (s : rep, ch : Ascii.ascii) : bool :=
        ret (fis_char s ch),
      Def Method "get" (s : rep, n : nat) : (option Ascii.ascii) :=
        ret (fget s n),
      Def Method "length" (s : rep, _ : unit) : nat :=
        ret (flength s),
      Def Method "take" (s : rep, n : nat) : unit :=
        ret (ftake s n),
      Def Method "drop" (s : rep, n : nat) : unit :=
        ret (fdrop s n),
      Def Method "splits" (s : rep, p : (item Ascii.ascii * production Ascii.ascii)) :
      (list nat) :=
        ret (fsplits s p) })%ADT
   (ComputationalADT.LiftcADT e) }.
Proof.
  eexists.
  finish_SharpeningADT_WithoutDelegation.
Defined.

Definition finish_Sharpening_SplitterADT
           {repT fnew fto_string fis_char fget flength ftake fdrop fsplits}
: Sharpened _
  := projT2 (@finish_Sharpening_SplitterADT'
               repT fnew fto_string fis_char fget flength ftake fdrop fsplits).
