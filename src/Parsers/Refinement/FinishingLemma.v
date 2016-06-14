Require Import Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Import Fiat.ADTNotation.BuildADT.
Require Import Fiat.ADTRefinement.
Require Import Fiat.Computation.Core.

Lemma finish_Sharpening_SplitterADT'
      {String : Type}
      {repT carrierT fnew fto_string fchar_at_matches fget flength ftake fdrop fsplits}
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
   (Def ADT
    { rep := repT,
      Def Constructor1 "new" (s: String) : rep :=
        ret (fnew s),,
      Def Method0 "to_string" (s : rep) : rep * String :=
        ret (fto_string s),
      Def Method2 "char_at_matches"(s : rep) (n : nat) (P : Ascii.ascii -> bool) : rep * bool  :=
        ret (fchar_at_matches s n P),
      Def Method1 "get" (s : rep) (n : nat) : rep * Ascii.ascii :=
        ret (fget s n),
      Def Method0 "length" (s : rep) : rep * nat :=
        ret (flength s),
      Def Method1 "take" (s : rep) (n : nat) : rep :=
        ret (ftake s n),
      Def Method1 "drop" (s : rep) (n : nat) : rep :=
        ret (fdrop s n),
      Def Method3 "splits" (s : rep) (idx : carrierT) (offset : nat) (len : nat) :
      rep * (list nat) :=
        ret (fsplits s idx offset len) })%ADTParsing
   (ComputationalADT.LiftcADT e) }.
Proof.
  eexists.
  simpl; finish_SharpeningADT_WithoutDelegation.
Defined.

Definition finish_Sharpening_SplitterADT
           {String}
           {repT carrierT fnew fto_string fchar_at_matches fget flength ftake fdrop fsplits}
: Sharpened _
  := projT2 (@finish_Sharpening_SplitterADT'
               String repT carrierT fnew fto_string fchar_at_matches fget flength ftake fdrop fsplits).
