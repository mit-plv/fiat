Require Import Fiat.ADTRefinement.GeneralPreBuildADTRefinements.
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
    { Def Constructor1 "new" (s: string) : rep :=
        ret (fnew s),
      Def Method0 "to_string" (s : rep) : rep * string :=
        ret (fto_string s),
      Def Method1 "is_char" (s : rep) (ch : Ascii.ascii) : rep * bool :=
        ret (fis_char s ch),
      Def Method1 "get" (s : rep) (n : nat) : rep * (option Ascii.ascii) :=
        ret (fget s n),
      Def Method0 "length" (s : rep) : rep * nat :=
        ret (flength s),
      Def Method1 "take" (s : rep) (n : nat) : rep * unit :=
        ret (ftake s n),
      Def Method1 "drop" (s : rep) (n : nat) : rep * unit :=
        ret (fdrop s n),
      Def Method2 "splits" (s : rep) (i : item Ascii.ascii) (p : production Ascii.ascii) :
      rep * (list nat) :=
        ret (fsplits s i p) })%ADTParsing
   (ComputationalADT.LiftcADT e) }.
Proof.
  eexists.
  simpl; finish_SharpeningADT_WithoutDelegation.
Defined.

Definition finish_Sharpening_SplitterADT
           {repT fnew fto_string fis_char fget flength ftake fdrop fsplits}
: Sharpened _
  := projT2 (@finish_Sharpening_SplitterADT'
               repT fnew fto_string fis_char fget flength ftake fdrop fsplits).
