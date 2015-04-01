(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.ParserADTSpecification.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Equality.
Require Import ADTSynthesis.ADTRefinement.
Require Import ADTSynthesis.Common.StringBound ADTSynthesis.Common.ilist.
Require Import ADTRefinement.BuildADTRefinements.HoneRepresentation.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section IndexedImpl.
  Context (G : grammar Ascii.ascii).

  Local Notation T := (String.string * (nat * nat))%type (only parsing).

  (** Reference implementation of a [String] that can be split; has a [string], and a start index, and a length *)
  Definition indexed_spec : ADT (string_rep Ascii.ascii) := ADTRep T {
    Def Constructor "new"(s : String.string) : rep :=
      ret (s, (0, String.length s)),

    Def Method "to_string"(s : rep, x : unit) : String.string :=
      ret (s, substring (fst (snd s)) (snd (snd s)) (fst s)),

    Def Method "is_char"(s : rep, ch : Ascii.ascii) : bool  :=
      ret (s, ((Nat.eq_dec (min (String.length (fst s) - fst (snd s)) (snd (snd s))) 1) && (option_dec Ascii.ascii_dec (String.get (fst (snd s)) (fst s)) (Some ch)))%bool),

    Def Method "length"(s : rep, x : unit) : nat :=
      ret (s, min (String.length (fst s) - fst (snd s)) (snd (snd s))),

    Def Method "take"(s : rep, n : nat) : unit :=
      ret ((fst s, (fst (snd s), min (snd (snd s)) n)), tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret ((fst s, (fst (snd s) + n, snd (snd s) - n)), tt),

    Def Method "splits"(s : rep, p : item Ascii.ascii * production Ascii.ascii) : list nat :=
      ls <- { ls : list nat | split_list_is_complete G (substring (fst (snd s)) (snd (snd s)) (fst s)) (fst p) (snd p) ls };
      ret (s, ls)
  }.

  Require Import ADTSynthesis.Common.IterateBoundedIndex.

  Lemma FirstStep
  : refineADT (string_spec G) indexed_spec.
  Proof.
    econstructor 1 with (AbsR := (fun r_o r_n =>
                                    substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o));
    eapply Iterate_Ensemble_BoundedIndex_equiv;
    simpl; unfold Ensemble_BoundedIndex_app_comm_cons;
    simpl; intuition; intros; try simplify with monad laws.
  Admitted.

  Lemma AllTheSteps
  : Sharpened (string_spec G).
    eapply SharpenStep.
    apply FirstStep.


  (** now I want to show that indexed_spec refines string_spec *)

End IndexedImpl.
