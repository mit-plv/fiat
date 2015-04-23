Require Import Coq.Arith.Compare_dec Omega
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations.

Section RangeClause.  
  Definition InRange (n : nat) (range : nat * nat) :=
    (fst range) <= n <= (snd range).

  Definition InRange_dec (n : nat) (range : nat * nat)
  : {InRange n range} + {~ InRange n range}.
    refine (
        if le_dec (fst range) n then
          if le_dec n (snd range) then
            left _
          else
            right _
        else
          right _); unfold InRange in *; intuition eauto.
  Defined.

  Global Instance DecideableEnsemble_InRange st :
    DecideableEnsemble (fun a => InRange a st) :=
    {| dec a := ?[InRange_dec a st] |}.
  Proof.
    intros; destruct (InRange_dec a st); intuition eauto; discriminate.
  Defined.

  Global Instance DecideableEnsemble_InRange_f
         (A : Type)
         (f : A -> nat)
         b :
    DecideableEnsemble (fun a => InRange (f a) b) :=
    {| dec a := ?[InRange_dec (f a) b ] |}.
  Proof.
    intros; destruct (InRange_dec (f a) b); intuition eauto; discriminate.
  Defined.
End RangeClause.