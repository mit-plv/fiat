Require Import Coq.Arith.Compare_dec Omega
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations.

Section RangeClause.
  Definition InRange (n : nat) (range : (option nat) * (option nat)) :=
    match range with
      | (None        , None        ) => True
      | (Some min_key, None        ) => min_key <= n
      | (None        , Some max_key) => n <= max_key
      | (Some min_key, Some max_key) => min_key <= n <= max_key
    end.

  Definition InRange_dec (n : nat) (range : option nat * option nat)
  : {InRange n range} + {~ InRange n range}.
    refine (
        match range with
          | (None        , None        ) =>
            left _
          | (Some min_key, None        ) =>
            if le_dec min_key n then
              left _
            else
              right _
          | (None        , Some max_key) =>
            if le_dec n max_key then
              left _
            else
              right _
          | (Some min_key, Some max_key) =>
            if le_dec min_key n then
              if le_dec n max_key then
                left _
              else
                right _
            else
              right _
        end); unfold InRange in *; intuition eauto.
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