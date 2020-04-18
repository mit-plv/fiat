(* Axiomatic Specification *)

Set Implicit Arguments.

Section ADTSection.

  Variable ADTValue : Type.

  Require Import Bedrock.Memory.

  Inductive Value :=
  | SCA : W -> Value
  | ADT : ADTValue -> Value.

  Fixpoint is_same_type (a b : Value) :=
    match a, b with
      | ADT _, ADT _ => true
      | SCA _, SCA _ => true
      | _, _ => false
    end.

  Require Import Bedrock.Platform.Cito.ListFacts1.

  Definition is_same_types := forall2 is_same_type.

  (* type_conforming precond : any n-length input list satisfying precond must conform to a n-length type signature. But inputs of different lengths can have different type signatures ('type' means ADT vs. scalar).
     This requirement is necessary for semantic-preserving compilation into Cito, which can nondeterministically interpret the inputs to an axiomatic call either as ADTs or as scalars, where the choice of ADT/scalar may not agree with Facade's state. *)
  Definition type_conforming precond := forall inputs1 inputs2, precond inputs1 -> precond inputs2 -> length inputs1 = length inputs2 -> is_same_types inputs1 inputs2 = true.

  Record AxiomaticSpec :=
    {
      PreCond (input : list Value) : Prop;
      PostCond (input_output : list (Value * option ADTValue)) (ret : Value) : Prop;
      PreCondTypeConform : type_conforming PreCond
    }.

  (* some facts *)

  Definition same_type a b :=
    match a, b with
      | ADT _, ADT _ => True
      | SCA _, SCA _ => True
      | _, _ => False
    end.

  Lemma is_same_type_sound a b : is_same_type a b = true -> same_type a b.
  Proof.
    destruct a; destruct b; simpl in *; intuition.
  Qed.

  Definition same_types ls1 ls2 := List.Forall2 same_type ls1 ls2.

  Lemma is_same_types_sound ls1 ls2 : is_same_types ls1 ls2 = true -> same_types ls1 ls2.
  Proof.
    eapply forall2_sound; eapply is_same_type_sound.
  Qed.

  Definition is_adt (v : Value) :=
    match v with
      | ADT _ => true
      | _ => false
    end.

  Require Import Bedrock.Platform.Cito.GeneralTactics.

  Lemma is_adt_iff v : is_adt v = true <-> exists a : ADTValue, v = ADT a.
  Proof.
    destruct v as [w | a]; simpl in *.
    split; intros; openhyp; discriminate.
    intuition.
    eexists; eauto.
  Qed.

End ADTSection.

Module ConformTactic.

  (* a tactic to discharge the PreCondTypeConform condition *)
  Ltac conform := unfold type_conforming; intros; openhyp; subst; reflexivity.

  Require Import Coq.Lists.List.

  (* a test and example usage *)
  Definition test_spec ADTValue : AxiomaticSpec ADTValue.
    refine
      {|
        PreCond := fun args => exists n, args = SCA _ n :: nil;
        PostCond := fun args ret => exists n r, args = (SCA _ n, None) :: nil /\ ret = SCA _ r
      |}.
    conform.
  Defined.

End ConformTactic.
