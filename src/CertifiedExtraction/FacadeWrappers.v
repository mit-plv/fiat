Require Import
        CertifiedExtraction.PureUtils
        CertifiedExtraction.Core
        Bedrock.Memory.

Definition bool2w b :=
  match b with
  | true => (Word.natToWord 32 1)
  | false => (Word.natToWord 32 0)
  end.

Lemma bool2w_inj:
  forall v v' : bool, bool2w v = bool2w v' -> v = v'.
Proof.
  destruct v, v'; (discriminate || reflexivity).
Qed.

Instance FacadeWrapper_bool {T : Type} : FacadeWrapper (Value T) bool.
Proof.
  refine {| wrap v := SCA _ (bool2w v) |};
  abstract (intros * H; inversion H; eauto using bool2w_inj).
Defined.

Ltac FacadeWrapper_t_step :=
  match goal with
  | _ => cleanup_pure
  | _ => progress simpl in *
  | [ H: FacadeWrapper _ _ |- _ ] => destruct H
  | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
  | [  |- _ = _ ] => progress f_equal
  | [ H: _ = _ |- _ ] => inversion H; solve [eauto]
  | _ => solve [eauto]
  end.

Ltac FacadeWrapper_t :=
  abstract (repeat FacadeWrapper_t_step).

Instance FacadeWrapper_SCA {av} : FacadeWrapper (Value av) W.
Proof.
  refine {| wrap := SCA av;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_Self {A: Type} : FacadeWrapper A A.
Proof.
  refine {| wrap := id;
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_Left {LType RType A: Type} (_: FacadeWrapper LType A) :
  FacadeWrapper (LType + RType)%type A.
Proof.
  refine {| wrap x := inl (wrap x);
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance FacadeWrapper_Right {LType RType A: Type} (_: FacadeWrapper RType A):
  FacadeWrapper (LType + RType)%type A.
Proof.
  refine {| wrap x := inr (wrap x);
            wrap_inj := _ |}; FacadeWrapper_t.
Defined.

Instance WrapInstance `{H: FacadeWrapper av A} : `{FacadeWrapper (Value av) A}.
Proof.
  refine {| wrap := fun a => @ADT av (wrap a);
            wrap_inj := _ |};
  FacadeWrapper_t.
Defined.

Lemma WrapInstance_wrap :
  forall `{H: FacadeWrapper av A} (x: A),
    wrap x = ADT (wrap x).
Proof.
  destruct H; intros; reflexivity.
Qed.
