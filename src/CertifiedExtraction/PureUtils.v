Ltac head_constant expr :=
  match expr with
  | ?f _ => head_constant f
  | ?f => f
  end.

Ltac no_duplicates :=
  match goal with
  | [ H: ?P, H': ?P' |- _ ] =>
    match type of P with
    | Prop => unify P P'; fail 2 "Duplicates found:" H "and" H' ":" P
    | _ => fail
    end
  | _ => idtac
  end.

Ltac deduplicate :=
  repeat match goal with
         | [ H: ?P, H': ?P' |- _ ] =>
           match type of P with
           | Prop => unify P P'; clear H' (* Fixme don't set evars? *)
           | _ => fail
           end
         | _ => idtac
         end.

Inductive Learnt {A: Type} (a: A) :=
  | AlreadyKnown : Learnt a.

Ltac learn fact :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] => fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
        lazymatch goal with
        | [ H: @Learnt type _ |- _ ] => fail 0 "fact" fact "of type" type "was already learnt through" H
        | _ => pose proof (AlreadyKnown fact); pose proof fact
        end
  end.

Ltac may_touch H :=
  match type of H with
  | Learnt _ => fail 1
  | _ => idtac
  end.

Ltac is_dec term :=
  match type of term with
  | {?p} + {?q}  => idtac
  end.

Lemma push_if :
  forall {A B} (f: A -> B) (x y: A) (b: bool),
    f (if b then x else y) = (if b then f x else f y).
Proof.
  intros; destruct b; reflexivity.
Qed.

Ltac unfold_and_subst :=       (* Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3259 *)
  repeat match goal with
         | [ H := _ |- _ ] => progress (unfold H in *; clear H)
         end; subst.

Definition dec2bool {P Q} (dec: {P} + {Q}) :=
  if dec then true else false.

Lemma dec2bool_correct {P Q A} :
  forall (dec: {P} + {Q}) (tp fp: A),
    (if dec then tp else fp) = if (dec2bool dec) then tp else fp.
Proof.
  intros; destruct dec; reflexivity.
Qed.

Lemma Some_neq :
  forall A (x y: A),
    Some x <> Some y <-> x <> y.
Proof.
  split; red; intros ** H; subst; try inversion H; intuition eauto.
Qed.

Ltac cleanup_pure :=
  match goal with
  | _ => tauto
  | _ => discriminate
  | _ => progress intros
  | _ => progress subst
  | [ |- ?a <-> ?b ] => split
  | [  |- ?a /\ ?b ] => split
  | [ H: ?a /\ ?b |- _ ] => destruct H
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: Some _ <> Some _ |- _ ] => rewrite Some_neq in H
  end.

Ltac not_match_p constr :=
  match constr with
  | context[match _ with _ => _ end] => fail 1
  | _ => idtac
  end.
