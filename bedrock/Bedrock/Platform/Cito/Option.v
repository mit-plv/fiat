Set Implicit Arguments.

Definition default A def (x : option A) :=
  match x with
    | Some v => v
    | None => def
  end.

Definition option_dec A (x : option A) : {a | x = Some a} + {x = None}.
  destruct x.
  left.
  exists a.
  eauto.
  right.
  eauto.
Qed.

Lemma option_map_some_elim A B (f : A -> B) o b : option_map f o = Some b -> exists a, o = Some a /\ f a = b.
Proof.
  intros H.
  destruct (option_dec o) as [[a Ha]| Hn]; [rewrite Ha in H | rewrite Hn in H; discriminate]; simpl in *.
  injection H; intros; subst.
  exists a; eauto.
Qed.

Lemma option_map_some_intro A B (f : A -> B) o a b : o = Some a -> b = f a -> option_map f o = Some b.
Proof.
  intros Ho Hb.
  destruct (option_dec o) as [[a' Ha]| Hn]; [rewrite Ha in * | rewrite Hn in *; discriminate]; simpl in *.
  injection Ho; intros; subst.
  eauto.
Qed.
