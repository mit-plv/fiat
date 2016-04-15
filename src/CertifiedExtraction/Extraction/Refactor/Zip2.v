Require Import List.

Fixpoint zip2 {A1 A2} (aa1: list A1) (aa2: list A2) :=
  match aa1, aa2 with
  | nil, _ => nil
  | _, nil => nil
  | ha1 :: ta1, ha2 :: ta2 => (ha1, ha2) :: (zip2 ta1 ta2)
  end.

Definition map2 {A1 A2 B} (f: A1 -> A2 -> B) aa1 aa2 :=
  map (fun pair => f (fst pair) (snd pair)) (zip2 aa1 aa2).

Ltac map_length_t :=
  repeat match goal with
         | [ H: cons _ _ = cons _ _ |- _ ] => inversion H; subst; clear H
         | [ H: S _ = S _ |- _ ] => inversion H; subst; clear H
         | _ => progress simpl in *; intros
         | _ => discriminate
         | _ => try f_equal; firstorder
         end.

Lemma map_map_sameLength {A1 A2 B}:
  forall {f g aa1 aa2},
    @map A1 B f aa1 = @map A2 B g aa2 ->
    Datatypes.length aa1 = Datatypes.length aa2.
Proof.
  induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map_snd_zip2 {A1 A2}:
  forall {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    map (@snd A1 A2) (@zip2 A1 A2 aa1 aa2) = aa2.
Proof.
  induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map_fst_zip2' {A1 A2 B}:
  forall {f: _ -> B} {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    map (fun x => f (fst x)) (@zip2 A1 A2 aa1 aa2) = map f aa1.
Proof.
  induction aa1; destruct aa2; map_length_t.
Qed.

Lemma in_zip2 :
  forall {A B} a b aa bb,
    In (a, b) (@zip2 A B aa bb) ->
    (In a aa /\ In b bb).
Proof. (* This lemma is weak *)
  induction aa; destruct bb;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         | [ aa: list ?a, H: forall _: list ?a, _ |- _ ] => specialize (H aa)
         end.
Qed.

Lemma in_zip2_map :
  forall {A B A' B'} fa fb a b aa bb,
    In (a, b) (@zip2 A B aa bb) ->
    In (fa a, fb b) (@zip2 A' B'  (map fa aa) (map fb bb)).
Proof.
  induction aa; destruct bb;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         end.
Qed.


Lemma zip2_maps_same :
  forall {A A' B'} fa fb aa,
    (@zip2 A' B' (@map A A' fa aa) (map fb aa)) =
    map (fun x => (fa x, fb x)) aa.
Proof.
  induction aa;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         end.
Qed.

Lemma map2_two_maps:
  forall {A B A' B' C} fa fb g aa bb,
    @map2 A B C (fun a b => g (fa a) (fb b)) aa bb =
    @map2 A' B' C (fun a b => g a b) (map fa aa) (map fb bb).
Proof.
  unfold map2;
  induction aa; destruct bb;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         | [ aa: list ?a, H: forall _: list ?a, _ |- _ ] => specialize (H aa)
         end.
Qed.

Lemma map2_snd {A1 A2}:
  forall {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    @map2 A1 A2 _ (fun x y => y) aa1 aa2 = aa2.
Proof.
  unfold map2; induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map2_fst {A1 A2}:
  forall {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    @map2 A1 A2 _ (fun x y => x) aa1 aa2 = aa1.
Proof.
  unfold map2; induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map2_fst' {A1 A2 B}:
  forall {aa1 aa2} f,
    Datatypes.length aa1 = Datatypes.length aa2 ->
    @map2 A1 A2 B (fun x y => f x) aa1 aa2 = map f aa1.
Proof.
  unfold map2; induction aa1; destruct aa2; map_length_t.
Qed.

Lemma two_maps_map2 :
  forall {A A1 A2 B} f1 f2 f aa,
    (@map2 A1 A2 B f (@map A _ f1 aa) (@map A _ f2 aa)) =
    map (fun x => f (f1 x) (f2 x)) aa.
Proof.
  intros; unfold map2; rewrite zip2_maps_same, map_map; reflexivity.
Qed.

Require Import Program.

Lemma in_zip2_map_map_eq :
  forall {A B A' fa fb a b aa bb},
    @map A A' fa aa = @map B A' fb bb ->
    In (a, b) (@zip2 A B aa bb) ->
    fa a = fb b.
Proof.
  intros;
  match goal with
  | [ H: map ?f ?l = map ?g ?l', H': In _ (zip2 ?l ?l') |- _ ] =>
    apply (in_zip2_map f g) in H';
      rewrite <- H, zip2_maps_same, in_map_iff in H';
      firstorder congruence
  end.
Qed.

