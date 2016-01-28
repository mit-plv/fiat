(** * Common facts about UIP and proof irrelevance *)
Require Coq.Strings.String.
Require Import Coq.Logic.EqdepFacts.

Set Implicit Arguments.

Lemma Eq_rect_eq_UIP_helper {U x y} (p : x = y :> U)
: p = match p in (_ = y) return (x = y) with eq_refl => eq_refl end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma Eq_rect_eq_UIP_ U : Eq_rect_eq U -> UIP_ U.
Proof.
  lazy; intro H.
  intros x y p1 p2.
  destruct p2.
  specialize (H x (fun y => x = y) eq_refl p1); simpl in *.
  rewrite <- Eq_rect_eq_UIP_helper in H.
  symmetry; assumption.
Qed.

Definition dec_eq_adjust' {U x} (p : forall y : U, {x = y} + {x <> y}) y
: {x = y} + {x <> y}
  := match p x, p y with
       | left pf, left pf' => left (eq_trans (eq_sym pf) pf')
       | right pf, _ => match pf eq_refl with end
       | _, right pf => right pf
     end.

Lemma concat_Vp {U x y} (p : x = y :> U)
: eq_trans (eq_sym p) p = eq_refl.
Proof.
  destruct p; reflexivity.
Defined.

Lemma dec_eq_uip' {U x y} (pf : x = y)
      (p : forall y : U, {x = y} + {x <> y})
: pf = match dec_eq_adjust' p y with
         | left pf' => pf'
         | right pf' => match pf' pf with end
       end.
Proof.
  destruct pf.
  unfold dec_eq_adjust'.
  destruct (p x) as [|n].
  { symmetry; apply concat_Vp. }
  { destruct (n eq_refl). }
Defined.

Lemma dec_eq_uip {U x}
      (dec : forall y : U, {x = y} + {x <> y})
      y
      (p q : x = y :> U)
: p = q.
Proof.
  etransitivity; [ | symmetry ].
  { apply (dec_eq_uip' _ dec). }
  { etransitivity; [ apply (dec_eq_uip' _ dec) | ].
    edestruct @dec_eq_adjust' as [|n]; try reflexivity.
    destruct (n p). }
Qed.

Ltac UIP_by_decide_equality :=
  intros; apply dec_eq_uip; repeat decide equality.

Lemma UIP_bool {x y : bool} (p q : x = y) : p = q.
Proof. UIP_by_decide_equality. Qed.
Lemma UIP_unit {x y : unit} (p q : x = y) : p = q.
Proof. UIP_by_decide_equality. Qed.
Lemma UIP_ascii {x y : Ascii.ascii} (p q : x = y) : p = q.
Proof. UIP_by_decide_equality. Qed.
Lemma UIP_string {x y : String.string} (p q : x = y) : p = q.
Proof. UIP_by_decide_equality. Qed.
