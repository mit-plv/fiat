Require Import
        Coq.Program.Program
        Coq.Lists.List.

Unset Implicit Arguments.

Require Import Coq.omega.Omega.

Require Import Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties.

(* Fixpoint pack_list {A} n m (seq: list A) (pack: list A) (default: A) : list (list A) := *)
(*   match n with *)
(*   | 0 => *)
(*     List.rev pack :: match seq with *)
(*                     | h :: t => pack_list n 1 t (h :: nil) default *)
(*                     | nil => nil *)
(*                     end *)
(*   | S n' => match seq with *)
(*            | h :: t => pack_list n' (S m) t (h :: pack) default *)
(*            | nil => pack_list n' (S m) nil (default :: pack) default *)
(*            end *)
(*   end. *)

Fixpoint map8 {A B} f a (seq: list A) : list B :=
  match seq with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t  => (f b0 b1 b2 b3 b4 b5 b6 b7) :: map8 f a t
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil => (f b0 b1 b2 b3 b4 b5 b6 a) :: nil
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil => (f b0 b1 b2 b3 b4 b5 a a) :: nil
  | b0 :: b1 :: b2 :: b3 :: b4 :: nil => (f b0 b1 b2 b3 b4 a a a) :: nil
  | b0 :: b1 :: b2 :: b3 :: nil => (f b0 b1 b2 b3 a a a a) :: nil
  | b0 :: b1 :: b2 :: nil => (f b0 b1 b2 a a a a a) :: nil
  | b0 :: b1 :: nil => (f b0 b1 a a a a a a) :: nil
  | b0 :: nil => (f b0 a a a a a a a) :: nil
  | nil => nil
  end.

(* Definition head8 {A B} f a (seq: list A) : list B := *)
(*   match seq with *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t  => (f b0 b1 b2 b3 b4 b5 b6 b7) :: nil *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil => (f b0 b1 b2 b3 b4 b5 b6 a) :: nil *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil => (f b0 b1 b2 b3 b4 b5 a a) :: nil *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: nil => (f b0 b1 b2 b3 b4 a a a) :: nil *)
(*   | b0 :: b1 :: b2 :: b3 :: nil => (f b0 b1 b2 b3 a a a a) :: nil *)
(*   | b0 :: b1 :: b2 :: nil => (f b0 b1 b2 a a a a a) :: nil *)
(*   | b0 :: b1 :: nil => (f b0 b1 a a a a a a) :: nil *)
(*   | b0 :: nil => (f b0 a a a a a a a) :: nil *)
(*   | nil => nil *)
(*   end. *)

(* Definition tail8 {A B} f a (seq: list A) : list B := *)
(*   match seq with *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t  => map8 f a t *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil => nil *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil => nil *)
(*   | b0 :: b1 :: b2 :: b3 :: b4 :: nil => nil *)
(*   | b0 :: b1 :: b2 :: b3 :: nil => nil *)
(*   | b0 :: b1 :: b2 :: nil => nil *)
(*   | b0 :: b1 :: nil => nil *)
(*   | b0 :: nil => nil *)
(*   | nil => nil *)
(*   end. *)

(* Lemma tail8_Array8 : *)
(*   forall  {A B} f a (seq: { s: list A | List.length s = 8}), *)
(*     tail8 (B := B) f a (`seq) = nil. *)
(* Proof. *)
(*   destruct seq as (seq & p). *)
(*   repeat (destruct seq; simpl in p; inversion p; []); reflexivity. *)
(* Qed. *)

(* Lemma map8_head_tail : *)
(*   forall {A B} f a (seq: list A), *)
(*     map8 (B := B) f a seq = (head8 f a seq) ++ tail8 f a seq. *)
(* Proof. *)
(*   do 8 (destruct seq; simpl; try reflexivity). *)
(* Qed. *)


Fixpoint map8induction {A} x (P: list A -> Prop) p0 p1 p2 p3 p4 p5 p6 p7
         (pind: forall b0 b1 b2 b3 b4 b5 b6 b7 t,
             P t -> P (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t)) :
  P x :=
  match x with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t  =>
    pind b0 b1 b2 b3 b4 b5 b6 b7 t (map8induction t P p0 p1 p2 p3 p4 p5 p6 p7 pind)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil => p7 b0 b1 b2 b3 b4 b5 b6
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil => p6 b0 b1 b2 b3 b4 b5
  | b0 :: b1 :: b2 :: b3 :: b4 :: nil => p5 b0 b1 b2 b3 b4
  | b0 :: b1 :: b2 :: b3 :: nil => p4 b0 b1 b2 b3
  | b0 :: b1 :: b2 :: nil => p3 b0 b1 b2
  | b0 :: b1 :: nil => p2 b0 b1
  | b0 :: nil => p1 b0
  | nil => p0
  end.


Lemma map8_inj {A B}:
  forall f a (v v' : {l : list A & {p : nat | Datatypes.length l = 8 * p} }),
    (forall x0 x1 x2 x3 x4 x5 x6 x7 x0' x1' x2' x3' x4' x5' x6' x7',
        f x0 x1 x2 x3 x4 x5 x6 x7 = f x0' x1' x2' x3' x4' x5' x6' x7' ->
        x0 = x0' /\ x1 = x1' /\ x2 = x2' /\ x3 = x3' /\ x4 = x4' /\ x5 = x5' /\ x6 = x6' /\ x7 = x7') ->
    (@map8 A B f a (projT1 v)) = (map8 f a (projT1 v')) ->
    v = v'.
Proof.
  intros.
  destruct v as (v & p & pr), v' as (v' & p' & pr'); simpl in *.

  cut (v = v'); intros; subst; f_equal.
  assert (p = p') by omega; subst; f_equal; auto using UipNat.UIP.

  generalize dependent v'; generalize dependent p; generalize dependent p'.
  induction v using map8induction; destruct p; intros; simpl in *; try (omega || discriminate);
    induction v' using map8induction; destruct p'; intros; simpl in *; try (omega || discriminate).
  reflexivity.
  inversion H0; apply H in H2; destruct_conjs; subst; repeat f_equal.
  eapply IHv with p' p; try omega; congruence.
Qed.

Lemma map8_length_top:
  forall {A B} f a (seq: list A),
    8 * List.length (map8 (B := B) f a seq) <= 7 + List.length seq.
Proof.
  intros; apply (map8induction seq); simpl; intros; omega.
Qed.

Lemma map8_length_bottom:
  forall {A B} f a (seq: list A),
    List.length seq <= 8 * List.length (map8 (B := B) f a seq).
Proof.
  intros; apply (map8induction seq); simpl; intros; omega.
Qed.

Lemma map8append {A B}:
  forall (bs: list A) (n: list A) f a,
    (exists p, List.length bs = 8 * p) ->
    map8 f a (bs ++ n) = map8 f a bs ++ map8 (B := B) f a n.
Proof.
  intros bs; apply (map8induction bs); [ destruct 1; simpl in *; intros; (reflexivity || omega).. | ].
  - simpl; intros; rewrite H; try apply eq_refl.
    destruct H0; destruct x; try omega.
    exists x; omega.
Qed.
