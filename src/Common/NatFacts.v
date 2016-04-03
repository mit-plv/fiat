Require Import Coq.omega.Omega.

Section NatFacts.
  Lemma le_r_le_max :
    forall x y z,
      x <= z -> x <= max y z.
  Proof.
    intros x y z;
    destruct (Max.max_spec y z) as [ (comp, eq) | (comp, eq) ];
    rewrite eq;
    omega.
  Qed.

  Lemma le_l_le_max :
    forall x y z,
      x <= y -> x <= max y z.
  Proof.
    intros x y z.
    rewrite Max.max_comm.
    apply le_r_le_max.
  Qed.

  Lemma le_neq_impl :
    forall m n, m < n -> m <> n.
  Proof.
    intros; omega.
  Qed.

  Lemma gt_neq_impl :
    forall m n, m > n -> m <> n.
  Proof.
    intros; omega.
  Qed.

  Lemma lt_refl_False :
    forall x,
      lt x x -> False.
  Proof.
    intros; omega.
  Qed.

  Lemma beq_nat_eq_nat_dec :
    forall x y,
      beq_nat x y = if eq_nat_dec x y then true else false.
  Proof.
    intros; destruct (eq_nat_dec _ _); [ apply beq_nat_true_iff | apply beq_nat_false_iff ]; assumption.
  Qed.

  Lemma min_minus_l x y
  : min (x - y) x = x - y.
  Proof. apply Min.min_case_strong; omega. Qed.
  Lemma min_minus_r x y
  : min x (x - y) = x - y.
  Proof. apply Min.min_case_strong; omega. Qed.

  Lemma sub_twice x y : x - (x - y) = min x y.
  Proof.
    clear; apply Min.min_case_strong; intro;
    omega.
  Qed.

  Lemma minus_ge {x y : nat} (H : x - y >= x) : {x = 0} + {y = 0}.
  Proof. destruct x; [ left | right]; omega. Qed.
End NatFacts.

Fixpoint minusr (n m : nat) {struct m} : nat
  := match m with
       | 0 => n
       | S l => minusr (pred n) l
     end.

Lemma minusr_minus n m
: minusr n m = minus n m.
Proof.
  revert m; induction n; simpl;
  induction m; simpl; auto.
Qed.

Delimit Scope natr_scope with natr.
Infix "-" := minusr : natr_scope.

Module minusr_notation.
  Infix "-" := minusr : nat_scope.
End minusr_notation.

Section dec_prod.
  Local Notation dec T := (T + (T -> False))%type (only parsing).
  Context (P : nat -> Type).
  Fixpoint dec_stabalize'
             (max : nat)
             (Hstable : forall n, n >= max -> P n -> P (S n))
             (Hdec : forall n, n <= max -> dec (P n))
             {struct max}
  : dec (forall n, P n).
  Proof.
    destruct max as [|max];
    [ clear dec_stabalize' | specialize (dec_stabalize' max) ].
    { destruct (Hdec 0 (le_refl _)) as [Hd|Hd]; [ left | right ].
      { intro n.
        induction n as [|n IHn].
        { assumption. }
        { apply Hstable; [ auto with arith | assumption ]. } }
      { intro Pn; apply Hd, Pn. } }
    { destruct (Hdec (S max)) as [Hdecmax|Hdecmax];
      [ reflexivity | | right; solve [ auto with nocore ] ].
      apply dec_stabalize'.
      { intros n Hn; specialize (Hstable n).
        unfold ge in *.
        destruct (le_lt_eq_dec _ _ Hn) as [pf|npf].
        { auto with nocore. }
        { intro; subst; assumption. } }
      { intros n pf.
        apply le_S in pf.
        auto with nocore. } }
  Defined.

  Local Notation iffT A B := ((A -> B) * (B -> A))%type (only parsing).

  Fixpoint dec_stabalize
             (max : nat)
             (Hstable : forall n, n >= max -> iffT (P n) (P (S n)))
             (Hdec : forall n, n <= max -> dec (P n))
             {struct max}
  : ({ n : nat & (n <= max) * P n }%type + (forall n, P n -> False))%type.
  Proof.
    destruct max as [|max];
    [ clear dec_stabalize | specialize (dec_stabalize max) ].
    { destruct (Hdec 0 (le_refl _)) as [Hd|Hd]; [ left | right ].
      { exists 0; split; [ reflexivity | assumption ]. }
      { intros n Pn. apply Hd.
        clear -Pn Hstable.
        specialize (fun n => Hstable n (le_0_n _)).
        induction n; [ assumption  | apply IHn ].
        apply Hstable; assumption. } }
    { destruct (Hdec (S max)) as [HdecSmax|HdecSmax];
      [ reflexivity | | ].
      { left; eexists; split; [ reflexivity | eassumption ]. }
      { destruct (Hdec max) as [Hdecmax|Hdecmax];
        [ solve [ auto with arith ] | | ].
        { left; eexists; split; [ | eassumption ]; auto with arith. }
        { destruct dec_stabalize as [[n [??]]|];
          [
          |
          | left; exists n; split; [ solve [ auto with arith ] | assumption ]
          | right; assumption ].
          { intros n Hn.
            destruct (le_lt_eq_dec _ _ Hn) as [pf|npf].
            pose proof (Hstable n).
            unfold ge in *.
            { auto with nocore. }
            { split; intro; subst;
              exfalso; eauto with nocore. } }
          { intros n pf.
            apply le_S in pf.
            auto with nocore. } } } }
  Defined.
End dec_prod.

Lemma nat_rect3_ext
       {A B C D}
       (P := fun n => forall (a : A n) (b : B n a), C n a b -> D)
       (z z' : P 0)
       (Hz : forall a b c, z a b c = z' a b c)
       (s s' : forall n, P n -> P (S n))
       (Hs : forall n f g (pf : forall a b c, f a b c = g a b c) a b c,
               s n f a b c = s' n g a b c)
       n a b c
: nat_rect P z s n a b c = nat_rect P z' s' n a b c.
Proof.
  revert a b c; induction n as [|n IHn]; simpl; intros.
  { apply Hz. }
  { apply Hs; intros.
    apply IHn. }
Qed.

Lemma minus_plus_min x y
: x - y + min y x = x.
Proof.
  apply Min.min_case_strong; omega.
Qed.

Lemma min_case_strong_r n m (P : nat -> Type)
: (n <= m -> P n) -> (m < n -> P m) -> P (min n m).
Proof.
  destruct (Compare_dec.le_lt_dec n m);
  first [ rewrite Min.min_r by omega
        | rewrite Min.min_l by omega ];
  auto.
Qed.

Lemma min_case_strong_l n m (P : nat -> Type)
: (n < m -> P n) -> (m <= n -> P m) -> P (min n m).
Proof.
  destruct (Compare_dec.le_lt_dec m n);
  first [ rewrite Min.min_r by omega
        | rewrite Min.min_l by omega ];
  auto.
Qed.

Lemma beq_0_1_leb x
: (EqNat.beq_nat x 1 || EqNat.beq_nat x 0)%bool = Compare_dec.leb x 1.
Proof.
  destruct x as [|[|]]; simpl; reflexivity.
Qed.

Lemma beq_S_leb x n
: (EqNat.beq_nat x (S n) || Compare_dec.leb x n)%bool = Compare_dec.leb x (S n).
Proof.
  revert x; induction n as [|n IHn]; simpl.
  { intros [|[|]]; reflexivity. }
  { intros [|x]; [ reflexivity | apply IHn ]. }
Qed.

Lemma min_max_sub {a x f}
  : min a (x - f) = x - (max (x - a) f).
Proof.
  apply Min.min_case_strong; apply Max.max_case_strong; omega.
Qed.
