Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.ZArith.ZArith
        Coq.Lists.List
        Fiat.Common.DecideableEnsembles
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation
        Bedrock.Word.

(* Decision procedures for propositions that crop up during
synthesis.*)

Lemma decides_True'
  : decides true True.
Proof.
  simpl; intros; exact I.
Qed.

Definition pair_eq_dec {A B}
           (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
           (B_eq_dec : forall a a' : B, {a = a'} + {a <> a'})
  : forall a a' : A * B, {a = a'} + {a <> a'}.
Proof.
  refine (fun a a' => match A_eq_dec (fst a) (fst a'), B_eq_dec (snd a) (snd a') with
                      | left _, left _ => _
                      | _, _ => _
                      end);
    decide equality.
Defined.

Definition decides_pair_eq {A B}
           (t : A -> A -> bool)
           (t' : B -> B -> bool)
           (decides_t : forall a a' : A , decides (t a a') (a = a'))
           (decides_t' : forall b b' : B , decides (t' b b') (b = b'))
  : forall ab ab' : A * B,
    decides (andb (t (fst ab) (fst ab')) (t' (snd ab) (snd ab'))) (ab = ab').
Proof.
  destruct ab; destruct ab'; simpl in *.
  pose proof (decides_t a a0);   pose proof (decides_t' b b0);
    unfold decides, If_Then_Else in *.
  destruct (t a a0);  destruct (t' b b0); simpl in *; congruence.
Qed.

Lemma decides_nat_eq :
  forall (n n' : nat),
    decides (EqNat.beq_nat n n') (n = n').
Proof.
  unfold decides, If_Then_Else; intros.
  destruct (EqNat.beq_nat n n') eqn: ? ;
    try eapply EqNat.beq_nat_true_iff;
    try eapply EqNat.beq_nat_false_iff; eauto.
Qed.

Lemma decides_word_eq {sz}:
  forall (w w' : word sz),
    decides (weqb w w') (w = w').
Proof.
  unfold decides, If_Then_Else; intros.
  destruct (weqb w w') eqn: ? ;
    unfold not; setoid_rewrite <- weqb_true_iff; congruence.
Qed.

Lemma decides_bool_eq :
  forall (b b' : bool),
    decides (eqb b b') (b = b').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct b; destruct b'; simpl; congruence.
Qed.

Lemma decides_unit_eq :
  forall (b b' : unit),
    decides true (b = b').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct b; destruct b'; simpl; congruence.
Qed.

Lemma decides_string_eq :
  forall (s s' : string),
    decides (String.eqb s s') (s = s').
Proof.
  unfold decides, If_Then_Else; intros.
  destruct (s =? s')%string eqn:?.
  eapply String.eqb_eq; eauto.
  eapply String.eqb_neq; eauto.
Qed.

Lemma decides_Fin_eq {n} :
  forall (b b' : Fin.t n),
    decides (fin_eq_dec b b') (b = b').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct (fin_eq_dec b b'); simpl; congruence.
Qed.

Lemma decides_EnumType_eq {A} {n} {tags} :
  forall (b b' : @EnumType n A tags),
    decides (fin_beq b b') (b = b').
Proof.
  unfold decides, If_Then_Else; intros.
  destruct (fin_beq b b') eqn: H' ;
    unfold not; intros;
      try rewrite fin_beq_dec in H';
      try rewrite fin_beq_neq_dec in H'; eauto.
Qed.

Lemma firstn_app {A}
  : forall (l1 l2 : list A),
    firstn (length l1) (l1 ++ l2) = l1.
Proof.
  induction l1; intros; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma decides_firstn_app {A}
  : forall (l1 l2 : list A),
    decides true (firstn (length l1) (l1 ++ l2) = l1).
Proof.
  apply firstn_app.
Qed.

Lemma firstn_self {A}
  : forall (l1 : list A),
    firstn (length l1) l1 = l1.
Proof.
  induction l1; intros; simpl; eauto.
  f_equal; eauto.
Qed.

Lemma decides_firstn_self {A}
  : forall (l1 : list A),
    decides true (firstn (length l1) l1 = l1).
Proof.
  intros; apply firstn_self.
Qed.

Lemma skipn_app {A}
  : forall (l1 l2 : list A),
    skipn (length l1) (l1 ++ l2) = l2.
Proof.
  induction l1; intros; simpl; eauto.
Qed.

Lemma decides_skipn_app {A}
  : forall (l1 l2 : list A),
    decides true (skipn (length l1) (l1 ++ l2) = l2).
Proof.
  apply skipn_app.
Qed.

Lemma firstn_skipn_app {A}
  : forall (l1 l2 l3 : list A),
    firstn (length l3) (skipn (length l1 + length l2) (l1 ++ l2 ++ l3)) = l3.
Proof.
  simpl; intros.
  rewrite <- app_length, List.app_assoc, skipn_app.
  apply firstn_self.
Qed.

Lemma decides_firstn_skipn_app {A}
  : forall (l1 l2 l3 : list A),
    decides true (firstn (length l3) (skipn (length l1 + length l2) (l1 ++ l2 ++ l3)) = l3).
Proof.
  intros; apply firstn_skipn_app.
Qed.

Lemma firstn_skipn_self' {A}
  : forall (n m o : nat) (l : list A),
    length l = n + m + o
    -> (firstn n l ++ firstn m (skipn n l) ++ firstn o (skipn (n + m) l))%list =
       l.
Proof.
  induction n; simpl.
  induction m; simpl; eauto.
  induction o; simpl.
  destruct l; simpl; eauto.
  intros; discriminate.
  destruct l; simpl; eauto.
  intros; f_equal; eauto.
  destruct l; simpl.
  intros; discriminate.
  intros; f_equal; eauto.
  destruct l; simpl.
  intros; discriminate.
  intros; f_equal; eauto.
Qed.

Lemma firstn_skipn_self'' {A}
  : forall (n m o : nat) (l : list A),
    length l = n + m + o
    ->
    decides true ((firstn n l ++ firstn m (skipn n l) ++ firstn o (skipn (n + m) l))%list =
                  l).
Proof.
  intros; eapply firstn_skipn_self'.
  Lia.lia.
Qed.

Lemma word_eq_self
  : forall (w : word 1),
    decides true (WS (whd w) WO = w).
Proof.
  simpl; intros; shatter_word w; reflexivity.
Qed.

Lemma firstn_lt_decides {A}:
  forall m n (l : list A),
    (lt m n)%nat
    -> decides true (lt (length (firstn m l)) n)%nat.
Proof.
  simpl; intros; rewrite firstn_length.
  eapply NPeano.Nat.min_lt_iff; eauto.
Qed.

Lemma whd_word_1_refl' :
  forall (b : word 1),
    decides true (WS (whd b) WO = b).
Proof.
  intros; destruct (shatter_word_S b) as [? [? ?] ]; subst.
  rewrite (shatter_word_0 x0); reflexivity.
Qed.

Lemma length_firstn_skipn_app {A}
  : forall (n m o : nat) (l : list A),
    length l = n + m + o
    -> (length (firstn m (skipn n l) )) = m.
Proof.
  induction n; simpl.
  induction m; simpl; eauto.
  induction o; simpl.
  destruct l; simpl; eauto.
  intros; discriminate.
  destruct l; simpl; eauto.
  intros; discriminate.
  intros; f_equal; eauto.
  destruct l; simpl.
  intros; discriminate.
  intros; f_equal; eauto.
Qed.


Lemma decides_length_firstn_skipn_app {A}
  : forall (n m o : nat) (l : list A),
    length l = n + (m + o)
    -> decides true (length (firstn m (skipn n l) ) = m).
Proof.
  intros.
  rewrite length_firstn_skipn_app with (o0 := o);
    simpl; Lia.lia.
Qed.

Lemma length_firstn_skipn_app' {A}
  : forall (n m o : nat) (l : list A),
    length l = n + m + o
    -> length (firstn o (skipn (n + m) l)) = o.
Proof.
  induction n; simpl.
  induction m; simpl; eauto.
  induction o; simpl.
  destruct l; simpl; eauto.
  destruct l; simpl; eauto.
  destruct l; simpl; eauto.
  intros; discriminate.
  intros; f_equal; eauto.
  destruct l; simpl.
  intros; discriminate.
  intros; f_equal; eauto.
Qed.


Lemma decides_length_firstn_skipn_app' {A}
  : forall (n m o : nat) (l : list A),
    length l = n + (m + o)
    -> decides true (length (firstn o (skipn (n + m) l) ) = o).
Proof.
  intros; rewrite length_firstn_skipn_app'; simpl; Lia.lia.
Qed.

Lemma length_firstn_skipn_app'' {A}
  : forall (n m o : nat) (l : list A),
    length l = n + m + o
    -> length (firstn n l) = n.
Proof.
  induction n; destruct l; simpl; intros;
    try discriminate; eauto.
Qed.

Lemma decides_length_firstn_skipn_app'' {A}
  : forall (n m o : nat) (l : list A),
    length l = n + (m + o)
    -> decides true (length (firstn n l ) = n).
Proof.
  intros; erewrite length_firstn_skipn_app'' with (o0 := o) (m0 := m);
    simpl; Lia.lia.
Qed.

Lemma lt_1_pow2_16
  : lt 1 (pow2 16).
Proof.
  intros.
  rewrite <- (wordToNat_natToWord_idempotent 16 1).
  eapply wordToNat_bound.
  simpl; eapply BinNat.N.ltb_lt; reflexivity.
Qed.

Lemma decides_Option_eq_None {B}
  : forall (s_opt : option B) b,
    (Ifopt s_opt as _ Then true Else false) = b
    -> decides (negb b) (s_opt = None).
Proof.
  intros; destruct s_opt; simpl in *; subst;
    simpl in *; congruence.
Qed.

Lemma firstn_skipn_self {A}
  : forall (n m o : nat) (l l1 l2 l3 : list A),
    (l1 ++ l2 ++ l3)%list = l ->
    length l1 = n ->
    length l2 = m ->
    length l3 = o ->
    l1 = firstn n l
    /\ l2 = firstn m (skipn n l)
    /\ l3 = firstn o (skipn (n + m) l).
Proof.
  intros; subst; intuition;
    eauto using firstn_skipn_app, skipn_app, firstn_app.
  rewrite skipn_app; symmetry; apply firstn_app.
Qed.
