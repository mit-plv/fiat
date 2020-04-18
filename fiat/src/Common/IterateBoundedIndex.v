Require Import Coq.Arith.Arith
        Coq.Lists.List
        Coq.Sets.Ensembles
        Coq.Strings.String
        Fiat.Common
        Fiat.Common.ilist
        Fiat.Common.BoundedLookup
        Fiat.Common.DecideableEnsembles.

Fixpoint app_assoc {A : Set} (As As' As'' : list A):
  As ++ (As' ++ As'') = (As ++ As') ++ As'' :=
  match As as As return
        As ++ (As' ++ As'') = (As ++ As') ++ As'' with
    | nil => eq_refl _
    | a :: As => (f_equal (fun l => a :: l) (app_assoc As As' As''))
  end.

Lemma app_comm_cons' {A : Set}:
  forall (a : A) As As',
    As ++ (a :: As') = (As ++ (a :: nil)) ++ As'.
Proof.
  intros; rewrite <- app_assoc; reflexivity.
Defined.

Section Iterate_Ensemble.

  Record prim_and (A B : Prop) : Prop :=
    { prim_fst : A;
      prim_snd : B }.

  Local Notation "A '/\' B" := (prim_and A B).

  Fixpoint Iterate_Ensemble_BoundedIndex'
           (Remaining : nat)
           (P : Ensemble (Fin.t Remaining))
           {struct Remaining}
    : Prop :=
    match Remaining return
          Ensemble (Fin.t Remaining)
                          -> Prop with
    | 0 => fun  P => True
    | S Remaining' =>
      fun P =>
        P (@Fin.F1 Remaining')
        /\ @Iterate_Ensemble_BoundedIndex' Remaining' (fun n' => P (@Fin.FS _ n'))
    end  P.

  Lemma Iterate_Ensemble_equiv'
    : forall (Remaining  : nat)
             (P : Ensemble (Fin.t Remaining)),
      (@Iterate_Ensemble_BoundedIndex'  Remaining P ->
       forall idx, P idx).
  Proof.
    induction Remaining; simpl; intros.
    - inversion idx.
    - revert IHRemaining  P H.
      pattern Remaining, idx; apply Fin.caseS; intros.
      + intuition.
      + intuition; eapply (IHRemaining _ prim_snd0).
  Qed.

  Lemma Iterate_Ensemble_equiv''
    : forall (Remaining  : nat)
             (P : Ensemble (Fin.t Remaining)),
      (forall idx, P idx)
      -> @Iterate_Ensemble_BoundedIndex'  Remaining P.
  Proof.
    induction Remaining; simpl; intros; intuition.
  Qed.

  Definition Iterate_Ensemble_BoundedIndex
             (m : nat)
             (P : Ensemble (Fin.t m)) : Prop :=
    @Iterate_Ensemble_BoundedIndex' m P.

  Corollary Iterate_Ensemble_BoundedIndex_equiv
  : forall m
           (P : Ensemble (Fin.t m)),
      Iterate_Ensemble_BoundedIndex P <->
      forall idx, P idx.
  Proof.
    split; intros.
    eapply Iterate_Ensemble_equiv';
      eauto using string_dec; destruct n; simpl; discriminate.
    eapply Iterate_Ensemble_equiv'';
      eauto using string_dec.
  Qed.

  (* Iterating with a filter *)
  Fixpoint Iterate_Ensemble_BoundedIndex_filter'
           ( Remaining : nat)
           (filter : Fin.t Remaining -> bool)
           (P : Ensemble (Fin.t Remaining))
           {struct Remaining}
    : Prop :=
    match Remaining return
            (@Fin.t Remaining -> bool)
            -> Ensemble (Fin.t Remaining)
                          -> Prop with
    | 0 => fun  filter P => True
    | S Remaining' =>
      fun  filter P =>
        if filter (@Fin.F1 Remaining') then
          P (@Fin.F1 Remaining')
          /\ @Iterate_Ensemble_BoundedIndex_filter' Remaining'
               (fun n' => filter (@Fin.FS _ n'))
               (fun n' => P (@Fin.FS _ n'))
        else
          @Iterate_Ensemble_BoundedIndex_filter' Remaining'
            (fun n' => filter (@Fin.FS _ n'))
            (fun n' => P (@Fin.FS _ n'))
    end  filter P.

  Lemma Iterate_Ensemble_equiv_filter'
    : forall (Remaining  : nat)
             (P : Ensemble (Fin.t Remaining))
             (filter : Ensemble (Fin.t Remaining))
             (filter_dec : DecideableEnsemble filter),
      (@Iterate_Ensemble_BoundedIndex_filter'  Remaining
                                              (@dec _ _ filter_dec)
                                              P ->
       forall idx, filter idx -> P idx).
  Proof.
    induction Remaining; simpl; intros.
    - inversion idx.
    - revert IHRemaining  filter filter_dec P H H0.
      pattern Remaining, idx; apply Fin.caseS; intros.
      + apply dec_decides_P in H0; rewrite H0 in H.
        intuition.
      + assert (forall a : Fin.t n, dec (Fin.FS a) = true <-> dec (Fin.FS a)) as decOK by intuition.
        case_eq (dec Fin.F1); intros; rewrite H1 in H; intuition;
        eapply dec_decides_P in H0.
        eapply (IHRemaining (fun n' : Fin.t n => P (Fin.FS n'))
                 (fun n' : Fin.t n => dec (Fin.FS n'))
                 {| dec n' :=  dec (Fin.FS n');
                    dec_decides_P := decOK
                 |}
                 prim_snd0); eauto.
        eapply (IHRemaining (fun n' : Fin.t n => P (Fin.FS n'))
                  (fun n' : Fin.t n => dec (Fin.FS n'))
                  {| dec n' :=  dec (Fin.FS n');
                     dec_decides_P := decOK
                  |}
                  H); eauto.
  Qed.

    Lemma Iterate_Ensemble_equiv_filter''
    : forall (Remaining  : nat)
             (P : Ensemble (Fin.t Remaining))
             (filter : Ensemble (Fin.t Remaining))
             (filter_dec : DecideableEnsemble filter),
      (forall idx, filter idx -> P idx)
      -> @Iterate_Ensemble_BoundedIndex_filter'  Remaining
                                                (@dec _ _ filter_dec)
                                                P.
  Proof.
    induction Remaining; simpl; intros.
    - eauto.
    - case_eq (dec Fin.F1); intros.
      + apply dec_decides_P in H0; intuition.
        assert (forall a : Fin.t Remaining, dec (Fin.FS a) = true <-> dec (Fin.FS a)) as decOK by intuition.
        eapply (IHRemaining (fun n' : Fin.t _ => P (Fin.FS n'))
                 (fun n' : Fin.t _ => dec (Fin.FS n'))
                 {| dec n' :=  dec (Fin.FS n');
                    dec_decides_P := decOK
                 |}); eauto.
        intros; eapply H; apply dec_decides_P; eauto.
      + assert (forall a : Fin.t Remaining, dec (Fin.FS a) = true <-> dec (Fin.FS a)) as decOK by intuition.
        eapply (IHRemaining (fun n' : Fin.t _ => P (Fin.FS n'))
                 (fun n' : Fin.t _ => dec (Fin.FS n'))
                 {| dec n' :=  dec (Fin.FS n');
                    dec_decides_P := decOK
                 |}); eauto.
        intros; eapply H; apply dec_decides_P; eauto.
  Qed.

  Definition Iterate_Ensemble_BoundedIndex_filter
             (Remaining : nat)
             (P : Ensemble (Fin.t Remaining))
             (filter : Fin.t Remaining -> bool)
    : Prop :=
    @Iterate_Ensemble_BoundedIndex_filter' Remaining filter P.

  Corollary Iterate_Ensemble_BoundedIndex_filter_equiv
  : forall (Bound : nat)
           (P : Ensemble (Fin.t Bound))
           (filter : Ensemble (Fin.t Bound))
           (filter_dec : DecideableEnsemble filter),
      Iterate_Ensemble_BoundedIndex_filter P dec <->
      forall idx : Fin.t Bound, filter idx -> P idx.
  Proof.
    split; intros.
    - eapply Iterate_Ensemble_equiv_filter';
      eauto using string_dec; destruct n; simpl; discriminate.
    - eapply Iterate_Ensemble_equiv_filter'' ;
      eauto using string_dec.
  Qed.

End Iterate_Ensemble.

(* Always expand these iterations. *)
Arguments Iterate_Ensemble_BoundedIndex_filter _ _ _ / .
Arguments Iterate_Ensemble_BoundedIndex _ _ / .

Section Iterate_Dep_Type.

  Local Notation Dep_Type A := (A -> Type).

  Fixpoint Iterate_Dep_Type_BoundedIndex'
           (Remaining : nat)
           (P : Dep_Type (Fin.t Remaining))
           {struct Remaining}
    : Type :=
    match Remaining return
           Dep_Type (Fin.t Remaining)
                          -> Type with
    | 0 => fun  P => unit
    | S Remaining' =>
      fun  P =>
        prim_prod (P (@Fin.F1 Remaining'))
                  (@Iterate_Dep_Type_BoundedIndex'
                      Remaining'
                     (fun n' => P (@Fin.FS _ n')))
    end  P.

  Fixpoint Iterate_Dep_Type_equiv'
           (Remaining : nat)
           (P : Dep_Type (Fin.t Remaining))
           (H : @Iterate_Dep_Type_BoundedIndex' Remaining P)
           idx
           {struct idx}
    : P idx :=
    match idx in Fin.t n return
          forall (P : Dep_Type (Fin.t n)),
            @Iterate_Dep_Type_BoundedIndex' n P
            -> P idx with
    | Fin.F1 i => fun P H => ilist.prim_fst H
    | Fin.FS i n' =>
      fun P H =>
        Iterate_Dep_Type_equiv' (fun i => P (Fin.FS i))
                                (ilist.prim_snd H) n'
    end P H.

  Fixpoint Iterate_Dep_Type_equiv''
           (Remaining  : nat)
    : forall (P : Dep_Type (Fin.t Remaining)),
      (forall idx, P idx)
      -> @Iterate_Dep_Type_BoundedIndex' Remaining P :=
    match Remaining return
          forall (P : Dep_Type (Fin.t Remaining)),
            (forall idx, P idx)
            -> @Iterate_Dep_Type_BoundedIndex' Remaining P with
    | 0 => fun P H => tt
    | S n' =>
      fun P H =>
        Build_prim_prod (H Fin.F1)
                        (Iterate_Dep_Type_equiv'' (fun i => P (Fin.FS i))
                                                  (fun i => H (Fin.FS i)))

    end.

  Definition Iterate_Dep_Type_BoundedIndex
             (m : nat)
             (P : Dep_Type (Fin.t m)) : Type :=
    @Iterate_Dep_Type_BoundedIndex' m P.

  Corollary Lookup_Iterate_Dep_Type
  : forall m
           (P : Dep_Type (Fin.t m)),
      Iterate_Dep_Type_BoundedIndex P ->
      forall idx, P idx.
  Proof.
    intros; eapply Iterate_Dep_Type_equiv' ; eassumption.
  Defined.

  Corollary Iterate_Dep_Type_BoundedIndex_equiv2
    : forall m
             (P : Dep_Type (Fin.t m)),
      (forall idx, P idx)
      -> Iterate_Dep_Type_BoundedIndex P.
  Proof.
    intros.
    eapply Iterate_Dep_Type_equiv'';
      eauto using string_dec.
  Defined.

  (* Iterating with a filter *)
  Fixpoint Iterate_Dep_Type_BoundedIndex_filter'
           ( Remaining : nat)
           (filter : Fin.t Remaining -> bool)
           (P : Dep_Type (Fin.t Remaining))
           {struct Remaining}
    : Type :=
    match Remaining return

            (@Fin.t Remaining -> bool)
            -> Dep_Type (Fin.t Remaining)
                          -> Type with
    | 0 => fun  filter P => True
    | S Remaining' =>
      fun  filter P =>
        if filter (@Fin.F1 Remaining') then
          prim_prod (P (@Fin.F1 Remaining'))
          (@Iterate_Dep_Type_BoundedIndex_filter'
                Remaining'
               (fun n' => filter (@Fin.FS _ n'))
               (fun n' => P (@Fin.FS _ n')))
        else
          @Iterate_Dep_Type_BoundedIndex_filter'
             Remaining'
            (fun n' => filter (@Fin.FS _ n'))
            (fun n' => P (@Fin.FS _ n'))
    end  filter P.

  Lemma Iterate_Dep_Type_equiv_filter'
    : forall (Remaining  : nat)
             (P : Dep_Type (Fin.t Remaining))
             (filter : Ensemble (Fin.t Remaining))
             (filter_dec : DecideableEnsemble filter),
      (@Iterate_Dep_Type_BoundedIndex_filter'  Remaining
                                              (@dec _ _ filter_dec)
                                              P ->
       forall idx, filter idx -> P idx).
  Proof.
    induction Remaining; simpl; intros.
    - inversion idx.
    - revert IHRemaining  filter filter_dec P X H.
      pattern Remaining, idx; apply Fin.caseS; intros.
      + apply dec_decides_P in H; rewrite H in X.
        intuition.
      + assert (forall a : Fin.t n, dec (Fin.FS a) = true <-> dec (Fin.FS a)) as decOK by intuition.
        case_eq (dec Fin.F1); intros; rewrite H0 in X; intuition.
        * eapply (IHRemaining

                    (fun n' : Fin.t n => P (Fin.FS n'))
                    (fun n' : Fin.t n => dec (Fin.FS n'))
                    {| dec n' :=  dec (Fin.FS n');
                       dec_decides_P := decOK
                    |}
                    prim_snd0); eauto using dec_decides_P.
          eapply dec_decides_P; eauto.
        * eapply (IHRemaining

                  (fun n' : Fin.t n => P (Fin.FS n'))
                  (fun n' : Fin.t n => dec (Fin.FS n'))
                  {| dec n' :=  dec (Fin.FS n');
                     dec_decides_P := decOK
                  |}
                  X); eauto.
          eapply dec_decides_P; eauto.
  Defined.

    Lemma Iterate_Dep_Type_equiv_filter''
    : forall (Remaining  : nat)
             (P : Dep_Type (Fin.t Remaining))
             (filter : Ensemble (Fin.t Remaining))
             (filter_dec : DecideableEnsemble filter),
      (forall idx, filter idx -> P idx)
      -> @Iterate_Dep_Type_BoundedIndex_filter'  Remaining
                                                (@dec _ _ filter_dec)
                                                P.
  Proof.
    induction Remaining; simpl; intros.
    - eauto.
    - case_eq (dec Fin.F1); intros.
      + apply dec_decides_P in H; intuition.
        assert (forall a : Fin.t Remaining, dec (Fin.FS a) = true <-> dec (Fin.FS a)) as decOK by intuition.
        eapply (IHRemaining

                 (fun n' : Fin.t _ => P (Fin.FS n'))
                 (fun n' : Fin.t _ => dec (Fin.FS n'))
                 {| dec n' :=  dec (Fin.FS n');
                    dec_decides_P := decOK
                 |}); eauto.
        intros; eapply X; apply dec_decides_P; eauto.
      + assert (forall a : Fin.t Remaining, dec (Fin.FS a) = true <-> dec (Fin.FS a)) as decOK by intuition.
        eapply (IHRemaining

                 (fun n' : Fin.t _ => P (Fin.FS n'))
                 (fun n' : Fin.t _ => dec (Fin.FS n'))
                 {| dec n' :=  dec (Fin.FS n');
                    dec_decides_P := decOK
                 |}); eauto.
        intros; eapply X; apply dec_decides_P; eauto.
  Defined.

  Definition Iterate_Dep_Type_BoundedIndex_filter
             (Remaining : nat)
             (P : Dep_Type (Fin.t Remaining))
             (filter : Fin.t Remaining -> bool)
    : Type :=
    @Iterate_Dep_Type_BoundedIndex_filter' Remaining filter P.

  Corollary Lookup_Iterate_Dep_Type_filter
  : forall (Bound : nat)
           (P : Dep_Type (Fin.t Bound))
           (filter : Ensemble (Fin.t Bound))
           (filter_dec : DecideableEnsemble filter),
      Iterate_Dep_Type_BoundedIndex_filter P dec ->
      forall idx : Fin.t Bound, filter idx -> P idx.
  Proof.
    intros.
    eapply Iterate_Dep_Type_equiv_filter' ; eassumption.
  Defined.

    Corollary Iterate_Dep_Type_BoundedIndex_filter_equiv2
  : forall (Bound : nat)
           (P : Dep_Type (Fin.t Bound))
           (filter : Ensemble (Fin.t Bound))
           (filter_dec : DecideableEnsemble filter),
      (forall idx : Fin.t Bound, filter idx -> P idx)
      -> Iterate_Dep_Type_BoundedIndex_filter P dec.
  Proof.
    intros; eapply Iterate_Dep_Type_equiv_filter'' ;
      eauto using string_dec.
  Defined.

  Fixpoint Update_Iterate_Dep_Type
           (n : nat)
           (k : Fin.t n)
           (P : Dep_Type (Fin.t n))
           (X0 : Iterate_Dep_Type_BoundedIndex P)
           (a' : P k )
           {struct k}
  : Iterate_Dep_Type_BoundedIndex P :=
    match k in Fin.t n return
          forall (P : Fin.t n -> Type),
            Iterate_Dep_Type_BoundedIndex P
            -> P k -> Iterate_Dep_Type_BoundedIndex P with
    | Fin.F1 _ => fun P X0 a' => Build_prim_prod a' (ilist.prim_snd X0)
    | Fin.FS i k' => fun P X0 a' => Build_prim_prod (ilist.prim_fst X0)
                                                    (Update_Iterate_Dep_Type k'
                                                                             (fun i => P (Fin.FS i)) (ilist.prim_snd X0) a')
    end P X0 a'.

  Definition Lookup_Update_Iterate_Dep_Type_eq {n}
    : forall (k : Fin.t n)
             (P : Fin.t n -> Type)
             (X0 : Iterate_Dep_Type_BoundedIndex P)
             (a' : P k ),
      Lookup_Iterate_Dep_Type P (Update_Iterate_Dep_Type k P X0 a') k = a'.
  Proof.
    induction k; simpl; intros.
    - eauto.
    - rewrite IHk; eauto.
  Qed.

  Definition Lookup_Update_Iterate_Dep_Type_neq {n}
    : forall (k k': Fin.t n)
             (P : Fin.t n -> Type)
             (X0 : Iterate_Dep_Type_BoundedIndex P)
             (a' : P k),
      k' <> k
      -> Lookup_Iterate_Dep_Type P (Update_Iterate_Dep_Type k P X0 a') k' =
         Lookup_Iterate_Dep_Type P X0 k'.
  Proof.
    induction k; simpl.
    - intro k'; pattern n, k'.
      match goal with
        |- ?P n k' => simpl; eapply (Fin.caseS P); simpl
      end; congruence.
    - intro k'; revert k IHk; pattern n, k'.
      match goal with
        |- ?P n k' => simpl; eapply (Fin.caseS P); simpl
      end; try congruence.
      intros.
      rewrite IHk; congruence.
  Qed.

End Iterate_Dep_Type.

(* Always expand these iterations as well. *)
Arguments Iterate_Dep_Type_BoundedIndex _ _ / .

 (*  Definition Iterate_Dep_Type_BoundedIndex_equiv_2 *)
 (*             {A : Set} {m} *)
 (*             (Bound : Vector.t A m) *)
 (*             (P : Dep_Type A) *)
 (*             (H : forall n, P (Vector.nth Bound n)) *)
 (*    : Iterate_Dep_Type_BoundedIndex P Bound. := @ith A P m Bound n il. *)

 (*  Corollary Iterate_Dep_Type_BoundedString_equiv_1 *)
 (*  : forall (Bound : list string) *)
 (*           (P : Dep_Type (BoundedIndex Bound)), *)
 (*      Iterate_Dep_Type_BoundedIndex P -> *)
 (*      forall idx, P idx. *)
 (*  Proof. *)
 (*    destruct idx as [idx [n nth_n]]. *)
 (*    eapply (Iterate_Dep_Type_equiv string_dec P); eauto; *)
 (*    destruct n0; simpl; discriminate. *)
 (*  Defined. *)

 (*  Fixpoint Iterate_Dep_Type_equiv' {A : Set} *)
 (*           (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*           (Bound : list A) *)
 (*  : forall (P : Dep_Type (BoundedIndex Bound)), *)
 (*      (forall idx, P idx) *)
 (*      -> Iterate_Dep_Type_BoundedIndex P := *)
 (*    match Bound return *)
 (*          forall (P : Dep_Type (BoundedIndex Bound)), *)
 (*            (forall idx, P idx) *)
 (*            -> Iterate_Dep_Type_BoundedIndex P *)
 (*    with *)
 (*      | nil => fun P p => tt *)
 (*      | b :: Bound' => fun P p => (p _, Iterate_Dep_Type_equiv' A_eq_dec _ *)
 (*                                                                (fun idx => p {|bindex := bindex idx; *)
 (*                                                                                indexb := *)
 (*                                               Build_IndexBound (b :: Bound') *)
 (*                                                                (S (ibound (indexb _))) *)
 (*                                                                (boundi (indexb _)) |})) *)
 (*    end. *)

 (*  Corollary Iterate_Dep_Type_BoundedIndex_equiv_2 *)
 (*            {A : Set} *)
 (*            (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall (Bound : list A) *)
 (*           (P : Dep_Type (BoundedIndex Bound)), *)
 (*      (forall idx, P idx) *)
 (*      -> Iterate_Dep_Type_BoundedIndex P. *)
 (*  Proof. *)
 (*    intros. *)
 (*    eapply Iterate_Dep_Type_equiv'; *)
 (*      eauto using string_dec. *)
 (*  Qed. *)

 (*  Corollary Iterate_Dep_Type_BoundedString_equiv_2 *)
 (*  : forall (Bound : list string) *)
 (*           (P : Dep_Type (BoundedIndex Bound)), *)
 (*      (forall idx, P idx) *)
 (*      -> Iterate_Dep_Type_BoundedIndex P. *)
 (*  Proof. *)
 (*    intros. *)
 (*    eapply Iterate_Dep_Type_equiv'; *)
 (*      eauto using string_dec. *)
 (*  Qed. *)

 (*  Lemma eq_proof_unicity_eq {A : Set} *)
 (*        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall *)
 (*      (As : list A) a n (nth_n nth_n' : nth_error As n = Some a) eq_nth, *)
 (*      eq_proofs_unicity_Opt_A A_eq_dec nth_n nth_n' = eq_nth. *)
 (*    intros. *)
 (*    destruct (eq_proofs_unicity_Opt_A A_eq_dec nth_n nth_n'). *)
 (*    apply Eqdep_dec.eq_proofs_unicity; intros; left. *)
 (*    apply Eqdep_dec.eq_proofs_unicity. *)
 (*    intros; destruct (Opt_A_eq_dec A_eq_dec x0 y0); eauto. *)
 (*  Qed. *)

 (*  Lemma Dep_Type_BoundedIndex_nth_eq_refl {A : Set} *)
 (*        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall *)
 (*      (As : list A) *)
 (*      (P : BoundedIndex As -> Type) *)
 (*      a n nth_n *)
 (*      (p : P {| bindex := a; indexb := {| ibound := n; boundi := nth_n |}|}), *)
 (*        (Dep_Type_BoundedIndex_nth_eq (a' := a) A_eq_dec P n nth_n nth_n p) *)
 (*      = p. *)
 (*  Proof. *)
 (*    intros. *)
 (*    unfold Dep_Type_BoundedIndex_nth_eq, eq_rect_r, eq_rect, eq_sym. *)
 (*    match goal with *)
 (*        |- context [indexb_ibound_eq ?a ?a' ?eq'] => *)
 (*        rewrite (fun A => Eqdep_dec.eq_proofs_unicity A (indexb_ibound_eq a a' eq') eq_refl) *)
 (*    end. *)
 (*    rewrite eq_proof_unicity_eq with (eq_nth := eq_refl); reflexivity. *)
 (*    intros; destruct (A_eq_dec x y); eauto. *)
 (*  Defined. *)

 (*  Lemma Dep_Type_BoundedIndex_nth_eq_iso {A : Set} *)
 (*        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall *)
 (*      (As : list A) *)
 (*      (P : Dep_Type (BoundedIndex As)) *)
 (*      a n nth nth' *)
 (*      (p : P {| bindex := a; indexb := {| ibound := n; boundi := nth |}|}), *)
 (*      Dep_Type_BoundedIndex_nth_eq *)
 (*        (a' := a) A_eq_dec P n nth' nth *)
 (*        (Dep_Type_BoundedIndex_nth_eq (a' := a) A_eq_dec P n nth nth' p) *)
 (*      = p. *)
 (*  Proof. *)
 (*    intros. *)
 (*    unfold Dep_Type_BoundedIndex_nth_eq, eq_rect_r, eq_rect, eq_sym. *)
 (*    match goal with *)
 (*        |- context [indexb_ibound_eq ?a ?a' ?eq'] => *)
 (*        rewrite (fun A => Eqdep_dec.eq_proofs_unicity A (indexb_ibound_eq a a' eq') eq_refl) *)
 (*    end. *)
 (*    match goal with *)
 (*        |- context [indexb_ibound_eq ?a ?a' ?eq'] => *)
 (*        rewrite (fun A => Eqdep_dec.eq_proofs_unicity A (indexb_ibound_eq a a' eq') eq_refl) *)
 (*    end. *)
 (*    rewrite <- (eq_proofs_unicity_Opt_A A_eq_dec nth nth'). *)
 (*    rewrite eq_proof_unicity_eq with (eq_nth := eq_refl). *)
 (*    reflexivity. *)
 (*    intros; destruct (A_eq_dec x y); eauto. *)
 (*    intros; destruct (A_eq_dec x y); eauto. *)
 (*  Defined. *)

 (*  Fixpoint Lookup_Iterate_Dep_Type {A : Set} *)
 (*           (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*           (Bound : list A) *)
 (*           (P : Dep_Type (BoundedIndex Bound)) *)
 (*           (X0 : Iterate_Dep_Type_BoundedIndex P) *)
 (*           idx n nth_n *)
 (*           {struct Bound} *)
 (*  : P {| bindex := idx; *)
 (*         indexb := {| ibound := n; *)
 (*                      boundi := nth_n |} |}. *)
 (*  refine (match n, Bound return *)
 (*                forall *)
 (*                       (P : Dep_Type (BoundedIndex Bound)) *)
 (*                       (X0 : Iterate_Dep_Type_BoundedIndex P) *)
 (*                       idx *)
 (*                       (nth_n : nth_error Bound n = Some idx), *)
 (*                  P {| bindex := idx; *)
 (*                       indexb := {| ibound := n; *)
 (*                                    boundi := nth_n |} |} *)
 (*          with *)
 (*            | 0, a :: Bound' => *)
 (*              fun P X0 idx nth_n => *)
 (*                Dep_Type_BoundedIndex_nth_eq A_eq_dec _ _ _ _ (fst X0) *)
 (*            | S n', a :: Bound' => fun P X0 idx nth_n => *)
 (*                                         Lookup_Iterate_Dep_Type A A_eq_dec Bound' _ (snd X0) _ _ _ *)
 (*            | _, [ ] => fun _ _ _ _ => _ *)
 (*          end  P X0 idx nth_n); simpl in *; discriminate. *)
 (*  Defined. *)

 (*  Fixpoint Update_Iterate_Dep_Type {A : Set} *)
 (*           (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*           (Bound : list A) *)
 (*           (P : Dep_Type (BoundedIndex Bound)) *)
 (*           (X0 : Iterate_Dep_Type_BoundedIndex P) *)
 (*           idx n nth_n *)
 (*           (a' : P {| bindex := idx; *)
 (*                     indexb := {| ibound := n; *)
 (*                                  boundi := nth_n |} |}) *)
 (*           {struct Bound} *)
 (*  : Iterate_Dep_Type_BoundedIndex P. *)
 (*  refine (match n, Bound return *)
 (*                forall *)
 (*                  (P : Dep_Type (BoundedIndex Bound)) *)
 (*                  (X0 : Iterate_Dep_Type_BoundedIndex P) *)
 (*                       idx *)
 (*                       (nth_n : nth_error Bound n = Some idx) *)
 (*                       (a' : P {| bindex := idx; *)
 (*                                  indexb := {| ibound := n; *)
 (*                                               boundi := nth_n |} |}), *)
 (*                  Iterate_Dep_Type_BoundedIndex P *)
 (*          with *)
 (*            | 0, a :: Bound' => fun P X0 idx nth_n a' => *)
 (*                                      (Dep_Type_BoundedIndex_nth_eq A_eq_dec _ _ _ _ a', *)
 (*                                       snd X0) *)
 (*            | S n', a :: Bound' => *)
 (*              fun P X0 idx nth_n a' => *)
 (*                (fst X0, *)
 (*                 Update_Iterate_Dep_Type A A_eq_dec Bound' _ (snd X0) *)
 (*                                           _ _ nth_n *)
 (*                                           (Dep_Type_BoundedIndex_nth_eq A_eq_dec _ _ _ _ a')) *)
 (*            | _, [ ] => fun  _ _ _ _ => _ *)
 (*          end  P X0 idx nth_n a'); simpl in *; try discriminate. *)
 (*  Defined. *)

 (*  Definition Lookup_Update_Iterate_Dep_Type_eq *)
 (*             {A : Set} *)
 (*             (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall *)
 (*      (Bound : list A) *)
 (*      (P : Dep_Type (BoundedIndex Bound)) *)
 (*      (X0 : Iterate_Dep_Type_BoundedIndex P) *)
 (*      idx n nth_n *)
 (*      (a' : P {| bindex := idx; *)
 (*                 indexb := {| ibound := n; *)
 (*                              boundi := nth_n |} |}), *)
 (*      Lookup_Iterate_Dep_Type *)
 (*        A_eq_dec P (Update_Iterate_Dep_Type A_eq_dec P X0 n nth_n a') _ nth_n = a'. *)
 (*  Proof. *)
 (*    induction Bound; destruct n; simpl; intros. *)
 (*    - discriminate. *)
 (*    - discriminate. *)
 (*    - injection nth_n; intros; subst. *)
 (*      apply (@Dep_Type_BoundedIndex_nth_eq_iso A A_eq_dec (idx :: Bound) P idx 0 nth_n eq_refl a'). *)
 (*    - rewrite <- (IHBound _ (snd X0) _ _ _ a') at -1. *)
 (*      f_equal. *)
 (*      f_equal. *)
 (*      unfold Dep_Type_BoundedIndex_nth_eq, eq_rect, eq_rect_r, eq_rect, eq_sym. *)
 (*      match goal with *)
 (*          |- context [indexb_ibound_eq ?a ?a' ?eq'] => *)
 (*          rewrite (fun A => Eqdep_dec.eq_proofs_unicity A (indexb_ibound_eq a a' eq') eq_refl) *)
 (*      end. *)
 (*      simpl; rewrite (@eq_proof_unicity_eq _ A_eq_dec Bound _ _ nth_n nth_n eq_refl). *)
 (*      reflexivity. *)
 (*      intros; destruct (A_eq_dec x y); intuition. *)
 (*  Qed. *)

 (*  Definition Lookup_Update_Iterate_Dep_Type_neq *)
 (*             {A : Set} *)
 (*             (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall *)
 (*      (Bound : list A) *)
 (*      (P : Dep_Type (BoundedIndex Bound)) *)
 (*      (X0 : Iterate_Dep_Type_BoundedIndex P) *)
 (*      idx n nth_n idx' n' *)
 (*      (nth_n' : nth_error Bound n' = Some idx') *)
 (*      (a' : P {| bindex := idx; *)
 (*                 indexb := {| ibound := n; *)
 (*                              boundi := nth_n |} |}), *)
 (*      n <> n' *)
 (*      -> Lookup_Iterate_Dep_Type *)
 (*        A_eq_dec P (Update_Iterate_Dep_Type A_eq_dec P X0 n nth_n a') _ nth_n' = *)
 (*      Lookup_Iterate_Dep_Type A_eq_dec P X0 _ nth_n'. *)
 (*  Proof. *)
 (*    induction Bound; destruct n; destruct n'; simpl; intros; try discriminate; eauto. *)
 (*    - congruence. *)
 (*    - apply (IHBound _ (snd X0)). *)
 (*      congruence. *)
 (*  Qed. *)

 (*  (* Iterating with a filter. *) *)
 (*  Fixpoint Iterate_Dep_Type_BoundedIndex_filter *)
 (*          {A : Set} *)
 (*          (Bound : list A) *)
 (*          (filter : nat -> bool) *)
 (*  {struct Bound} : Dep_Type (BoundedIndex Bound) -> Type := *)
 (*    match Bound return *)
 (*          Dep_Type (BoundedIndex Bound) -> Type *)
 (*    with *)
 (*      | nil => fun _ => unit *)
 (*      | a :: Bound' => *)
 (*        fun P => *)
 (*        if filter 0 *)
 (*        then *)
 (*          prod *)
 (*            (P {| bindex := a; *)
 (*                  indexb := {| ibound := 0; *)
 (*                               boundi := @eq_refl _ (nth_error (a :: Bound') 0) |} |}) *)
 (*            (Iterate_Dep_Type_BoundedIndex_filter (fun n => filter (S n)) *)
 (*                                                  (fun H => P {|bindex := bindex H; *)
 (*                                                                indexb :=                                                Build_IndexBound (a :: Bound') *)
 (*                                                                                                                                          (S (ibound (indexb H))) *)
 (*                                                                                                                                          (boundi (indexb H)) *)
 (* |})) *)
 (*        else *)
 (*          Iterate_Dep_Type_BoundedIndex_filter (fun n => filter (S n)) *)
 (*                                               (fun H => P {|bindex := bindex H; *)
 (*                                                             indexb :=                                                Build_IndexBound (a :: Bound') *)
 (*                                                                                                                                       (S (ibound (indexb H))) *)
 (*                                                                                                                                       (boundi (indexb H)) |}) *)
 (*    end. *)

 (*  Fixpoint Iterate_Dep_Type_filter_equiv {A : Set} *)
 (*        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*        (Bound : list A) *)
 (*        {struct Bound} *)
 (*  : forall *)
 (*      (P : Dep_Type (BoundedIndex Bound)) *)
 (*      (filter : Ensemble nat) *)
 (*      (filter_dec : DecideableEnsemble filter) *)
 (*      (X : Iterate_Dep_Type_BoundedIndex_filter (@dec _ _ filter_dec) P) *)
 (*      idx n nth_n, *)
 (*      filter n -> *)
 (*      P {| bindex := idx; *)
 (*           indexb := {| ibound := n; *)
 (*                        boundi := nth_n |} |}. *)
 (*  refine (match Bound return *)
 (*                forall (P : Dep_Type (BoundedIndex Bound)) *)
 (*                       (filter : Ensemble nat) *)
 (*                       (filter_dec : DecideableEnsemble filter) *)
 (*                       (X : Iterate_Dep_Type_BoundedIndex_filter (@dec _ _ filter_dec) P) *)
 (*                       idx n nth_n, *)
 (*                  filter n -> *)
 (*                  P {| bindex := idx; *)
 (*                       indexb := {| ibound := n; *)
 (*                                    boundi := nth_n |} |} *)
 (*          with *)
 (*            | nil => _ *)
 (*            | a :: Bound' => _ *)
 (*          end); intros; eauto. *)
 (*  - destruct n; simpl in *; discriminate. *)
 (*  - setoid_rewrite <- dec_decides_P in H; *)
 (*    destruct n; simpl in *. *)
 (*    + rewrite H in X; eapply (Dep_Type_BoundedIndex_nth_eq A_eq_dec _ _ _ _ (fst X)). *)
 (*    + case_eq (dec 0); intros; rewrite H0 in X. *)
 (*      * apply (fun A' => Iterate_Dep_Type_filter_equiv A A_eq_dec Bound' *)
 (*                                                       (fun H => P {|bindex := bindex H; *)
 (*                                                                     indexb :=                                               Build_IndexBound (a :: Bound') *)
 (*                                                                                                                                              (S (ibound (indexb H))) *)
 (*                                                                                                                                              (boundi (indexb H))  |}) *)
 (*                                                       (fun n => filter (S n)) *)
 (*                                                       {| dec := _; *)
 (*                                                          dec_decides_P := A' |} (snd X) idx n nth_n). *)
 (*        intros; apply dec_decides_P. *)
 (*        apply dec_decides_P; eauto. *)
 (*      * apply (fun A' => Iterate_Dep_Type_filter_equiv A A_eq_dec Bound' *)
 (*                                                       (fun H => P {|bindex := bindex H; *)
 (*                                                                     indexb :=                                               Build_IndexBound (a :: Bound') *)
 (*                                                                                                                                              (S (ibound (indexb H))) *)
 (*                                                                                                                                              (boundi (indexb H)) *)
 (*                                                                   |}) *)
 (*                                          (fun n => filter (S n)) *)
 (*                                          {| dec := _; *)
 (*                                             dec_decides_P := A' |} X idx n nth_n). *)
 (*      intros; apply dec_decides_P. *)
 (*      apply dec_decides_P; eauto. *)
 (*  Defined. *)

 (*  Corollary Iterate_Dep_Type_BoundedIndex_filter_equiv_1 *)
 (*            {A : Set} *)
 (*            (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*    : forall (Bound : list A) *)
 (*           (P : Dep_Type (BoundedIndex Bound)) *)
 (*           (filter : Ensemble nat) *)
 (*           (filter_dec : DecideableEnsemble filter), *)
 (*      Iterate_Dep_Type_BoundedIndex_filter dec P -> *)
 (*      forall idx : BoundedIndex Bound, filter (ibound idx) -> P idx. *)
 (*  Proof. *)
 (*    intros; destruct idx as [idx [n nth_n] ]; simpl in *. *)
 (*    eapply Iterate_Dep_Type_filter_equiv; eauto using string_dec. *)
 (*  Qed. *)

 (*  Corollary Iterate_Dep_Type_BoundedString_filter_equiv_1 *)
 (*  : forall (Bound : list string) *)
 (*           (P : Dep_Type (BoundedIndex Bound)) *)
 (*           (filter : Ensemble nat) *)
 (*           (filter_dec : DecideableEnsemble filter), *)
 (*      Iterate_Dep_Type_BoundedIndex_filter dec P -> *)
 (*      forall idx : BoundedIndex Bound, filter (ibound idx) -> P idx. *)
 (*  Proof. *)
 (*    intros; destruct idx as [idx [n nth_n] ]; simpl in *. *)
 (*    eapply Iterate_Dep_Type_filter_equiv; eauto using string_dec. *)
 (*  Qed. *)

 (*  Lemma Iterate_Dep_Type_filter_equiv' *)
 (*        {A : Set} *)
 (*        (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall (Bound : list A) *)
 (*           (P : Dep_Type (BoundedIndex Bound)) *)
 (*           (filter : Ensemble nat) *)
 (*           (filter_dec : DecideableEnsemble filter), *)
 (*      (forall idx, filter (ibound (indexb idx)) -> P idx) *)
 (*      -> Iterate_Dep_Type_BoundedIndex_filter (@dec _ _ filter_dec) P. *)
 (*  Proof. *)
 (*    induction Bound; simpl; try constructor; intros. *)
 (*    intros; case_eq (dec 0); try split; intros; eauto. *)
 (*    - eapply X; apply dec_decides_P; simpl; auto. *)
 (*    - eapply (IHBound _ (fun n => filter (S n)) *)
 (*                      {| dec := _; *)
 (*                         dec_decides_P n := (dec_decides_P (S n)) |}); eauto. *)
 (*    - eapply (IHBound _ (fun n => filter (S n)) *)
 (*                      {| dec := _; *)
 (*                         dec_decides_P n := (dec_decides_P (S n)) |}); eauto. *)
 (*  Qed. *)

 (*  Corollary Iterate_Dep_Type_BoundedIndex_filter_equiv_2 *)
 (*            {A : Set} *)
 (*            (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'}) *)
 (*  : forall (Bound : list A) *)
 (*           (P : Dep_Type (BoundedIndex Bound)) *)
 (*           (filter : Ensemble nat) *)
 (*           (filter_dec : DecideableEnsemble filter), *)
 (*      (forall idx : BoundedIndex Bound, filter (ibound idx) -> P idx) *)
 (*      -> Iterate_Dep_Type_BoundedIndex_filter dec P. *)
 (*  Proof. *)
 (*    intros; eapply Iterate_Dep_Type_filter_equiv'; *)
 (*    eauto using string_dec. *)
 (*  Qed. *)

 (*  Corollary Iterate_Dep_Type_BoundedString_filter_equiv_2 *)
 (*  : forall (Bound : list string) *)
 (*           (P : Dep_Type (BoundedIndex Bound)) *)
 (*           (filter : Ensemble nat) *)
 (*           (filter_dec : DecideableEnsemble filter), *)
 (*      (forall idx : BoundedIndex Bound, filter (ibound idx) -> P idx) *)
 (*      -> Iterate_Dep_Type_BoundedIndex_filter dec P. *)
 (*  Proof. *)
 (*    intros; eapply Iterate_Dep_Type_filter_equiv'; *)
 (*    eauto using string_dec. *)
 (*  Qed. *)
