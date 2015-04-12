(** * Miscellaneous Well-Foundedness Facts *)
Require Import Coq.Setoids.Setoid Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Classes.Morphisms Coq.Init.Wf.

Set Implicit Arguments.

Section wf.
  Section wf_prod.
    Context A B (RA : relation A) (RB : relation B).

    Definition prod_relation : relation (A * B)
      := fun ab a'b' =>
           RA (fst ab) (fst a'b') \/ (fst a'b' = fst ab /\ RB (snd ab) (snd a'b')).

    Fixpoint well_founded_prod_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : well_founded RB) {struct wf_A}
    : Acc prod_relation (a, b)
      := match wf_A with
           | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc RB b') : Acc prod_relation (a, b')
                              := Acc_intro
                                   _
                                   (fun ab =>
                                      match ab as ab return prod_relation ab (a, b') -> Acc prod_relation ab with
                                        | (a'', b'') =>
                                          fun pf =>
                                            match pf with
                                              | or_introl pf'
                                                => @well_founded_prod_relation_helper
                                                     _ _
                                                     (fa _ pf')
                                                     wf_B
                                              | or_intror (conj pfa pfb)
                                                => match wf_B' with
                                                     | Acc_intro fb
                                                       => eq_rect
                                                            _
                                                            (fun a'' => Acc prod_relation (a'', b''))
                                                            (wf_B_rec _ (fb _ pfb))
                                                            _
                                                            pfa
                                                   end
                                            end
                                      end)
                             ) b (wf_B b)
         end.

    Definition well_founded_prod_relation : well_founded RA -> well_founded RB -> well_founded prod_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_prod_relation_helper; auto.
    Defined.
  End wf_prod.

  Section wf_sig.
    Context A B (RA : relation A) (RB : forall a : A, relation (B a)).

    Definition sigT_relation : relation (sigT B)
      := fun ab a'b' =>
           RA (projT1 ab) (projT1 a'b') \/ (exists pf : projT1 a'b' = projT1 ab, RB (projT2 ab)
                                                                                    (eq_rect _ B (projT2 a'b') _ pf)).

    Fixpoint well_founded_sigT_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : forall a, well_founded (@RB a)) {struct wf_A}
    : Acc sigT_relation (existT _ a b).
    Proof.
      refine match wf_A with
               | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc (@RB a) b') : Acc sigT_relation (existT _ a b')
                                  := Acc_intro
                                       _
                                       (fun ab =>
                                          match ab as ab return sigT_relation ab (existT _ a b') -> Acc sigT_relation ab with
                                            | existT a'' b'' =>
                                              fun pf =>
                                                match pf with
                                                  | or_introl pf'
                                                    => @well_founded_sigT_relation_helper
                                                         _ _
                                                         (fa _ pf')
                                                         wf_B
                                                  | or_intror (ex_intro pfa pfb)
                                                    => match wf_B' with
                                                         | Acc_intro fb
                                                           => _(*eq_rect
                                                            _
                                                            (fun a'' => Acc sigT_relation (existT B a'' _(*b''*)))
                                                            (wf_B_rec _ (fb _ _(*pfb*)))
                                                            _
                                                            pfa*)
                                                       end
                                                end
                                          end)
                                 ) b (wf_B a b)
             end;
      simpl in *.
      destruct pfa; simpl in *.
      exact (wf_B_rec _ (fb _ pfb)).
    Defined.

    Definition well_founded_sigT_relation : well_founded RA
                                            -> (forall a, well_founded (@RB a))
                                            -> well_founded sigT_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_sigT_relation_helper; auto.
    Defined.
  End wf_sig.

  Section wf_projT1.
    Context A (B : A -> Type) (R : relation A).

    Definition projT1_relation : relation (sigT B)
      := fun ab a'b' =>
           R (projT1 ab) (projT1 a'b').

    Definition well_founded_projT1_relation : well_founded R -> well_founded projT1_relation.
    Proof.
      intros wf [a b]; hnf in *.
      induction (wf a) as [a H IH].
      constructor.
      intros y r.
      specialize (IH _ r (projT2 y)).
      destruct y.
      exact IH.
    Defined.
  End wf_projT1.
End wf.

Section Fix_rect.
  Context A (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : A -> Type) (F : forall x : A, (forall y : A, R y x -> P y) -> P x)
          (Q : forall x, P x -> Type)
          (H : forall x, (forall y, R y x -> Q y (@Fix A R Rwf P F y)) -> Q x (@F x (fun (y : A) (_ : R y x) => @Fix A R Rwf P F y)))
          (F_ext : forall (x : A) (f g : forall y : A, R y x -> P y),
                   (forall (y : A) (p : R y x), f y p = g y p) -> F _ f = F _ g).

  Definition Fix_rect x
  : @Q x (@Fix A R Rwf P F x).
  Proof.
    induction (Rwf x).
    rewrite Init.Wf.Fix_eq; auto.
  Defined.
End Fix_rect.

Local Ltac Fix_Proper_t Fix_eq wf :=
  let H := fresh "H" in
  let a := fresh "a" in
  unfold forall_relation, pointwise_relation, respectful;
  intros ?? H a; repeat intro;
  induction (wf a);
  rewrite !Fix_eq; [ erewrite H; [ reflexivity | .. ] | .. ]; eauto; intros;
  [ etransitivity; [ symmetry; apply H; reflexivity | apply H; eassumption ]; reflexivity
  | etransitivity; [ apply H; eassumption | symmetry; apply H; reflexivity ]; reflexivity ].


Global Instance Fix_Proper_eq {A R wf P}
: Proper
    ((forall_relation (fun a =>
                         (forall_relation (fun a' => pointwise_relation _ eq))
                           ==> eq))
       ==> (forall_relation (fun a => eq)))
    (@Fix A R wf P).
Proof. Fix_Proper_t @Coq.Init.Wf.Fix_eq wf. Qed.

Local Ltac Fix_eq_t F_ext Rwf :=
  intros;
  unfold Fix;
  rewrite <- Fix_F_eq;
  apply F_ext; intros;
  repeat match goal with
           | [ |- appcontext[Fix_F _ _ (?f ?x)] ] => generalize (f x)
         end;
  clear -F_ext Rwf;
  match goal with
    | [ |- forall x : Acc _ ?a, _ ] => induction (Rwf a)
  end;
  intros; rewrite <- !Fix_F_eq;
  apply F_ext; eauto.

(** A variant of [Fix] that has a nice [Fix_eq] for functions which
    doesn't require [functional_extensionality]. *)
Section Fix1.
  Context A (B : A -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a, B a -> Type).

  Local Notation Fix1 := (@Fix A R Rwf (fun a : A => forall b, @P a b)).

  Section F.
    Context (F : forall x : A, (forall y : A, R y x -> forall b, @P y b) -> forall b, @P x b).

    Definition Fix1_eq
               (F_ext : forall x (f g : forall y, R y x -> forall b, @P y b),
                          (forall y (p : R y x) b, f y p b = g y p b)
                          -> forall b, @F x f b = @F x g b)
    : forall a b, @Fix1 F a b = @F a (fun y (_ : R y a) => @Fix1 F y) b.
    Proof. Fix_eq_t F_ext Rwf. Defined.

    Definition Fix1_rect
               (Q : forall a b, @P a b -> Type)
               (H : forall x, (forall y, R y x -> forall b, @Q y b (@Fix1 F y b))
                              -> forall b, @Q x b (@F x (fun y (_ : R y x) => @Fix1 F y) b))
               (F_ext : forall x (f g : forall y, R y x -> forall b, @P y b),
                          (forall y (p : R y x) b, f y p b = g y p b)
                          -> forall b, @F x f b = @F x g b)
               a b
    : @Q a b (@Fix1 F a b).
    Proof.
      induction (Rwf a).
      rewrite Fix1_eq; auto.
    Defined.
  End F.

  Global Instance Fix1_Proper_eq
  : Proper
      ((forall_relation (fun a =>
                           (forall_relation (fun a' => pointwise_relation _ (forall_relation (fun b => eq))))
                             ==> (forall_relation (fun b => eq)))
                        ==> (forall_relation (fun a => forall_relation (fun b => eq)))))
      Fix1.
  Proof. Fix_Proper_t @Fix1_eq Rwf. Qed.
End Fix1.

Arguments Fix1_Proper_eq {A B R Rwf P} _ _ _ _ _.

(** A variant of [Fix] that has a nice [Fix_eq] for functions which
    doesn't require [functional_extensionality]. *)
Section Fix2.
  Context A (B : A -> Type) (C : forall a, B a -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b, C a b -> Type).

  Local Notation Fix2 := (@Fix A R Rwf (fun a : A => forall b c, @P a b c)).

  Section F.
    Context (F : forall x : A, (forall y : A, R y x -> forall b c, @P y b c) -> forall b c, @P x b c).

    Definition Fix2_eq
               (F_ext : forall x (f g : forall y, R y x -> forall b c, @P y b c),
                          (forall y (p : R y x) b c, f y p b c = g y p b c)
                          -> forall b c, @F x f b c = @F x g b c)
    : forall a b c, @Fix2 F a b c = @F a (fun y (_ : R y a) => @Fix2 F y) b c.
    Proof. Fix_eq_t F_ext Rwf. Defined.

    Definition Fix2_rect
               (Q : forall a b c, @P a b c -> Type)
               (H : forall x, (forall y, R y x -> forall b c, @Q y b c (@Fix2 F y b c))
                              -> forall b c, @Q x b c (@F x (fun y (_ : R y x) => @Fix2 F y) b c))
               (F_ext : forall x (f g : forall y, R y x -> forall b c, @P y b c),
                          (forall y (p : R y x) b c, f y p b c = g y p b c)
                          -> forall b c, @F x f b c = @F x g b c)
               a b c
    : @Q a b c (@Fix2 F a b c).
    Proof.
      induction (Rwf a).
      rewrite Fix2_eq; auto.
    Defined.
  End F.

  Global Instance Fix2_Proper_eq
  : Proper
      ((forall_relation (fun a =>
                           (forall_relation (fun a' => pointwise_relation _ (forall_relation (fun b => forall_relation (fun c => eq)))))
                             ==> (forall_relation (fun b => forall_relation (fun c => eq))))
                        ==> (forall_relation (fun a => forall_relation (fun b => forall_relation (fun c => eq))))))
      Fix2.
  Proof. Fix_Proper_t @Fix2_eq Rwf. Qed.
End Fix2.

Arguments Fix2_Proper_eq {A B C R Rwf P} _ _ _ _ _ _.

(** A variant of [Fix] that has a nice [Fix_eq] for functions which
    doesn't require [functional_extensionality]. *)
Section Fix3.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c, D a b c -> Type).

  Local Notation Fix3 := (@Fix A R Rwf (fun a : A => forall b c d, @P a b c d)).

  Section F.
    Context (F : forall x : A, (forall y : A, R y x -> forall b c d, @P y b c d) -> forall b c d, @P x b c d).

    Definition Fix3_eq
               (F_ext : forall x (f g : forall y, R y x -> forall b c d, @P y b c d),
                          (forall y (p : R y x) b c d, f y p b c d = g y p b c d)
                          -> forall b c d, @F x f b c d = @F x g b c d)
    : forall a b c d, @Fix3 F a b c d = @F a (fun y (_ : R y a) => @Fix3 F y) b c d.
    Proof. Fix_eq_t F_ext Rwf. Defined.

    Definition Fix3_rect
               (Q : forall a b c d, @P a b c d -> Type)
               (H : forall x, (forall y, R y x -> forall b c d, @Q y b c d (@Fix3 F y b c d))
                              -> forall b c d, @Q x b c d (@F x (fun y (_ : R y x) => @Fix3 F y) b c d))
               (F_ext : forall x (f g : forall y, R y x -> forall b c d, @P y b c d),
                          (forall y (p : R y x) b c d, f y p b c d = g y p b c d)
                          -> forall b c d, @F x f b c d = @F x g b c d)
               a b c d
    : @Q a b c d (@Fix3 F a b c d).
    Proof.
      induction (Rwf a).
      rewrite Fix3_eq; auto.
    Defined.
  End F.

  Global Instance Fix3_Proper_eq
  : Proper
      ((forall_relation (fun a =>
                           (forall_relation (fun a' => pointwise_relation _ (forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => eq))))))
                             ==> (forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => eq))))))
         ==> (forall_relation (fun a => forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => eq))))))
      Fix3.
  Proof. Fix_Proper_t @Fix3_eq Rwf. Qed.
End Fix3.

Arguments Fix3_Proper_eq {A B C D R Rwf P} _ _ _ _ _ _ _.

Section Fix4.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type) (E : forall a b c, D a b c -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c d, E a b c d -> Type).

  Local Notation Fix4 := (@Fix A R Rwf (fun a : A => forall b c d e, @P a b c d e)).

  Section F.
    Context (F : forall x : A, (forall y : A, R y x -> forall b c d e, @P y b c d e) -> forall b c d e, @P x b c d e).

    Definition Fix4_eq
               (F_ext : forall x (f g : forall y, R y x -> forall b c d e, @P y b c d e),
                          (forall y (p : R y x) b c d e, f y p b c d e = g y p b c d e)
                          -> forall b c d e, @F x f b c d e = @F x g b c d e)
    : forall a b c d e, @Fix4 F a b c d e = @F a (fun y (_ : R y a) => @Fix4 F y) b c d e.
    Proof. Fix_eq_t F_ext Rwf. Defined.

    Definition Fix4_rect
               (Q : forall a b c d e, @P a b c d e -> Type)
               (H : forall x, (forall y, R y x -> forall b c d e, @Q y b c d e (@Fix4 F y b c d e))
                              -> forall b c d e, @Q x b c d e (@F x (fun y (_ : R y x) => @Fix4 F y) b c d e))
               (F_ext : forall x (f g : forall y, R y x -> forall b c d e, @P y b c d e),
                          (forall y (p : R y x) b c d e, f y p b c d e = g y p b c d e)
                          -> forall b c d e, @F x f b c d e = @F x g b c d e)
               a b c d e
    : @Q a b c d e (@Fix4 F a b c d e).
    Proof.
      induction (Rwf a).
      rewrite Fix4_eq; auto.
    Defined.
  End F.

  Global Instance Fix4_Proper_eq
  : Proper
      ((forall_relation (fun a =>
                           (forall_relation (fun a' => pointwise_relation _ (forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => forall_relation (fun e => eq)))))))
                             ==> (forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => forall_relation (fun e => eq)))))))
         ==> (forall_relation (fun a => forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => forall_relation (fun e => eq)))))))
      Fix4.
  Proof. Fix_Proper_t @Fix4_eq Rwf. Qed.
End Fix4.

Arguments Fix4_Proper_eq {A B C D E R Rwf P} _ _ _ _ _ _ _ _.

Section Fix5.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type) (E : forall a b c, D a b c -> Type) (H : forall a b c d, E a b c d -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c d e, H a b c d e -> Type).

  Local Notation Fix5 := (@Fix A R Rwf (fun a : A => forall b c d e h, @P a b c d e h)).

  Section F.
    Context (F : forall x : A, (forall y : A, R y x -> forall b c d e h, @P y b c d e h) -> forall b c d e h, @P x b c d e h).

    Definition Fix5_eq
               (F_ext : forall x (f g : forall y, R y x -> forall b c d e h, @P y b c d e h),
                          (forall y (p : R y x) b c d e h, f y p b c d e h = g y p b c d e h)
                          -> forall b c d e h, @F x f b c d e h = @F x g b c d e h)
    : forall a b c d e h, @Fix5 F a b c d e h = @F a (fun y (_ : R y a) => @Fix5 F y) b c d e h.
    Proof. Fix_eq_t F_ext Rwf. Defined.

    Definition Fix5_rect
               (Q : forall a b c d e h, @P a b c d e h -> Type)
               (H0 : forall x, (forall y, R y x -> forall b c d e h, @Q y b c d e h (@Fix5 F y b c d e h))
                              -> forall b c d e h, @Q x b c d e h (@F x (fun (y : A) (_ : R y x) => @Fix5 F y) b c d e h))
               (F_ext : forall x (f g : forall y, R y x -> forall b c d e h, @P y b c d e h),
                          (forall y (p : R y x) b c d e h, f y p b c d e h = g y p b c d e h)
                          -> forall b c d e h, @F x f b c d e h = @F x g b c d e h)
               a b c d e h
    : @Q a b c d e h (@Fix5 F a b c d e h).
    Proof.
      induction (Rwf a).
      rewrite Fix5_eq; auto.
    Defined.
  End F.

  Global Instance Fix5_Proper_eq
  : Proper
      ((forall_relation (fun a =>
                           (forall_relation (fun a' => pointwise_relation _ (forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => forall_relation (fun e => forall_relation (fun h => eq))))))))
                             ==> (forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => forall_relation (fun e => forall_relation (fun h => eq))))))))
         ==> (forall_relation (fun a => forall_relation (fun b => forall_relation (fun c => forall_relation (fun d => forall_relation (fun e => forall_relation (fun h => eq))))))))
      Fix5.
  Proof. Fix_Proper_t @Fix5_eq Rwf. Qed.
End Fix5.

Arguments Fix5_Proper_eq {A B C D E H R Rwf P} _ _ _ _ _ _ _ _ _.
