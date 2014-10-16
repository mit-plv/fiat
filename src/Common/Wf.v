(** * Miscellaneous Well-Foundedness Facts *)
Require Import Coq.Setoids.Setoid Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat.

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

(** A variant of [Fix] that has a nice [Fix_eq] for functions which
    doesn't require [functional_extensionality]. *)
Section Fix.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c, D a b c -> Type)
          (F : forall x : A, (forall y : A, R y x -> forall b c d, P y b c d) -> forall b c d, P x b c d).

  Definition Fix3 a b c d : @P a b c d
    := @Fix { a : A & { b : B a & { c : C b & D c } } }
            (fun x y => R (projT1 x) (projT1 y))
            (well_founded_projT1_relation Rwf)
            (fun abcd => P (projT2 (projT2 (projT2 abcd))))
            (fun x f => @F (projT1 x) (fun y r b c d => f (existT _ y (existT _ b (existT _ c d))) r) _ _ _)
            (existT _ a (existT _ b (existT _ c d))).

  Definition Fix3_eq
             (F_ext : forall x (f g : forall y, R y x -> forall b c d, @P y b c d),
                        (forall y (p : R y x) b c d, f y p b c d = g y p b c d)
                        -> forall b c d, @F x f b c d = @F x g b c d)
  : forall a b c d, @Fix3 a b c d = @F a (fun y (_ : R y a) b c d => @Fix3 y b c d) b c d.
  Proof.
    intros.
    unfold Fix3; simpl.
    match goal with
      | [ |- @Fix ?A ?R ?Rwf ?P ?F ?x = _ ]
        => refine (@Coq.Init.Wf.Fix_eq A R Rwf P F _ x)
    end.
    intros; apply F_ext; intros.
    match goal with
      | [ H : forall y p, ?f y p = ?g y p
                          |- ?f ?y ?p = ?g ?y ?p ]
        => exact (H y p)
    end.
  Defined.
End Fix.
