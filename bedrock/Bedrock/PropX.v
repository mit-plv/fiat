(* An adaptation of Ni & Shao's XCAP assertion logic *)

Require Import Coq.Lists.List.

Set Implicit Arguments.


Section machine.
  Variables pc state : Type.

  Inductive propX : list Type -> Type :=
  | Inj : forall G, Prop -> propX G
  | Cptr : forall G, pc -> (state -> propX G) -> propX G
  | And : forall G, propX G -> propX G -> propX G
  | Or : forall G, propX G -> propX G -> propX G
  | Imply : forall G, propX G -> propX G -> propX G
  | Forall : forall G A, (A -> propX G) -> propX G
  | Exists : forall G A, (A -> propX G) -> propX G

  | Var0 : forall G A, A -> propX (A :: G)
  | Lift : forall G A, propX G -> propX (A :: G)
  | ForallX : forall G A, propX (A :: G) -> propX G
  | ExistsX : forall G A, propX (A :: G) -> propX G.

  Implicit Arguments Inj [G].
  Implicit Arguments Var0 [G A].
  Implicit Arguments Lift [G A].

  Definition PropX := propX nil.

  Fixpoint last (G : list Type) : Type :=
    match G with
      | nil => unit
      | T :: nil => T
      | _ :: G' => last G'
    end.

  Fixpoint eatLast (G : list Type) : list Type :=
    match G with
      | nil => nil
      | _ :: nil => nil
      | x :: G' => x :: eatLast G'
    end.

  Fixpoint subst G (p : propX G) : (last G -> PropX) -> propX (eatLast G) :=
    match p with
      | Inj _ P => fun _ => Inj P
      | Cptr _ i f => fun p' => Cptr i (fun x => subst (f x) p')
      | And _ p1 p2 => fun p' => And (subst p1 p') (subst p2 p')
      | Or _ p1 p2 => fun p' => Or (subst p1 p') (subst p2 p')
      | Imply _ p1 p2 => fun p' => Imply (subst p1 p') (subst p2 p')
      | Forall _ _ f => fun p' => Forall (fun x => subst (f x) p')
      | Exists _ _ f => fun p' => Exists (fun x => subst (f x) p')

      | Var0 G A v => match G return (last (A :: G) -> PropX) -> propX (eatLast (A :: G)) with
                        | nil => fun p' => p' v
                        | _ :: _ => fun _ => Var0 v
                      end

      | Lift G A p1 => match G return propX G -> ((last G -> PropX) -> propX (eatLast G))
                         -> (last (A :: G) -> PropX) -> propX (eatLast (A :: G)) with
                         | nil => fun p1 _ _ => p1
                         | _ :: _ => fun _ subst_p1 p' => Lift (subst_p1 p')
                       end p1 (subst p1)

      | ForallX G A p1 => fun p' =>
        match G return propX (A :: G) -> propX (eatLast (A :: G)) -> propX (eatLast G) with
          | nil => fun p1 _ => ForallX p1
          | _ :: _ => fun _ rc => ForallX rc
        end p1 (subst p1 (match G return (last G -> PropX) -> last (A :: G) -> PropX with
                            | nil => fun _ _ => Inj True
                            | _ => fun p' => p'
                          end p'))
      | ExistsX G A p1 => fun p' =>
        match G return propX (A :: G) -> propX (eatLast (A :: G)) -> propX (eatLast G) with
          | nil => fun p1 _ => ExistsX p1
          | _ :: _ => fun _ rc => ExistsX rc
        end p1 (subst p1 (match G return (last G -> PropX) -> last (A :: G) -> PropX with
                            | nil => fun _ _ => Inj True
                            | _ => fun p' => p'
                          end p'))
    end.

  Definition Subst A (p : propX (A :: nil)) (p' : A -> PropX) : PropX := subst p p'.

  Definition spec := state -> PropX.
  Definition codeSpec := pc -> option spec.

  Section specs.
    Variable specs : codeSpec.

    Inductive valid (G : list PropX) : PropX -> Prop :=
    | Env : forall P,
      In P G
      -> valid G P

    | Inj_I : forall (p : Prop),
      p
      -> valid G (Inj p)

    | Inj_E : forall p Q,
      valid G (Inj p)
      -> (p -> valid G Q)
      -> valid G Q

    | Cptr_I : forall f a,
      specs f = Some (fun x => a x)
      -> valid G (Cptr f a)

    | Cptr_E : forall f a Q,
      valid G (Cptr f a)
      -> (specs f = Some (fun x => a x) -> valid G Q)
      -> valid G Q

    | And_I : forall P Q,
      valid G P
      -> valid G Q
      -> valid G (And P Q)

    | And_E1 : forall P Q,
      valid G (And P Q)
      -> valid G P
    | And_E2 : forall P Q,
      valid G (And P Q)
      -> valid G Q

    | Or_I1 : forall P Q,
      valid G P
      -> valid G (Or P Q)
    | Or_I2 : forall P Q,
      valid G Q
      -> valid G (Or P Q)

    | Or_E : forall P Q R,
      valid G (Or P Q)
      -> valid (P :: G) R
      -> valid (Q :: G) R
      -> valid G R

    | Imply_I : forall P Q,
      valid (P :: G) Q
      -> valid G (Imply P Q)

    | Imply_E : forall P Q,
      valid G (Imply P Q)
      -> valid G P
      -> valid G Q

    | Forall_I : forall A P,
      (forall B : A, valid G (P B))
      -> valid G (Forall P)

    | Forall_E : forall A P (B : A),
      valid G (Forall P)
      -> valid G (P B)

    | Exists_I : forall A P (B : A),
      valid G (P B)
      -> valid G (Exists P)

    | Exists_E : forall A P Q,
      valid G (Exists P)
      -> (forall B : A, valid (P B :: G) Q)
      -> valid G Q

    | ForallX_I : forall A P,
      (forall a : A -> PropX, valid G (Subst P a))
      -> valid G (ForallX P)

    | ExistsX_I : forall A P (a : A -> PropX),
      valid G (Subst P a)
      -> valid G (ExistsX P).

    Inductive normal (G : list PropX) : PropX -> Prop :=
    | Coer : forall P,
      neutral G P
      -> normal G P

    | NoInj_I : forall p : Prop,
      p
      -> normal G (Inj p)

    | NoInj_E : forall p Q,
      neutral G (Inj p)
      -> (p -> normal G Q)
      -> normal G Q

    | NoCptr_I : forall f a,
      specs f = Some (fun x => a x)
      -> normal G (Cptr f a)

    | NoCptr_E : forall f a Q,
      neutral G (Cptr f a)
      -> (specs f = Some (fun x => a x) -> normal G Q)
      -> normal G Q

    | NoAnd_I : forall P Q,
      normal G P
      -> normal G Q
      -> normal G (And P Q)

    | NoOr_I1 : forall P Q,
      normal G P
      -> normal G (Or P Q)
    | NoOr_I2 : forall P Q,
      normal G Q
      -> normal G (Or P Q)

    | NoOr_E : forall P Q R,
      neutral G (Or P Q)
      -> normal (P :: G) R
      -> normal (Q :: G) R
      -> normal G R

    | NoImply_I : forall P Q,
      normal (P :: G) Q
      -> normal G (Imply P Q)

    | NoForall_I : forall A P,
      (forall B : A, normal G (P B))
      -> normal G (Forall P)

    | NoExists_I : forall A P (B : A),
      normal G (P B)
      -> normal G (Exists P)

    | NoExists_E : forall A P Q,
      neutral G (Exists P)
      -> (forall B : A, normal (P B :: G) Q)
      -> normal G Q

    | NoForallX_I : forall A P,
      (forall a : A -> PropX, normal G (Subst P a))
      -> normal G (ForallX P)

    | NoExistsX_I : forall A P (a : A -> PropX),
      normal G (Subst P a)
      -> normal G (ExistsX P)

    with neutral (G : list PropX) : PropX -> Prop :=
    | NoEnv : forall P,
      In P G
      -> neutral G P

    | NoAnd_E1 : forall P Q,
      neutral G (And P Q)
      -> neutral G P
    | NoAnd_E2 : forall P Q,
      neutral G (And P Q)
      -> neutral G Q

    | NoImply_E : forall P Q,
      neutral G (Imply P Q)
      -> normal G P
      -> neutral G Q

    | NoForall_E : forall A P (B : A),
      neutral G (Forall P)
      -> neutral G (P B).

    Scheme normal_min := Minimality for normal Sort Prop
    with neutral_min := Minimality for neutral Sort Prop.

    Combined Scheme normal_neutral_min from normal_min, neutral_min.

    Inductive normalP (G : list PropX) : PropX -> Prop :=
    | NopCoer : forall P,
      neutralP G P
      -> normalP G P

    | NopInj_I : forall p : Prop,
      p
      -> normalP G (Inj p)

    | NopInj_E : forall p Q,
      neutralP G (Inj p)
      -> (p -> normalP G Q)
      -> normalP G Q

    | NopCptr_I : forall f a,
      specs f = Some (fun x => a x)
      -> normalP G (Cptr f a)

    | NopCptr_E : forall f a Q,
      neutralP G (Cptr f a)
      -> (specs f = Some (fun x => a x) -> normalP G Q)
      -> normalP G Q

    | NopAnd_I : forall P Q,
      normalP G P
      -> normalP G Q
      -> normalP G (And P Q)

    | NopOr_I1 : forall P Q,
      normalP G P
      -> normalP G (Or P Q)
    | NopOr_I2 : forall P Q,
      normalP G Q
      -> normalP G (Or P Q)

    | NopOr_E : forall P Q R,
      neutralP G (Or P Q)
      -> normalP (P :: G) R
      -> normalP (Q :: G) R
      -> normalP G R

    | NopImply_I : forall P Q,
      normalP (P :: G) Q
      -> normalP G (Imply P Q)

    | NopForall_I : forall A P,
      (forall B : A, normalP G (P B))
      -> normalP G (Forall P)

    | NopExists_I : forall A P (B : A),
      normalP G (P B)
      -> normalP G (Exists P)

    | NopExists_E : forall A P Q,
      neutralP G (Exists P)
      -> (forall B : A, normalP (P B :: G) Q)
      -> normalP G Q

    | NopForallX_I : forall A P,
      (forall a : A -> PropX, normalP G (Subst P a))
      -> normalP G (ForallX P)

    | NopExistsX_I : forall A P (a : A -> PropX),
      normalP G (Subst P a)
      -> normalP G (ExistsX P)

    with neutralP (G : list PropX) : PropX -> Prop :=
    | Coer' : forall P,
      normalP G P
      -> neutralP G P

    | NopEnv : forall P,
      In P G
      -> neutralP G P

    | NopAnd_E1 : forall P Q,
      neutralP G (And P Q)
      -> neutralP G P
    | NopAnd_E2 : forall P Q,
      neutralP G (And P Q)
      -> neutralP G Q

    | NopImply_E : forall P Q,
      neutralP G (Imply P Q)
      -> normalP G P
      -> neutralP G Q

    | NopForall_E : forall A P (B : A),
      neutralP G (Forall P)
      -> neutralP G (P B).

    Scheme normalP_min := Minimality for normalP Sort Prop
    with neutralP_min := Minimality for neutralP Sort Prop.

    Combined Scheme normalP_neutralP_min from normalP_min, neutralP_min.


    Inductive seq (G : list PropX) : PropX -> Prop :=
    | Inj_R : forall p : Prop,
      p
      -> seq G (Inj p)

    | Inj_L : forall (p : Prop) Q,
      In (Inj p) G
      -> (p -> seq G Q)
      -> seq G Q

    | Cptr_R : forall f a,
      specs f = Some (fun x => a x)
      -> seq G (Cptr f a)

    | Cptr_L : forall f a Q,
      In (Cptr f a) G
      -> (specs f = Some (fun x => a x) -> seq G Q)
      -> seq G Q

    | And_R : forall P Q,
      seq G P
      -> seq G Q
      -> seq G (And P Q)

    | And_L1 : forall P Q R,
      In (And P Q) G
      -> seq (P :: G) R
      -> seq G R
    | And_L2 : forall P Q R,
      In (And P Q) G
      -> seq (Q :: G) R
      -> seq G R

    | Or_R1 : forall P Q,
      seq G P
      -> seq G (Or P Q)
    | Or_R2 : forall P Q,
      seq G Q
      -> seq G (Or P Q)

    | Or_L : forall P Q R,
      In (Or P Q) G
      -> seq (P :: G) R
      -> seq (Q :: G) R
      -> seq G R

    | Imply_R : forall P Q,
      seq (P :: G) Q
      -> seq G (Imply P Q)

    | Imply_L : forall P Q R,
      In (Imply P Q) G
      -> seq G P
      -> seq (Q :: G) R
      -> seq G R

    | Init : forall P,
      In P G
      -> seq G P

    | Forall_R : forall A P,
      (forall B : A, seq G (P B))
      -> seq G (Forall P)

    | Forall_L : forall A P (B : A) Q,
      In (Forall P) G
      -> seq (P B :: G) Q
      -> seq G Q

    | Exists_R : forall A P (B : A),
      seq G (P B)
      -> seq G (Exists P)

    | Exists_L : forall A P Q,
      In (Exists P) G
      -> (forall B : A, seq (P B :: G) Q)
      -> seq G Q

    | ForallX_R : forall A P,
      (forall a : A -> PropX, seq G (Subst P a))
      -> seq G (ForallX P)

    | ExistsX_R : forall A P (a : A -> PropX),
      seq G (Subst P a)
      -> seq G (ExistsX P).


    Inductive seqP (G : list PropX) : PropX -> Prop :=
    | Cut : forall P Q,
      seqP G P
      -> seqP (P :: G) Q
      -> seqP G Q

    | CInj_R : forall p : Prop,
      p
      -> seqP G (Inj p)

    | CInj_L : forall (p : Prop) Q,
      In (Inj p) G
      -> (p -> seqP G Q)
      -> seqP G Q

    | CCptr_R : forall f a,
      specs f = Some (fun x => a x)
      -> seqP G (Cptr f a)

    | CCptr_L : forall f a Q,
      In (Cptr f a) G
      -> (specs f = Some (fun x => a x) -> seqP G Q)
      -> seqP G Q

    | CAnd_R : forall P Q,
      seqP G P
      -> seqP G Q
      -> seqP G (And P Q)

    | CAnd_L1 : forall P Q R,
      In (And P Q) G
      -> seqP (P :: G) R
      -> seqP G R
    | CAnd_L2 : forall P Q R,
      In (And P Q) G
      -> seqP (Q :: G) R
      -> seqP G R

    | COr_R1 : forall P Q,
      seqP G P
      -> seqP G (Or P Q)
    | COr_R2 : forall P Q,
      seqP G Q
      -> seqP G (Or P Q)

    | COr_L : forall P Q R,
      In (Or P Q) G
      -> seqP (P :: G) R
      -> seqP (Q :: G) R
      -> seqP G R

    | CImply_R : forall P Q,
      seqP (P :: G) Q
      -> seqP G (Imply P Q)

    | CImply_L : forall P Q R,
      In (Imply P Q) G
      -> seqP G P
      -> seqP (Q :: G) R
      -> seqP G R

    | CInit : forall P,
      In P G
      -> seqP G P

    | CForall_R : forall A P,
      (forall B : A, seqP G (P B))
      -> seqP G (Forall P)

    | CForall_L : forall A P (B : A) Q,
      In (Forall P) G
      -> seqP (P B :: G) Q
      -> seqP G Q

    | CExists_R : forall A P (B : A),
      seqP G (P B)
      -> seqP G (Exists P)

    | CExists_L : forall A P Q,
      In (Exists P) G
      -> (forall B : A, seqP (P B :: G) Q)
      -> seqP G Q

    | CForallX_R : forall A P,
      (forall a : A -> PropX, seqP G (Subst P a))
      -> seqP G (ForallX P)

    | CExistsX_R : forall A P (a : A -> PropX),
      seqP G (Subst P a)
      -> seqP G (ExistsX P).

    Hint Constructors valid normal neutral normalP neutralP seqP.


    Theorem normal_neutral_sound : forall G,
      (forall P, normal G P -> valid G P)
      /\ (forall P, neutral G P -> valid G P).
    Proof.
      apply normal_neutral_min; try solve [
        intros; ((eapply Or_I1; assumption) ||
                 (eapply Or_I2; assumption))
      | eauto ].
    Qed.

    Theorem normalP_neutralP_sound : forall G,
      (forall P, normalP G P -> valid G P)
      /\ (forall P, neutralP G P -> valid G P).
    Proof.
      apply normalP_neutralP_min; try solve [
        intros; ((eapply Or_I1; assumption) ||
                 (eapply Or_I2; assumption))
      | eauto ].
    Qed.

    Theorem normalP_complete : forall G P, valid G P -> normalP G P.
    Proof.
      induction 1; eauto.
    Qed.

    Theorem neutralP_complete : forall G P, valid G P -> neutralP G P.
    Proof.
      induction 1; eauto.
    Qed.

    Hint Extern 1 (In _ _) => simpl; tauto.

    Hint Extern 3 (incl _ _) =>
      let x := fresh "x" in intro x;
        repeat match goal with
                 | [ H : incl _ _ |- _ ] => generalize (H x); clear H
               end; simpl; intuition (subst; assumption).

    Theorem incl_cons : forall A x (G G' : list A),
      incl G G'
      -> incl (x :: G) (x :: G').
    Proof.
      auto.
    Qed.

    Hint Resolve incl_cons.

    Lemma normal_neutral_weaken : forall G,
      (forall Q, normal G Q
      -> (forall G', incl G G'
        -> normal G' Q))
    /\ (forall Q, neutral G Q
      -> (forall G', incl G G'
        -> neutral G' Q)).
    Proof.
      apply normal_neutral_min; eauto; eauto 7.
    Qed.

    Lemma normal_weaken : forall G Q, normal G Q
      -> forall G', incl G G'
        -> normal G' Q.
    Proof.
      generalize normal_neutral_weaken; firstorder.
    Qed.

    Lemma neutral_weaken : forall G Q, neutral G Q
      -> forall G', incl G G'
        -> neutral G' Q.
    Proof.
      generalize normal_neutral_weaken; firstorder.
    Qed.

    Hint Extern 1 (normal _ _) =>
      match goal with
        | [ H : normal _ _ |- _ ] => apply (normal_weaken H)
      end.

    Hint Extern 1 (neutral _ _) =>
      match goal with
        | [ H : neutral _ _ |- _ ] => apply (neutral_weaken H)
      end.

    Lemma incl_cons2 : forall A (P P0 : A) G G0,
      incl G (P :: G0)
      -> incl (P0 :: G) (P :: P0 :: G0).
    Proof.
      auto.
    Qed.

    Hint Immediate incl_cons2.

    Lemma In_incl : forall A (ls1 ls2 : list A) x,
      In x ls1
      -> incl ls1 ls2
      -> In x ls2.
    Proof.
      intuition.
    Qed.

    Hint Resolve In_incl.

    Lemma subst_Env : forall P0 G P G0,
      In P0 G
      -> incl G (P :: G0)
      -> neutral G0 P
      -> neutral G0 P0.
    Proof.
      intros ? ? ? ? H1 H2; generalize (H2 _ H1); simpl; intuition; subst; auto.
    Qed.

    Hint Immediate subst_Env.

    Lemma normal_neutral_subst : forall P PG, (forall Q, normal PG Q
      -> (forall G, incl PG (P :: G)
        -> neutral G P
        -> normal G Q))
    /\ (forall Q, neutral PG Q
      -> (forall G, incl PG (P :: G)
        -> neutral G P
        -> neutral G Q)).
    Proof.
      intro; apply normal_neutral_min; eauto; eauto 7.
    Qed.

    Lemma normal_subst : forall G P Q,
      normal (P :: G) Q
      -> neutral G P
      -> normal G Q.
    Proof.
      generalize normal_neutral_subst; firstorder.
    Qed.

    Hint Resolve normal_subst.

    Theorem seq_sound : forall G P, seq G P -> normal G P.
    Proof.
      induction 1; eauto.
    Qed.

    Hint Resolve Init Inj_R Cptr_R And_R Or_R1 Or_R2 Imply_R Forall_R Exists_R ForallX_R ExistsX_R.

    Ltac ready con := eapply con; solve [ instantiate; eauto 7 ].

    Ltac doLeft := intros;
      ready Inj_L || ready Cptr_L || ready And_L1 || ready And_L2 || ready Or_L
        || ready Imply_L || ready Forall_L || ready Exists_L.

    Theorem seq_weaken : forall G p, seq G p
      -> forall G', incl G G'
        -> seq G' p.
    Proof.
      induction 1; eauto; doLeft.
    Qed.

    Section seq_complete.
      Hint Resolve seq_weaken.

      Theorem seq_complete : forall G,
        (forall P, normal G P
          -> seq G P)
        /\ (forall P, neutral G P
          -> forall Q, seq (P :: G) Q
            -> seq G Q).
      Proof.
        apply normal_neutral_min; eauto; intros;
          match goal with
            | [ H : _ |- _ ] => apply H; doLeft
          end.
      Qed.
    End seq_complete.

    Hint Extern 2 (seq _ _) =>
      match goal with
        | [ H : seq _ _ |- _ ] => apply (seq_weaken H)
        | [ H : forall x : ?A, seq _ _, B : ?A |- _ ] => apply (seq_weaken (H B))
      end.

    Lemma normalP_neutralP_weaken : forall G,
      (forall Q, normalP G Q
        -> (forall G', incl G G'
          -> normalP G' Q))
      /\ (forall Q, neutralP G Q
        -> (forall G', incl G G'
          -> neutralP G' Q)).
      apply normalP_neutralP_min; eauto; eauto 7.
    Qed.

    Lemma normalP_weaken : forall G Q, normalP G Q
      -> forall G', incl G G'
        -> normalP G' Q.
      generalize normalP_neutralP_weaken; firstorder.
    Qed.

    Lemma neutralP_weaken : forall G Q, neutralP G Q
      -> forall G', incl G G'
        -> neutralP G' Q.
      generalize normalP_neutralP_weaken; firstorder.
    Qed.

    Hint Extern 1 (normalP _ _) =>
      match goal with
        | [ H : normalP _ _ |- _ ] => apply (normalP_weaken H)
      end.

    Hint Extern 1 (neutralP _ _) =>
      match goal with
        | [ H : neutralP _ _ |- _ ] => apply (neutralP_weaken H)
      end.

    Lemma subst_EnvP : forall P0 G P G0,
      In P0 G
      -> incl G (P :: G0)
      -> neutralP G0 P
      -> neutralP G0 P0.
      intros ? ? ? ? H1 H2; generalize (H2 _ H1); simpl; intuition; subst; auto.
    Qed.

    Hint Immediate subst_EnvP.

    Lemma normalP_neutralP_subst : forall P PG,
      (forall Q, normalP PG Q
        -> (forall G, incl PG (P :: G)
          -> neutralP G P
          -> normalP G Q))
      /\ (forall Q, neutralP PG Q
        -> (forall G, incl PG (P :: G)
          -> neutralP G P
          -> neutralP G Q)).
    Proof.
      intro; apply normalP_neutralP_min; try solve [ eauto ].
      intros; eapply NopOr_E. eapply H0. eassumption. eassumption. eauto. eauto.
    Qed.

    Lemma normalP_subst : forall G P Q,
      normalP (P :: G) Q
      -> neutralP G P
      -> normalP G Q.
    Proof.
      generalize normalP_neutralP_subst; firstorder.
    Qed.

    Hint Resolve normalP_subst.

    Theorem seqP_sound : forall G P, seqP G P -> normalP G P.
    Proof.
      induction 1; eauto.
    Qed.

    Theorem seqP_weaken : forall G p, seqP G p
      -> forall G', incl G G'
        -> seqP G' p.
    Proof.
      induction 1; eauto.
    Qed.

    Hint Resolve seqP_weaken.

    Theorem seqP_complete : forall G,
      (forall P, normalP G P
        -> seqP G P)
      /\ (forall P, neutralP G P
        -> forall Q, seqP (P :: G) Q
          -> seqP G Q).
    Proof.
      apply normalP_neutralP_min; eauto.
    Qed.

    Lemma destruct_PropX' : forall G (P : propX G),
      match G return propX G -> Prop with
        | nil => fun P =>
          (exists p, P = Inj p)
          \/ (exists i, exists f, P = Cptr i f)
          \/ (exists p1, exists p2, P = And p1 p2)
          \/ (exists p1, exists p2, P = Or p1 p2)
          \/ (exists p1, exists p2, P = Imply p1 p2)
          \/ (exists A, exists p1 : A -> _, P = Forall p1)
          \/ (exists A, exists p1 : A -> _, P = Exists p1)
          \/ (exists A, exists p1 : propX (A :: _), P = ForallX p1)
          \/ (exists A, exists p1 : propX (A :: _), P = ExistsX p1)
        | _ => fun _ => True
      end P.
    Proof.
      destruct P; destruct G; eauto 11.
    Qed.

    Theorem destruct_PropX : forall P : PropX,
      (exists p, P = Inj p)
      \/ (exists i, exists f, P = Cptr i f)
      \/ (exists p1, exists p2, P = And p1 p2)
      \/ (exists p1, exists p2, P = Or p1 p2)
      \/ (exists p1, exists p2, P = Imply p1 p2)
      \/ (exists A, exists p1 : A -> _, P = Forall p1)
      \/ (exists A, exists p1 : A -> _, P = Exists p1)
      \/ (exists A, exists p1 : propX (A :: _), P = ForallX p1)
      \/ (exists A, exists p1 : propX (A :: _), P = ExistsX p1).
    Proof.
      intros; exact (destruct_PropX' P).
    Qed.

    Ltac innerPredicative := let GG := fresh "GG" in induction 1; intro GG; destruct GG; intuition;
      try match goal with
            | [ H1 : incl _ _, H2 : In _ _ |- _ ] => generalize (H1 _ H2); simpl; intuition; subst; intuition
          end;
      repeat match goal with
               | [ H : _ -> forall GG : list Type, _ |- _ ] => specialize (fun pf => H pf nil); simpl in H
               | [ H : forall GG : list Type, _ |- _ ] => specialize (H nil); simpl in H
             end;
      doLeft || solve [ eauto ]
        || (try match goal with
                  | [ _ : match ?P with Inj _ _ => _ | Cptr _ _ _ => _ | And _ _ _ => _ | Or _ _ _ => _ | Imply _ _ _ => _
                            | Forall _ _ _ => _ | Exists _ _ _ => _ | Var0 _ _ _ => _ | Lift _ _ _ => _
                            | ForallX _ _ _ => _ | ExistsX _ _ _ => _ end |- _ ] => specialize (destruct_PropX P); intro;
                  repeat match goal with
                           | [ H : _ \/ _ |- _ ] => destruct H
                           | [ H : ex _ |- _ ] => destruct H
                         end; subst; intuition
                end;
        try match goal with
              | [ H : ex _ |- _ ] => destruct H
            end;
        repeat match goal with
                 | [ _ : incl _ (?P :: _), H : forall P' : propX nil, _ |- _ ] =>
                   specialize (H P); simpl in H
                 | [ _ : incl _ (?P :: _), H : forall pf (P' : propX nil), _ |- _ ] =>
                   eapply Exists_L; [ solve [ eauto ] | intro witness;
                     specialize (H witness P); simpl in H ]
                 | [ _ : incl _ (?P :: _), x : _, H : forall pf (P' : propX nil), _ |- _ ] =>
                   specialize (H x P); simpl in H
               end;
        match goal with
          | [ H : _, G0 : _, P1 : propX nil |- _ ] =>
            solve [ apply H with (P1 :: G0); auto ]
          | [ H : _, G0 : _, P1 : _ -> propX nil, A : Type |- _ ] =>
            match goal with
            | [ B : A |- _ ] => solve [ apply H with B (P1 B :: G0); eauto ]
            end
          | _ => solve [ eauto | doLeft ]
          | [ H : _, G0 : _, P1 : propX nil |- _ ] =>
            solve [ apply H with (P1 :: G0); eauto ]
          | _ => solve [ eauto 8 ]
        end).

    Lemma inner_Inj : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG return (propX GG -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Inj GG' P => P
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_Cptr : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG return (propX GG -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Cptr GG' i P =>
                  match GG' return (_ -> propX GG') -> Prop with
                    | nil => fun P =>
                      specs i = Some (fun x => P x)
                      /\ (forall st (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P st :: G0) -> seq G0 (P st) -> seq G0 Q0)
                    | _ => fun _ => False
                  end P
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_And : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG return (propX GG -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | And GG' P1 P2 =>
                  match GG' return propX GG' -> propX GG' -> Prop with
                    | nil => fun P1 P2 =>
                      seq G P1
                      /\ seq G P2
                      /\ (forall (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
                      /\ (forall (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
                    | _ => fun _ _ => False
                  end P1 P2
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_Or1 : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG return (propX GG -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Or GG' P1 P2 =>
                  match GG' return propX GG' -> propX GG' -> Prop with
                    | nil => fun P1 P2 =>
                      seq G P1
                      /\ (forall (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
                    | _ => fun _ _ => False
                  end P1 P2
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_Or2 : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG return (propX GG -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Or GG' P1 P2 =>
                  match GG' return propX GG' -> propX GG' -> Prop with
                    | nil => fun P1 P2 =>
                      seq G P2
                      /\ (forall (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
                    | _ => fun _ _ => False
                  end P1 P2
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_Imply : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG return (propX GG -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Imply GG' P1 P2 =>
                  match GG' return propX GG' -> propX GG' -> Prop with
                    | nil => fun P1 P2 =>
                      seq (P1 :: G) P2
                      /\ (forall (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
                      /\ (forall (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
                    | _ => fun _ _ => False
                  end P1 P2
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_Forall : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG return (propX GG -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Forall GG' A0 P =>
                  match GG' return (A0 -> propX GG') -> Prop with
                    | nil => fun P =>
                      (forall B : A0, seq G (P B)) /\
                      (forall (a : A0) (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P a :: G0) -> seq G0 (P a) -> seq G0 Q0)
                    | _ => fun _ => False
                  end P
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_Exists : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG as GG0 return (propX GG0 -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | Exists GG' A0 P =>
                  match GG' return (A0 -> propX GG') -> Prop with
                    | nil => fun P =>
                      (exists B, seq G (P B)) /\
                      (forall (a : A0) (PG0 : list PropX) (Q0 : PropX),
                        seq PG0 Q0 ->
                        forall G0 : list (propX nil),
                          incl PG0 (P a :: G0) -> seq G0 (P a) -> seq G0 Q0)
                    | _ => fun _ => False
                  end P
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_ForallX : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG as GG0 return (propX GG0 -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | ForallX GG' A0 P =>
                  match GG' return propX (_ :: GG') -> Prop with
                    | nil => fun P => forall B, seq G (Subst P B)
                    | _ => fun _ => False
                  end P
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Lemma inner_ExistsX : forall PG Q, seq PG Q
      -> forall (GG : list Type) (P' : propX GG) (G : list PropX),
        match GG as GG0 return (propX GG0 -> Prop) with
          | nil =>
            fun P' =>
              match P' with
                | ExistsX GG' A0 P =>
                  match GG' return propX (_ :: GG') -> Prop with
                    | nil => fun P => exists B, seq G (Subst P B)
                    | _ => fun _ => False
                  end P
                | _ => False
              end -> incl PG (P' :: G) -> seq G Q
          | T :: l => fun _ : propX (T :: l) => True
        end P'.
    Proof.
      innerPredicative.
    Qed.

    Ltac outerPredicative :=
      induction 2; intuition;
        try match goal with
              | [ |- match ?E with Inj _ _ => _ | Cptr _ _ _ => _ | And _ _ _ => _ | Or _ _ _ => _ | Imply _ _ _ => _
                       | Forall _ _ _ => _ | Exists _ _ _ => _ | Var0 _ _ _ => _ | Lift _ _ _ => _ | ForallX _ _ _ => _ | ExistsX _ _ _ => _ end ] =>
              specialize (destruct_PropX E); intro;
                repeat match goal with
                         | [ H : _ \/ _ |- _ ] => destruct H
                         | [ H : ex _ |- _ ] => destruct H
                       end; subst; intuition; doLeft
            end;
        match goal with
          | [ H : _, _ : incl _ (?P :: _) |- _ ] => solve [ apply (inner_Inj H P); intuition
            | apply (inner_Cptr H P); intuition
            | apply (inner_And H P); intuition
            | apply (inner_Or1 H P); intuition
            | apply (inner_Or2 H P); intuition
            | apply (inner_Imply H P); intuition
            | apply (inner_Forall H P); intuition
            | apply (inner_Exists H P); intuition eauto
            | apply (inner_ForallX H P); intuition
            | apply (inner_ExistsX H P); intuition eauto ]
        end.

    Lemma outer_Inj' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Inj GG' _ => incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_Inj : forall PG Q, seq PG Q
      -> forall G P, seq G (Inj P) -> incl PG (Inj P :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_Inj' H H0); eauto.
    Qed.

    Lemma outer_Cptr' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Cptr GG' i P1 =>
            match GG' return (_ -> propX GG') -> Prop with
              | nil => fun P1 =>
                forall st (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (P1 st :: G0) -> seq G0 (P1 st) -> seq G0 Q0
              | _ => fun _ => False
            end P1 -> incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_Cptr : forall PG Q, seq PG Q
      -> forall G i P1, seq G (Cptr i P1)
        -> (forall st (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (P1 st :: G0) -> seq G0 (P1 st) -> seq G0 Q0)
        -> incl PG (Cptr i P1 :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_Cptr' H H0); eauto.
    Qed.

    Lemma outer_And' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | And GG' P1 P2 =>
            match GG' return propX GG' -> propX GG' -> Prop with
              | nil => fun P1 P2 =>
                (forall (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
                /\ (forall (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
              | _ => fun _ _ => False
            end P1 P2 -> incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_And : forall PG Q, seq PG Q
      -> forall G P1 P2, seq G (And P1 P2)
        -> (forall (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
        ->  (forall (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
        -> incl PG (And P1 P2 :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_And' H H0); eauto.
    Qed.

    Lemma outer_Or' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Or GG' P1 P2 =>
            match GG' return propX GG' -> propX GG' -> Prop with
              | nil => fun P1 P2 =>
                (forall (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
                /\ (forall (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
              | _ => fun _ _ => False
            end P1 P2 -> incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_Or : forall PG Q, seq PG Q
      -> forall G P1 P2, seq G (Or P1 P2)
        -> (forall (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
        ->  (forall (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
        -> incl PG (Or P1 P2 :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_Or' H H0); eauto.
    Qed.

    Lemma outer_Imply' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Imply GG' P1 P2 =>
            match GG' return propX GG' -> propX GG' -> Prop with
              | nil => fun P1 P2 =>
                (forall (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
                /\ (forall (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
              | _ => fun _ _ => False
            end P1 P2 -> incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_Imply : forall PG Q, seq PG Q
      -> forall G P1 P2, seq G (Imply P1 P2)
        -> (forall (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (P1 :: G0) -> seq G0 P1 -> seq G0 Q0)
        ->  (forall (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (P2 :: G0) -> seq G0 P2 -> seq G0 Q0)
        -> incl PG (Imply P1 P2 :: G) -> seq G Q.
      intros; specialize (outer_Imply' H H0); eauto.
    Qed.

    Lemma outer_Forall' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Forall GG' A p =>
            match GG' return (A -> propX GG') -> Prop with
              | nil => fun p =>
                forall (a : A) (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (p a :: G0) -> seq G0 (p a) -> seq G0 Q0
              | _ => fun _ => False
            end p -> incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_Forall : forall PG Q, seq PG Q
      -> forall G A (p : A -> _), seq G (Forall p) ->
        (forall (a : A) (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (p a :: G0) -> seq G0 (p a) -> seq G0 Q0)
        -> incl PG (Forall p :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_Forall' H H0); eauto.
    Qed.

    Lemma outer_Exists' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | Exists GG' A p =>
            match GG' return (A -> propX GG') -> Prop with
              | nil => fun p =>
                forall (a : A) (PG0 : list PropX) (Q0 : PropX),
                  seq PG0 Q0 ->
                  forall G0 : list (propX nil),
                    incl PG0 (p a :: G0) -> seq G0 (p a) -> seq G0 Q0
              | _ => fun _ => False
            end p -> incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_Exists : forall PG Q, seq PG Q
      -> forall G A p, seq G (Exists p) ->
        (forall (a : A) (PG0 : list PropX) (Q0 : PropX),
          seq PG0 Q0 ->
          forall G0 : list (propX nil),
            incl PG0 (p a :: G0) -> seq G0 (p a) -> seq G0 Q0)
        -> incl PG (Exists p :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_Exists' H H0); eauto.
    Qed.

    Lemma outer_ForallX' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | ForallX _ A p =>
            incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_ForallX : forall PG Q, seq PG Q
      -> forall G A (p : propX (A :: _)), seq G (ForallX p) ->
        incl PG (ForallX p :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_ForallX' H H0); eauto.
    Qed.

    Lemma outer_ExistsX' : forall PG Q, seq PG Q
      -> forall G P, seq G P ->
        match P with
          | ExistsX _ A p =>
            incl PG (P :: G) -> seq G Q
          | _ => True
        end.
    Proof.
      outerPredicative.
    Qed.

    Lemma outer_ExistsX : forall PG Q, seq PG Q
      -> forall G A (p : propX (A :: _)), seq G (ExistsX p) ->
        incl PG (ExistsX p :: G) -> seq G Q.
    Proof.
      intros; specialize (outer_ExistsX' H H0); eauto.
    Qed.

    Hint Immediate outer_Inj outer_Cptr outer_And outer_Or outer_Imply
      outer_Forall outer_Exists outer_ForallX outer_ExistsX.

    Lemma cut_admissibility' : forall GG (P : propX GG),
      match GG return propX GG -> Prop with
        | _ :: _ => fun _ => True
        | nil => fun P => forall PG Q, seq PG Q
          -> forall G, incl PG (P :: G)
          -> seq G P
          -> seq G Q
      end P.
    Proof.
      induction P; destruct G; intuition eauto.
    Qed.

    Theorem cut_admissibility : forall P G Q,
      seq G P
      -> seq (P :: G) Q
      -> seq G Q.
    Proof.
      intros; eapply (@cut_admissibility' nil); eauto.
    Qed.

    Hint Resolve cut_admissibility.

    Theorem cut_elimination : forall G P,
      seqP G P
      -> seq G P.
    Proof.
      induction 1; eauto; doLeft.
    Qed.

    Lemma seqP_complete' : forall G P, normalP G P
      -> seqP G P.
    Proof.
      generalize seqP_complete; firstorder.
    Qed.

    Theorem normalization : forall G P,
      valid G P
      -> normal G P.
    Proof.
      intros; apply seq_sound; apply cut_elimination; apply seqP_complete';
        apply normalP_complete; assumption.
    Qed.

    Definition interp := valid nil.

    Lemma neutral_contra' : forall G P, neutral G P
      -> G = nil
      -> False.
    Proof.
      induction 1; simpl in *; intros; subst; intuition.
    Qed.

    Lemma neutral_contra : forall P, neutral nil P
      -> False.
    Proof.
      intros; eapply neutral_contra'; eauto.
    Qed.

    Hint Immediate neutral_contra.

    Hint Unfold interp.

    Theorem normal_sound : forall G P, normal G P -> valid G P.
      generalize normal_neutral_sound; firstorder.
    Qed.

    Hint Immediate normal_sound.

    Lemma interp_sound : forall P, interp P
      -> match P with
           | Inj _ p => p
           | Cptr G f a => match G return (_ -> propX G) -> Prop with
                             | nil => fun a => specs f = Some (fun x => a x)
                             | _ => fun _ => False
                           end a
           | And G P1 P2 => match G return propX G -> propX G -> Prop with
                              | nil => fun P1 P2 => interp P1 /\ interp P2
                              | _ => fun _ _ => False
                            end P1 P2
           | Or G P1 P2 => match G return propX G -> propX G -> Prop with
                             | nil => fun P1 P2 => interp P1 \/ interp P2
                             | _ => fun _ _ => False
                           end P1 P2
           | Imply G P1 P2 => match G return propX G -> propX G -> Prop with
                                | nil => fun P1 P2 => interp P1 -> interp P2
                                | _ => fun _ _ => False
                              end P1 P2
           | Forall G _ P1 => match G return (_ -> propX G) -> Prop with
                                | nil => fun P1 => forall x, interp (P1 x)
                                | _ => fun _ => False
                              end P1
           | Exists G _ P1 => match G return (_ -> propX G) -> Prop with
                                | nil => fun P1 => exists x, interp (P1 x)
                                | _ => fun _ => False
                              end P1
           | ForallX G _ P1 => match G return propX (_ :: G) -> Prop with
                                | nil => fun P1 => forall x, interp (Subst P1 x)
                                | _ => fun _ => False
                              end P1
           | ExistsX G _ P1 => match G return propX (_ :: G) -> Prop with
                                 | nil => fun P1 => exists x, interp (Subst P1 x)
                                 | _ => fun _ => False
                               end P1
           | _ => False
         end.
      intros ? H; apply normalization in H; inversion H; subst; clear H; try solve [ elimtype False; eauto ]; intuition eauto.
    Qed.

    Ltac sound := intros; match goal with
                            | [ H : interp _ |- _ ] => solve [ apply interp_sound in H; auto ]
                          end.

    Theorem Inj_sound : forall p, interp (Inj p) -> p.
      sound.
    Qed.

    Theorem Cptr_sound : forall f a, interp (Cptr f a)
      -> specs f = Some (fun x => a x).
      sound.
    Qed.

    Theorem And_sound : forall P Q, interp (And P Q)
      -> interp P /\ interp Q.
      sound.
    Qed.

    Theorem Or_sound : forall P Q, interp (Or P Q)
      -> interp P \/ interp Q.
      sound.
    Qed.

    Theorem Imply_sound : forall P Q, interp (Imply P Q)
      -> interp P -> interp Q.
      sound.
    Qed.

    Theorem Forall_sound : forall A (P : A -> _), interp (Forall P)
      -> forall x, interp (P x).
      sound.
    Qed.

    Theorem Exists_sound : forall A (P : A -> _), interp (Exists P)
      -> exists x, interp (P x).
      sound.
    Qed.

    Theorem ForallX_sound : forall A (P : propX (A :: nil)), interp (ForallX P)
      -> forall f, interp (Subst P f).
      sound.
    Qed.

    Theorem ExistsX_sound : forall A (P : propX (A :: nil)), interp (ExistsX P)
      -> exists f, interp (Subst P f).
      sound.
    Qed.
  End specs.
End machine.

Implicit Arguments Inj [pc state G].
Implicit Arguments Var0 [pc state G A].
Implicit Arguments Lift [pc state G A].
Notation "[| p |]" := (Inj p%type) : PropX_scope.
Infix "/\" := And : PropX_scope.
Infix "\/" := Or : PropX_scope.
Infix "--->" := Imply (at level 86, right associativity) : PropX_scope.

Notation "'Al' x , P" := (Forall (fun x => P)) (x ident, at level 89) : PropX_scope.
Notation "'Al' x : A , P" := (Forall (fun x : A => P)) (x ident, at level 89) : PropX_scope.
Notation "'Ex' x , P" := (Exists (fun x => P)) (x ident, at level 89) : PropX_scope.
Notation "'Ex' x : A , P" := (Exists (fun x : A => P)) (x ident, at level 89) : PropX_scope.

Notation "'AlX' , P" := (ForallX P) (at level 89) : PropX_scope.
Notation "'AlX' : A , P" := (ForallX (A := A) P) (at level 89) : PropX_scope.
Notation "'ExX' , P" := (ExistsX P) (at level 89) : PropX_scope.
Notation "'ExX' : A , P" := (ExistsX (A := A) P) (at level 89) : PropX_scope.

Notation "#0" := (fun x => Var0 x) : PropX_scope.
Notation "#1" := (fun x => Lift (Var0 x)) : PropX_scope.
Notation "#2" := (fun x => Lift (Lift (Var0 x))) : PropX_scope.
Notation "#3" := (fun x => Lift (Lift (Lift (Var0 x)))) : PropX_scope.
Notation "#4" := (fun x => Lift (Lift (Lift (Lift (Var0 x))))) : PropX_scope.
Notation "#5" := (fun x => Lift (Lift (Lift (Lift (Lift (Var0 x)))))) : PropX_scope.
Notation "#6" := (fun x => Lift (Lift (Lift (Lift (Lift (Lift (Var0 x))))))) : PropX_scope.
Notation "#7" := (fun x => Lift (Lift (Lift (Lift (Lift (Lift (Lift (Var0 x)))))))) : PropX_scope.
Notation "#8" := (fun x => Lift (Lift (Lift (Lift (Lift (Lift (Lift (Lift (Var0 x))))))))) : PropX_scope.

Delimit Scope PropX_scope with PropX.
Bind Scope PropX_scope with PropX propX.

Arguments Scope interp [type_scope type_scope _ PropX_scope].
Arguments Scope valid [type_scope type_scope _ PropX_scope PropX_scope].
