Require Import Coq.Lists.List.

Require Import Bedrock.PropX.

Set Implicit Arguments.


Notation "i @@ sp" := (ExX, Cptr i #0 /\ Al st, sp st ---> #0 st)%PropX
  (no associativity, at level 39) : PropX_scope.

Section machine.
  Variables pc state : Type.

  Inductive subs : list Type -> Type :=
  | SNil : subs nil
  | SCons : forall T Ts, (last (T :: Ts) -> PropX pc state) -> subs (eatLast (T :: Ts)) -> subs (T :: Ts).

  Fixpoint SPush G T (s : subs G) (f : T -> PropX pc state) : subs (T :: G) :=
    match s in subs G return subs (T :: G) with
      | SNil => SCons _ nil f SNil
      | SCons T' Ts f' s' => SCons T (T' :: Ts) f' (SPush s' f)
    end.

  Fixpoint SHead G (s : subs G) : hd (Empty_set : Type) G -> PropX pc state:=
    match s in subs G return hd (Empty_set : Type) G -> PropX pc state with
      | SNil => fun x => match x with end
      | SCons T G' f s' =>
        match G' return (last (T :: G') -> _) -> (hd (Empty_set : Type) (eatLast (T :: G')) -> PropX pc state) -> (T -> PropX pc state) with
          | nil => fun f _ => f
          | _ :: _ => fun _ SHead_s' => SHead_s'
        end f (SHead s')
    end.

  Fixpoint STail G (s : subs G) : subs (tl G) :=
    match s in subs G return subs (tl G) with
      | SNil => SNil
      | SCons T G' f s' =>
        match G' return (last (T :: G') -> _) -> subs (tl (eatLast (T :: G'))) -> subs G' with
          | nil => fun _ _ => SNil
          | T' :: G'' => fun f STail_s' => SCons T' G'' f STail_s'
        end f (STail s')
    end.

  Fixpoint Substs G (s : subs G) : propX pc state G -> PropX pc state :=
    match s in subs G return propX pc state G -> PropX pc state with
      | SNil => fun p => p
      | SCons _ _ f s' => fun p => Substs s' (subst p f)
    end.

  Section specs.
    Variable specs : codeSpec pc state.

    Section weaken.
      Hint Constructors valid.

      Hint Extern 1 (In _ _) => simpl; tauto.

      Hint Extern 3 (incl _ _) =>
        let x := fresh "x" in intro x;
          repeat match goal with
                   | [ H : incl _ _ |- _ ] => generalize (H x); clear H
                 end; simpl; intuition (subst; assumption).

      Theorem incl_cons : forall A x (G G' : list A),
        incl G G'
        -> incl (x :: G) (x :: G').
        auto.
      Qed.

      Hint Resolve incl_cons.

      Lemma valid_weaken : forall G Q, valid (state := state) specs G Q
        -> forall G', incl G G'
          -> valid specs G' Q.
      Proof.
        induction 1; intros.
        intuition.
        intuition.
        eapply Inj_E; [ eauto | auto ].
        intuition.
        eapply Cptr_E; [ eauto | auto ].
        intuition.
        eapply And_E1; [ eauto ].
        eapply And_E2; [ eauto ].
        eapply Or_I1; eapply IHvalid; eassumption.
        eapply Or_I2; eapply IHvalid; eassumption.
        eapply Or_E. eapply IHvalid1; eassumption. eapply IHvalid2. clear -H2. eauto.  eapply IHvalid3. clear -H2. eauto.
        intuition.
        eapply Imply_E; [ eauto | auto ].
        intuition.
        eapply Forall_E. eauto.
        eapply Exists_I; eauto.
        eapply Exists_E; eauto.
        intuition.
        eapply ExistsX_I; eauto.
      Qed.

      Theorem interp_weaken : forall Q, interp (state := state) specs Q
        -> forall G, valid specs G Q.
        intros; eapply valid_weaken; eauto.
      Qed.

      Theorem valid_weaken1 : forall G (P : PropX pc state), valid specs G P
        -> forall T, valid specs (T :: G) P.
        intros; eapply valid_weaken; eauto.
      Qed.
    End weaken.

    Fixpoint simplify G (p : propX pc state G) : subs G -> Prop :=
      match p with
        | Inj _ P => fun _ => P
        | Cptr _ f a => fun s => specs f = Some (fun x => Substs s (a x))
        | And _ p1 p2 => fun s => simplify p1 s /\ simplify p2 s
        | Or _ p1 p2 => fun s => simplify p1 s \/ simplify p2 s
        | Imply _ p1 p2 => fun s => interp specs (Substs s (Imply p1 p2))
        | Forall _ _ p1 => fun s => forall x, simplify (p1 x) s
        | Exists _ _ p1 => fun s => exists x, simplify (p1 x) s
        | Var0 _ _ v => fun s => interp specs (SHead s v)
        | Lift _ _ p1 => fun s => simplify p1 (STail s)
        | ForallX _ _ p1 => fun s => forall a, simplify p1 (SPush s a)
        | ExistsX _ _ p1 => fun s => exists a, simplify p1 (SPush s a)
      end.

    Lemma Substs_Inj : forall G (s : subs G) P,
      Substs s (Inj P)= Inj P.
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Cptr_fwd : forall G (s : subs G) f a,
      interp specs (Substs s (Cptr f a))
      -> interp specs (Cptr f (fun x => Substs s (a x))).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Cptr_bwd : forall G (s : subs G) f a,
      interp specs (Cptr f (fun x => Substs s (a x)))
      -> interp specs (Substs s (Cptr f a)).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_And : forall G (s : subs G) p1 p2,
      Substs s (And p1 p2) = And (Substs s p1) (Substs s p2).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Or : forall G (s : subs G) p1 p2,
      Substs s (Or p1 p2) = Or (Substs s p1) (Substs s p2).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Imply : forall G (s : subs G) p1 p2,
      Substs s (Imply p1 p2) = Imply (Substs s p1) (Substs s p2).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Forall_fwd : forall G (s : subs G) A (p1 : A -> _),
      interp specs (Substs s (Forall p1))
      -> interp specs (Forall (fun x => Substs s (p1 x))).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Forall_bwd : forall G (s : subs G) A (p1 : A -> _),
      interp specs (Forall (fun x => Substs s (p1 x)))
      -> interp specs (Substs s (Forall p1)).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Exists_fwd : forall G (s : subs G) A (p1 : A -> _),
      interp specs (Substs s (Exists p1))
      -> interp specs (Exists (fun x => Substs s (p1 x))).
      induction s; simpl; intuition.
    Qed.

    Lemma Substs_Exists_bwd : forall G (s : subs G) A (p1 : A -> _),
      interp specs (Exists (fun x => Substs s (p1 x)))
      -> interp specs (Substs s (Exists p1)).
      induction s; simpl; intuition.
    Qed.

    Lemma subs_nil' : forall G (s : subs G) p,
      match G return subs G -> Prop with
        | nil => fun s => Substs s p = p
        | _ :: _ => fun _ => True
      end s.
      destruct s; simpl; intuition.
    Qed.

    Theorem subs_nil : forall (s : subs nil) p, Substs s p = p.
      intros; apply (subs_nil' s).
    Qed.

    Hint Immediate subs_nil.

    Lemma Substs_Var0' : forall G (s : subs G),
      match G return subs G -> Prop with
        | nil => fun _ => True
        | T :: G' => fun s => forall v, Substs s (Var0 v) = SHead s v
      end s.
      induction s; simpl; intuition.
      destruct Ts; simpl in *; intuition.
    Qed.

    Lemma Substs_Var0 : forall T G (s : subs (T :: G)) v,
      Substs s (Var0 v) = SHead s v.
      intros; apply (Substs_Var0' s); assumption.
    Qed.

    Lemma Substs_Lift' : forall G (s : subs G),
      match G return subs G -> Prop with
        | nil => fun _ => True
        | T :: G' => fun s => forall p1, Substs s (Lift p1) = Substs (STail s) p1
      end s.
      induction s; simpl; intuition.
      destruct Ts; simpl in *; intuition.
    Qed.

    Lemma Substs_Lift : forall T G (s : subs (T :: G)) p1,
      Substs s (Lift p1) = Substs (STail s) p1.
      intros; apply (Substs_Lift' s); assumption.
    Qed.

    Theorem Imply_easyL'' : forall G (p1 p2 p : PropX pc state),
      valid specs G (Imply p1 (Imply p2 p))
      -> valid specs G (Imply (And p1 p2) p).
      intros.
      apply Imply_I.
      eapply Imply_E.
      eapply Imply_E.
      apply valid_weaken1; eauto.
      eapply And_E1; apply Env; simpl; tauto.
      eapply And_E2; apply Env; simpl; tauto.
    Qed.

    Hint Rewrite Substs_Inj Substs_And Substs_Or Substs_Imply Substs_Var0 Substs_Lift : Substs.

    Hint Resolve interp_weaken valid_weaken1.

    Lemma simplify_bwd_ForallX : forall G A s (p : propX pc state (A :: G)),
      (forall a, interp specs (Substs (SPush s a) p))
      -> interp specs (Substs s (AlX : A, p)).
      induction s; simpl; intuition.
      apply ForallX_I; auto.
    Qed.

    Lemma simplify_bwd_ExistsX : forall G A a s (p : propX pc state (A :: G)),
      interp specs (Substs (SPush s a) p)
      -> interp specs (Substs s (ExX : A, p)).
      induction s; simpl; intuition.
      apply ExistsX_I with a; auto.
    Qed.

    Lemma simplify_bwd' : forall G (p : propX pc state G) s,
      simplify p s
      -> interp specs (Substs s p).
      induction p; simpl; intuition; autorewrite with Substs in *.

      apply Inj_I; auto.
      apply Substs_Cptr_bwd; apply Cptr_I; auto.
      apply And_I; auto.
      apply Or_I1; auto.
      apply Or_I2; auto.
      apply Substs_Forall_bwd; apply Forall_I; auto.
      apply Substs_Exists_bwd; destruct H0 as [x]; apply Exists_I with x; auto.
      assumption.
      auto.
      apply simplify_bwd_ForallX; firstorder.
      destruct H as [x]; apply simplify_bwd_ExistsX with x; firstorder.
    Qed.

    Lemma simplify_bwd : forall p,
      simplify p SNil
      -> interp specs p.
      intros; change (interp specs (Substs SNil p)); apply simplify_bwd'; auto.
    Qed.

    Lemma simplify_fwd_ForallX : forall G A a s (p : propX pc state (A :: G)),
      interp specs (Substs s (AlX  : A, p))
      -> interp specs (Substs (SPush s a) p).
      induction s; simpl; intuition.
      apply ForallX_sound; auto.
    Qed.

    Lemma simplify_fwd_ExistsX : forall G A s (p : propX pc state (A :: G)),
      interp specs (Substs s (ExX  : A, p))
      -> exists a, interp specs (Substs (SPush s a) p).
      induction s; simpl; intuition.
      apply ExistsX_sound; auto.
    Qed.

    Lemma simplify_fwd' : forall G (p : propX pc state G) s,
      interp specs (Substs s p)
      -> simplify p s.
      induction p; simpl; intuition; autorewrite with Substs in *.

      apply (Inj_sound H).
      apply Substs_Cptr_fwd in H0; apply (Cptr_sound H0).
      apply And_sound in H; intuition.
      apply And_sound in H; intuition.
      apply Or_sound in H; intuition.
      apply Substs_Forall_fwd in H0; specialize (Forall_sound H0); intuition.
      apply Substs_Exists_fwd in H0; specialize (Exists_sound H0); firstorder.
      assumption.
      auto.
      apply IHp; apply simplify_fwd_ForallX; auto.
      apply simplify_fwd_ExistsX in H; firstorder.
    Qed.

    Lemma simplify_fwd : forall p,
      interp specs p
      -> simplify p SNil.
      intros; apply simplify_fwd'; auto.
    Qed.

    Fixpoint simplifyH G (p : propX pc state G) : subs G -> Prop :=
      match p with
        | Inj _ P => fun _ => P
        | Cptr _ f a => fun s => exists a', specs f = Some a' /\ forall x, a' x = Substs s (a x)
        | And _ p1 p2 => fun s => simplifyH p1 s /\ simplifyH p2 s
        | Or _ p1 p2 => fun s => simplifyH p1 s \/ simplifyH p2 s
        | _ => fun _ => True
      end.

    Lemma Substs_Cptr : forall G (s : subs G) f a,
      exists a', Substs s (Cptr f a) = Cptr f a'
        /\ forall x, a' x = Substs s (a x).
      induction s; simpl; intuition eauto.
    Qed.

    Lemma simplifyH_ok : forall G (p : propX pc state G) s PG p',
      In (Substs s p) PG
      -> (simplifyH p s -> valid specs PG (Substs s p'))
      -> valid specs PG (Substs s p').
      induction p; simpl; intuition; autorewrite with Substs in *.

      eapply Inj_E; [ constructor; eauto | auto ].

      destruct (Substs_Cptr s p p0) as [? [ Heq ] ]; rewrite Heq in *.
      eapply Cptr_E; [ constructor; eauto | eauto ].

      assert (valid specs PG (Substs s p1 ---> Substs s p2 ---> Substs s p')%PropX).
      repeat apply Imply_I.
      apply IHp1.
      simpl; tauto.
      intro.
      apply IHp2.
      simpl; tauto.
      eauto.
      eapply Imply_E.
      eapply Imply_E.
      eassumption.
      eapply And_E1; econstructor; eauto.
      eapply And_E2; econstructor; eauto.

      eapply Or_E.
      constructor; eauto.
      intuition.
      intuition.
    Qed.

    Theorem simplify_Imply : forall p1 p2,
      (simplifyH p1 SNil -> simplify p2 SNil)
      -> interp specs (Imply p1 p2).
      intros.
      change (interp specs (Imply (Substs SNil p1) (Substs SNil p2))).
      apply Imply_I.
      eapply simplifyH_ok.
      simpl; tauto.
      intros.
      apply valid_weaken1.
      apply simplify_bwd.
      auto.
    Qed.

    Theorem Imply_easyL' : forall G (p1 p2 p : PropX pc state),
      (simplifyH p1 SNil -> valid specs G (Imply p2 p))
      -> valid specs G (Imply (And p1 p2) p).
      intros; apply Imply_easyL''.
      apply Imply_I.
      change (p2 ---> p)%PropX with (Substs SNil (p2 ---> p)%PropX).
      eapply simplifyH_ok.
      simpl; tauto.
      intro.
      simpl.
      apply valid_weaken1; auto.
    Qed.

    Theorem Imply_easyL : forall (p1 p2 p : PropX pc state),
      (simplifyH p1 SNil -> interp specs (Imply p2 p))
      -> interp specs (Imply (And p1 p2) p).
      intros; apply Imply_easyL'; auto.
    Qed.

    Theorem Imply_trans' : forall G (p1 p2 p3 : PropX pc state),
      valid specs G (Imply p1 p2)
      -> valid specs G (Imply p2 p3)
      -> valid specs G (Imply p1 p3).
      intros; apply Imply_I.
      eapply Imply_E.
      apply valid_weaken1; eassumption.
      eapply Imply_E.
      apply valid_weaken1; eassumption.
      apply Env; simpl; tauto.
    Qed.

    Theorem Imply_trans : forall p1 p2 p3 : PropX pc state,
      interp specs (Imply p1 p2)
      -> interp specs (Imply p2 p3)
      -> interp specs (Imply p1 p3).
      unfold interp; intros; eapply Imply_trans'; eauto.
    Qed.

    Theorem Imply_easyEx' : forall G T (p1 : T -> _) (p : PropX pc state),
      (forall x, valid specs G (Imply (p1 x) p))
      -> valid specs G (Imply (Exists p1) p).
      intros; apply Imply_I.
      eapply Exists_E.
      apply Env; simpl; tauto.
      intros.
      eapply Imply_E.
      eapply valid_weaken.
      apply H.
      red; intuition.
      apply Env; simpl; tauto.
    Qed.

    Theorem Imply_easyEx : forall T (p1 : T -> _) (p : PropX pc state),
      (forall x, interp specs (Imply (p1 x) p))
      -> interp specs (Imply (Exists p1) p).
      unfold interp; intros; apply Imply_easyEx'; auto.
    Qed.

    Theorem Env1 : forall (G : list (PropX pc state)) P, valid specs (P :: G) P.
      intros; apply Env; simpl; tauto.
    Qed.
  End specs.
End machine.

Ltac propx :=
  repeat match goal with
           | [ H : interp _ _ |- _ ] => apply simplify_fwd in H; progress simpl in H
         end;
  try (apply simplify_bwd; simpl(*;
    repeat (apply simplify_Imply; simpl; intro)*)).

Ltac propxFo' := intuition auto.

Ltac doImply H := eapply Imply_E; [ apply H | apply simplify_bwd; simpl; propxFo' ].

Ltac propxFo := propxFo'; repeat progress (propx; propxFo');
  repeat match goal with
           | [ H : True |- _ ] => clear H
           | [ |- simplify _ _ _ ] => apply simplify_fwd'; simpl; auto
           | [ H : simplify _ _ _ |- _ ] => apply simplify_bwd' in H; simpl in H
           | [ H : ex _ |- _ ] => destruct H; propxFo'
         end.

Hint Resolve interp_weaken Env1.

Ltac ensureNoUnifs E :=
  first [ has_evar E; fail 1 | idtac ].

Ltac ensureNotUnif E :=
  first [ ensureNoUnifs E
        | match E with
            | ?f _ => ensureNotUnif f
            | ?f _ _ => ensureNotUnif f
            | ?f _ _ _ => ensureNotUnif f
            | ?f _ _ _ _ => ensureNotUnif f
          end ].
