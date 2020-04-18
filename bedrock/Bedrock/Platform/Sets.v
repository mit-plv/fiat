Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Bags.

Set Implicit Arguments.


(** * A stronger [starL_weaken] *)

Section starL_weaken_mem.
  Variable A : Type.
  Variables P P' : A -> HProp.

  Theorem starL_weaken_mem : forall ls,
    List.Forall (fun x => P x ===> P' x) ls
    -> starL P ls ===> starL P' ls.
    induction 1; simpl; intuition.
    sepLemma.
    apply Himp_star_frame; auto.
  Qed.
End starL_weaken_mem.


(** * Generic set functionality *)

Module Type S.
  Parameter A : Type.
  Parameter eq_dec : forall x y : A, {x = y} + {x <> y}.
End S.

Module Make(M : S).
  Import M.

  Definition set := A -> Prop.

  Definition mem (x : A) (s : set) := s x.
  Infix "%in" := mem (at level 70, no associativity).

  Definition empty : set := fun _ => False.

  Definition equiv (s1 s2 : set) := forall x, s1 x <-> s2 x.
  Infix "%=" := equiv (at level 70, no associativity).

  Definition incl (s1 s2 : set) : Prop := forall x, s1 x -> s2 x.
  Infix "%<=" := incl (at level 70, no associativity).

  Definition add (s : set) (x : A) : set := fun x' => x' = x \/ s x'.
  Infix "%+" := add (at level 50, left associativity).

  Definition del (s : set) (x : A) : set := fun x' => x' <> x /\ s x'.
  Infix "%-" := del (at level 50, left associativity).

  Ltac sets := subst;
    repeat match goal with
             | [ H : _ %= _ |- _ ] => generalize dependent H
             | [ H : _ %<= _ |- _ ] => generalize dependent H
             | [ H : _ %in _ |- _ ] => generalize dependent H
             | [ H : ~ _ %in _ |- _ ] => generalize dependent H
             | [ H : _ %in _ -> False |- _ ] => generalize dependent H
             | [ H : _ \is _ |- _ ] => generalize dependent H
             | [ H : @eq W _ _ |- _ ] => generalize dependent H
             | [ H : ~(@eq W _ _) |- _ ] => generalize dependent H
           end; clear;
    unfold equiv, empty, incl, mem, add, del, propToWord, IF_then_else; intuition idtac;
      repeat (match goal with
                | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
                | [ |- context[if ?E then _ else _] ] => destruct E; subst
                | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; subst
              end; intuition idtac);
      try match goal with
            | [ |- _ \/ _ ] => right; intuition idtac
          end;
      repeat match goal with
               | [ x : A, H : forall p : A, _ |- _ ] => specialize (H x)
             end;
      try subst; intuition (try (discriminate || omega)).

  Hint Extern 5 (_ %= _) => sets.
  Hint Extern 5 (_ %<= _) => sets.
  Hint Extern 5 (_ %in _) => sets.
  Hint Extern 5 (~ _ %in _) => sets.
  Hint Extern 5 (_ \is _) => sets.

  Theorem equiv_symm : forall b1 b2,
    b1 %= b2
    -> b2 %= b1.
    sets.
  Qed.

  Theorem equiv_trans : forall b1 b2 b3,
    b1 %= b2
    -> b2 %= b3
    -> b1 %= b3.
    sets.
  Qed.

  Lemma incl_refl : forall b,
    b %<= b.
    sets.
  Qed.

  Lemma incl_trans : forall b1 b2 b3,
    b1 %<= b2
    -> b2 %<= b3
    -> b1 %<= b3.
    sets.
  Qed.

  Lemma incl_mem : forall x b1 b2,
    x %in b1
    -> b1 %<= b2
    -> x %in b2.
    sets.
  Qed.

  Lemma exists_starL_fwd : forall A (P : A -> _) Q,
    (Ex x, P x) * Q ===> Ex x, P x * Q.
    sepLemma.
  Qed.

  Lemma exists_starR_bwd : forall P A (Q : A -> _),
    Ex x, P * Q x ===> P * (Ex x, Q x).
    sepLemma.
  Qed.

  Definition setify (ls : list A) : set :=
    fold_left add ls empty.

  Section starS.
    Variable G : list Type.
    Definition predS := A -> hpropB G.
    Variable P : predS.

    Open Scope Sep_scope.

    Definition starS (s : set) : hpropB G :=
      Ex ls, [| s %= setify ls |] * [| NoDup ls |] * starL P ls.
  End starS.

  Theorem starS_substH_fwd : forall T (P : predS (T :: nil)) b v,
    substH (starS P b) v ===> starS (fun x => substH (P x) v) b.
    unfold starS; intros; autorewrite with sepFormula.
    apply Himp'_ex; intro; apply Himp_ex_c; eexists.
    autorewrite with sepFormula.
    apply Himp_star_frame.
    apply Himp_refl.
    rewrite starL_substH.
    apply Himp_refl.
  Qed.

  Theorem starS_substH_bwd : forall T (P : predS (T :: nil)) b v,
    starS (fun x => substH (P x) v) b ===> substH (starS P b) v.
    unfold starS; intros; autorewrite with sepFormula.
    apply Himp'_ex; intro; apply Himp_ex_c; eexists.
    autorewrite with sepFormula.
    apply Himp_star_frame.
    apply Himp_refl.
    rewrite starL_substH.
    apply Himp_refl.
  Qed.

  Hint Constructors NoDup.

  Section starS_closed.
    Variable P : predS nil.

    Ltac to_himp := repeat intro.
    Ltac from_himp := match goal with
                        | [ |- interp ?specs (?p ?x ?y ---> ?q ?x ?y) ] =>
                          generalize dependent y; generalize dependent x; generalize dependent specs;
                            change (p ===> q)
                      end.

    Theorem starS_empty_bwd : Emp ===> starS P empty.
      to_himp; apply existsR with nil; from_himp; sepLemma.
    Qed.

    Lemma setify_cong : forall ls b1 b2,
      b1 %= b2
      -> fold_left add ls b1 %= fold_left add ls b2.
      induction ls; simpl; intuition.
    Qed.

    Lemma add_something : forall v ls b,
      fold_left add ls (b %+ v) %= fold_left add ls b %+ v.
      induction ls; simpl; intuition.
      eapply equiv_trans; [ | apply IHls ].
      apply setify_cong; auto.
    Qed.

    Lemma setify_include' : forall v ls b b',
      In v ls
      -> b %= fold_left add ls b'
      -> v %in b.
      induction ls; simpl; intuition (subst; eauto).
      assert (b %= fold_left add ls b' %+ v) by (eapply equiv_trans; [ eassumption | apply add_something ]); auto.
    Qed.

    Lemma setify_include : forall v ls b,
      In v ls
      -> b %= setify ls
      -> v %in b.
      intros; eapply setify_include'; eauto.
    Qed.

    Lemma setify_omit : forall v ls b,
      ~v %in b
      -> b %= setify ls
      -> ~In v ls.
      intuition.
      specialize (setify_include _ _ H1 H0); assumption.
    Qed.

    Hint Immediate setify_omit.

    Theorem starS_add_bwd : forall b v, ~v %in b -> starS P b * P v ===> starS P (b %+ v).
      intros; eapply Himp_trans; [ apply exists_starL_fwd | ]; cbv beta.
      to_himp; apply existsL; intro ls; apply existsR with (v :: ls); from_himp.
      simpl; generalize (starL P ls); generalize (P v); sepLemma.
      unfold setify in *; simpl.
      apply equiv_symm; eapply equiv_trans; [ apply add_something | ]; auto.
      eauto.
    Qed.

    Fixpoint nuke (p : A) (ls : list A) : list A :=
      match ls with
        | nil => nil
        | p' :: ls => if eq_dec p p' then ls else p' :: nuke p ls
      end.

    Lemma starL_del_fwd : forall v ls, In v ls
      -> starL P ls ===> P v * starL P (nuke v ls).
      induction ls; unfold setify in *; simpl in *; intuition subst.
      destruct (eq_dec v v); apply Himp_refl || tauto.
      destruct (eq_dec v a); subst; try apply Himp_refl.
      simpl.
      eapply Himp_trans.
      apply Himp_star_frame; [ apply Himp_refl | apply H ].
      generalize (starL P (nuke v ls)); generalize (P a); generalize (P v); sepLemma.
    Qed.

    Lemma In_nuke : forall v x ls,
      In x (nuke v ls)
      -> In x ls.
      induction ls; simpl; intuition;
        match goal with
          | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; subst; simpl in *; intuition
        end.
    Qed.

    Hint Immediate In_nuke.

    Lemma NoDup_nuke : forall v ls,
      NoDup ls
      -> NoDup (nuke v ls).
      induction 1; simpl; intuition;
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E; subst
        end; eauto.
    Qed.

    Hint Immediate NoDup_nuke.

    Lemma setify_cases : forall v ls b,
      v %in fold_left add ls b
      -> In v ls \/ v %in b.
      induction ls; simpl; intuition.
      apply IHls in H; intuition sets.
    Qed.

    Lemma setify_In : forall v ls,
      v %in setify ls
      -> In v ls.
      intros; apply setify_cases in H; intuition.
    Qed.

    Lemma setify_In' : forall v ls b,
      v %in b
      -> b %= setify ls
      -> In v ls.
      intros; apply setify_In; sets.
    Qed.

    Hint Immediate setify_In'.

    Lemma add_to_del : forall b b' v,
      ~v %in b'
      -> b %= b' %+ v
      -> b %- v %= b'.
      sets.
    Qed.

    Lemma setify_nuke' : forall v ls, NoDup ls
      -> forall b b', In v ls
      -> ~v %in b'
      -> b %= fold_left add ls b'
      -> b %- v %= fold_left add (nuke v ls) b'.
      induction 1; simpl; intuition subst;
        match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E; subst; intuition
        end.
      assert (b %= fold_left add l b' %+ v) by (eapply equiv_trans; [ eassumption | apply add_something ]); auto.

      apply add_to_del; auto.
      intro.
      apply setify_cases in H4; destruct H4; intuition.

      apply IHNoDup in H3; auto.
      intros.
      assert (v %in b' \/ v = x) by sets.
      tauto.
    Qed.

    Lemma setify_nuke : forall v ls b,
      NoDup ls
      -> In v ls
      -> b %= setify ls
      -> b %- v %= setify (nuke v ls).
      intros; apply setify_nuke'; auto.
    Qed.

    Theorem starS_del_fwd : forall b v, v %in b
      -> starS P b ===> P v * starS P (b %- v).
      intros; eapply Himp_trans; [ | apply exists_starR_bwd ]; cbv beta.
      to_himp; apply existsL; intro ls; apply existsR with (nuke v ls).
      specialize (starL_del_fwd v ls);
        generalize (starL P ls); generalize (P v); generalize (starL P (nuke v ls)).
      intros; from_himp.
      sepLemma.
      apply setify_nuke; eauto.
      transitivity (h0 * h)%Sep; eauto.
      sepLemma.
    Qed.

    Lemma fun_fun_fun : forall A P Q R,
      P * (Ex ls : A, Q ls * R ls)
      ===> (Ex ls : A, Q ls * (P * R ls)).
      sepLemma.
    Qed.

    Lemma del_to_add : forall b b' v,
      v %in b
      -> b %- v %= b'
      -> b %= b' %+ v.
      intros.
      assert (b %- v %+ v %= b' %+ v) by sets.
      clear H0.
      apply equiv_trans with (b %- v %+ v); auto.
      clear H1.
      unfold mem, equiv, del, add in *.
      intros.
      destruct (eq_dec v x); subst; intuition.
    Qed.

    Theorem starS_del_bwd : forall b v, v %in b
      -> P v * starS P (b %- v) ===> starS P b.
      unfold starS; intros.
      eapply Himp_trans; [ apply fun_fun_fun | ]; cbv beta.
      apply Himp'_ex; intro ls.
      apply Himp_ex_c; exists (v :: ls).
      simpl.
      apply Himp_star_frame; [ | apply Himp_refl ].
      apply Himp_star_pure_c; intro.
      apply Himp_star_pure_cc.
      unfold setify in *; simpl.
      eapply equiv_trans; [ | apply equiv_symm; apply add_something ].

      apply del_to_add; auto.

      sepLemma.
      constructor; auto.
      intro.
      eapply setify_include in H2; eauto.
      sets.
    Qed.

    Lemma star_cancel_right : forall a b c, b ===> c -> b * a ===> c * a.
      sepLemma.
    Qed.

    Lemma starS_equiv : forall P a b, a %= b -> starS P a ===> starS P b.
      intros; unfold starS; to_himp; apply existsL; intros; apply existsR with x; from_himp; eapply star_cancel_right; sepLemma.
    Qed.

    Variable P' : predS nil.

    Theorem starS_weaken : forall b,
      (forall x, x %in b -> P x ===> P' x)
      -> starS P b ===> starS P' b.
      unfold starS; intros.
      apply Himp'_ex; intro; apply Himp_ex_c; eexists.
      eapply Himp_trans; [ apply Himp_star_assoc | ].
      apply Himp_star_pure_c; intro.
      apply Himp_star_frame.
      instantiate (1 := x); sepLemma.
      apply starL_weaken_mem; auto.
      apply Forall_forall; intros.
      apply H.
      eapply setify_include; eauto.
    Qed.

    Section starS_weak.
      Hypothesis HP' : forall x, P x ===>* P' x.

      Theorem starS_weaken_weak : forall b, starS P b ===>* starS P' b.
        unfold HimpWeak in *; propxFo.
        do 4 esplit; eauto.
        split.
        eauto 10.
        apply simplify_fwd.
        eapply starL_weaken_weak; eauto.
      Qed.
    End starS_weak.
  End starS_closed.

End Make.
