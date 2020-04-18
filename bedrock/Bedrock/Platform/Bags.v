Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.

Set Implicit Arguments.


(** * Iterated star *)

Section starL.
  Variable A : Type.
  Variable G : list Type.
  Variable P : A -> hpropB G.

  Open Scope Sep_scope.

  Fixpoint starL (ls : list A) : hpropB G :=
    match ls with
      | nil => Emp
      | x :: ls => P x * starL ls
    end.
End starL.

Theorem starL_substH : forall A G (P : A-> hpropB G) v ls,
  substH (starL P ls) v = starL (fun x => substH (P x) v) ls.
  induction ls; simpl; intuition (autorewrite with sepFormula; congruence).
Qed.

Definition HimpWeak (P Q : HProp) :=
  forall specs stn m, interp specs (P stn m)
    -> interp specs (Q stn m).

Infix "===>*" := HimpWeak (no associativity, at level 90).

Theorem use_HimpWeak : forall P Q p P' specs,
  interp specs (![P * Q] p)
  -> P ===>* P'
  -> interp specs (![P' * Q] p).
  rewrite sepFormula_eq; propxFo.
  do 3 esplit; eauto.
  propxFo.
Qed.

Section starL_weaken.
  Variable A : Type.
  Variables P P' : A -> HProp.

  Section starL_strong.
    Hypothesis HP' : forall x, P x ===> P' x.

    Theorem starL_weaken : forall ls,
      starL P ls ===> starL P' ls.
      induction ls; simpl; intuition.
      sepLemma.
      apply Himp_star_frame; auto.
    Qed.
  End starL_strong.

  Section starL_weak.
    Hypothesis HP' : forall x, P x ===>* P' x.

    Theorem starL_weaken_weak : forall ls,
      starL P ls ===>* starL P' ls.
      unfold HimpWeak in *; induction ls; simpl; propxFo.
      do 3 esplit; eauto; propxFo.
    Qed.
  End starL_weak.
End starL_weaken.

Lemma propToWord_elim_not1 : forall P b,
  P \is b
  -> b <> 1
  -> ~P.
  unfold propToWord, IF_then_else; intuition.
Qed.

Hint Immediate propToWord_elim_not1.


(** * Generic bag functionality *)

Module Type S.
  Parameter A : Type.
  Parameter eq_dec : forall x y : A, {x = y} + {x <> y}.
End S.

Module Make(M : S).
  Import M.

  Definition bag := A -> nat.

  Definition mem (x : A) (b : bag) := (b x > 0)%nat.
  Infix "%in" := mem (at level 70, no associativity).

  Definition empty : bag := fun _ => O.

  Definition equiv (b1 b2 : bag) := forall x, b1 x = b2 x.
  Infix "%=" := equiv (at level 70, no associativity).

  Definition incl (b1 b2 : bag) : Prop := forall x, (b1 x <= b2 x)%nat.
  Infix "%<=" := incl (at level 70, no associativity).

  Definition add (b : bag) (x : A) : bag := fun x' => if eq_dec x' x then S (b x') else b x'.
  Infix "%+" := add (at level 50, left associativity).

  Definition del (b : bag) (x : A) : bag := fun x' => if eq_dec x' x then pred (b x') else b x'.
  Infix "%-" := del (at level 50, left associativity).

  Ltac bags := subst;
    repeat match goal with
             | [ H : _ %= _ |- _ ] => generalize dependent H
             | [ H : _ %<= _ |- _ ] => generalize dependent H
             | [ H : _ %in _ |- _ ] => generalize dependent H
             | [ H : ~ _ %in _ |- _ ] => generalize dependent H
             | [ H : _ \is _ |- _ ] => generalize dependent H
             | [ H : @eq W _ _ |- _ ] => generalize dependent H
             | [ H : ~(@eq W _ _) |- _ ] => generalize dependent H
           end; clear;
    unfold equiv, empty, incl, mem, add, del, propToWord, IF_then_else; intuition idtac;
      repeat (match goal with
                | [ H : (_, _) = (_, _) |- _ ] => injection H; clear H; intros; subst
                | [ |- context[if ?E then _ else _] ] => destruct E; subst
                | [ _ : context[if ?E then _ else _] |- _ ] => destruct E; subst
                | [ H : forall p : W * W, _ |- _ ] => rewrite H in *
              end; intuition idtac);
      try match goal with
            | [ |- _ \/ _ ] => right; intuition idtac
          end;
      repeat match goal with
               | [ H : forall p : A, _ |- _ ] => rewrite H in *
             end; auto; try (discriminate || omega).

  Hint Extern 5 (_ %= _) => bags.
  Hint Extern 5 (_ %<= _) => bags.
  Hint Extern 5 (_ %in _) => bags.
  Hint Extern 5 (~ _ %in _) => bags.
  Hint Extern 5 (_ \is _) => bags.

  Theorem equiv_symm : forall b1 b2,
    b1 %= b2
    -> b2 %= b1.
    bags.
  Qed.

  Theorem equiv_trans : forall b1 b2 b3,
    b1 %= b2
    -> b2 %= b3
    -> b1 %= b3.
    bags.
  Qed.

  Lemma incl_refl : forall b,
    b %<= b.
    bags.
  Qed.

  Lemma incl_trans : forall b1 b2 b3,
    b1 %<= b2
    -> b2 %<= b3
    -> b1 %<= b3.
    bags.
  Qed.

  Lemma incl_mem : forall x b1 b2,
    x %in b1
    -> b1 %<= b2
    -> x %in b2.
    bags.
    specialize (H0 x).
    omega.
  Qed.

  Lemma exists_starL_fwd : forall A (P : A -> _) Q,
    (Ex x, P x) * Q ===> Ex x, P x * Q.
    sepLemma.
  Qed.

  Lemma exists_starR_bwd : forall P A (Q : A -> _),
    Ex x, P * Q x ===> P * (Ex x, Q x).
    sepLemma.
  Qed.

  Definition bagify (ls : list A) : bag :=
    fold_left add ls empty.

  Section starB.
    Variable G : list Type.
    Definition predB := A -> hpropB G.
    Variable P : predB.

    Open Scope Sep_scope.

    Definition starB (b : bag) : hpropB G :=
      Ex ls, [| b %= bagify ls |] * starL P ls.
  End starB.

  Theorem starB_substH_fwd : forall T (P : predB (T :: nil)) b v,
    substH (starB P b) v ===> starB (fun x => substH (P x) v) b.
    unfold starB; intros; autorewrite with sepFormula.
    apply Himp'_ex; intro; apply Himp_ex_c; eexists.
    autorewrite with sepFormula.
    apply Himp_star_frame.
    apply Himp_refl.
    rewrite starL_substH.
    apply Himp_refl.
  Qed.

  Theorem starB_substH_bwd : forall T (P : predB (T :: nil)) b v,
    starB (fun x => substH (P x) v) b ===> substH (starB P b) v.
    unfold starB; intros; autorewrite with sepFormula.
    apply Himp'_ex; intro; apply Himp_ex_c; eexists.
    autorewrite with sepFormula.
    apply Himp_star_frame.
    apply Himp_refl.
    rewrite starL_substH.
    apply Himp_refl.
  Qed.

  Section starB_closed.
    Variable P : predB nil.

    Ltac to_himp := repeat intro.
    Ltac from_himp := match goal with
                        | [ |- interp ?specs (?p ?x ?y ---> ?q ?x ?y) ] =>
                          generalize dependent y; generalize dependent x; generalize dependent specs;
                            change (p ===> q)
                      end.

    Theorem starB_empty_bwd : Emp ===> starB P empty.
      to_himp; apply existsR with nil; from_himp; sepLemma.
    Qed.

    Lemma bagify_cong : forall ls b1 b2,
      b1 %= b2
      -> fold_left add ls b1 %= fold_left add ls b2.
      induction ls; simpl; intuition.
    Qed.

    Lemma add_something : forall v ls b,
      fold_left add ls (b %+ v) %= fold_left add ls b %+ v.
      induction ls; simpl; intuition.
      eapply equiv_trans; [ | apply IHls ].
      apply bagify_cong; auto.
    Qed.

    Theorem starB_add_bwd : forall b v, starB P b * P v ===> starB P (b %+ v).
      intros; eapply Himp_trans; [ apply exists_starL_fwd | ]; cbv beta.
      to_himp; apply existsL; intro ls; apply existsR with (v :: ls); from_himp.
      simpl; generalize (starL P ls); generalize (P v); sepLemma.
      unfold bagify in *; simpl.
      apply equiv_symm; eapply equiv_trans; [ apply add_something | ]; auto.
    Qed.

    Fixpoint nuke (p : A) (ls : list A) : list A :=
      match ls with
        | nil => nil
        | p' :: ls => if eq_dec p p' then ls else p' :: nuke p ls
      end.

    Lemma starL_del_fwd : forall v ls, In v ls
      -> starL P ls ===> P v * starL P (nuke v ls).
      induction ls; unfold bagify in *; simpl in *; intuition subst.
      destruct (eq_dec v v); apply Himp_refl || tauto.
      destruct (eq_dec v a); subst; try apply Himp_refl.
      simpl.
      eapply Himp_trans.
      apply Himp_star_frame; [ apply Himp_refl | apply H ].
      generalize (starL P (nuke v ls)); generalize (P a); generalize (P v); sepLemma.
    Qed.

    Lemma del_something : forall v ls b,
      v %in b
      -> fold_left add ls (b %- v) %= fold_left add ls b %- v.
      induction ls; simpl; intuition.
      eapply equiv_trans; [ | apply IHls ].
      apply bagify_cong; auto.
      auto.
    Qed.

    Lemma bagify_nuke' : forall v ls, In v ls
      -> forall b, fold_left add (nuke v ls) b %= fold_left add ls b %- v.
      induction ls; simpl; intuition subst.
      destruct (eq_dec v v); intuition.
      eapply equiv_trans; [ | apply del_something ].
      apply bagify_cong; auto.
      auto.
      destruct (eq_dec v a); subst.
      eapply equiv_trans; [ | apply del_something ].
      apply bagify_cong; auto.
      auto.
      simpl; auto.
    Qed.

    Lemma bagify_nuke : forall v ls, In v ls
      -> bagify (nuke v ls) %= bagify ls %- v.
      intros; apply bagify_nuke'; auto.
    Qed.

    Lemma bagify_In' : forall v ls b b',
      v %in b
      -> b %= fold_left add ls b'
      -> In v ls \/ v %in b'.
      unfold bagify; induction ls; simpl; intuition.
      eapply IHls in H; [ | eauto ].
      intuition (eauto; bags).
    Qed.

    Lemma bagify_In : forall v ls b,
      v %in b
      -> b %= bagify ls
      -> In v ls.
      intros.
      eapply bagify_In' in H0; eauto.
      intuition bags.
    Qed.

    Hint Resolve bagify_In bagify_nuke.

    Theorem starB_del_fwd : forall b v, v %in b
      -> starB P b ===> P v * starB P (b %- v).
      intros; eapply Himp_trans; [ | apply exists_starR_bwd ]; cbv beta.
      to_himp; apply existsL; intro ls; apply existsR with (nuke v ls).
      specialize (starL_del_fwd v ls);
        generalize (starL P ls); generalize (P v); generalize (starL P (nuke v ls)).
      intros; from_himp.
      sepLemma.
      eapply equiv_trans; [ | apply equiv_symm; apply bagify_nuke ].
      auto.
      eauto.
      transitivity (h0 * h)%Sep; eauto.
      sepLemma.
    Qed.

    Lemma fun_fun_fun : forall A P Q R,
      P * (Ex ls : A, Q ls * R ls)
      ===> (Ex ls : A, Q ls * (P * R ls)).
      sepLemma.
    Qed.

    Lemma undel_something' : forall v b x b',
      v %in b
      -> (b %- v) x = b' x
      -> b x = (b' %+ v) x.
      unfold mem, del, add; intros.
      destruct (eq_dec x v); subst; omega.
    Qed.

    Lemma undel_something : forall v b ls,
      v %in b
      -> b %- v %= bagify ls
      -> b %= bagify (v :: ls).
      unfold bagify, equiv; simpl; intros.
      specialize (H0 x).
      rewrite add_something.
      apply undel_something'; auto.
    Qed.

    Theorem starB_del_bwd : forall b v, v %in b
      -> P v * starB P (b %- v) ===> starB P b.
      unfold starB; intros.
      eapply Himp_trans; [ apply fun_fun_fun | ]; cbv beta.
      apply Himp'_ex; intro ls.
      apply Himp_ex_c; exists (v :: ls).
      apply Himp_star_pure_c; intro.
      apply Himp_star_pure_cc.
      apply undel_something; auto.
      apply Himp_refl.
    Qed.

    Variable P' : predB nil.

    Section starB_strong.
      Hypothesis HP' : forall x, P x ===> P' x.

      Theorem starB_weaken : forall b,
        starB P b ===> starB P' b.
        unfold starB; intro.
        apply Himp'_ex; intro; apply Himp_ex_c; eexists.
        apply Himp_star_frame.
        apply Himp_refl.
        apply starL_weaken; auto.
      Qed.
    End starB_strong.

    Section starB_weak.
      Hypothesis HP' : forall x, P x ===>* P' x.

      Theorem starB_weaken_weak : forall b, starB P b ===>* starB P' b.
        unfold HimpWeak in *; propxFo.
        do 4 esplit; eauto.
        propxFo.
        eapply starL_weaken_weak; eauto.
      Qed.
    End starB_weak.
  End starB_closed.

  Lemma equiv_empty : forall ls, empty %= bagify ls
    -> ls = nil.
    unfold bagify; destruct ls; simpl; intuition.
    eapply equiv_symm in H; eapply equiv_trans in H; [ | eapply equiv_symm; eapply add_something ].
    elimtype False.
    generalize dependent (fold_left add ls empty); intros.
    bags.
    specialize (H a).
    destruct (eq_dec a a); congruence.
  Qed.

  Theorem starB_empty_fwd : forall P, starB P empty ===> Emp.
    unfold starB; intros; intro.
    apply himp_ex_p; intros.
    apply himp_star_pure_c; intro H.
    apply equiv_empty in H; subst.
    reflexivity.
  Qed.

End Make.


(** * Specific instantiations *)

Module W_Key.
  Definition A := W.

  Definition eq_dec := @weq 32.
End W_Key.

Module W_Bag := Make(W_Key).

Module W_W_Key.
  Definition A := (W * W)%type.

  Theorem eq_dec : forall x y : W * W, {x = y} + {x <> y}.
    decide equality; apply weq.
  Qed.
End W_W_Key.

Module W_W_Bag := Make(W_W_Key).


(** * Abstract data type for word pairs *)

Section adt.
  Import W_W_Bag.

  Variable P : bag -> W -> HProp.
  (* Abstract predicate for the data structure *)

  Variable res : nat.
  (* How many reserved stack slots? *)

  Definition initS : spec := SPEC reserving res
    PRE[_] mallocHeap 0
    POST[R] P empty R * mallocHeap 0.

  Definition isEmptyS : spec := SPEC("b") reserving res
    Al b,
    PRE[V] P b (V "b") * mallocHeap 0
    POST[R] [| (b %= empty) \is R |] * P b (V "b") * mallocHeap 0.

  Definition enqueueS : spec := SPEC("b", "v1", "v2") reserving res
    Al b,
    PRE[V] P b (V "b") * mallocHeap 0
    POST[_] P (b %+ (V "v1", V "v2")) (V "b") * mallocHeap 0.

  Definition dequeueS : spec := SPEC("b", "r") reserving res
    Al b,
    PRE[V] [| ~(b %= empty) |] * P b (V "b") * V "r" =?> 2 * mallocHeap 0
    POST[_] Ex v1, Ex v2, [| (v1, v2) %in b |] * P (b %- (v1, v2)) (V "b") * (V "r" ==*> v1, v2) * mallocHeap 0.
End adt.
