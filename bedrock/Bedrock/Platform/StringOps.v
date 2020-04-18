Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Coq.Strings.Ascii Bedrock.Platform.Wrap Bedrock.Platform.Arrays8.

Set Implicit Arguments.

Definition W_of_ascii (ch : ascii) : W := N_of_ascii ch.
Coercion W_of_ascii : ascii >-> W.


Section Params.
  Variables str len pos output : string.
  Variable const : string.

  Variable A : Type. (* Type for a single unified [Al] quantifier in the block spec *)
  Variable precondition : A -> vals -> HProp.
  Variable postcondition : list B -> A -> vals -> W -> HProp.

  Lemma himp_refl : forall specs (P Q : HProp),
    P = Q
    -> himp specs P Q.
    intros; subst; reflexivity.
  Qed.

  Hint Extern 1 (himp _ _ _) =>
    try (apply himp_star_frame; try reflexivity);
    apply himp_refl;
      match goal with
        | [ H : _ |- _ ] => apply H
      end; intros; autorewrite with sepFormula; reflexivity.

  Lemma precondition_sel : forall a V, precondition a (sel V) = precondition a V.
    auto.
  Qed.

  Lemma postcondition_sel : forall bs a V, postcondition bs a (sel V) = postcondition bs a V.
    auto.
  Qed.

  Hint Rewrite precondition_sel postcondition_sel : sepFormula.

  Lemma bound_narrow : forall len (len' : W) pos offset spacing,
    len = wordToNat len'
    -> (wordToNat pos + offset + S spacing <= wordToNat len')%nat
    -> pos ^+ natToW offset < natToW len.
    intros; subst; unfold natToW; rewrite natToWord_wordToNat; auto.
    pre_nomega.
    rewrite wordToNat_wplus.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize offset); eapply goodSize_weaken; eauto.
    instantiate (1 := len'); auto.
    eapply goodSize_weaken; eauto.
    rewrite wordToNat_natToWord_idempotent; auto.
    instantiate (1 := len'); auto.
    change (goodSize offset); eapply goodSize_weaken; eauto.
    instantiate (1 := len'); auto.
  Qed.

  Implicit Arguments bound_narrow [len len' pos offset spacing].

  Ltac evalu :=
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => generalize dependent H
           end;
    evaluate auto_ext; intros;
    try match goal with
          | [ H : length _ = wordToNat _, H' : (_ <= _)%nat |- _ ] => specialize (bound_narrow H H'); intro
        end;
    evaluate auto_ext; intros; simpl in *;
    repeat match goal with
             | [ H : evalInstrs _ _ _ = _ |- _ ] => clear H
             | [ H : evalCond _ _ _ _ _ = _ |- _ ] => clear H
             | [ H : _ \/ _ |- _ ] => clear H
           end;
    try match goal with
          | [ st : (settings * state)%type |- _ ] => destruct st; simpl in *
        end.

  Ltac tweak_precondition :=
    etransitivity; [ apply himp_star_comm | ]; apply himp_star_frame; try reflexivity;
      [ match goal with
          | [ H : _ |- _ ] => apply H; solve [ descend ]
        end ].

  Ltac finish := descend; repeat (step auto_ext; descend); descend;
    eauto || nomega || tweak_precondition || step auto_ext.

  Ltac t := try app; simp; handle_IH; evalu; finish.

  Lemma goodSize_length : forall a s,
    goodSize (String.length (String a s))
    -> goodSize (String.length s).
    intros; eapply goodSize_weaken; (cbv beta; simpl; eauto).
  Qed.

  Hint Immediate goodSize_length.

  Hint Rewrite wordToNat_wminus using nomega : N.


  (** * Derived command to check whether a string matches a constant. *)
  Section StringEq.
    Fixpoint StringEq' (const : string) (offset : nat) : chunk :=
      match const with
        | "" => output <- 1
        | String ch const' =>
          Rp <- pos + offset;;
          Rp <-*8 str + Rp;;
          If (Rp = ch) {
            StringEq' const' (S offset)
          } else {
            output <- 0
          }
      end%SP.

    Definition StringEqSpec' (const : string) (offset : nat) :=
      Al bs, Al x : A,
      PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |]
      * [| wordToNat (V pos) + offset + String.length const <= wordToNat (V len) |]%nat
      POST[R] postcondition bs x V R.

    Notation StringEqVcs := (fun _ ns _ => (~In "rp" ns) :: In str ns :: In len ns :: In pos ns :: In output ns
      :: not (str = len) :: not (str = pos) :: not (str = output)
      :: not (len = pos) :: not (len = output)
      :: not (pos = output)
      :: (forall a V V',
        (forall x, x <> output -> sel V x = sel V' x)
        -> precondition a V ===> precondition a V')
      :: (forall bs a V V' r,
        (forall x, x <> output -> sel V x = sel V' x)
        -> postcondition bs a V r = postcondition bs a V' r)
      :: goodSize (String.length const)
      :: nil).

    Definition StringEq'' (offset : nat) : chunk.
      refine (WrapC (StringEq' const offset)
        (StringEqSpec' const offset)
        (StringEqSpec' const offset)
        StringEqVcs
        _ _); [ abstract (wrap0; generalize dependent offset; generalize dependent st; generalize dependent pre;
          induction const; propxFo;
            match goal with
              | [ _ : interp _ (Postcondition _ _) |- _ ] =>
                app; [ post; handle_IH; finish
                  | eauto
                  | post; t ]
              | _ => t
            end)
          | abstract (generalize dependent offset; induction const; wrap0;
            try match goal with
                  | [ H : _ |- vcs _ ] => apply H; wrap0; post
                end; t) ].
    Defined.

    Definition StringEqSpec :=
      Al bs, Al x : A,
      PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |]
      * [| V pos <= V len |]
      POST[R] postcondition bs x V R.

    Definition StringEq : chunk.
      refine (WrapC (
        output <- len - pos;;
        If (String.length const <= output) {
          StringEq'' O
        } else {
          output <- 0
        })%SP
      StringEqSpec
      StringEqSpec
      StringEqVcs
      _ _); abstract (wrap0;
        (try app; simp;
          match goal with
            | [ H : evalInstrs _ _ _ = _ |- _ ] => evalu
            | _ => idtac
          end; autorewrite with sepFormula in *; finish)).
    Defined.
  End StringEq.


  (* Alternate sequencing operator, which generates twistier code but simpler postconditions and VCs *)
  Definition SimpleSeq (ch1 ch2 : chunk) : chunk := fun ns res =>
    Structured nil (fun im mn H => Seq_ H (toCmd ch1 mn H ns res) (toCmd ch2 mn H ns res)).

  Infix ";;" := SimpleSeq : SP_scope.

  (** * Derived command to append a string constant to a buffer. *)

  Section StringWrite.
    Fixpoint StringWrite' (const : string) (offset : nat) : chunk :=
      match const with
        | "" => Skip
        | String ch const' =>
          Rp <- pos + offset;;
          str + Rp *<-8 ch;;
          StringWrite' const' (S offset)
      end%SP.

    Definition StringWriteSpec' (const : string) (offset : nat) :=
      Al bs, Al x : A,
      PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |]
        * [| wordToNat (V pos) + offset + String.length const <= wordToNat (V len) |]%nat
      POST[R] postcondition bs x V R.

    Notation StringWriteVcs := (fun _ ns _ => (~In "rp" ns) :: In str ns :: In len ns :: In pos ns :: In output ns
      :: not (str = len) :: not (str = pos) :: not (str = output)
      :: not (len = pos) :: not (len = output)
      :: not (pos = output)
      :: (forall a V V',
        (forall x, x <> output -> x <> pos -> sel V x = sel V' x)
        -> precondition a V ===> precondition a V')
      :: (forall bs bs' a V V' r,
        (forall x, x <> output -> x <> pos -> sel V x = sel V' x)
        -> postcondition bs a V r = postcondition bs' a V' r)
      :: goodSize (String.length const)
      :: nil).

    Definition StringWrite'' (offset : nat) : chunk.
      refine (WrapC (StringWrite' const offset)
        (StringWriteSpec' const offset)
        (StringWriteSpec' const offset)
        StringWriteVcs
        _ _); [ abstract (wrap0; generalize dependent offset; generalize dependent st; generalize dependent pre;
          induction const; propxFo;
            match goal with
              | [ _ : interp _ (Postcondition _ _) |- _ ] =>
                app; [ post; handle_IH; finish
                  | eauto
                  | post; t ]
              | _ => t
            end)
          | abstract (generalize dependent offset; induction const; wrap0;
            try match goal with
                  | [ H : _ |- vcs _ ] => apply H; wrap0; post
                end; t) ].
    Defined.

    Definition StringWriteSpec :=
      Al bs, Al x : A,
      PRE[V] precondition x V * array8 bs (V str) * [| length bs = wordToNat (V len) |]
        * [| V pos <= V len |]
      POST[R] postcondition bs x V R.

    Lemma simplify_inc : forall (u v : W) w,
      (wordToNat v + 0 + w <= wordToNat u)%nat
      -> goodSize w
      -> v ^+ natToW w <= u.
      intros; pre_nomega; rewrite wordToNat_wplus; autorewrite with N; try omega.
      apply goodSize_weaken with (wordToNat u); eauto.
    Qed.

    Hint Immediate simplify_inc.

    Definition StringWrite : chunk.
      refine (WrapC (
        If (output = 1) {
          Skip
        } else {
          output <- len - pos;;
          If (String.length const <= output) {
            StringWrite'' O;;
            pos <- pos + String.length const;;
            output <- 0
          } else {
            output <- 1
          }
        })%SP
      StringWriteSpec
      StringWriteSpec
      StringWriteVcs
      _ _); abstract (wrap0;
        (try app; simp;
          match goal with
            | [ H : evalInstrs _ _ _ = _ |- _ ] => evalu
            | [ H : evalCond _ _ _ _ _ = _ |- _ ] => evalu
            | _ => idtac
          end; autorewrite with sepFormula in *; finish)).
    Defined.
  End StringWrite.

End Params.
