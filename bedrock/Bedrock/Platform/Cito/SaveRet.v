Require Import Bedrock.Platform.AutoSep.

Set Implicit Arguments.

Section TopLevel.

  Variable vars : list string.

  Variable var : option string.

  Definition is_state sp vs : HProp :=
    locals vars vs 0 (sp ^+ $8).

  Definition new_pre : assert :=
    x ~> ExX, Ex vs,
    ![^[is_state x#Sp vs] * #0]x.

  Require Import Bedrock.Platform.Cito.Semantics.

  Definition runs_to x_pre x :=
    forall specs other vs,
      interp specs (![is_state x_pre#Sp vs * other ] x_pre) ->
      Regs x Sp = x_pre#Sp /\
      interp specs (![is_state (Regs x Sp) (upd_option vs var x_pre#Rv) * other ] (fst x_pre, x)).

  Definition post (pre : assert) :=
    st ~> Ex st_pre,
    pre (fst st, st_pre) /\
    [| runs_to (fst st, st_pre) (snd st) |].

  Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

  Definition syn_req :=
    match var with
      | Some x => List.In x vars
      | None => True
    end.

  Definition verifCond pre := imply pre new_pre :: syn_req :: nil.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Definition Strline := Straightline_ imports modName.

  Definition SaveRv lv := Strline (IL.Assign lv (RvLval (LvReg Rv)) :: nil).

  Definition vars_start := 4 * 2.
  Definition var_slot x := LvMem (Sp + (vars_start + variablePosition vars x)%nat)%loc.

  Definition Skip := Straightline_ imports modName nil.

  Definition body :=
    match var with
      | None => Skip
      | Some x => SaveRv (var_slot x)
    end.

  Require Import Bedrock.Platform.Wrap.

  Opaque mult.
  Opaque evalInstrs.

  Lemma evalInstrs_write_var : forall sm x s,
    evalInstrs sm x (Assign (var_slot s) Rv :: nil)
    = evalInstrs sm x (Assign (LvMem (Imm ((Regs x Sp ^+ natToW vars_start) ^+ natToW (variablePosition vars s)))) Rv :: nil).
    Transparent evalInstrs.
    simpl.
    intros.
    replace (Regs x Sp ^+ natToW (vars_start + variablePosition vars s))
      with (Regs x Sp ^+ natToW vars_start ^+ natToW (variablePosition vars s)); auto.
    rewrite natToW_plus.
    words.
    Opaque evalInstrs.
  Qed.

  Lemma postOk : forall specs pre x,
    interp specs (Postcondition (body pre) x)
    -> imply pre new_pre
    -> syn_req
    -> exists x0, interp specs (pre (fst x, x0))
      /\ runs_to (fst x, x0) (snd x).
    intros.
    unfold syn_req, body, runs_to in *.
    destruct var; simpl in *; post.

    Focus 2.
    Transparent evalInstrs.
    simpl in H2.
    Opaque evalInstrs.
    injection H2; clear H2; intros; subst.
    descend; eauto.

    Opaque mult.

    Opaque mult.
    Opaque evalInstrs.

    rewrite evalInstrs_write_var in *.
    generalize H2; intro Hs.
    apply H0 in Hs; clear H0; post.
    clear_fancy.
    unfold vars_start in H3.
    change (4 * 2) with 8 in *.
    descend.
    eauto.
    clear H.
    unfold is_state in H0.
    evaluate auto_ext.
    destruct x; simpl in *.
    intuition.
    unfold is_state.
    step auto_ext.
  Qed.
  Opaque evalInstrs.

  Lemma verifCondOk : forall pre,
    imply pre new_pre
    -> syn_req
    -> vcs (VerifCond (body pre)).
    unfold syn_req, body; intros.
    destruct var; wrap0.
    rewrite evalInstrs_write_var in *.
    apply H in H1; clear H; post.
    unfold is_state in H.
    unfold vars_start in *.
    change (4 * 2) with 8 in *.
    clear_fancy.
    evaluate auto_ext.
    Transparent evalInstrs.
    discriminate.
    Opaque evalInstrs.
  Qed.

  Definition compile : cmd imports modName.
    refine (Wrap imports imports_global modName body post verifCond _ _).

    Opaque mult.
    Opaque evalInstrs.

    abstract (unfold verifCond; wrap0;
      match goal with
        | [ H : interp _ _ |- _ ] =>
          apply postOk in H; post; descend; eauto
      end).

    Opaque mult.
    Opaque evalInstrs.

    abstract (unfold verifCond; wrap0; eauto using verifCondOk).
 Defined.

End TopLevel.
