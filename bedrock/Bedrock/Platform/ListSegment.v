Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.
Require Import Coq.Lists.List Bedrock.Platform.SinglyLinkedList.

Set Implicit Arguments.


(** The nephew of the king of the abstract predicates *)

Module Type LIST_SEGMENT.
  Parameter lseg : list W -> W -> W -> HProp.

  Axiom lseg_extensional : forall ls p p', HProp_extensional (lseg ls p p').

  Axiom nil_bwd : forall (p p' : W),
    [| p = p' |] ===> lseg nil p p'.

  Axiom nil_bwd' : forall ls (p p' : W), p = p'
    -> [| ls = nil |] ===> lseg ls p p'.

  Axiom append_bwd : forall p' ls p,
    (Ex ls', Ex x, Ex p'', [| ls = ls' ++ x :: nil |] * lseg ls' p p'' * [| freeable p'' 2 |]
      * [| p'' <> 0 |] * (p'' ==*> x, p'))
    ===> lseg ls p p'.

  Axiom sll_fwd : forall ls (p p' : W), p' = 0
    -> lseg ls p p' ===> sll ls p.
End LIST_SEGMENT.

Module ListSegment : LIST_SEGMENT.
  Open Scope Sep_scope.

  Fixpoint lseg (ls : list W) (p p' : W) : HProp :=
    match ls with
      | nil => [| p = p' |]
      | x :: ls' => [| freeable p 2 |] * [| p <> 0 |] * Ex p'', (p ==*> x, p'') * lseg ls' p'' p'
    end.

  Theorem lseg_extensional : forall ls (p p' : W), HProp_extensional (lseg ls p p').
    destruct ls; reflexivity.
  Qed.

  Theorem nil_bwd : forall (p p' : W),
    [| p = p' |] ===> lseg nil p p'.
    sepLemma.
  Qed.

  Theorem nil_bwd' : forall ls (p p' : W), p = p'
    -> [| ls = nil |] ===> lseg ls p p'.
    destruct ls; sepLemma.
  Qed.

  Theorem append_bwd' : forall x p' ls p,
    (Ex p'', lseg ls p p'' * [| freeable p'' 2 |]
      * [| p'' <> 0 |] * (p'' ==*> x, p'))
    ===> lseg (ls ++ x :: nil) p p'.
    induction ls; sepLemma.
    etransitivity; [ | apply IHls ]; sepLemma.
  Qed.

  Theorem append_bwd : forall p' ls p,
    (Ex ls', Ex x, Ex p'', [| ls = ls' ++ x :: nil |] * lseg ls' p p'' * [| freeable p'' 2 |]
      * [| p'' <> 0 |] * (p'' ==*> x, p'))
    ===> lseg ls p p'.
    sepLemma; etransitivity; [ | apply append_bwd' ]; sepLemma.
  Qed.

  Theorem sll_fwd : forall ls (p p' : W), p' = 0
    -> lseg ls p p' ===> sll ls p.
    induction ls; sepLemma; [
      etransitivity; [ | apply SinglyLinkedList.nil_bwd; auto ]
      | etransitivity; [ | apply SinglyLinkedList.cons_bwd; auto ] ]; sepLemma.
  Qed.
End ListSegment.

Import ListSegment.
Export ListSegment.
Hint Immediate sll_extensional.
