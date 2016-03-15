Require Export
        Coq.Lists.List
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.Basics.

Create HintDb call_helpers_db discriminated.

Ltac learn_all_WeakEq_remove hyp lhs :=
  match lhs with
  | StringMap.add ?k _ ?lhs' => try learn (WeakEq_remove k hyp); learn_all_WeakEq_remove hyp lhs'
  | _ => idtac
  end.

Lemma combine_inv :
  forall A B input output combined,
    List.length input = List.length output ->
    @List.combine A B input output = combined ->
    input = fst (List.split combined) /\ output = snd (List.split combined).
Proof.
  intros; subst; rewrite List.combine_split; intuition eauto.
Qed.

Hint Resolve SameValues_Pop_Both : call_helpers_db.

(* Hint Extern 1 (_ ≲ Nil ∪ _) => simpl : call_helpers_db. *)
Hint Resolve SameValues_Nil_inv : call_helpers_db.

Ltac may_touch H :=
  match type of H with
  | context[@Learnt] => fail 1
  | _ => idtac
  end.

Ltac facade_cleanup_call :=
  match goal with
  | _ => progress cbv beta iota delta [add_remove_many] in *
  | _ => progress cbv beta iota delta [sel] in *
  | [ H: Axiomatic ?s = Axiomatic ?s' |- _ ] => inversion H; subst; clear H
  | [ H: PreCond ?f _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PreCond] in H
  | [ H: PostCond ?f _ _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PostCond] in H
  | [  |- PreCond ?f _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PreCond]
  | [  |- PostCond ?f _ _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PostCond]
  | [ H: WeakEq ?lhs _ |- _ ] => progress learn_all_WeakEq_remove H lhs
  | [ |- context[ListFacts4.mapM] ] => progress simpl ListFacts4.mapM
  | [ H: context[ListFacts4.mapM] |- _ ] => progress simpl ListFacts4.mapM in H
  | [ H: List.combine ?a ?b = _, H': List.length ?a = List.length ?b |- _ ] => learn (combine_inv a b H' H)
  | [ |-  context[List.split (cons _ _)] ] => simpl
  | [ H: context[List.split (cons _ _)] |- _ ] => may_touch H; simpl in H
  | [ H: List.cons _ _ = List.cons _ _ |- _ ] => inversion H; try subst; clear H
  | _ => GLabelMapUtils.normalize
  | _ => solve [GLabelMapUtils.decide_mapsto_maybe_instantiate]
  | [  |- exists _, _ ] => eexists
  end.

Ltac facade_eauto :=
  eauto 3 with call_helpers_db SameValues_db;
  eauto with call_helpers_db SameValues_db.

Hint Resolve WeakEq_Refl : call_helpers_db.
(* Hint Resolve WeakEq_Trans : call_helpers_db. *)
Hint Resolve WeakEq_remove_notIn : call_helpers_db.
Hint Resolve WeakEq_pop_SCA : call_helpers_db.
Hint Resolve WeakEq_pop_SCA_left : call_helpers_db.

Instance WrapInstance `{H: FacadeWrapper av A} : `{FacadeWrapper (Value av) A}.
Proof.
  refine {| wrap := fun a => @ADT av (wrap a);
            wrap_inj := _ |};
  FacadeWrapper_t.
Defined.

Lemma WrapInstance_wrap :
  forall `{H: FacadeWrapper av A} (x: A),
    wrap x = ADT (wrap x).
Proof.
  destruct H; intros; reflexivity.
Qed.

Hint Extern 1 => rewrite WrapInstance_wrap : call_helpers_db.
