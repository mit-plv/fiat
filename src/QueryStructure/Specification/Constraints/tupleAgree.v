Require Import  Coq.Lists.List
        Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Schema.

Lemma tupleAgree_empty :
  forall {heading} (tup1 tup2: @RawTuple heading),
    tupleAgree tup1 tup2 [] <-> True.
Proof.
  unfold tupleAgree; intuition.
Qed.

Lemma tupleAgree_unfold :
  forall {heading} (tup1 tup2: @RawTuple heading) attr more,
    tupleAgree tup1 tup2 (attr :: more) <->
    (GetAttributeRaw tup1 attr = GetAttributeRaw tup2 attr) /\ tupleAgree tup1 tup2 more.
Proof.
  unfold tupleAgree; simpl; split; intros; intuition; subst; intuition.
Qed.

Fixpoint tupleAgree_computational
         {h}
         (tup1 tup2 : @RawTuple h)
         (attrlist : list (Attributes h)) :=
  match attrlist with
    | [] => True
    | attr :: more => GetAttributeRaw tup1 attr = GetAttributeRaw tup2 attr /\ tupleAgree_computational tup1 tup2 more
  end.

Lemma tupleAgree_equivalence :
  forall {h} tup1 tup2 attrlist,
    @tupleAgree h tup1 tup2 attrlist <->
    @tupleAgree_computational h tup1 tup2 attrlist.
Proof.
  induction attrlist; simpl; intros.
  apply tupleAgree_empty.
  rewrite tupleAgree_unfold, IHattrlist.
  reflexivity.
Qed.
