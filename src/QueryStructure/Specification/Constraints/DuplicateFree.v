Require Import
        Coq.Lists.List
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.QueryStructure.

Definition DuplicateFree {heading} (tup1 tup2 : @RawTuple heading) := tup1 <> tup2.

Fixpoint BuildFinUpTo (n : nat) {struct n} : list (Fin.t n) :=
  match n return list (Fin.t n) with
  | 0  => nil
  | S n' => cons (@Fin.F1 _) (map (@Fin.FS _) (BuildFinUpTo n'))
  end.

Definition allAttributes heading
  : list (Attributes heading) :=
  BuildFinUpTo (NumAttr heading).

Fixpoint tupleAgree_computational'
         {h}
         (tup1 tup2 : @RawTuple h)
         (attrlist : list (Attributes h))
  {struct attrlist} :=
  match attrlist with
  | nil => True
  | cons attr nil => GetAttributeRaw tup1 attr = GetAttributeRaw tup2 attr
  | attr :: more => GetAttributeRaw tup1 attr = GetAttributeRaw tup2 attr /\ tupleAgree_computational' tup1 tup2 more
  end.
