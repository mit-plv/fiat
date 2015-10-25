Local Notation iffT A B := ((A -> B) * (B -> A))%type.

Definition pull_forall_sigT {A B C}
: iffT (forall a : A, { b : B a & C a b })
       { b : forall a : A, B a & forall a, C a (b a) }.
Proof.
  split.
  { intro f.
    exists (fun a => projT1 (f a)).
    exact (fun a => projT2 (f a)). }
  { intros f a.
    exists (projT1 f a).
    exact (projT2 f a). }
Defined.
