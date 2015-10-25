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

Ltac pull_forall_sigT :=
  idtac;
  (lazymatch goal with
  | [ |- sigT (fun f : forall a : ?A, @?B a => forall a' : ?A, @?C f a') ]
    => (let H := fresh in
        pose proof (fun C' => fst (@pull_forall_sigT A B C')) as H;
        cbv beta in H;
        let f' := fresh in
        let H' := fresh in
        edestruct H as [f' H']; clear H;
        [
        | exists f';
          let a := fresh in
          intro a; specialize (H' a);
          pattern a, (f' a);
          eexact H' ];
        cbv beta; intro)
   end).
