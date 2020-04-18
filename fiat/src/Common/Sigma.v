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

Definition pull_forall2_sigT {A B X C}
: iffT (forall a : A, { b : B a & forall x : X, C x a b })
       { b : forall a : A, B a & forall x a, C x a (b a) }.
Proof.
  split.
  { intro f.
    exists (fun a => projT1 (f a)).
    exact (fun x a => projT2 (f a) x). }
  { intros f a.
    exists (projT1 f a).
    exact (fun x => projT2 f x a). }
Defined.


Definition pull_forall3_sigT {A B X Y C}
: iffT (forall a : A, { b : B a & forall (x : X) (y : Y x), C x y a b })
       { b : forall a : A, B a & forall x y a, C x y a (b a) }.
Proof.
  split.
  { intro f.
    exists (fun a => projT1 (f a)).
    exact (fun x y a => projT2 (f a) x y). }
  { intros f a.
    exists (projT1 f a).
    exact (fun x y => projT2 f x y a). }
Defined.

Ltac pull_forall_sigT :=
  idtac;
  (lazymatch goal with
  | [ |- sigT (fun f : forall a : ?A, @?B a => forall a' : ?A, _) ]
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
  | [ |- sigT (fun f : forall a : ?A, @?B a => forall (x' : ?X) (a' : ?A), _) ]
    => (let H := fresh in
        pose proof (fun C' => fst (@pull_forall3_sigT A B X C')) as H;
        cbv beta in H;
        let f' := fresh in
        let H' := fresh in
        edestruct H as [f' H']; clear H;
        [
        | exists f';
          let a := fresh in
          let x := fresh in
          intros x a; specialize (H' x a);
          pattern x, a, (f' a);
          eexact H' ];
        cbv beta; intro)
  | [ |- sigT (fun f : forall a : ?A, @?B a => forall (x' : ?X) (y' : @?Y x') (a' : ?A), _) ]
    => (let H := fresh in
        pose proof (fun C' => fst (@pull_forall3_sigT A B X Y C')) as H;
        cbv beta in H;
        let f' := fresh in
        let H' := fresh in
        edestruct H as [f' H']; clear H;
        [
        | exists f';
          let a := fresh in
          let x := fresh in
          let y := fresh in
          intros x y a; specialize (H' x y a);
          pattern x, y, a, (f' a);
          eexact H' ];
        cbv beta; intro)
   end).
