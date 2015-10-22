Ltac head_constant expr :=
  match expr with
  | ?f _ => head_constant f
  | ?f => f
  end.

Ltac no_duplicates :=
  match goal with
  | [ H: ?P, H': ?P' |- _ ] =>
    match type of P with
    | Prop => unify P P'; fail 2 "Duplicates found:" H "and" H' ":" P
    | _ => fail
    end
  | _ => idtac
  end.

Ltac deduplicate :=
  repeat match goal with
         | [ H: ?P, H': ?P' |- _ ] =>
           match type of P with
           | Prop => unify P P'; clear H' (* Fixme don't set evars? *)
           | _ => fail
           end
         | _ => idtac
         end.

(* Inductive Learnt : Prop -> Type := *)
(*   | AlreadyKnown : forall A, Learnt A. *)

(* Ltac learn fact := *)
(*   let type := type of fact in *)
(*   match goal with *)
(*   | [ H: Learnt type |- _ ] => fail 1 fact "of type" type "is already known" *)
(*   | _ => pose proof (AlreadyKnown type); pose proof fact *)
(*   end. *)

(* Definition Learnt {A} (a: A) := *)
(*   True. *)

(* Ltac learn fact := *)
(*   match goal with *)
(*   | [ H: Learnt fact |- _ ] => fail 1 fact "is already known" *)
(*   | _ => assert (Learnt fact) by exact I; pose proof fact *)
(*   end. *)

Inductive Learnt {A: Type} (a: A) :=
  | AlreadyKnown : Learnt a.

Ltac learn fact :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] => fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
        lazymatch goal with
        | [ H: @Learnt type _ |- _ ] => fail 0 "fact" fact "of type" type "was already learnt through" H
        | _ => pose proof (AlreadyKnown fact); pose proof fact
        end
  end.
