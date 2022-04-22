(*+ Invertable functions *)
(*Note: this is a special case of Invertible relations bellow. We
separate for modularity and easier automation/debugging.*)

(* | Type class defining invertible functions. It accepts a
  predicate P for partially-invertible functions (e.g. nat -> word
  ) *)
Class ConditionallyInvertible {A B : Type} (F: A -> B)(P : A -> Prop) (F': B -> A) :=
  { CInvRoundTrip : forall a, P a -> F' (F a) = a }.

(* This lemma restates the invertible condition as a manipulation of
  equations.   *)
Lemma CInv_equation :
  forall A B F P F' {CInv: @ConditionallyInvertible A B F P F'},
  forall a b, P a -> F a = b -> a = F' b.
Proof. intros * ? *  ? HH. rewrite <- HH.
       rewrite CInvRoundTrip; auto. Qed.

(* | For any equation in the hypothesis that uses an invertible function in the left hand side, it moves the function to the right hand side (and solves the secondary generated subgoals) *)
Ltac subst_invertible_functions:=
  simpl in *;
  repeat match goal with
         | [ H: ?f ?x = _ |- _ ] =>
             eapply (CInv_equation _ _ f) in H;
             (*Solve the subgoals of inversion*)
             [  |
               (*Find the right typeclass *) now typeclasses eauto  |
               (* Solve the predicate *) now simpl in *; eauto
             ];
             try subst x
         end.


(*+ Invertable relations *)

(* | Type class defining invertible relations. The predicate can send an element in the domain to many elements in the image. Elements in the codomain have at most one element in the preimage. It accepts a
  predicate P for partially-invertible relations (e.g. nat -> word
  ) *)
Class ConditionallyInvertibleRel {A B : Type} (F: A -> B -> Prop)(P : A -> Prop) (F': B -> A) :=
  { CInvRoundTripRel : forall a, P a -> forall b, F a b -> a = F' b }.

(* | For any equation in the hypothesis that uses an invertible function in the left hand side, it moves the function to the right hand side (and solves the secondary generated subgoals) *)
Ltac subst_invertible_relations:=
  simpl in *;
  repeat match goal with
         | [ H: ?f ?x ?y |- _ ] =>
             eapply CInvRoundTripRel in H;
             (*Solve the subgoals of inversion*)
             [  |
               (*Find the right typeclass *) now typeclasses eauto  |
               (* Solve the predicate *) now simpl in *; eauto
             ];
             try subst x
         end.

Ltac subst_invertible:= simpl in *; repeat first [subst_invertible_functions | subst_invertible_relations]. 
