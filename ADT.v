Require Import String Omega.

Set Implicit Arguments.


(** * Basic ADT definitions *)

(** To avoid wallowing in dependent types, we'll use this guy often. *)
Record dyn := Dyn {
  Ty : Type;
  Va : Ty
}.

(** Hoare logic-style total correctness specification of a method *)
Definition methodSpec :=
  dyn    (* Initial model *)
  -> nat (* Actual argument*)
  -> dyn (* Final model *)
  -> nat (* Return value *)
  -> Prop.

(** Interface of an ADT *)
Record ADT := {
  Model : Type;
  (** The way we model state mathematically *)

  MethodSpecs : string -> methodSpec
  (** A specification for each method *)
}.


(** Implementation type of a method in Gallina *)
Definition methodTypeD (State : Type) :=
  State -> nat -> State * nat.

(** Usual Hoare logic notion of implementating a method spec *)
Definition methodCorrect (ms : methodSpec) (Model State : Type)
  (RepInv : Model -> State -> Prop)
  (mb : methodTypeD State) :=
  forall m s, RepInv m s
    -> forall x,
      let (s', y) := mb s x in
        exists m', RepInv m' s'
          /\ ms (Dyn m) x (Dyn m') y.

(** One implementation of an ADT *)
Record ADTimpl (A : ADT) := {
  State : Type;
  (** Real state type in Gallina *)

  RepInv : Model A -> State -> Prop;
  (** Relationship between abstract (specification) and concrete (implementation) states *)

  MethodBodies : string -> methodTypeD State;
  (** An implementation of each method *)

  MethodsCorrect : forall name, methodCorrect (MethodSpecs A name) RepInv
    (MethodBodies name)
  (** All methods satisfy their specs. *)
}.


(** * A simple pairing combinator *)

(** When does a method spec force no state mutation? *)
Definition observer (ms : methodSpec) :=
  forall m x m' y, ms m x m' y
    -> m = m'.

(** When is a method not returning any data, but probably instead just causing side effects? *)
Definition mutator (ms : methodSpec) :=
  forall m x m' y, ms m x m' y
    -> y = 0.

Section paired.
  Variables A B : ADT.
  (** Let's compose these two ADTs. *)

  (** We'll want to classify each method as follows: *)
  Inductive methodSort :=
  | ObserverA (* Observer implemented by [A] *)
  | ObserverB (* Observer implemented by [B] *)
  | Mutator   (* Mutator implemented by _both_ *)
  | Dummy     (* Just gets a dummy implementation in composition *).

  (** When is one of these classifications accurate? *)
  Definition methodSort_accurate (s : methodSort) (name : string) :=
    match s with
      | ObserverA => observer (MethodSpecs A name)
      | ObserverB => observer (MethodSpecs B name)
      | Mutator => mutator (MethodSpecs A name) /\ mutator (MethodSpecs B name)
      | Dummy => True
    end.

  (** Require client code to classify the methods for us. *)
  Variable sortOf : string -> methodSort.

  (** The composed ADT *)
  Definition pairedADT := {|
    Model := Model A * Model B;
    MethodSpecs := fun name => match sortOf name with
                                 | ObserverA => fun m x m' y =>
                                   exists (m1 : Model A) (m2 : Model B), m = Dyn (m1, m2)
                                     /\ exists (m1' : Model A), m' = Dyn (m1', m2)
                                       /\ MethodSpecs A name (Dyn m1) x (Dyn m1') y
                                 | ObserverB => fun m x m' y =>
                                   exists (m1 : Model A) (m2 : Model B), m = Dyn (m1, m2)
                                     /\ exists (m2' : Model B), m' = Dyn (m1, m2')
                                       /\ MethodSpecs B name (Dyn m2) x (Dyn m2') y
                                 | Mutator => fun m x m' y =>
                                   exists (m1 : Model A) (m2 : Model B), m = Dyn (m1, m2)
                                     /\ exists (m1' : Model A) (m2' : Model B), m' = Dyn (m1', m2')
                                       /\ MethodSpecs A name (Dyn m1) x (Dyn m1') y
                                       /\ MethodSpecs B name (Dyn m2) x (Dyn m2') y
                                 | _ => fun _ _ _ _ => True
                               end
  |}.

  (** Now we show how to implement it. *)
  Variable Ai : ADTimpl A.
  Variable Bi : ADTimpl B.

  Hint Extern 1 (@ex (_ * _) _) => eexists (_, _).

  Hypothesis sortOf_accurate : forall name, methodSort_accurate (sortOf name) name.

  Definition pairedImpl : ADTimpl pairedADT.
    refine {|
      State := State Ai * State Bi;
      RepInv := fun (m : Model pairedADT) s => RepInv Ai (fst m) (fst s)
        /\ RepInv Bi (snd m) (snd s);
      MethodBodies := fun name => match sortOf name as s with
                                    | ObserverA => fun s x =>
                                      let (s', y) := MethodBodies Ai name (fst s) x in
                                        ((s', snd s), y)
                                    | ObserverB => fun s x =>
                                      let (s', y) := MethodBodies Bi name (snd s) x in
                                        ((fst s, s'), y)
                                    | Mutator => fun s x =>
                                      let (s1, _) := MethodBodies Ai name (fst s) x in
                                        let (s2, _) := MethodBodies Bi name (snd s) x in
                                          ((s1, s2), 0)
                                    | Dummy => fun s _ => (s, 0)
                                  end
    |}.

    simpl; intros.
    generalize (sortOf_accurate name).
    destruct (sortOf name); simpl; unfold observer, mutator, methodCorrect;
      (simpl; intuition; simpl in *).

    specialize (MethodsCorrect Ai name a (fst s) H1 x); simpl; intuition.
    destruct MethodBodies; firstorder eauto 10.

    specialize (MethodsCorrect Bi name b (snd s) H2 x); simpl; intuition.
    destruct MethodBodies; firstorder eauto 10.

    specialize (MethodsCorrect Ai name a (fst s) H2 x); simpl; intuition.
    destruct MethodBodies; firstorder.
    specialize (MethodsCorrect Bi name b (snd s) H3 x); simpl; intuition.
    destruct MethodBodies; firstorder.
    repeat esplit; simpl; eauto.
    replace 0 with n; eauto.
    replace 0 with n0; eauto.

    eauto.
  Defined.
End paired.


(** * An example, composing "min" and "max" calculators for nat sets *)

Definition set := nat -> Prop.
Definition add (s : set) (n : nat) : set := fun m => m = n \/ s m.

Require Import Min Max.

Definition NatLower : ADT := {|
  Model := set;
  MethodSpecs := fun s =>
    if string_dec s "add"
      then fun d x d' y => y = 0
        /\ exists m : set, d = Dyn m /\ d' = Dyn (add m x)
      else if string_dec s "lowerBound"
        then fun d _ d' n => exists m : set, d = Dyn m /\ d = d' /\ forall v, m v -> n <= v
        else fun _ _ _ _ => True
|}.

Definition NatUpper : ADT := {|
  Model := set;
  MethodSpecs := fun s =>
    if string_dec s "add"
      then fun d x d' y => y = 0
        /\ exists m : set, d = Dyn m /\ d' = Dyn (add m x)
      else if string_dec s "upperBound"
        then fun d _ d' n => exists m : set, d = Dyn m /\ d = d' /\ forall v, m v -> n >= v
        else fun _ _ _ _ => True
|}.

Hint Immediate le_min_l le_min_r le_max_l le_max_r.

Lemma min_trans : forall n m v,
  n <= v
  -> min n m <= v.
  intros; destruct (min_spec n m); omega.
Qed.

Lemma max_trans : forall n m v,
  n >= v
  -> max n m >= v.
  intros; destruct (max_spec n m); omega.
Qed.

Hint Resolve min_trans max_trans.

Definition NatLowerI : ADTimpl NatLower.
  refine {|
    State := nat;
    RepInv := fun (m : Model NatLower) n => forall v, m v -> n <= v;
    MethodBodies := fun s =>
      if string_dec s "add"
        then fun bound x => (min bound x, 0)
        else if string_dec s "lowerBound"
          then fun bound _ => (bound, bound)
          else fun bound _ => (bound, 0)
  |};
  abstract (simpl; intro;
    repeat match goal with
             | [ |- context[if ?E then _ else _ ] ] => destruct E
           end; unfold methodCorrect; simpl; intuition eauto; repeat esplit; eauto;
    unfold add; simpl; intuition (subst; eauto)).
Defined.

Definition NatUpperI : ADTimpl NatUpper.
  refine {|
    State := nat;
    RepInv := fun (m : Model NatUpper) n => forall v, m v -> n >= v;
    MethodBodies := fun s =>
      if string_dec s "add"
        then fun bound x => (max bound x, 0)
        else if string_dec s "upperBound"
          then fun bound _ => (bound, bound)
          else fun bound _ => (bound, 0)
  |};
  abstract (simpl; intro;
    repeat match goal with
             | [ |- context[if ?E then _ else _ ] ] => destruct E
           end; unfold methodCorrect; simpl; intuition eauto; repeat esplit; eauto;
    unfold add; simpl; intuition (subst; eauto)).
Defined.

Definition NatLowerUpper_sortOf (s : string) :=
  if string_dec s "add"
    then Mutator
    else if string_dec s "lowerBound"
      then ObserverA
      else if string_dec s "upperBound"
        then ObserverB
        else Dummy.

Definition NatLowerUpper : ADT := pairedADT NatLower NatUpper NatLowerUpper_sortOf.

Definition NatLowerUpperI : ADTimpl NatLowerUpper.
  refine (pairedImpl NatLowerUpper_sortOf NatLowerI NatUpperI _);
    abstract (unfold NatLowerUpper_sortOf; intros;
      repeat match goal with
               | [ |- context[if ?E then _ else _ ] ] => destruct E; subst
             end; simpl; unfold mutator, observer; simpl; firstorder).
Defined.

Definition s0 : State NatLowerUpperI := (10, 100).
Definition s1 := fst (MethodBodies NatLowerUpperI "add" s0 2).
Definition s2 := fst (MethodBodies NatLowerUpperI "add" s1 105).

Eval compute in snd (MethodBodies NatLowerUpperI "lowerBound" s2 0).
Eval compute in snd (MethodBodies NatLowerUpperI "upperBound" s2 0).
