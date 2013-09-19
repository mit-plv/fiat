Require Import String Omega.

Generalizable All Variables.
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
(** We require that the path between the before/after models be refl,
    because this allows us to not need UIP. *)
Definition observer (ms : methodSpec) :=
  forall T (m m' : T) x y, ms (Dyn m) x (Dyn m') y
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

  Local Hint Extern 1 (@ex (_ * _) _) => eexists (_, _).

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



Section prod.
  Variable model : Type.
  Variables ASpec BSpec : string -> methodSpec.

  Let A := {| Model := model; MethodSpecs := ASpec |}.
  Let B := {| Model := model; MethodSpecs := BSpec |}.

  (** Let's compose these two ADTs. *)

  (** Require client code to classify the methods for us. *)
  Variable sortOf : string -> methodSort.

  (** The composed ADT, which doesn't duplicate models *)
  Definition prodADT := {|
    Model := model;
    MethodSpecs := fun name => match sortOf name with
                                 | ObserverA => fun m x m' y =>
                                   exists (m0 : model) (m'0 : model),
                                     m = Dyn m0 /\ m' = Dyn m'0
                                     /\ MethodSpecs A name (Dyn m0) x (Dyn m'0) y
                                 | ObserverB => fun m x m' y =>
                                   exists (m0 : model) (m'0 : model),
                                     m = Dyn m0 /\ m' = Dyn m'0
                                     /\ MethodSpecs B name (Dyn m0) x (Dyn m'0) y
                                 | Mutator => fun m x m' y =>
                                   exists (m0 : model) (m'0 : model),
                                     m = Dyn m0 /\ m' = Dyn m'0
                                     /\ MethodSpecs A name (Dyn m0) x (Dyn m'0) y
                                     /\ MethodSpecs B name (Dyn m0) x (Dyn m'0) y
                                 | _ => fun _ _ _ _ => True
                               end
  |}.

  (** Now we show how to implement it. *)
  Variable Ai : ADTimpl A.
  Variable Bi : ADTimpl B.

  Local Hint Extern 1 (@ex (_ * _) _) => eexists (_, _).

  Hypothesis sortOf_accurate : forall name, methodSort_accurate A B (sortOf name) name.

  Definition methods_match_mutation name
    := forall (m m' m'' : model) x y y',
         ASpec name (Dyn m) x (Dyn m') y
         -> BSpec name (Dyn m) x (Dyn m'') y'
         -> m' = m''.

  Hypothesis mutators_match
  : forall name,
      match sortOf name with
        | Mutator => methods_match_mutation name
        | _ => True
      end.

  Local Hint Extern 1 => symmetry.

  Local Ltac fin_tac :=
    match goal with
      | [ H : RepInv ?i ?m ?s |- RepInv ?i ?m' ?s ] => replace m' with m; eauto
      | [ H : ?spec ?name ?d1 ?x (Dyn ?d2) ?n |- ?spec ?name ?d1 ?x (Dyn ?d2') ?n' ]
        => replace n' with n; eauto;
           replace d2' with d2; eauto
    end.

  Definition prodImpl : ADTimpl prodADT.
    refine {|
      State := State Ai * State Bi;
      RepInv := fun (m : Model prodADT) s => RepInv Ai m (fst s)
        /\ RepInv Bi m (snd s);
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

    simpl; intros name m s H x.
    generalize (sortOf_accurate name).
    generalize (mutators_match name).
    destruct (sortOf name); simpl; unfold observer, mutator, methodCorrect, methods_match_mutation;
      (simpl; intuition; simpl in *);
      match goal with
        | [ H1 : RepInv Ai m (fst s), H2 : RepInv Bi m (snd s) |- _ ]
          => specialize (MethodsCorrect Ai name m (fst s) H1 x);
            specialize (MethodsCorrect Bi name m (snd s) H2 x)
      end;
      repeat destruct MethodBodies;
      intros;
      firstorder;
      simpl in *;
      try solve [ repeat esplit; (eassumption || fin_tac)
                | repeat esplit; [ eassumption | | ]; fin_tac
                | repeat esplit; [ | eassumption | ]; fin_tac ].
  Defined.
End prod.

(** * An example, composing binary commutative associative calculators for computable nat multisets *)

Definition multiset := nat -> nat.
Definition add (s : multiset) (n : nat) : multiset
  := fun m => if eq_nat_dec n m
              then S (s m)
              else s m.

Require Import Min Max List.

Fixpoint make_specs (spec_list : list (string * methodSpec))
  := fun s
     => match spec_list with
          | cons spec specs
            => if string_dec s (fst spec)
               then snd spec
               else make_specs specs s
          | nil => fun _ _ _ _ => True
        end.

Arguments make_specs / .

Definition common_multiset_specs : list (string * methodSpec)
  := ("add"%string,
      fun d x d' y
      => y = 0
         /\ (exists m : multiset, d = Dyn m /\ d' = Dyn (add m x)))::nil.

Arguments common_multiset_specs / .

Definition make_accessor
           (model : Type) (f : nat -> model -> nat -> Prop)
: methodSpec
  := fun d n d' n'
     => exists m : model,
          d = Dyn m /\ d = d'
          /\ f n m n'.

Arguments make_accessor / .

Coercion sumbooltobool A B : {A} + {B} -> bool := fun x => if x then true else false.

Infix "<=" := le_dec : bool_scope.
Infix "<" := lt_dec : bool_scope.
Infix ">=" := ge_dec : bool_scope.
Infix ">" := gt_dec : bool_scope.
Infix "->" := implb : bool_scope.

Definition NatBinOp
           (opname : string)
           (op : nat -> nat -> nat)
           (is_assoc : forall x y z, op x (op y z) = op (op x y) z)
           (is_comm : forall x y, op x y = op y x)
: ADT
  := {|
      Model := multiset;
      MethodSpecs :=
        make_specs ((opname,
                     make_accessor (fun _ (m : multiset) n
                                    => exists l : list nat,
                                         (forall v, m v = count_occ eq_nat_dec l v)
                                         /\ match l with
                                              | nil => True
                                              | cons x xs => n = fold_right op x xs
                                            end))
                      ::common_multiset_specs)
    |}.

Local Ltac rewrite_hyp' :=
  match goal with
    | [ H : _ |- _ ] => rewrite H
  end.

Require Import Omega.

Local Obligation Tactic :=
  eauto with arith;
  try solve [ repeat match goal with
                       | _ => progress (simpl; rewrite_hyp'; trivial)
                       | [ |- _ -> _ ] => let x := fresh in intro x; induction x; trivial
                     end
            | intros; omega ].

Program Definition NatLower : ADT
  := NatBinOp "lowerBound" min _ _.

Program Definition NatUpper : ADT
  := NatBinOp "upperBound" max _ _.

Program Definition NatSum : ADT
  := NatBinOp "sum" plus _ _.

Program Definition NatProd : ADT
  := NatBinOp "prod" mult _ _.


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

Require Import FunctionalExtensionality.

Arguments add _ _ _ / .


Section def_NatBinOpI.

  Local Ltac induction_list_then tac :=
    lazymatch goal with
      | [ l : list _ |- _ ]
        => repeat match goal with
                    | [ H : appcontext[l] |- _ ] => clear H
                  end;
          induction l; tac
    end.

  Local Ltac manipulate_op op_assoc op_comm :=
    match goal with
      | _ => reflexivity
      | _ => progress simpl in *
      | _ => apply op_comm
      | _ => rewrite <- ?op_assoc; revert op_assoc op_comm; rewrite_hyp'; intros
      | _ => rewrite ?op_assoc; revert op_assoc op_comm; rewrite_hyp'; intros
      | _ => rewrite <- ?op_assoc; f_equal; []
      | _ => rewrite ?op_assoc; f_equal; []
      | _ => apply op_comm
    end.

  Local Ltac deep_manipulate_op op op_assoc op_comm can_comm_tac :=
    repeat match goal with
             | _ => progress repeat manipulate_op op_assoc op_comm
             | [ |- appcontext[op ?a ?b] ]
               => can_comm_tac a b;
                 rewrite (op_comm a b);
                 let new_can_comm_tac :=
                     fun x y =>
                       can_comm_tac x y;
                       try (unify x a;
                            unify y b;
                            fail 1 "Cannot commute" a "and" b "again")
                 in deep_manipulate_op op op_assoc op_comm new_can_comm_tac
           end.

  Local Ltac solve_after_induction_list op op_assoc op_comm :=
    solve [ deep_manipulate_op op op_assoc op_comm ltac:(fun a b => idtac) ].


  Local Ltac t :=
    repeat match goal with
             | _ => assumption
             | _ => intro
             | _ => progress simpl in *
             | [ |- appcontext[if string_dec ?A ?B then _ else _ ] ]
               => destruct (string_dec A B)
             | _ => progress subst
             | [ H : ex _ |- _ ] => destruct H
             | [ H : and _ _ |- _ ] => destruct H
             | _ => split
             | [ H : option _ |- _ ] => destruct H
             | [ H : _ |- _ ] => solve [ inversion H ]
             | [ |- appcontext[match ?x with _ => _ end] ] => destruct x
             | [ H : appcontext[match ?x with _ => _ end] |- _  ] => destruct x
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
             | _ => progress f_equal; []
             | _ => apply functional_extensionality_dep; intro
             | _ => progress intuition
             | _ => repeat esplit; reflexivity
             | [ H : _ |- _ ] => rewrite H; try (rewrite H; fail 1)
           end.

  Local Ltac t' op op_assoc op_comm :=
    repeat first [ progress t
                 | progress induction_list_then ltac:(solve_after_induction_list op op_assoc op_comm) ].

  Definition NatBinOpI (default_val : nat) opname (H : if string_dec opname "add"%string then False else True)
  : `(ADTimpl (@NatBinOp opname op op_assoc op_comm)).
  Proof.
    intros.
    refine {|
        State := option nat;
        RepInv := fun (m : Model (NatBinOp opname op op_assoc op_comm)) n
                  => exists l : list nat,
                       (forall v, m v = count_occ eq_nat_dec l v)
                       /\ match l with
                            | nil => n = None
                            | cons x xs => n = Some (fold_right op x xs)
                          end;
        MethodBodies := fun s =>
                          if string_dec s "add"
                          then fun val x => (match val with
                                               | None => Some x
                                               | Some x' => Some (op x x')
                                             end,
                                             0)
                          else if string_dec s opname
                               then fun val _ => (val,
                                                  match val with
                                                    | None => default_val
                                                    | Some x => x
                                                  end)
                               else fun val _ => (val, 0)
      |}.
    intro name.
    simpl.
    destruct (string_dec name "add"%string) as [Hadd | Hadd];
      [ intros m [n|] [l [H0 H1]] x;
        (exists (add m x));
        repeat split;
        try (exists (x::l));
        abstract t' op op_assoc op_comm
      | destruct (string_dec name opname) as [Hop | Hop];
        [ intros m [n|] [l [H0 H1]] x;
          repeat (split || exists m || exists l);
          abstract t' op op_assoc op_comm
        | intros m [n|] [l [H0 H1]] x;
          [ repeat split;
            try (exists (add (fun _ => 0) n));
            repeat split;
            try (exists (n::nil));
            abstract (repeat split)
          | repeat split;
            try (exists m);
            repeat split;
            try (exists l);
            abstract (repeat split; assumption) ]
      ]].
  Defined.
End def_NatBinOpI.

Definition NatLowerI : ADTimpl NatLower
  := NatBinOpI 0 "lowerBound" I _ _ _.

Definition NatUpperI : ADTimpl NatUpper
  := NatBinOpI 0 "upperBound" I _ _ _.

Definition NatSumI : ADTimpl NatSum
  := NatBinOpI 0 "sum" I _ _ _.

Definition NatProdI : ADTimpl NatProd
  := NatBinOpI 1 "prod" I _ _ _.

Local Open Scope string_scope.

Definition NatLowerUpper_sortOf (s : string) :=
  if string_dec s "add"
    then Mutator
    else if string_dec s "lowerBound"
      then ObserverA
      else if string_dec s "upperBound"
        then ObserverB
        else Dummy.

Definition NatLowerUpperPair : ADT := pairedADT NatLower NatUpper NatLowerUpper_sortOf.
Definition NatLowerUpperProd : ADT := prodADT (Model NatLower) (MethodSpecs NatLower) (MethodSpecs NatUpper) NatLowerUpper_sortOf.

Local Ltac pair_I_tac :=
  intros;
  repeat match goal with
           | [ |- context[if ?E then _ else _ ] ] => destruct E; subst
         end;
  simpl; unfold mutator, observer; simpl; firstorder.

Definition NatLowerUpperPairI : ADTimpl NatLowerUpperPair.
  refine (pairedImpl NatLowerUpper_sortOf NatLowerI NatUpperI _);
  unfold NatLowerUpper_sortOf.
  intro name.
  destruct (string_dec name "add");
    [ | destruct (string_dec name "lowerBound");
      [ | destruct (string_dec name "upperBound") ]];
    simpl;
    subst;
    simpl;
    try solve [ pair_I_tac ].
  admit.
  admit.
Defined.

Definition s0 : State NatLowerUpperPairI := (Some 10, Some 100).
Definition s1 := fst (MethodBodies NatLowerUpperPairI "add" s0 2).
Definition s2 := fst (MethodBodies NatLowerUpperPairI "add" s1 105).

Eval compute in snd (MethodBodies NatLowerUpperPairI "lowerBound" s2 0).
Eval compute in snd (MethodBodies NatLowerUpperPairI "upperBound" s2 0).



Definition NatSumProd_sortOf (s : string) :=
  if string_dec s "add"
  then Mutator
  else if string_dec s "sum"
       then ObserverA
       else if string_dec s "prod"
            then ObserverB
            else Dummy.

Definition NatSumProd : ADT := pairedADT NatSum NatProd NatSumProd_sortOf.

Definition NatSumProdI : ADTimpl NatSumProd.
  refine (pairedImpl NatSumProd_sortOf NatSumI NatProdI _);
  unfold NatSumProd_sortOf;
  abstract pair_I_tac.
Defined.

Definition s0' : State NatSumProdI := (Some 10, Some 100).
Definition s1' := fst (MethodBodies NatSumProdI "add" s0' 2).
Definition s2' := fst (MethodBodies NatSumProdI "add" s1' 105).

Eval compute in snd (MethodBodies NatSumProdI "sum" s2' 0).
Eval compute in snd (MethodBodies NatSumProdI "prod" s2' 0).
