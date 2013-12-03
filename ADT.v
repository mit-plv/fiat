Require Import String Omega.

Generalizable All Variables.
Set Implicit Arguments.


(** * Basic ADT definitions *)

(** Hoare logic-style total correctness specification of a method *)
Definition methodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Ty (* Final model *)
  -> nat (* Return value *)
  -> Prop.

(** Interface of an ADT *)
Record ADT := {
  Model : Type;
  (** The way we model state mathematically *)

  MethodSpecs : string -> methodSpec Model
  (** A specification for each method *)
}.


(** Implementation type of a method in Gallina *)
Definition methodTypeD (State : Type) :=
  State -> nat -> State * nat.

(** Usual Hoare logic notion of implementating a method spec *)
Definition methodCorrect (Model State : Type) (ms : methodSpec Model)
  (RepInv : Model -> State -> Prop)
  (mb : methodTypeD State) :=
  forall m s, RepInv m s
    -> forall x,
      let (s', y) := mb s x in
        exists m', RepInv m' s'
          /\ ms m x m' y.

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
Definition observer Model (ms : methodSpec Model) :=
  forall m x m' y, ms m x m' y
    -> m = m'.

(** When is a method not returning any data, but probably instead just causing side effects? *)
Definition mutator Model (ms : methodSpec Model) :=
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
  Definition pairedADT :=
    {|
      Model := Model A * Model B;
      MethodSpecs := fun name => match sortOf name with
                                   | ObserverA
                                     => fun m x m' y
                                        => MethodSpecs A name (fst m) x (fst m') y
                                   | ObserverB
                                     => fun m x m' y
                                        => MethodSpecs B name (snd m) x (snd m') y
                                   | Mutator
                                     => fun m x m' y
                                        => MethodSpecs A name (fst m) x (fst m') y
                                           /\ MethodSpecs B name (snd m) x (snd m') y
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

    simpl; intros name.
    generalize (sortOf_accurate name).
    destruct (sortOf name); simpl; unfold observer, mutator, methodCorrect;
    (simpl; intuition; simpl in *).

    - specialize (MethodsCorrect Ai name a (fst s) H1 x); simpl; intuition.
      destruct MethodBodies; firstorder eauto 10.

    - specialize (MethodsCorrect Bi name b (snd s) H2 x); simpl; intuition.
      destruct MethodBodies; firstorder eauto 10.

    - specialize (MethodsCorrect Ai name a (fst s) H2 x); simpl; intuition.
      destruct MethodBodies; firstorder.
      specialize (MethodsCorrect Bi name b (snd s) H3 x); simpl; intuition.
      destruct MethodBodies; firstorder.
      eexists (_, _); simpl.
      repeat esplit; simpl; eauto.
      replace 0 with n; eauto.
      replace 0 with n0; eauto.

    - eauto.
  Defined.
End paired.



Section prod.
  Variable model : Type.
  Variables ASpec BSpec : string -> methodSpec model.

  Let A := {| Model := model; MethodSpecs := ASpec |}.
  Let B := {| Model := model; MethodSpecs := BSpec |}.

  (** Let's compose these two ADTs. *)

  (** Require client code to classify the methods for us. *)
  Variable sortOf : string -> methodSort.

  (** The composed ADT, which doesn't duplicate models *)
  Definition prodADT :=
    {|
      Model := model;
      MethodSpecs := fun name => match sortOf name with
                                   | ObserverA => MethodSpecs A name
                                   | ObserverB => MethodSpecs B name
                                   | Mutator => fun m x m' y =>
                                                  MethodSpecs A name m x m' y
                                                  /\ MethodSpecs B name m x m' y
                                   | _ => fun _ _ _ _ => True
                                 end
    |}.

  (** Now we show how to implement it. *)
  Variable Ai : ADTimpl A.
  Variable Bi : ADTimpl B.

  Local Hint Extern 1 (@ex (_ * _) _) => eexists (_, _).

  Hypothesis sortOf_accurate : forall name, methodSort_accurate A B (sortOf name) name.

  Definition methods_match_mutation name
    := forall m x m' m'' x' x'',
         ASpec name m x m' x'
         -> BSpec name m x m'' x''
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
      | [ H : ?spec ?name ?d1 ?x ?d2 ?n |- ?spec ?name ?d1 ?x ?d2' ?n' ]
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

Fixpoint make_specs model (spec_list : list (string * methodSpec model))
  := fun s
     => match spec_list with
          | cons spec specs
            => if string_dec s (fst spec)
               then snd spec
               else make_specs specs s
          | nil => fun _ _ _ _ => True
        end.

Arguments make_specs / .

Definition common_multiset_specs (addname : string) : list (string * methodSpec multiset)
  := (addname,
      fun d x d' y
      => y = 0
         /\ d' = add d x)::nil.

Arguments common_multiset_specs / .

Definition make_accessor
           (model : Type) (f : nat -> model -> nat -> Prop)
: methodSpec model
  := fun d n d' n'
     => d = d'
        /\ f n d n'.

Arguments make_accessor / .

Coercion sumbooltobool A B : {A} + {B} -> bool := fun x => if x then true else false.

Infix "<=" := le_dec : bool_scope.
Infix "<" := lt_dec : bool_scope.
Infix ">=" := ge_dec : bool_scope.
Infix ">" := gt_dec : bool_scope.
Infix "->" := implb (at level 99, right associativity) : bool_scope.

Definition NatBinOp
           (addname : string)
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
                      ::common_multiset_specs addname)
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

Program Definition NatLower addName lowerBoundName : ADT
  := NatBinOp addName lowerBoundName min _ _.

Program Definition NatUpper addName upperBoundName : ADT
  := NatBinOp addName upperBoundName max _ _.

Program Definition NatSum addName sumName : ADT
  := NatBinOp addName sumName plus _ _.

Program Definition NatProd addName prodName : ADT
  := NatBinOp addName prodName mult _ _.


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

  Definition NatBinOpI (default_val : nat) addname opname (H : if string_dec addname opname then False else True)
  : `(ADTimpl (@NatBinOp addname opname op op_assoc op_comm)).
  Proof.
    intros.
    refine {|
        State := option nat;
        RepInv := fun (m : Model (NatBinOp addname opname op op_assoc op_comm)) n
                  => exists l : list nat,
                       (forall v, m v = count_occ eq_nat_dec l v)
                       /\ match l with
                            | nil => n = None
                            | cons x xs => n = Some (fold_right op x xs)
                          end;
        MethodBodies := fun s =>
                          if string_dec s addname
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
    repeat match goal with
             | [ H : False |- _ ] => destruct H
             | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
             | [ H : ?x = ?x -> False |- _ ] => destruct (H eq_refl)
             | [ |- appcontext[if ?E then _ else _] ] => let H := fresh "H'0" in
                                                         destruct E as [H|H]; subst
             | [ H : appcontext[if ?E then _ else _] |- _ ] => let H := fresh "H'0" in
                                                               destruct E as [H|H]; subst
           end;
      try solve [intros m [n|] [l [H0 H1]] x;
                  (exists (add m x));
                  repeat split;
                  try (exists (x::l));
                  abstract t' op op_assoc op_comm
                | intros m [n|] [l [H0 H1]] x;
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
                ].
  Defined.
End def_NatBinOpI.

Definition NatLowerI addName lowerBoundName H : ADTimpl (NatLower addName lowerBoundName)
  := NatBinOpI 0 addName lowerBoundName H _ _ _.

Definition NatUpperI addName upperBoundName H : ADTimpl (NatUpper addName upperBoundName)
  := NatBinOpI 0 addName upperBoundName H _ _ _.

Definition NatSumI addName sumName H : ADTimpl (NatSum addName sumName)
  := NatBinOpI 0 addName sumName H  _ _ _.

Definition NatProdI addName prodName H : ADTimpl (NatProd addName prodName)
  := NatBinOpI 1 addName prodName H _ _ _.

Local Open Scope string_scope.

Definition NatLowerUpper_sortOf (s : string) :=
  if string_dec s "add"
    then Mutator
    else if string_dec s "lowerBound"
      then ObserverA
      else if string_dec s "upperBound"
        then ObserverB
        else Dummy.

Definition NatLowerUpperPair : ADT
  := pairedADT (NatLower "add" "lowerBound")
               (NatUpper "add" "upperBound")
               NatLowerUpper_sortOf.
Definition NatLowerUpperProd : ADT
  := prodADT (MethodSpecs (NatLower "add" "lowerBound"))
             (MethodSpecs (NatUpper "add" "upperBound"))
             NatLowerUpper_sortOf.

Local Ltac pair_I_tac :=
  repeat match goal with
           | _ => intro
           | _ => progress simpl in *
           | [ |- context[if ?E then _ else _ ] ] => destruct E; subst
         end;
  simpl; unfold mutator, observer; simpl; instantiate; firstorder (subst; eauto).

Definition NatLowerUpperPairI : ADTimpl NatLowerUpperPair.
  refine (pairedImpl NatLowerUpper_sortOf
                     (NatLowerI "add" "lowerBound" I)
                     (NatUpperI "add" "upperBound" I)
                     _);
  unfold NatLowerUpper_sortOf.
  abstract pair_I_tac.
Defined.

Definition NatLowerUpperProdI : ADTimpl NatLowerUpperProd.
  refine (prodImpl NatLowerUpper_sortOf
                   (NatLowerI "add" "lowerBound" I)
                   (NatUpperI "add" "upperBound" I)
                   _
                   _);
  unfold NatLowerUpper_sortOf;
  abstract pair_I_tac.
Defined.



Definition s0pair : State NatLowerUpperPairI := (Some 10, Some 100).
Definition s1pair := fst (MethodBodies NatLowerUpperPairI "add" s0pair 2).
Definition s2pair := fst (MethodBodies NatLowerUpperPairI "add" s1pair 105).

Eval compute in snd (MethodBodies NatLowerUpperPairI "lowerBound" s2pair 0).
Eval compute in snd (MethodBodies NatLowerUpperPairI "upperBound" s2pair 0).

Definition s0prod : State NatLowerUpperProdI := (Some 10, Some 100).
Definition s1prod := fst (MethodBodies NatLowerUpperProdI "add" s0prod 2).
Definition s2prod := fst (MethodBodies NatLowerUpperProdI "add" s1prod 105).

Eval compute in snd (MethodBodies NatLowerUpperProdI "lowerBound" s2prod 0).
Eval compute in snd (MethodBodies NatLowerUpperProdI "upperBound" s2prod 0).



Definition NatSumProd_sortOf (s : string) :=
  if string_dec s "add"
  then Mutator
  else if string_dec s "sum"
       then ObserverA
       else if string_dec s "prod"
            then ObserverB
            else Dummy.

Definition NatSumProdPair : ADT
  := pairedADT (NatSum "add" "sum")
               (NatProd "add" "prod")
               NatSumProd_sortOf.
Definition NatSumProdProd : ADT
  := prodADT (MethodSpecs (NatSum "add" "sum"))
             (MethodSpecs (NatProd "add" "prod"))
             NatSumProd_sortOf.

Definition NatSumProdPairI : ADTimpl NatSumProdPair.
  refine (pairedImpl NatSumProd_sortOf
                     (NatSumI "add" "sum" I)
                     (NatProdI "add" "prod" I)
                     _);
  unfold NatSumProd_sortOf;
  abstract pair_I_tac.
Defined.

Definition NatSumProdProdI : ADTimpl NatSumProdProd.
  refine (prodImpl NatSumProd_sortOf
                   (NatSumI "add" "sum" I)
                   (NatProdI "add" "prod" I)
                   _
                   _);
  unfold NatSumProd_sortOf;
  abstract pair_I_tac.
Defined.

Definition s0'pair : State NatSumProdPairI := (Some 10, Some 100).
Definition s1'pair := fst (MethodBodies NatSumProdPairI "add" s0'pair 2).
Definition s2'pair := fst (MethodBodies NatSumProdPairI "add" s1'pair 105).

Eval compute in snd (MethodBodies NatSumProdPairI "sum" s2'pair 0).
Eval compute in snd (MethodBodies NatSumProdPairI "prod" s2'pair 0).

Definition s0'prod : State NatSumProdProdI := (Some 10, Some 100).
Definition s1'prod := fst (MethodBodies NatSumProdProdI "add" s0'prod 2).
Definition s2'prod := fst (MethodBodies NatSumProdProdI "add" s1'prod 105).

Eval compute in snd (MethodBodies NatSumProdProdI "sum" s2'prod 0).
Eval compute in snd (MethodBodies NatSumProdProdI "prod" s2'prod 0).
