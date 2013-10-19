Require Import String Omega List.

Generalizable All Variables.
Set Implicit Arguments.

(* Coq's build in tactics don't work so well with things like [iff]
   so split them up into multiple hypotheses *)
Ltac split_in_context ident funl funr :=
  repeat match goal with
           | [ H : context p [ident] |- _ ] =>
             let H0 := context p[funl] in let H0' := eval simpl in H0 in assert H0' by (apply H);
               let H1 := context p[funr] in let H1' := eval simpl in H1 in assert H1' by (apply H);
                 clear H
         end.

Ltac split_iff := split_in_context iff (fun a b : Prop => a -> b) (fun a b : Prop => b -> a).

Ltac split_and' :=
  repeat match goal with
           | [ H : ?a /\ ?b |- _ ] => let H0 := fresh in let H1 := fresh in
             assert (H0 := fst H); assert (H1 := snd H); clear H
         end.
Ltac split_and := split_and'; split_in_context and (fun a b : Type => a) (fun a b : Type => b).

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => pose proof defn
    end.


(** * Basic ADT definitions *)

(** Hoare logic-style total correctness specification of a mutator method *)
Definition mutatorMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
  -> Ty (* Final model *)
(*  -> nat (* Return value *) *)
  -> Prop.

(** Hoare logic-style total correctness specification of an obeserver method *)
Definition observerMethodSpec (Ty : Type) :=
  Ty    (* Initial model *)
  -> nat (* Actual argument*)
(*  -> Ty (* Final model *) *)
  -> nat (* Return value *)
  -> Prop.

(** Interface of an ADT *)
Record ADT :=
  {
    Model : Type;
    (** The way we model state mathematically *)

    MutatorIndex : Type;
    (** The index set of mutators *)

    ObserverIndex : Type;
    (** The index set of observers *)

    MutatorMethodSpecs : MutatorIndex -> mutatorMethodSpec Model;
    (** A specification for each mutator method *)

    ObserverMethodSpecs : ObserverIndex -> observerMethodSpec Model
    (** A specification for each observer method *)
  }.

(** Implementation type of a method in Gallina *)
Definition methodTypeD (State : Type) :=
  State -> nat -> State * nat.

(** Usual Hoare logic notion of implementating a mutator method spec *)
Definition mutatorMethodCorrect (Model State : Type)
           (ms : mutatorMethodSpec Model)
           (RepInv : Model -> State -> Prop)
           (mb : methodTypeD State)
  := forall m s,
       RepInv m s
       -> forall x,
            let s'y := mb s x in
            exists m', RepInv m' (fst s'y)
                       /\ ms m x m'
                       /\ (snd s'y) = 0.

Definition observerMethodCorrect (Model State : Type)
           (ms : observerMethodSpec Model)
           (RepInv : Model -> State -> Prop)
           (mb : methodTypeD State)
  := forall m s,
       RepInv m s
       -> forall x,
            let s'y := mb s x in
            RepInv m (fst s'y)
            /\ ms m x (snd s'y).

(** One implementation of an ADT *)
Record ADTimpl (A : ADT) :=
  {
    State : Type;
    (** Real state type in Gallina *)

    RepInv : Model A -> State -> Prop;
    (** Relationship between abstract (specification) and concrete (implementation) states *)

    MutatorMethodBodies : MutatorIndex A -> methodTypeD State;
    (** An implementation of each mutator method *)

    ObserverMethodBodies : ObserverIndex A -> methodTypeD State;
    (** An implementation of each observer method *)

    MutatorMethodsCorrect : forall idx, mutatorMethodCorrect
                                          (MutatorMethodSpecs A idx)
                                          RepInv
                                          (MutatorMethodBodies idx);
    (** All mutator methods satisfy their specs. *)

    ObserverMethodsCorrect : forall idx, observerMethodCorrect
                                           (ObserverMethodSpecs A idx)
                                           RepInv
                                           (ObserverMethodBodies idx)
    (** All observer methods satisfy their specs. *)
  }.


(** * A simple pairing combinator *)

Section paired.
  Variables A B : ADT.
  (** Let's compose these two ADTs. *)

  Variable mutatorIndex : Type.
  Variable observerIndex : Type.
  Variable mutatorMap : mutatorIndex -> MutatorIndex A * MutatorIndex B.
  Variable observerMap : observerIndex -> ObserverIndex A + ObserverIndex B.

  (** The composed ADT *)
  Definition pairedADT :=
    {|
      Model := Model A * Model B;
      MutatorIndex := mutatorIndex;
      ObserverIndex := observerIndex;
      MutatorMethodSpecs idx :=
        let s := mutatorMap idx in
        fun m x m' => MutatorMethodSpecs A (fst s) (fst m) x (fst m')
                      /\ MutatorMethodSpecs B (snd s) (snd m) x (snd m');
      ObserverMethodSpecs idx :=
        fun m x y => match observerMap idx with
                       | inl idx' => ObserverMethodSpecs A idx' (fst m) x y
                       | inr idx' => ObserverMethodSpecs B idx' (snd m) x y
                     end
    |}.

  (** Now we show how to implement it. *)
  Variable Ai : ADTimpl A.
  Variable Bi : ADTimpl B.

  Definition pairedImpl : ADTimpl pairedADT.
  Proof.
    refine {|
        State := State Ai * State Bi;
        RepInv := fun (m : Model pairedADT) s
                  => RepInv Ai (fst m) (fst s)
                     /\ RepInv Bi (snd m) (snd s);
        MutatorMethodBodies name :=
          fun s x
          => ((fst (MutatorMethodBodies Ai (fst (mutatorMap name)) (fst s) x),
               fst (MutatorMethodBodies Bi (snd (mutatorMap name)) (snd s) x)),
              0);
        ObserverMethodBodies name :=
          fun s x
          => match observerMap name with
               | inl name'
                 => let sy := ObserverMethodBodies Ai name' (fst s) x in
                    ((fst sy, snd s), snd sy)
               | inr name'
                 => let sy := ObserverMethodBodies Bi name' (snd s) x in
                    ((fst s, fst sy), snd sy)
             end
      |};
    repeat match goal with
             | _ => intro
             | _ => progress simpl in *
             | [ idx : mutatorIndex, H : RepInv Ai _ _ /\ RepInv Bi _ _, x : nat |- _ ]
               => generalize (MutatorMethodsCorrect Ai (fst (mutatorMap idx)) _ _ (proj1 H) x);
                 generalize (MutatorMethodsCorrect Bi (snd (mutatorMap idx)) _ _ (proj2 H) x);
                 destruct (mutatorMap idx), H; simpl in *;
                 clear idx;
                 progress repeat destruct MutatorMethodBodies;
                 firstorder; subst
             | [ idx : observerIndex |- _ ]
               => destruct (observerMap idx) as [idx'|idx']; clear idx
             | _ => eexists (_, _)
             | _ => progress (repeat esplit; try eassumption)
             | _ => apply ObserverMethodsCorrect
             | _ => progress firstorder intuition
           end.
  Defined.
End paired.

Section prod.
  Variable model : Type.
  Variables AMutIndex BMutIndex AObsIndex BObsIndex : Type.
  Variable AMutSpec : AMutIndex -> mutatorMethodSpec model.
  Variable BMutSpec : BMutIndex -> mutatorMethodSpec model.
  Variable AObsSpec : AObsIndex -> observerMethodSpec model.
  Variable BObsSpec : BObsIndex -> observerMethodSpec model.

  Let A := {| Model := model;
              MutatorMethodSpecs := AMutSpec;
              ObserverMethodSpecs := AObsSpec |}.
  Let B := {| Model := model;
              MutatorMethodSpecs := BMutSpec;
              ObserverMethodSpecs := BObsSpec |}.

  Variable mutatorIndex : Type.
  Variable observerIndex : Type.
  Variable mutatorMap : mutatorIndex -> MutatorIndex A * MutatorIndex B.
  Variable observerMap : observerIndex -> ObserverIndex A + ObserverIndex B.

  (** Let's compose these two ADTs. *)
  (** The composed ADT, which doesn't duplicate models *)
  Definition prodADT :=
    {|
      Model := model;
      MutatorMethodSpecs idx :=
        fun m x m' => MutatorMethodSpecs A (fst (mutatorMap idx)) m x m'
                      /\ MutatorMethodSpecs B (snd (mutatorMap idx)) m x m';
      ObserverMethodSpecs idx :=
        fun m x y => match observerMap idx with
                       | inl idx' => ObserverMethodSpecs A idx' m x y
                       | inr idx' => ObserverMethodSpecs B idx' m x y
                     end
    |}.

  (** Now we show how to implement it. *)
  Variable Ai : ADTimpl A.
  Variable Bi : ADTimpl B.

  Local Hint Extern 1 (@ex (_ * _) _) => eexists (_, _).

  Hypothesis mutators_match
  : forall idx,
      forall m x m' m'',
        AMutSpec (fst (mutatorMap idx)) m x m'
        -> BMutSpec (snd (mutatorMap idx)) m x m''
        -> m' = m''.

  Local Hint Extern 1 => symmetry.

  Definition prodImpl : ADTimpl prodADT.
    refine {|
      State := State Ai * State Bi;
      RepInv := fun (m : Model prodADT) s
                => RepInv Ai m (fst s)
                   /\ RepInv Bi m (snd s);
      MutatorMethodBodies idx :=
        fun s x =>
          let s1 := fst (MutatorMethodBodies Ai (fst (mutatorMap idx)) (fst s) x) in
          let s2 := fst (MutatorMethodBodies Bi (snd (mutatorMap idx)) (snd s) x) in
          ((s1, s2), 0);
      ObserverMethodBodies idx :=
        match observerMap idx with
          | inl idx' =>
            fun s x =>
              let s'y := ObserverMethodBodies Ai idx' (fst s) x in
              ((fst s'y, snd s), snd s'y)
          | inr idx' =>
            fun s x =>
              let s'y := ObserverMethodBodies Bi idx' (snd s) x in
              ((fst s, fst s'y), snd s'y)
        end
      |};
    intro idx;
    try (assert (MM := mutators_match idx));
    repeat intro;
    simpl in *;
    match goal with
      | [ |- appcontext[mutatorMap ?idx] ]
        => destruct (mutatorMap idx); clear idx
      | [ |- appcontext[observerMap ?idx] ]
        => destruct (observerMap idx); clear idx
    end;
    simpl in *;
    repeat split;
    try first [ apply (ObserverMethodsCorrect Ai)
              | apply (ObserverMethodsCorrect Bi) ];
    simpl in *; intuition.
    edestruct (MutatorMethodsCorrect Ai); try eassumption.
    edestruct (MutatorMethodsCorrect Bi); try eassumption.
    simpl in *.
    intuition.
    match goal with
      | [ AM : AMutSpec _ _ _ _, BM : BMutSpec _ _ _ _ |- _ ]
        => specialize (MM _ _ _ _ AM BM); subst
    end.
    repeat esplit; eassumption.
  Defined.
End prod.

(** A transformation (approximately, injection) from one ADT to another *)

Section inj.
  Variables A B : ADT.
  (** Let's compose these two ADTs. *)

  Variable BtoA : Model B -> Model A.
  Variable mutatorMap : MutatorIndex B -> MutatorIndex A.
  Variable observerMap : ObserverIndex B -> ObserverIndex A.
  Hypothesis mutatorSpecMap
  : forall idx m x m',
      MutatorMethodSpecs A (mutatorMap idx) (BtoA m) x m'
      -> exists m'',
           m' = BtoA m''
           /\ MutatorMethodSpecs B idx m x m''.
  Hypothesis observerSpecMap
  : forall idx m x y,
      ObserverMethodSpecs A (observerMap idx) (BtoA m) x y
      -> ObserverMethodSpecs B idx m x y.

  Variable Ai : ADTimpl A.

  Definition injImpl : ADTimpl B.
  Proof.
    refine {|
        State := State Ai;
        RepInv := fun (m : Model B) s
                  => RepInv Ai (BtoA m) s;
        MutatorMethodBodies name := MutatorMethodBodies Ai (mutatorMap name);
        ObserverMethodBodies name := ObserverMethodBodies Ai (observerMap name)
      |};
    intro idx;
    let H := fresh in
    first [ assert (H := MutatorMethodsCorrect Ai (mutatorMap idx))
          | assert (H := ObserverMethodsCorrect Ai (observerMap idx)) ];
      let inv := fresh in
      let x := fresh in
      intros ? ? inv x;
        specialize (H _ _ inv x);
        simpl in *;
        intuition;
        let m := fresh "m" in
        destruct H as [m H];
          split_and.
    let H0 := match goal with
                | [ H : _ |- _ ] => constr:(@mutatorSpecMap _ _ _ _ H)
              end in
    let m := fresh "m" in
    destruct H0 as [m ?];
      split_and;
      exists m;
      subst;
      intuition.
   Defined.
End inj.


(** * An example, composing binary commutative associative calculators for computable nat multisets *)

Definition multiset := nat -> nat.
Definition add (s : multiset) (n : nat) : multiset
  := fun m => if eq_nat_dec n m
              then S (s m)
              else s m.

Require Import Min Max List.

Coercion sumbooltobool A B : {A} + {B} -> bool := fun x => if x then true else false.

Infix "<=" := le_dec : bool_scope.
Infix "<" := lt_dec : bool_scope.
Infix ">=" := ge_dec : bool_scope.
Infix ">" := gt_dec : bool_scope.
(*Infix "->" := implb : bool_scope.*)

(*
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
*)


Definition add_spec : mutatorMethodSpec multiset
  := fun m x m' => forall k, m' k = (add m x) k.

Arguments add_spec / .

Definition bin_op_spec (op : nat -> nat -> nat) (default_value : nat)
: observerMethodSpec multiset
  := fun m x n => exists l : list nat,
                    (forall v, m v = count_occ eq_nat_dec l v)
                    /\ match l with
                         | nil => n = default_value
                         | cons z zs => n = fold_right op z zs
                       end.

Arguments bin_op_spec / .

Definition NatBinOp
           (op : nat -> nat -> nat)
           (is_assoc : forall x y z, op x (op y z) = op (op x y) z)
           (is_comm : forall x y, op x y = op y x)
           (default_value : nat)
: ADT
  := {|
      Model := multiset;
      MutatorIndex := unit;
      ObserverIndex := unit;
      MutatorMethodSpecs u := add_spec;
      ObserverMethodSpecs u := bin_op_spec op default_value
    |}.

Local Ltac rewrite_hyp' :=
  match goal with
    | [ H : _ |- _ ] => rewrite H
  end.

Local Obligation Tactic :=
  eauto with arith;
  try solve [ repeat match goal with
                       | _ => progress (simpl; rewrite_hyp'; trivial)
                       | [ |- _ -> _ ] => let x := fresh in intro x; induction x; trivial
                     end
            | intros; omega ].

Program Definition NatLower default_value : ADT
  := NatBinOp min _ _ default_value.

Program Definition NatUpper default_value : ADT
  := NatBinOp max _ _ default_value.

Program Definition NatSum default_value : ADT
  := NatBinOp plus _ _ default_value.

Program Definition NatProd default_value : ADT
  := NatBinOp mult _ _ default_value.


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
             | _ => progress intuition
             | _ => repeat esplit; reflexivity
             | [ H : _ |- _ ] => rewrite H; try (rewrite H; fail 1)
           end.

  Local Ltac t' op op_assoc op_comm :=
    repeat first [ progress t
                 | progress induction_list_then ltac:(solve_after_induction_list op op_assoc op_comm) ].

  Definition NatBinOpI
  : `(ADTimpl (@NatBinOp op op_assoc op_comm default_value)).
  Proof.
    intros.
    refine {|
        State := option nat;
        RepInv := fun (m : Model (NatBinOp op op_assoc op_comm default_value)) n
                  => exists l : list nat,
                       (forall v, m v = count_occ eq_nat_dec l v)
                       /\ match l with
                            | nil => n = None
                            | cons x xs => n = Some (fold_right op x xs)
                          end;
        MutatorMethodBodies u val x := (match val with
                                          | None => Some x
                                          | Some x' => Some (op x x')
                                        end,
                                        0);
        ObserverMethodBodies u val x := (val,
                                         match val with
                                           | None => default_value
                                           | Some x => x
                                         end)
      |};
      intros [];
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

Definition NatLowerI default_val : ADTimpl (NatLower default_val)
  := NatBinOpI _ _ _ _.

Definition NatUpperI default_val : ADTimpl (NatUpper default_val)
  := NatBinOpI _ _ _ _.

Definition NatSumI default_val : ADTimpl (NatSum default_val)
  := NatBinOpI _ _ _ _.

Definition NatProdI default_val : ADTimpl (NatProd default_val)
  := NatBinOpI _ _ _ _.

Local Open Scope string_scope.

Definition NatSumProd_spec : ADT
  := {| Model := multiset;
        MutatorIndex := unit;
        ObserverIndex := unit + unit;
        MutatorMethodSpecs u := add_spec;
        ObserverMethodSpecs u m x n :=
          match u with
            | inl _ => bin_op_spec plus 0 m x n
            | inr _ => bin_op_spec mult 1 m x n
          end
     |}.

Record PartialADTimpl (A : ADT) :=
  {
    PState : Type;
    (** Real state type in Gallina *)

    PRepInv : Model A -> PState -> Prop;
    (** Relationship between abstract (specification) and concrete (implementation) states *)

    PMutatorMethodBodies : MutatorIndex A -> methodTypeD PState;
    (** An implementation of each mutator method *)

    PObserverMethodBodies : ObserverIndex A -> option (methodTypeD PState);
    (** An implementation of each observer method *)

    PMutatorMethodsCorrect : forall idx, mutatorMethodCorrect
                                           (MutatorMethodSpecs A idx)
                                           PRepInv
                                           (PMutatorMethodBodies idx);
    (** All mutator methods satisfy their specs. *)

    PObserverMethodsCorrect : forall idx, match PObserverMethodBodies idx with
                                            | Some body => observerMethodCorrect
                                                             (ObserverMethodSpecs A idx)
                                                             PRepInv
                                                             body
                                            | None => True
                                          end
    (** All observer methods satisfy their specs. *)
  }.

Definition IsFull_PartialADTimpl A (impl : PartialADTimpl A)
  := forall idx, PObserverMethodBodies impl idx <> None.

Definition ADTimpl_of_PartialADTimpl A impl (H : @IsFull_PartialADTimpl A impl)
: ADTimpl A
  := {|
      State := PState impl;
      RepInv := PRepInv impl;
      MutatorMethodBodies := PMutatorMethodBodies impl;
      ObserverMethodBodies := (fun idx : ObserverIndex A
                               => match PObserverMethodBodies impl idx
                                        as b
                                        return b <> None -> _
                                  with
                                    | Some body => fun _ => body
                                    | None => fun x : None <> None
                                              => match x eq_refl with end
                                  end (H idx));
      MutatorMethodsCorrect := PMutatorMethodsCorrect impl;
      ObserverMethodsCorrect := (fun idx : ObserverIndex A =>
                                   match
                                     PObserverMethodBodies impl idx as b
                                     return
                                     (forall n : b <> None,
                                        match b with
                                          | Some body =>
                                            observerMethodCorrect
                                              (ObserverMethodSpecs A idx)
                                              (PRepInv impl)
                                              body
                                          | None => True
                                        end ->
                                        observerMethodCorrect
                                          (ObserverMethodSpecs A idx)
                                          (PRepInv impl)
                                          (match b with
                                             | Some body => fun _ => body
                                             | None => _
                                           end n))
                                   with
                                     | Some m => fun _ corr => corr
                                     | None => fun x : None <> None =>
                                                 match x eq_refl with end
                                   end
                                     (H idx)
                                     (PObserverMethodsCorrect impl idx))
    |}.

Coercion PartialADTimpl_of_ADTimpl A (impl : ADTimpl A)
: PartialADTimpl A
  := {|
      PState := State impl;
      PRepInv := RepInv impl;
      PMutatorMethodBodies := MutatorMethodBodies impl;
      PObserverMethodBodies idx := Some (ObserverMethodBodies impl idx);
      PMutatorMethodsCorrect := MutatorMethodsCorrect impl;
      PObserverMethodsCorrect := ObserverMethodsCorrect impl
    |}.


Section pairedPartial.
  Variables A B : ADT.
  (** Let's compose these two ADTs. *)

  Variable mutatorIndex : Type.
  Variable observerIndex : Type.
  Variable mutatorMap : mutatorIndex -> MutatorIndex A * MutatorIndex B.
  Variable observerMap : observerIndex -> ObserverIndex A + ObserverIndex B.

  (** Now we show how to implement it. *)
  Variable Ai : PartialADTimpl A.
  Variable Bi : PartialADTimpl B.

  Definition pairedPartialImpl
  : PartialADTimpl (pairedADT A B mutatorMap observerMap).
  Proof.
    refine {|
        PState := PState Ai * PState Bi;
        PRepInv := fun (m : Model (pairedADT A B mutatorMap observerMap)) s
                   => PRepInv Ai (fst m) (fst s)
                      /\ PRepInv Bi (snd m) (snd s);
        PMutatorMethodBodies name :=
          fun s x
          => ((fst (PMutatorMethodBodies Ai (fst (mutatorMap name)) (fst s) x),
               fst (PMutatorMethodBodies Bi (snd (mutatorMap name)) (snd s) x)),
              0);
        PObserverMethodBodies name :=
          match observerMap name with
            | inl name'
              => match PObserverMethodBodies Ai name' with
                   | Some body => Some (fun s x
                                        => let sy := body (fst s) x in
                                           ((fst sy, snd s), snd sy))
                   | None => None
                 end
            | inr name'
              => match PObserverMethodBodies Bi name' with
                   | Some body => Some (fun s x
                                        => let sy := body (snd s) x in
                                           ((fst s, fst sy), snd sy))
                   | None => None
                 end
          end
      |};
    repeat match goal with
             | _ => intro
             | _ => progress simpl in *
             | [ idx : mutatorIndex, H : PRepInv Ai _ _ /\ PRepInv Bi _ _, x : nat |- _ ]
               => generalize (PMutatorMethodsCorrect Ai (fst (mutatorMap idx)) _ _ (proj1 H) x);
                 generalize (PMutatorMethodsCorrect Bi (snd (mutatorMap idx)) _ _ (proj2 H) x);
                 destruct (mutatorMap idx), H; simpl in *;
                 clear idx;
                 progress repeat destruct PMutatorMethodBodies;
                 simpl in *;
                 firstorder; subst
             | [ idx : ObserverIndex _ |- appcontext[PRepInv ?Ai] ]
               => unique_pose (PObserverMethodsCorrect Ai idx)
             | [ |- appcontext[match PObserverMethodBodies ?i ?name with _ => _ end] ]
               => destruct (PObserverMethodBodies i name);
                 simpl in *;
                 unfold observerMethodCorrect in *;
                 split_and;
                 intros;
                 split;
                 try solve [ intuition ]
             | [ idx : observerIndex |- _ ]
               => destruct (observerMap idx) as [idx'|idx']; clear idx
             | _ => eexists (_, _)
             | _ => progress (repeat esplit; try eassumption)
             | _ => apply PObserverMethodsCorrect
             | _ => progress firstorder intuition
           end.
  Defined.
End pairedPartial.

Section prodPartial.
  Variable model : Type.
  Variables AMutIndex BMutIndex AObsIndex BObsIndex : Type.
  Variable AMutSpec : AMutIndex -> mutatorMethodSpec model.
  Variable BMutSpec : BMutIndex -> mutatorMethodSpec model.
  Variable AObsSpec : AObsIndex -> observerMethodSpec model.
  Variable BObsSpec : BObsIndex -> observerMethodSpec model.

  Let A := {| Model := model;
              MutatorMethodSpecs := AMutSpec;
              ObserverMethodSpecs := AObsSpec |}.
  Let B := {| Model := model;
              MutatorMethodSpecs := BMutSpec;
              ObserverMethodSpecs := BObsSpec |}.

  Variable mutatorIndex : Type.
  Variable observerIndex : Type.
  Variable mutatorMap : mutatorIndex -> MutatorIndex A * MutatorIndex B.
  Variable observerMap : observerIndex -> ObserverIndex A + ObserverIndex B.

  Local Notation prodADT := (prodADT AMutSpec BMutSpec
                                     AObsSpec BObsSpec
                                     mutatorMap
                                     observerMap).

  (** Now we show how to implement it. *)
  Variable Ai : PartialADTimpl A.
  Variable Bi : PartialADTimpl B.

  Local Hint Extern 1 (@ex (_ * _) _) => eexists (_, _).

  Hypothesis mutators_match
  : forall idx,
      forall m x m' m'',
        AMutSpec (fst (mutatorMap idx)) m x m'
        -> BMutSpec (snd (mutatorMap idx)) m x m''
        -> m' = m''.

  Local Hint Extern 1 => symmetry.

  Definition prodPartialImpl : PartialADTimpl prodADT.
  Proof.
    refine {|
        PState := PState Ai * PState Bi;
        PRepInv := fun (m : Model prodADT) s
                   => PRepInv Ai m (fst s)
                      /\ PRepInv Bi m (snd s);
        PMutatorMethodBodies idx :=
          fun s x =>
            let s1 := fst (PMutatorMethodBodies Ai (fst (mutatorMap idx)) (fst s) x) in
            let s2 := fst (PMutatorMethodBodies Bi (snd (mutatorMap idx)) (snd s) x) in
            ((s1, s2), 0);
        PObserverMethodBodies idx :=
          match observerMap idx with
            | inl idx' =>
              match PObserverMethodBodies Ai idx' with
                | Some body => Some (fun s x =>
                                       let s'y := body (fst s) x in
                                       ((fst s'y, snd s), snd s'y))
                | None => None
              end
            | inr idx' =>
              match PObserverMethodBodies Bi idx' with
                | Some body => Some (fun s x =>
                                       let s'y := body (snd s) x in
                                       ((fst s, fst s'y), snd s'y))
                | None => None
              end
          end
      |};
    intro idx;
    try (assert (MM := mutators_match idx));
    repeat intro;
    simpl in *;
    match goal with
      | [ |- appcontext[mutatorMap ?idx] ]
        => destruct (mutatorMap idx); clear idx
      | [ |- appcontext[observerMap ?idx] ]
        => destruct (observerMap idx); clear idx
    end;
    simpl in *;
    repeat split;
    try match goal with
          | [ |- appcontext[PObserverMethodBodies ?i ?idx] ]
            => pose proof (PObserverMethodsCorrect i idx);
              destruct (PObserverMethodBodies i idx)
        end;
    simpl in *;
    unfold observerMethodCorrect in *;
    split_and;
    simpl in *;
    intuition.
    - edestruct (PMutatorMethodsCorrect Ai); try eassumption.
      edestruct (PMutatorMethodsCorrect Bi); try eassumption.
      simpl in *.
      intuition.
      match goal with
        | [ AM : AMutSpec _ _ _ _, BM : BMutSpec _ _ _ _ |- _ ]
          => specialize (MM _ _ _ _ AM BM); subst
      end.
      repeat esplit; eassumption.
  Defined.
End prodPartial.


(** A transformation (approximately, injection) from one ADT to another *)

Section injPartial.
  Variables A B : ADT.
  (** Let's compose these two ADTs. *)

  Variable AtoB : Model A -> Model B.
  Variable BtoA : Model B -> Model A.
  Variable mutatorMap : MutatorIndex B -> MutatorIndex A.
  Variable observerMap : ObserverIndex B -> ObserverIndex A.
  Hypothesis mutatorSpecMap
  : forall idx m x m',
      MutatorMethodSpecs A (mutatorMap idx) (BtoA m) x m'
      -> exists m'',
           m' = BtoA m''
           /\ MutatorMethodSpecs B idx m x m''.
  Hypothesis observerSpecMap
  : forall idx m x y,
      ObserverMethodSpecs A (observerMap idx) (BtoA m) x y
      -> ObserverMethodSpecs B idx m x y.


  Variable Ai : PartialADTimpl A.

  Definition injPartialImpl : PartialADTimpl B.
  Proof.
    refine {|
        PState := PState Ai;
        PRepInv := fun (m : Model B) s
                  => PRepInv Ai (BtoA m) s;
        PMutatorMethodBodies name := PMutatorMethodBodies Ai (mutatorMap name);
        PObserverMethodBodies name := PObserverMethodBodies Ai (observerMap name)
      |};
    intro idx;
    let H := fresh in
    first [ assert (H := PMutatorMethodsCorrect Ai (mutatorMap idx))
          | assert (H := PObserverMethodsCorrect Ai (observerMap idx));
            edestruct PObserverMethodBodies; trivial ];
      let inv := fresh in
      let x := fresh in
      intros ? ? inv x;
        specialize (H _ _ inv x);
        simpl in *;
        intuition;
        let m := fresh "m" in
        destruct H as [m H];
          split_and.
    let H0 := match goal with
                | [ H : _ |- _ ] => constr:(@mutatorSpecMap _ _ _ _ H)
              end in
    let m := fresh "m" in
    destruct H0 as [m ?];
      split_and;
      exists m;
      subst;
      intuition.
  Defined.
End injPartial.


(** Notes: it should be m' = BtoA m' m'' in mutators_match; actually we probably want [mutators_match : forall idx m x m', MutatorMethodSpecs B (Ms idx) (AtoB m) x m' -> exists m'', AtoB m'' = m'] *)
Lemma add_component A B (Bimpl : ADTimpl B) later
  (Is : ObserverIndex A -> ObserverIndex B + later)
  (unlater : later -> ObserverIndex A)
  (Ms : MutatorIndex A -> MutatorIndex B)
  (AtoB : Model A -> Model B)
  (mutators_match : forall idx,
    forall m x m',
      MutatorMethodSpecs B (Ms idx) (AtoB m) x m'
      -> exists m'', m' = AtoB m''
                     /\ MutatorMethodSpecs A idx m x m'')
  (mutators_match_hammer : forall idx,
    forall m x m' m'',
      MutatorMethodSpecs B (Ms idx) (AtoB m) x m'
      -> MutatorMethodSpecs A idx m x m''
      -> m' = AtoB m'')
  (observers_match : forall idx,
    match Is idx with
      | inr _ => True
      | inl idx' =>
        forall m x y,
          ObserverMethodSpecs A idx m x y
          <-> ObserverMethodSpecs B idx' (AtoB m) x y
    end)
  (almost_adjunction : forall idx l, Is idx = inr l -> idx = unlater l)
  : PartialADTimpl {| Model := Model A;
    MutatorIndex := MutatorIndex A;
    ObserverIndex := later;
    MutatorMethodSpecs := MutatorMethodSpecs A;
    ObserverMethodSpecs i := ObserverMethodSpecs A (unlater i)
  |}
  -> PartialADTimpl A.
Proof.
  intro Aimpl.
  pose (Bimpl : PartialADTimpl _) as Bimpl'.
  Print Implicit injPartialImpl.
  let A' := match type of Aimpl with PartialADTimpl ?A' => constr:(A') end in
  pose (@pairedPartialImpl
          A' B
          (MutatorIndex A)
          (ObserverIndex A)
          (fun idx => (idx, Ms idx))
          (fun idx => match Is idx with
                        | inl idx' => inr idx'
                        | inr idx' => inl idx'
                      end)
          Aimpl
          Bimpl')
    as ABimpl;
    let AB := match type of ABimpl with PartialADTimpl ?AB => constr:(AB) end in
    apply (fun g h =>
            @injPartialImpl
              AB A
              (fun a => (a, AtoB a))
              (fun x => x)
              (fun x => x)
              g h
              ABimpl);
    simpl in *;
    try solve [ intuition ];
    [
    | solve [ intros idx; intros;
              specialize (observers_match idx);
              repeat match goal with
                       | [ H : appcontext[Is idx] |- _ ] => revert H
                     end;
              case_eq (Is idx);
              intros;
              split_iff;
              rewrite ?Htos' in *;
              intuition;
              erewrite <- almost_adjunction in * by eassumption; trivial
            ] ].
  - intros idx m x [m'A m'B] ?; simpl in *.
    intuition.
    f_equal.
    esplit; intuition eauto; f_equal.
    eapply mutators_match_hammer; try eassumption.
Defined.

Lemma no_observers (A : ADT) (Hreally : ObserverIndex A -> False)
  (Himplementable : forall idx m x,
    exists m', MutatorMethodSpecs A idx m x m')
  : PartialADTimpl A.
  refine {| PState := unit;
    PRepInv := fun _ _ => True;
    PMutatorMethodBodies := fun _ _ _ => (tt, 0);
    PObserverMethodBodies := fun _ => None
  |}; auto.

  intro.
  hnf; simpl; intros.
  edestruct Himplementable.
  eauto.
Defined.

Goal PartialADTimpl NatSumProd_spec.
Proof.
  pose proof (add_component NatSumProd_spec
    (NatSumI 0)
    (later := unit)).

  eapply (add_component NatSumProd_spec
    (NatSumI 0)
    (later := unit)
    (fun x => x)
    (fun x => inr x)
    (fun x => x) (fun x => x));
  auto.
  - simpl.
    simpl; intros.
    eexists; repeat esplit; trivial.
  - destruct idx; simpl.
    intros.
    Require Import FunctionalExtensionality.
    extensionality n.
    rewrite H, H0; auto.

  - destruct idx; intuition.

  - let A := match goal with |- PartialADTimpl ?A => constr:(A) end in
    eapply (add_component A
                          (NatProdI 1) (later := Empty_set)
                          (fun x => inl x)
                          (fun x => match x with end)
                          (fun x => x)
                          (fun x => x));
      simpl; auto.
    + simpl.
      simpl; intros.
      eexists; repeat esplit; trivial.
    + intros.
      Require Import FunctionalExtensionality.
      extensionality n.
      rewrite H, H0; auto.

    + tauto.
    + destruct l.

    + apply no_observers; simpl; intros.
      destruct H.
      exists (fun k => if eq_nat_dec x k then S (m k) else m k).
      auto.
Defined.


Existing Class ADTimpl.
Hint Extern 1 (ADTimpl _) => eapply NatLowerI : typeclass_instances.
Hint Extern 1 (ADTimpl _) => eapply NatUpperI : typeclass_instances.
Hint Extern 1 (ADTimpl _) => eapply NatSumI : typeclass_instances.
Hint Extern 1 (ADTimpl _) => eapply NatProdI : typeclass_instances.
Hint Extern 2 (ADTimpl _) => eapply pairedImpl : typeclass_instances.

Record refine (from to : ADT) :=
  {
    MakeImpl : ADTimpl from -> ADTimpl to;
    MapMutator : MutatorIndex to -> option (MutatorIndex from);
    MapObserver : ObserverIndex to -> option (ObserverIndex from)
  }.

Definition empty :=
  {|
    Model := unit;
    MutatorIndex := Empty_set;
    ObserverIndex := Empty_set;

    MutatorMethodSpecs := fun x : Empty_set => match x with end;
    ObserverMethodSpecs := fun x : Empty_set => match x with end
  |}.

Definition emptyI : ADTimpl empty :=
  {|
    State := unit;
    RepInv := fun _ _ => True;
    MutatorMethodBodies := fun x : MutatorIndex empty => match x with end;
    ObserverMethodBodies := fun x : Empty_set => match x with end;
    MutatorMethodsCorrect := fun x : Empty_set => match x with end;
    ObserverMethodsCorrect := fun x : Empty_set => match x with end
  |}.


Definition ADTimpl' (to : ADT) := refine empty to.

Theorem finish : forall to (ai' : ADTimpl' to), ADTimpl to.
  destruct 1; eauto using emptyI.
Defined.

Definition easy from : refine from from :=
  {|
    MakeImpl := fun x => x;
    MapMutator := fun x => Some x;
    MapObserver := fun x => Some x
  |}.

Section refinePaired.
  Variables from new : ADT.

  Variable mutatorIndex : Type.
  Variable observerIndex : Type.
  Variable mutatorMap : mutatorIndex -> MutatorIndex from * MutatorIndex new.
  Variable observerMap : observerIndex -> ObserverIndex from + ObserverIndex new.

  Definition refinePaired to (newI : ADTimpl new)
  : refine (pairedADT from new mutatorMap observerMap) to
    -> refine from to
    := fun r =>
         {| MakeImpl fromI := MakeImpl r (pairedImpl _ _ fromI newI);
            MapMutator toIndex :=
              match MapMutator r toIndex with
                | None => None
                | Some idx => Some (fst (mutatorMap idx))
              end;
            MapObserver toIndex :=
              match MapObserver r toIndex with
                | None => None
                | Some idx => match observerMap idx with
                                | inl idx' => Some idx'
                                | inr idx' => None
                              end
              end
         |}.
End refinePaired.

Goal ADTimpl NatSumProd_spec.
Proof.
  eapply finish.
  unfold NatSumProd_spec.
  eapply refinePaired.


Section pairedAlgorithmic.
  Variables A B : ADT.

  Variable mutatorIndex : Type.
  Variable observerIndex : Type.
  Variable mutatorMap : mutatorIndex -> MutatorIndex A * MutatorIndex B.
  Variable observerMap : observerIndex -> ObserverIndex A + ObserverIndex B.

  (** The composed ADT *)
  Definition pairedADT :=
    {|
      Model := Model A * Model B;
      MutatorIndex := mutatorIndex;
      ObserverIndex := observerIndex;
      MutatorMethodSpecs idx :=
        let s := mutatorMap idx in
        fun m x m' => MutatorMethodSpecs A (fst s) (fst m) x (fst m')
                      /\ MutatorMethodSpecs B (snd s) (snd m) x (snd m');
      ObserverMethodSpecs idx :=
        fun m x y => match observerMap idx with
                       | inl idx' => ObserverMethodSpecs A idx' (fst m) x y
                       | inr idx' => ObserverMethodSpecs B idx' (snd m) x y
                     end
    |}.

  (** Now we show how to implement it. *)
  Variable Ai : ADTimpl A.
  Variable Bi : ADTimpl B.
    ADTimpl a1
    -> ADTimpl a2
    -> ADTimpl a.


Typeclasses eauto := debug.
Goal ADTimpl NatSumProd_spec.
  unfold NatSumProd_spec.



unfold NatSumProd_spec.
let f := lazymatch goal with |- ADTimpl {| MutatorMethodSpecs := ?f |} => constr:(f) end in
let f' := constr:(fun idx ma mb x m'a m'b => f idx (ma, mb) x (m'a, m'b)) in
let f'' := (eval simpl in f') in
let f0f1 := lazymatch f'' with
              | (fun idx ma mb x m'a m'b => @?f0 idx ma x m'a /\ @?f1 idx mb x m'b)
                => constr:((f0, f1))
            end in
let AMutatorMethodSpecs := constr:(fst f0f1) in
let BMutatorMethodSpecs := constr:(snd f0f1) in
let fObs := match goal with |- ADTimpl {| ObserverMethodSpecs := ?f |} => constr:(f) end in
let f'Obs := constr:(fun idx ma mb x y => fObs idx (ma, mb) x y) in
let f''Obs := (eval simpl in f'Obs) in
let f0f1Obs := lazymatch f''Obs with
                 | (fun idx ma mb x y =>
                      match idx with
                        | inl idx' => @?f0 ma x y idx'
                        | inr idx' => @?f1 mb x y idx'
                      end)
                   => constr:((f0, f1))
               end in
let AObserverMethodSpecs := constr:(fst f0f1Obs) in
let BObserverMethodSpecs := constr:(snd f0f1Obs) in
lazymatch goal with
  | [ |- ADTimpl
           {|
             Model := ?AModel * ?BModel;
             MutatorIndex := ?mutatorIndex;
             ObserverIndex := ?observerIndex
           |} ]
    => pose proof (@pairedImpl
                     (@Build_ADT AModel _ _ AMutatorMethodSpecs (fun idx' ma x y => AObserverMethodSpecs ma x y idx'))
                     (@Build_ADT BModel _ _ BMutatorMethodSpecs (fun idx' mb x y => BObserverMethodSpecs mb x y idx'))
                     mutatorIndex
                     observerIndex
                     (fun x => (x, x))
                     (fun x => x));
      unfold pairedADT in *; simpl in *
end.
    eapply X;
    eauto with typeclass_instances.
Defined.

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
