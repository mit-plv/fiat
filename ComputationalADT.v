Require Import String Omega List.
Require Import Common Computation.
Require Import FunctionalExtensionality.

Generalizable All Variables.
Set Implicit Arguments.

Ltac get_mut_spec_of_generic_impl ADTimpl MutatorMethodSpecs Ai :=
  let A := match type of Ai with ADTimpl ?A => constr:(A) end in
  let AMutSpec' := constr:(MutatorMethodSpecs A) in
  let AMutSpec := (eval simpl in AMutSpec') in
  match goal with
    | [ H : AMutSpec _ _ _ _ |- _ ] => constr:(H)
  end.
Ltac generic_impl_has_mut_spec ADTimpl MutatorMethodSpecs Ai := idtac; get_mut_spec_of_generic_impl ADTimpl MutatorMethodSpecs Ai.

Ltac generic_impl_t'' ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect :=
  match goal with
    | _ => eassumption
    | _ => intro
    | _ => progress simpl in *
    | _ => progress split_and
    | _ => progress inversion_computes_to
    | _ => progress subst
    | _ => split
    | _ => progress destruct_sum_in_match
    | [ Ai : ADTimpl ?A |- _ ] => eapply (@ObserverMethodsCorrect A Ai)
    | [ Ai : ADTimpl ?A |- _ ]
      => (not_tac (generic_impl_has_mut_spec ADTimpl MutatorMethodSpecs Ai));
        edestruct (@MutatorMethodsCorrect A Ai); try eassumption; [];
        instantiate
    | _ => progress apply_hyp
  end.

Ltac generic_impl_t' ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect :=
  repeat generic_impl_t'' ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect.

Ltac generic_impl_t ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect :=
  repeat first [ progress generic_impl_t' ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect
               | eexists (_, _)
               | esplit
               | progress eapply_hyp' ].

Ltac solve_partial_impl_to_impl' :=
  match goal with
    | [ |- _ <> None ] => simpl; exact (@Some_ne_None _ _)
    | [ |- None <> _ ] => simpl; exact (@None_ne_Some _ _)
    | [ |- forall x : unit, @?P x ] => refine (@unit_rect P _)
    | [ |- forall x : sum ?A ?B, @?P x ] => refine (@sum_rect A B P _ _)
    | _ => progress hnf
    | [ |- forall x : ?T, @?P x ]
      => let T' := (eval hnf in T) in
         progress change (forall x : T', P x)
  end.

Ltac solve_partial_impl_to_impl := repeat solve_partial_impl_to_impl'.

(** * Basic ADT definitions *)
Section comp_env.
  (** We have one ambiant [funcs] and [denote_funcs] around for everything. *)
  Variable funcs : string -> Type * Type.
  Variable denote_funcs : forall name, fst (funcs name) -> Comp funcs (snd (funcs name)).

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

  (** Implementation type of a method *)
  Definition methodTypeD (State : Type) :=
    State -> nat -> Comp funcs (State * nat).

  (** Usual Hoare logic notion of implementating a mutator method spec *)

  Definition mutatorMethodCorrect (Model State : Type)
             (ms : mutatorMethodSpec Model)
             (RepInv : Model -> State -> Prop)
             (mb : methodTypeD State)
    := forall m s,
         RepInv m s
         -> forall x,
              let s'y := mb s x in
              forall s'y_value,
                computes_to denote_funcs s'y s'y_value
                -> exists m', RepInv m' (fst s'y_value)
                              /\ ms m x m'
                              /\ (snd s'y_value) = 0.

  Definition observerMethodCorrect (Model State : Type)
             (ms : observerMethodSpec Model)
             (RepInv : Model -> State -> Prop)
             (mb : methodTypeD State)
    := forall m s,
         RepInv m s
         -> forall x,
              let s'y := mb s x in
              forall s'y_value,
                computes_to denote_funcs s'y s'y_value
                -> RepInv m (fst s'y_value)
                   /\ ms m x (snd s'y_value).

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

  Ltac impl_t'' := generic_impl_t'' ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect.
  Ltac impl_t' := generic_impl_t' ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect.
  Ltac impl_t := generic_impl_t ADTimpl MutatorMethodSpecs ObserverMethodsCorrect MutatorMethodsCorrect.

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
            => (x'1 <- MutatorMethodBodies Ai (fst (mutatorMap name)) (fst s) x;
                x'2 <- MutatorMethodBodies Bi (snd (mutatorMap name)) (snd s) x;
                ret ((fst x'1, fst x'2), 0))%comp;
          ObserverMethodBodies name :=
            fun s x
            => match observerMap name with
                 | inl name'
                   => let sy := ObserverMethodBodies Ai name' (fst s) x in
                      (sy' <- sy;
                       ret ((fst sy', snd s), snd sy'))%comp
                 | inr name'
                   => let sy := ObserverMethodBodies Bi name' (snd s) x in
                      (sy' <- sy;
                       ret ((fst s, fst sy'), snd sy'))%comp
               end
        |};
      abstract impl_t.
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

    (*Local Hint Extern 1 (@ex (_ * _) _) => eexists (_, _).*)

    Hypothesis mutators_match
    : forall idx,
      forall m x m' m'',
        AMutSpec (fst (mutatorMap idx)) m x m'
        -> BMutSpec (snd (mutatorMap idx)) m x m''
        -> m' = m''.

    Local Hint Extern 1 => apply symmetry.

    Definition prodImpl : ADTimpl prodADT.
      refine {|
          State := State Ai * State Bi;
          RepInv := fun (m : Model prodADT) s
                    => RepInv Ai m (fst s)
                       /\ RepInv Bi m (snd s);
          MutatorMethodBodies idx :=
            fun s x =>
              (s1 <- MutatorMethodBodies Ai (fst (mutatorMap idx)) (fst s) x;
               s2 <- MutatorMethodBodies Bi (snd (mutatorMap idx)) (snd s) x;
               ret ((fst s1, fst s2), 0))%comp;
          ObserverMethodBodies idx :=
            match observerMap idx with
              | inl idx' =>
                fun s x =>
                  (s'y <- ObserverMethodBodies Ai idx' (fst s) x;
                   ret ((fst s'y, snd s), snd s'y))%comp
              | inr idx' =>
                fun s x =>
                  (s'y <- ObserverMethodBodies Bi idx' (snd s) x;
                   ret ((fst s, fst s'y), snd s'y))%comp
            end
        |};
      abstract (
          intro idx;
          try (assert (MM := mutators_match idx));
          impl_t';
          match goal with
            | [ AM : AMutSpec _ _ _ _, BM : BMutSpec _ _ _ _ |- _ ]
              => specialize (MM _ _ _ _ AM BM); subst
          end;
          impl_t
        ).
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
      abstract (
          impl_t';
          edestruct mutatorSpecMap; try eassumption;
          impl_t
        ).
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
          MutatorMethodBodies u val x := (ret (match val with
                                                 | None => Some x
                                                 | Some x' => Some (op x x')
                                               end,
                                               0))%comp;
          ObserverMethodBodies u val x := (ret (val,
                                                match val with
                                                  | None => default_value
                                                  | Some x => x
                                                end))%comp
        |};
        intros [];
        solve [ (intros m [n|] [l [H0 H1] ] x ? ?);
                inversion_computes_to; subst; simpl in *;
                (exists (add m x));
                repeat split;
                try (exists (x::l));
                abstract t' op op_assoc op_comm
              | intros m [n|] [l [H0 H1] ] x ? ?;
                       inversion_computes_to; subst; simpl in *;
                repeat (split || exists m || exists l);
                abstract t' op op_assoc op_comm
              | intros m [n|] [l [H0 H1] ] x ? ?;
                       inversion_computes_to; subst; simpl in *;
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

  Section nat_op_ex.
    Variable default_val : nat.

    Definition NatLowerI : ADTimpl (NatLower default_val)
      := NatBinOpI _ _ _ _.

    Definition NatUpperI : ADTimpl (NatUpper default_val)
      := NatBinOpI _ _ _ _.

    Definition NatSumI : ADTimpl (NatSum default_val)
      := NatBinOpI _ _ _ _.

    Definition NatProdI : ADTimpl (NatProd default_val)
      := NatBinOpI _ _ _ _.
  End nat_op_ex.

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

  Class IsFull_PartialADTimpl A (impl : PartialADTimpl A)
    := full_partial_ADT_impl_has_no_nones
       : forall idx, PObserverMethodBodies impl idx <> None.

  Hint Extern 1 (IsFull_PartialADTimpl _) => progress solve_partial_impl_to_impl : typeclass_instances.

  Definition ADTimpl_of_PartialADTimpl A impl `{H : @IsFull_PartialADTimpl A impl}
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

  Global Arguments ADTimpl_of_PartialADTimpl [A] impl {H}.

  Coercion PartialADTimpl_of_ADTimpl A (impl : @ADTimpl A)
  : PartialADTimpl A
    := {|
        PState := State impl;
        PRepInv := RepInv impl;
        PMutatorMethodBodies := MutatorMethodBodies impl;
        PObserverMethodBodies idx := Some (ObserverMethodBodies impl idx);
        PMutatorMethodsCorrect := MutatorMethodsCorrect impl;
        PObserverMethodsCorrect := ObserverMethodsCorrect impl
      |}.


  Ltac p_impl_t'' := generic_impl_t'' PartialADTimpl MutatorMethodSpecs PObserverMethodsCorrect PMutatorMethodsCorrect.
  Ltac p_impl_t' := generic_impl_t' PartialADTimpl MutatorMethodSpecs PObserverMethodsCorrect PMutatorMethodsCorrect.
  Ltac p_impl_t := generic_impl_t PartialADTimpl MutatorMethodSpecs PObserverMethodsCorrect PMutatorMethodsCorrect.


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
            => (A_val <- PMutatorMethodBodies Ai (fst (mutatorMap name)) (fst s) x;
                B_val <- PMutatorMethodBodies Bi (snd (mutatorMap name)) (snd s) x;
                ret ((fst A_val, fst B_val), 0))%comp;
          PObserverMethodBodies name :=
            match observerMap name with
              | inl name'
                => match PObserverMethodBodies Ai name' with
                     | Some body => Some (fun s x
                                          => (sy <- body (fst s) x;
                                              ret ((fst sy, snd s), snd sy))%comp)
                     | None => None
                   end
              | inr name'
                => match PObserverMethodBodies Bi name' with
                     | Some body => Some (fun s x
                                          => (sy <- body (snd s) x;
                                              ret ((fst s, fst sy), snd sy))%comp)
                     | None => None
                   end
            end
        |};
      abstract (
          repeat intro;
          unfold observerMethodCorrect; simpl;
          destruct_sum_in_match;
          simpl in *;
            repeat match goal with
                     | [ |- appcontext[PObserverMethodBodies ?Ai ?x] ]
                       => generalize (PObserverMethodsCorrect Ai x);
                     destruct (PObserverMethodBodies Ai x)
                   end;
          p_impl_t
        ).
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

    Local Hint Extern 1 => apply symmetry.

    Definition prodPartialImpl : PartialADTimpl prodADT.
    Proof.
      refine {|
          PState := PState Ai * PState Bi;
          PRepInv := fun (m : Model prodADT) s
                     => PRepInv Ai m (fst s)
                        /\ PRepInv Bi m (snd s);
          PMutatorMethodBodies idx :=
            fun s x =>
              (s1 <- PMutatorMethodBodies Ai (fst (mutatorMap idx)) (fst s) x;
               s2 <- PMutatorMethodBodies Bi (snd (mutatorMap idx)) (snd s) x;
               ret ((fst s1, fst s2), 0))%comp;
          PObserverMethodBodies idx :=
            match observerMap idx with
              | inl idx' =>
                match PObserverMethodBodies Ai idx' with
                  | Some body => Some (fun s x =>
                                         (s'y <- body (fst s) x;
                                          ret ((fst s'y, snd s), snd s'y))%comp)
                  | None => None
                end
              | inr idx' =>
                match PObserverMethodBodies Bi idx' with
                  | Some body => Some (fun s x =>
                                         (s'y <- body (snd s) x;
                                          ret ((fst s, fst s'y), snd s'y))%comp)
                  | None => None
                end
            end
        |};
      abstract (
          intro idx;
          try (assert (MM := mutators_match idx));
          repeat intro;
          unfold observerMethodCorrect; simpl;
          destruct_sum_in_match;
          simpl in *;
            repeat match goal with
                     | [ |- appcontext[PObserverMethodBodies ?Ai ?x] ]
                       => generalize (PObserverMethodsCorrect Ai x);
                     destruct (PObserverMethodBodies Ai x)
                   end;
          p_impl_t';
          try match goal with
                | [ AM : AMutSpec _ _ _ _, BM : BMutSpec _ _ _ _ |- _ ]
                  => specialize (MM _ _ _ _ AM BM); subst
              end;
          p_impl_t
        ).
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
      abstract (
          repeat intro;
          unfold observerMethodCorrect in *; simpl;
          destruct_sum_in_match;
          simpl in *;
            repeat match goal with
                     | [ |- appcontext[PObserverMethodBodies ?Ai ?x] ]
                       => generalize (PObserverMethodsCorrect Ai x);
                     destruct (PObserverMethodBodies Ai x)
                   end;
          unfold observerMethodCorrect in *; simpl;
          p_impl_t';
          try solve [ p_impl_t ];
          edestruct mutatorSpecMap; try eassumption;
          p_impl_t
        ).
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
              PMutatorMethodBodies := fun _ _ _ => (ret (tt, 0))%comp;
              PObserverMethodBodies := fun _ => None
           |}; auto.
    repeat intro; simpl in *.
    inversion_computes_to; subst; simpl.
    edestruct Himplementable.
    repeat esplit; eassumption.
  Defined.

  Local Ltac nat_sum_prod_pi_t :=
    repeat match goal with
             | _ => intro
             | _ => eassumption
             | _ => esplit
             | _ => apply functional_extensionality_dep; intro
             | _ => rewrite_hyp; exact eq_refl
             | _ => progress destruct_sum_in_match
             | _ => progress destruct_head_hnf Empty_set
           end.

  Definition NatSumProdPI : PartialADTimpl NatSumProd_spec.
  Proof.
    eapply (add_component NatSumProd_spec
                          (NatSumI 0)
                          (later := unit)
                          (fun x => x)
                          (fun x => inr x)
                          (fun x => x) (fun x => x));
    try solve [ nat_sum_prod_pi_t ]; [].
    let A := match goal with |- PartialADTimpl ?A => constr:(A) end in
    eapply (add_component A
                          (NatProdI 1) (later := Empty_set)
                          (fun x => inl x)
                          (fun x => match x with end)
                          (fun x => x)
                          (fun x => x));
    try solve [ nat_sum_prod_pi_t ]; []; simpl.
    apply no_observers; simpl;
    solve [ nat_sum_prod_pi_t ].
  Defined.

  Definition NatSumProdI : ADTimpl NatSumProd_spec
    := ADTimpl_of_PartialADTimpl NatSumProdPI.

(*
  Existing Class ADTimpl.
  Hint Extern 1 (ADTimpl _) => eapply NatLowerI : typeclass_instances.
  Hint Extern 1 (ADTimpl _) => eapply NatUpperI : typeclass_instances.
  Hint Extern 1 (ADTimpl _) => eapply NatSumI : typeclass_instances.
  Hint Extern 1 (ADTimpl _) => eapply NatProdI : typeclass_instances.
  Hint Extern 2 (ADTimpl _) => eapply pairedImpl : typeclass_instances.

  Record refine (from_ to : ADT) :=
    {
      MakeImpl : ADTimpl from_ -> ADTimpl to;
      MapMutator : MutatorIndex to -> option (MutatorIndex from_);
      MapObserver : ObserverIndex to -> option (ObserverIndex from_)
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

  Definition easy from_ : refine from_ from_ :=
    {|
      MakeImpl := fun x => x;
      MapMutator := fun x => Some x;
      MapObserver := fun x => Some x
    |}.

  Section refinePaired.
    Variables from_ new : ADT.

    Variable mutatorIndex : Type.
    Variable observerIndex : Type.
    Variable mutatorMap : mutatorIndex -> MutatorIndex from_ * MutatorIndex new.
    Variable observerMap : observerIndex -> ObserverIndex from_ + ObserverIndex new.

    Definition refinePaired to (newI : ADTimpl new)
    : refine (pairedADT from_ new mutatorMap observerMap) to
      -> refine from_ to
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

(*
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
      *)
*)
End comp_env.
