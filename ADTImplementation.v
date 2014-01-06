Require Import String.
Require Export ADT.

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
    | _ => progress inversion_by computes_to_inv
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

(** * Basic ADT definitions *)
Section comp_env.
  (** We have one ambiant [funcs] and [denote_funcs] around for everything. *)
  Variable funcs : string -> Type * Type.
  Variable denote_funcs : forall name, fst (funcs name) -> Comp funcs (snd (funcs name)).

  (** We set up some notations so we don't need to think about [funcs] and [denote_funcs]. *)
  Local Notation methodTypeD := (methodTypeD funcs).
  Local Notation mutatorMethodCorrect := (@mutatorMethodCorrect funcs denote_funcs).
  Local Notation observerMethodCorrect := (@observerMethodCorrect funcs denote_funcs).

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

  Definition ADTimpl_is_computational A (Ai : ADTimpl A) : Prop
    := (forall i s x,
          (exists m, RepInv Ai m s)
          -> is_computational denote_funcs (MutatorMethodBodies Ai i s x))
       /\ (forall i s x,
             (exists m, RepInv Ai m s)
             -> is_computational denote_funcs (ObserverMethodBodies Ai i s x)).

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


  (** Every spec is trivially implementable using [Pick]. *)
  Section pick.
    Variables A : ADT.
    Variable state : Type.
    Variable rep_inv : Model A -> state -> Prop.

    Definition pickImpl : ADTimpl A.
    Proof.
      refine {|
          State := state;
          RepInv := rep_inv;
          MutatorMethodBodies idx :=
            fun s x
            => (s' <- { s' : state
                      | forall m,
                          rep_inv m s
                          -> exists m',
                               rep_inv m' s'
                               /\ MutatorMethodSpecs A idx m x m' };
                ret (s', 0))%comp;
          ObserverMethodBodies idx :=
            fun s x
            => (x' <- { x' : nat | forall m,
                                     rep_inv m s ->
                                     ObserverMethodSpecs A idx m x x' };
                ret (s, x'))%comp
        |};
      abstract (
          repeat intro; simpl;
          inversion_by computes_to_inv; subst; simpl;
          eauto;
          match goal with
            | [ H : forall m : Model A, rep_inv _ _ -> exists m' : Model A, _ |- _ ]
              => edestruct H; try eassumption; [];
            split_and;
            repeat esplit; eassumption
          end
        ).
    Defined.
  End pick.
End comp_env.
