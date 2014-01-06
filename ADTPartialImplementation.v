Require Import String.
Require Export ADT ADTImplementation.

Generalizable All Variables.
Set Implicit Arguments.

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
Record PartialADTimpl funcs denote_funcs (A : ADT) :=
  {
    PState : Type;
    (** Real state type in Gallina *)

    PRepInv : Model A -> PState -> Prop;
    (** Relationship between abstract (specification) and concrete (implementation) states *)

    PMutatorMethodBodies : MutatorIndex A -> methodTypeD funcs PState;
    (** An implementation of each mutator method *)

    PObserverMethodBodies : ObserverIndex A -> option (methodTypeD funcs PState);
    (** An implementation of each observer method *)

    PMutatorMethodsCorrect : forall idx, mutatorMethodCorrect
                                           denote_funcs
                                           (MutatorMethodSpecs A idx)
                                           PRepInv
                                           (PMutatorMethodBodies idx);
    (** All mutator methods satisfy their specs. *)

    PObserverMethodsCorrect : forall idx, match PObserverMethodBodies idx with
                                            | Some body => observerMethodCorrect
                                                             denote_funcs
                                                             (ObserverMethodSpecs A idx)
                                                             PRepInv
                                                             body
                                            | None => True
                                          end
  (** All observer methods satisfy their specs. *)
  }.

Coercion PartialADTimpl_of_ADTimpl funcs denote_funcs A
         (impl : @ADTimpl funcs denote_funcs A)
: PartialADTimpl denote_funcs A
  := {|
      PState := State impl;
      PRepInv := RepInv impl;
      PMutatorMethodBodies := MutatorMethodBodies impl;
      PObserverMethodBodies idx := Some (ObserverMethodBodies impl idx);
      PMutatorMethodsCorrect := MutatorMethodsCorrect impl;
      PObserverMethodsCorrect := ObserverMethodsCorrect impl
    |}.

Class IsFull_PartialADTimpl funcs denote_funcs A
      (impl : @PartialADTimpl funcs denote_funcs A)
  := full_partial_ADT_impl_has_no_nones
     : forall idx, PObserverMethodBodies impl idx <> None.

Hint Extern 1 (IsFull_PartialADTimpl _) => progress solve_partial_impl_to_impl : typeclass_instances.


Section comp_env.
  (** We have one ambiant [funcs] and [denote_funcs] around for everything. *)
  Variable funcs : string -> Type * Type.
  Variable denote_funcs : forall name, fst (funcs name) -> Comp funcs (snd (funcs name)).

  (** We set up some notations so we don't need to think about [funcs] and [denote_funcs]. *)
  Local Notation methodTypeD := (methodTypeD funcs).
  Local Notation mutatorMethodCorrect := (@mutatorMethodCorrect funcs denote_funcs).
  Local Notation observerMethodCorrect := (@observerMethodCorrect funcs denote_funcs).
  Local Notation ADTimpl := (@ADTimpl funcs denote_funcs).
  Local Notation "'PartialADTimpl'" := (@PartialADTimpl funcs denote_funcs).

  Definition ADTimpl_of_PartialADTimpl
             A impl
             `{H : @IsFull_PartialADTimpl funcs denote_funcs A impl}
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

  Ltac p_impl_t'' := generic_impl_t'' PartialADTimpl MutatorMethodSpecs (@PObserverMethodsCorrect funcs denote_funcs) (@PMutatorMethodsCorrect funcs denote_funcs) idtac.
  Ltac p_impl_t' := generic_impl_t' PartialADTimpl MutatorMethodSpecs (@PObserverMethodsCorrect funcs denote_funcs) (@PMutatorMethodsCorrect funcs denote_funcs) idtac.
  Ltac p_impl_t := generic_impl_t PartialADTimpl MutatorMethodSpecs (@PObserverMethodsCorrect funcs denote_funcs) (@PMutatorMethodsCorrect funcs denote_funcs) idtac.

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
          unfold ADT.observerMethodCorrect; simpl;
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
          unfold ADT.observerMethodCorrect; simpl;
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
          unfold ADT.observerMethodCorrect in *; simpl;
          destruct_sum_in_match;
          simpl in *;
            repeat match goal with
                     | [ |- appcontext[PObserverMethodBodies ?Ai ?x] ]
                       => generalize (PObserverMethodsCorrect Ai x);
                     destruct (PObserverMethodBodies Ai x)
                   end;
          unfold ADT.observerMethodCorrect in *; simpl;
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
    inversion_by computes_to_inv; subst; simpl.
    edestruct Himplementable.
    repeat esplit; eassumption.
  Defined.
End comp_env.
