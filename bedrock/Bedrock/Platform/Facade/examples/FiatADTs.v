Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory.
Require Import Coq.Sets.Ensembles.

Require Bedrock.Bedrock.

Inductive ADTValue :=
  | List : list W -> ADTValue
  | Junk : False -> ADTValue
  | FEnsemble : Ensemble W -> ADTValue.

Require Import Bedrock.Platform.Cito.ADT.

Module Adt <: ADT.

  Definition ADTValue := ADTValue.

End Adt.

Require Import Coq.Lists.List Coq.Program.Program.

Definition SCAZero {t} := SCA t (Word.natToWord 32 0).
Definition SCAOne  {t} := SCA t (Word.natToWord 32 1).

Ltac crush_types :=
  unfold type_conforming, same_types, same_type; intros;
  repeat match goal with
           | [ H: exists t, _ |- _ ] => destruct H
         end; subst;
  intuition.

Section ListADTSpec.

  Definition List_new : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (List [])
      |}; crush_types.
  Defined.

  Definition List_delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists l, args = [ADT (List l)];
        PostCond := fun args ret => exists l, args = [(ADT (List l), None)] /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (List (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (List (h :: t)), Some (List t)) ] /\
                        ret = SCA ADTValue h
      |}; crush_types.
  Defined.

  Definition List_empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (List l), Some (List l))] /\
                        exists w, ret = SCA _ w /\ Bedrock.Programming.propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition List_push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l w,
                       args = [ADT (List l); SCA _ w];
        PostCond := fun args ret =>
                      exists l w,
                        args = [ (ADT (List l), Some (List (w :: l))); (SCA _ w, None) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (List l), Some (List l)) ] /\
                        ret = ADT (List l)
      |}; crush_types.
  Defined.

  Definition List_rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (List l), Some (List (rev l))) ] /\
                        ret = SCAZero
      |}; crush_types.
  Defined.

  Definition List_length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (List l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (List l), Some (List l)) ] /\
                        ret = SCA _ (Word.natToWord _ (length l))
      |}; crush_types.
  Defined.

End ListADTSpec.

Section FiniteSetADTSpec.

  (* Def Constructor sEmpty (_ : unit) : rep := ret (Empty_set _), *)
  Definition FEnsemble_sEmpty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     args = [];
        PostCond := fun args ret =>
                      args = []
                      /\ ret = ADT (FEnsemble (Empty_set _))
      |}; crush_types.
  Defined.

  Definition FEnsemble_sDelete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists s, args = [ADT (FEnsemble s)];
        PostCond := fun args ret =>
                      exists s, args = [(ADT (FEnsemble s), None)]
                      /\ ret = SCAZero
      |}; crush_types.
  Defined.

  (* Def Method sAdd (s : rep , w : W) : unit :=
      ret (Add _ s w, tt) *)
  Definition FEnsemble_sAdd : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists s w, args = [ADT (FEnsemble s); SCA _ w];
        PostCond := fun args ret =>
                      exists s w, args = [(ADT (FEnsemble s), Some (FEnsemble (Ensembles.Add _ s w)));
                                           (SCA _ w, None)]
                                  /\ ret = SCAZero
      |}; crush_types.
  Defined.

  (* Def Method sRemove (s : rep , w : W) : unit :=
      ret (Subtract _ s w, tt) *)
  Definition FEnsemble_sRemove : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists s w, args = [ADT (FEnsemble s); SCA _ w];
        PostCond := fun args ret =>
                      exists s w, args = [(ADT (FEnsemble s), Some (FEnsemble (Subtract _ s w)));
                                           (SCA _ w, None)]
                                  /\ ret = SCAZero
      |}; crush_types.
  Defined.

  (* Def Method sIn (s : rep , w : W) : bool :=
        (b <- { b : bool | b = true <-> Ensembles.In _ s w };
         ret (s, b)) *)
  Definition FEnsemble_sIn : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists s w, args = [ADT (FEnsemble s); SCA _ w];
        PostCond := fun args ret =>
                      exists s w, args = [(ADT (FEnsemble s), Some (FEnsemble s));
                                         (SCA _ w, None)]
                                  /\ exists w', ret = SCA _ w'
                                                /\ Bedrock.Programming.propToWord (Ensembles.In _ s w) w'
      |}; crush_types.
  Defined.

  (* These definitions should be imported *)
  Definition EnsembleListEquivalence
             {A}
             (ensemble : Ensemble A)
             (seq : list A) :=
    NoDup seq /\
    forall x, Ensembles.In _ ensemble x <-> List.In x seq.

  Definition cardinal U (A : Ensemble U) (n : nat) : Prop :=
    exists ls, EnsembleListEquivalence A ls /\ Datatypes.length ls = n.

  (* Def Method sSize (s : rep , _ : unit) : nat :=
          (n <- { n : nat | cardinal _ s n };
           ret (s, n)) *)
  Definition FEnsemble_sSize : AxiomaticSpec ADTValue.
        refine {|
        PreCond := fun args =>
                     exists s, args = [ADT (FEnsemble s)];
        PostCond := fun args ret =>
                      exists s n, args = [(ADT (FEnsemble s), Some (FEnsemble s))]
                                  /\ @cardinal _ s n
                                  /\ ret = SCA _ (Word.natToWord 32 n)
          |}; crush_types.
  Defined.

End FiniteSetADTSpec.
