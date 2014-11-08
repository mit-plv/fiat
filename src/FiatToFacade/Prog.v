Require Import FiatToFacade.Superset.
Require Import Computation.Core.
Require Import Facade.DFacade.

(*Require Import ADTSynthesis.ADTRefinement.GeneralRefinements.
Require Import StringMap.
Require Import ADT.

Require Import ADTRefinement.

Definition SomecADTs
           {ADTSpec}
           (Impl : FullySharpened ADTSpec)
           {av} wrapper
           (state : State av)
           (cADTs : StringMap.t (ComputationalADT.cRep (projT1 Impl))) :=
  forall k,
    StringMap.MapsTo k (wrapper v) cADTs ->
    exists s : ADT.Core.Rep ADTSpec,
      ADTRefinement.AbsR (projT2 Impl) s /\
      StringMap.MapsTo k (wrapper s).

Check @AllADTs. *)

Definition ProgOk {av env} prog initial_knowledge initial_scas final_scas initial_adts final_adts :=
  forall initial_state,
    initial_knowledge /\
    SomeSCAs initial_state initial_scas /\
    AllADTs initial_state initial_adts  ->
    Safe env prog initial_state /\
    forall final_state,
      @RunsTo av env prog initial_state final_state ->
      SomeSCAs final_state final_scas /\
      AllADTs final_state final_adts.

Check ProgOk.

Definition Prog {av env} initial_knowledge initial_scas final_scas initial_adts final_adts :=
  { prog | @ProgOk av env prog initial_knowledge initial_scas final_scas initial_adts final_adts }%comp.
