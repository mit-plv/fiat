Require Import FiatToFacade.Superset.
Require Import Computation.Core.
Require Import Facade.

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

Definition Prog {av env} initial_knowledge initial_scas final_scas initial_adts final_adts :=
  { prog | @ProgOk av env prog initial_knowledge initial_scas final_scas initial_adts final_adts }%comp.
