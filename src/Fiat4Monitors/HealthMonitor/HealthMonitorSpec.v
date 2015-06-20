Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Program.Program
        Coq.Sets.Ensembles
        Coq.Arith.Arith.
Require Import
        Fiat.Common.IterateBoundedIndex
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Messages
        Fiat.Fiat4Monitors.RADL_Flags
        Fiat.Fiat4Monitors.RADL_Nodes
        Fiat.Fiat4Monitors.LandsharkTopics
        Fiat.Fiat4Monitors.LandsharkNodes
        Bedrock.Word.

Section HealthMonitorSpec.

  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope ADTSig_scope.
  Open Scope ADT_scope.

  Definition HealthMonitorSig
  : ADTSig :=                         (* A RADL Node is modeled as an ADT with a  *)
    ADTsignature {                    (* single constructor and a step function. *)
        Constructor RADL_Init      : unit -> rep,
        Method      RADL_Step      : rep x ((cRep (radl_in_t health_monitor)) * (cRep (radl_in_flags_t health_monitor)))
                                     -> rep x (Memory.W * Memory.W * (cRep (radl_out_t health_monitor))
                                               * (cRep (radl_out_flags_t health_monitor)))
      }.

  Inductive BitAtIndex (P : nat -> bool -> Prop)
    : forall n, Word.word n -> nat -> Prop :=
  | WordIndex_hd : forall n b w,
      P n b -> BitAtIndex P (@WS b n w) 0
  | WordIndex_tl : forall n n' b w,
      BitAtIndex P w n'
      -> BitAtIndex P (@WS b n w) (S n').

  Fixpoint Iterate_Build_Word
             (n : nat)
             (P : nat -> bool -> Prop)
    : Comp (Word.word n)
    :=  match n with
        | S n =>
          b <- {b | P (S n) b};
            w <- Iterate_Build_Word P;
            ret (WS b w)
        | 0 => ret WO
        end.

  Definition foo :
    forall idx, 
    snd
    (MethodDomCod (FlagADTSig (RADL_Subscriptions health_monitor))
                  (BuildGetFlagMethodID (RADL_Subscriptions health_monitor) idx)) -> Memory.W.
      intro; eapply Iterate_Dep_Type_BoundedIndex_equiv_1 with (idx := idx).
      admit.
      cbv delta [health_monitor] beta iota.
      cbv delta [RADL_Subscriptions] beta iota.
      cbv delta [LiftTopics] beta iota zeta.
      Set Printing All.
      match goal with
        |- context [@Build_IndexBound ?A ?B ?C ?D ?E] =>
        let bob := fresh in 
        set (bob := C) in *
      end.
      match goal with
        |- context [@Build_IndexBound ?A ?B ?C ?D ?E] =>
        let bob := fresh in 
        set (bob := C) in *
      end.
      

      cbv delta [map] beta iota zeta.
      cbv beta.
      simpl.
      Print Iterate_Dep_Type_equiv.
      Print Dep_Type_BoundedIndex_nth_eq.
      with
      (P := fun idx => snd
                         (MethodDomCod (FlagADTSig (RADL_Subscriptions health_monitor))
                                       (BuildGetFlagMethodID (RADL_Subscriptions health_monitor) idx)) -> Memory.W).
      Focus 3.
      apply Iterate_Dep_Type.

      
  Variable bar :
    forall idx, 
    snd
    (MethodDomCod (MessageADTSig (RADL_Subscriptions health_monitor))
                  (BuildGetMessageMethodID (RADL_Subscriptions health_monitor) idx)) -> Memory.W.

  Definition HealthMonitorSpec : ADT HealthMonitorSig :=
    ADTRep unit (* Since RADL Nodes are untrusted, we'll treat their state as completely unknown *)
           { Def Constructor RADL_Init (_ : _) : rep := ret tt,
             Def Method RADL_Step (r : rep, in' : (cRep (radl_in_t health_monitor) * (cRep (radl_in_flags_t health_monitor)))) : _ :=
               let (in_, in_flags) := in' in
               health_reports <- {report |
                                  forall n,
                                    BitAtIndex
                                      (fun n b =>
                                         forall a nth_n t,
                                           radl_is_timeout (foo _ (snd (CallFlagGetMethod in_flags {| bindex := a;
                                                                              indexb := {| ibound := n;
                                                                                           boundi := nth_n |} |} t))) = b)
                                      report n};
             flag_reports <- {report | 
                              forall n,
                                BitAtIndex
                                  (fun n b =>
                                     forall a nth_n t,
                                       radl_is_timeout (bar _
                                                            (snd (CallMessageGetMethod in_ {| bindex := a;
                                                                                                     indexb := {| ibound := n;
                                                                                                                  boundi := nth_n |} |} t))) = b)
                                  report n};
             ret (tt, (health_reports, flag_reports, inil _, inil _))
           }.
  


  
End HealthMonitorSpec.
