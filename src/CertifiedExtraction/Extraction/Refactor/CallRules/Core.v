Require Export Program.
Require Export Fiat.Computation.Notations. (* FIXME remove *)
Require Export Refactor.Basics.
Require Export Refactor.TupleToListW.
Require Export Refactor.EnsemblesOfTuplesAndListW.

Require Export
        Fiat.CertifiedExtraction.Extraction.External.Core
        Fiat.CertifiedExtraction.Benchmarks.QueryStructureWrappers.

Require Export Bedrock.Platform.Facade.examples.QsADTs.

Ltac QS_t := match goal with
             | |- not_mapsto_adt _ _ = true => eapply not_In_Telescope_not_in_Ext_not_mapsto_adt; eassumption
             | _ => SameValues_Facade_t_step
             | _ => facade_cleanup_call
             | _ => LiftPropertyToTelescope_t
             | _ => PreconditionSet_t
             end.

Ltac not_mapsto_adt_external_t :=
  PreconditionSet_t;
  repeat match goal with
         | [ H: ?k <> ?s |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] =>
           apply not_mapsto_adt_neq_remove'; [ congruence | ]
         | [ H: ?s <> ?k |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] =>
           apply not_mapsto_adt_neq_remove'; [ congruence | ]
         | [  |- not_mapsto_adt ?k (StringMap.add ?k _ _) = true ] =>
           apply not_mapsto_adt_eq_SCA
         end.

Ltac side_conditions_fast :=
  repeat match goal with
         | _ => apply CompileDeallocSCA_discretely; [ .. | apply ProgOk_Chomp_Some; intros ]
         | |- NotInTelescope _ _ => simpl; repeat (split; intro; [ congruence | intros ]); eassumption
         | [  |- _ ∉ _ ] => decide_not_in
         end.

Ltac fiat_t :=
  repeat (eapply BindComputes || apply PickComputes || apply ReturnComputes || simpl).

Hint Resolve Empty_lift : call_helpers_db.
Hint Resolve TupleToListW_length : call_helpers_db.