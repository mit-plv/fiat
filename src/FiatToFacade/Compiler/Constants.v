Require Import FiatToFacade.Compiler.Prerequisites.

Unset Implicit Arguments.

Lemma compile_constant :
  forall {av env} (vret: StringMap.key),
  forall (w: W) init_knowledge init_scas init_adts,
    ~ StringMap.In vret init_adts ->
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> w]::init_scas)
                  init_adts init_adts)
           (ret (Assign vret w)).
Proof.
  unfold Prog, ProgOk, refine; unfold_coercions; intros;
  inversion_by computes_to_inv;
  constructor; intros;
  subst;
  destruct_pairs;
  split.

  (* Safe *)
  econstructor.
  compute; reflexivity.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  intros; inversion_facade.
  split; rewrite_Eq_in_goal.

  match goal with
    | [ H: eval _ (Const _) = Some _ |- _ ] => injection H; intros; subst
  end; apply SomeSCAs_chomp; assumption.

  apply add_adts_pop_sca; assumption.
Qed.
