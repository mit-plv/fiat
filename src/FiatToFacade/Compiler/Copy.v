Require Import FiatToFacade.Compiler.Prerequisites.

Unset Implicit Arguments.

Lemma copy_word :
  forall {av env},
  forall k1 {k2} w adts scas knowledge,
    scas[k1 >> SCA _ w] ->
    ~ StringMap.In k2 adts ->
    refine (@Prog av env knowledge
                  scas ([k2 >sca> w]::scas)
                  adts adts)
           (ret (Assign k2 k1)).
Proof.
  unfold refine, Prog, ProgOk; intros; constructor; intros.
  inversion_by computes_to_inv; subst.

  split.

  (* Safe *)
  eauto using assign_safe.

  (* RunsTo *) (* TODO: extract to lemma *)
  intros; inversion_facade; split;
  rewrite_Eq_in_goal; pose proof (H2 _ _ H). (* TODO: Put in scas_adts_mapsto *)
  erewrite mapsto_eval in H7 by eauto; autoinj.
  eauto using SomeSCAs_chomp.
  eauto using add_adts_pop_sca.
Qed.
