Require Import Core.
Require Import FiatToFacade.Loop FiatToFacade.FacadeNotations.

Lemma pull_forall :
  forall {A B C D} (f: D -> A -> B -> C -> Prop) b,
    (forall (x1: A) (x2: B) (x3: C),
       refine { p | f p x1 x2 x3 }%facade
              b) ->
    refine { p | forall x1 x2 x3,
                       f p x1 x2 x3 }%facade
           b.
Proof.
  unfold refine; intros; econstructor; intros.
  generalize (H x1 x2 x3 _ H0); intros.
  inversion_by computes_to_inv.
  assumption.
Qed.

Lemma pull_forall_loop_sca :
  forall env b loop knowledge
         scas adts vseq vret thead tis_empty,
    (forall head acc seq,
       refine  { cloop | SCALoopBodyProgCondition env loop cloop knowledge
                                                  scas adts vseq vret thead tis_empty
                                                  head acc seq } b) ->
    refine { cloop | SCALoopBodyOk env loop cloop knowledge
                                   scas adts vseq vret thead tis_empty }%facade b.
Proof.
  eauto using pull_forall.
Qed.

Lemma pull_forall_loop_adt :
  forall  acc_type wrapper env b loop knowledge
         scas adts vseq vret thead tis_empty,
    (forall head acc seq,
       refine  { cloop | @ADTLoopBodyProgCondition env acc_type loop cloop knowledge
                                                   scas adts vseq vret thead tis_empty
                                                   acc wrapper head seq } b) ->
    refine { cloop | @ADTLoopBodyOk env acc_type loop cloop knowledge
                                    scas adts vseq vret thead tis_empty wrapper }%facade b.
Proof.
  eauto using pull_forall.
Qed.
