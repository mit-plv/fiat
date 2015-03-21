Require Import ADTSynthesis.Computation ADTSynthesis.Common.
Require Import ADTSynthesis.FiatToFacade.Loop ADTSynthesis.FiatToFacade.FacadeNotations.

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


Lemma pull_forall_loop_pair :
  forall  acc_type wsca wadt env b loop knowledge
         scas adts vseq vsca vadt thead tis_empty,
    (forall head acc seq,
       refine  { cloop | @PairLoopBodyProgCondition env acc_type loop cloop knowledge
                                                    scas adts vseq vsca vadt thead tis_empty
                                                    acc wsca wadt head seq } b) ->
    refine { cloop | @PairLoopBodyOk env acc_type loop cloop knowledge
                                     scas adts vseq vsca vadt thead tis_empty wsca wadt }%facade b.
Proof.
  eauto using pull_forall.
Qed.


Lemma pull_forall_loop_adt_pair :
  forall  acc_type wsca wadt env b loop knowledge
         scas adts vseq vsca vadt thead tis_empty,
    (forall head acc seq,
       refine  { cloop | @ADTPairLoopBodyProgCondition env acc_type loop cloop knowledge
                                                    scas adts vseq vsca vadt thead tis_empty
                                                    acc wsca wadt head seq } b) ->
    refine { cloop | @ADTPairLoopBodyOk env acc_type loop cloop knowledge
                                     scas adts vseq vsca vadt thead tis_empty wsca wadt }%facade b.
Proof.
  eauto using pull_forall.
Qed.
