Require Import FiatToFacade.Compiler.Prerequisites.

(*
Lemma compile_snd :
  forall {av env} vfst vsnd knowledge adts scas adt_type (wrapper: adt_type -> av) pair,
    refine
    (@Prog av env knowledge
           scas ([vsnd >sca> snd pair]::scas)
           adts adts)
    (p <- (@Prog av env knowledge
                 scas ([vsnd >sca> snd pair]::scas)
                 adts ([vfst >adt> wrapper (fst pair)]::adts));
     cleanup <- (@Prog av env knowledge
                       ([vsnd >sca> snd pair]::scas) ([vsnd >sca> snd pair]::scas)
                       ([vfst >adt> wrapper (fst pair)]::adts) adts);
     ret (p; cleanup)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  repeat (safe_seq; intros).
  specialize_states.
  assumption.

  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto.
  intuition.
Qed.
 *)
Unset Implicit Arguments.
      
Lemma compile_pair_sca :
  forall {pair_type av env knowledge} vadt (wadt: pair_type -> av) {vsca} {wsca: pair_type -> W} adts inter_adts final_adts scas pair,
    refine
    (@Prog av env knowledge
           scas ([vsca >sca> wsca pair]::scas)
           adts final_adts)
    (p <- (@Prog av env knowledge
                 scas ([vsca >sca> wsca pair]::scas)
                 adts ([vadt >adt> wadt pair]::inter_adts));
     cleanup <- (@Prog av env knowledge
                       ([vsca >sca> wsca pair]::scas) ([vsca >sca> wsca pair]::scas)
                       ([vadt >adt> wadt pair]::inter_adts) final_adts);
     ret (p; cleanup)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  repeat (safe_seq; intros).
  specialize_states.
  assumption.

  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto.
  intuition.
Qed.

Lemma compile_pair_adt :
  forall {pair_type av env knowledge} vsca (wsca: pair_type -> W) {vadt} {wadt: pair_type -> av} adts inter_adts final_adts scas pair,
    refine
    (@Prog av env knowledge
           scas scas
           adts ([vadt >adt> wadt pair]::final_adts))
    (p <- (@Prog av env knowledge
                 scas ([vsca >sca> wsca pair]::scas)
                 adts ([vadt >adt> wadt pair]::inter_adts));
     cleanup <- (@Prog av env knowledge
                       ([vsca >sca> wsca pair]::scas) scas
                       ([vadt >adt> wadt pair]::inter_adts) ([vadt >adt> wadt pair]::final_adts));
     ret (p; cleanup)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  repeat (safe_seq; intros).
  specialize_states.
  assumption.

  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto.
  intuition.
Qed.


Lemma compile_adt_pair :
  forall {pair_type av env knowledge} vadt1 vadt2 {wadt1 wadt2: pair_type -> av} adts inter_adts final_adts scas pair,
    refine
    (@Prog av env knowledge
           scas scas
           adts ([vadt2 >adt> wadt2 pair]::final_adts))
    (p <- (@Prog av env knowledge
                 scas scas
                 adts ([vadt1 >adt> wadt1 pair]::[vadt2 >adt> wadt2 pair]::inter_adts));
     cleanup <- (@Prog av env knowledge
                       scas scas
                       ([vadt1 >adt> wadt1 pair]::[vadt2 >adt> wadt2 pair]::inter_adts)
                       ([vadt2 >adt> wadt2 pair]::final_adts));
     ret (p; cleanup)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  repeat (safe_seq; intros).
  specialize_states.
  assumption.

  intros;
    repeat inversion_facade;
    specialize_states;
    scas_adts_mapsto.
  intuition.
Qed.
