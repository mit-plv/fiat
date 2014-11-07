Require Import FiatToFacade.Compiler.Prerequisites FiatToFacade.Compiler.ADTs.ListsInversion.
Require Import Facade.FacadeADTs.
Require Import List GLabelMap.

Unset Implicit Arguments.

Ltac compile_list_helper runs_to :=
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs; scas_adts_mapsto;
  [ econstructor; eauto 2 using mapsto_eval;
    [ scas_adts_mapsto;
      eauto using mapM_MapsTo_0, mapM_MapsTo_1, mapM_MapsTo_2
    | eapply not_in_adts_not_mapsto_adt;
      [ eassumption | map_iff_solve intuition ]
    | simpl; repeat eexists; reflexivity ]
  | match goal with
      | H: context[RunsTo] |- _ => eapply runs_to in H; eauto
    end; split; repeat rewrite_Eq_in_goal
  ].

Lemma compile_list_push :
  forall {env},
  forall vseq vhead f vdiscard,
  forall scas adts knowledge head seq,
    GLabelMap.find f env = Some (Axiomatic List_push) ->
    ~ StringMap.In vdiscard adts ->
    ~ StringMap.In vseq scas ->
    vhead <> vseq ->
    vseq <> vdiscard ->
    scas[vhead >> SCA _ head] ->
    refine (@Prog _ env knowledge
                  scas ([vdiscard >sca> 0]::scas)
                  ([vseq >adt> List seq]::adts) ([vseq >adt> List (head :: seq)]::adts))
           (ret (Call vdiscard f (vseq :: vhead :: nil))%facade).
Proof.
  compile_list_helper runsto_cons.

  eauto using SomeSCAs_chomp, add_sca_pop_adts.
  apply add_adts_pop_sca; map_iff_solve trivial.
  apply AllADTs_chomp_remove.
  match goal with
    | H: AllADTs _ _ |- _ => rewrite H
  end; trickle_deletion; reflexivity.
Qed.

Lemma compile_list_delete :
  forall env f vret vseq seq knowledge scas adts adts',
    GLabelMap.find f env = Some (Axiomatic List_delete) ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vseq scas ->
    adts[vseq >> ADT (List seq)] ->
    StringMap.Equal adts' (StringMap.remove vseq adts) ->
    refine (@Prog _ env knowledge
                  scas ([vret >sca> 0]::scas)
                  adts adts')
           (ret (Call vret f (vseq :: nil)))%facade.
Proof.
  compile_list_helper runsto_delete.

  eauto using SomeSCAs_chomp, SomeSCAs_not_In_remove.
  
  apply add_adts_pop_sca.
  map_iff_solve intuition.
  eauto using AllADTs_chomp_remove'.
Qed.

Lemma compile_list_new :
  forall {env},
  forall scas adts knowledge,
  forall vret f,
    GLabelMap.find f env = Some (Axiomatic List_new) ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vret scas ->
    refine (@Prog _ env knowledge
                  scas scas
                  adts ([vret >adt> List nil]::adts))
           (ret (Call vret f nil)%facade).
Proof.
  compile_list_helper runsto_new.
  
  eauto using add_sca_pop_adts.
  eauto using AllADTs_chomp. 
Qed.

Lemma compile_copy :
  forall {env},
  forall scas adts knowledge seq,
  forall vret vfrom f,
    GLabelMap.find f env = Some (Axiomatic List_copy) ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vret scas ->
    ~ StringMap.In vfrom scas ->
    adts[vfrom >> ADT (List seq)] ->
    refine (@Prog _ env knowledge
                  scas scas
                  adts ([vret >adt> List seq]::adts))
           (ret (Call vret f (vfrom :: nil))%facade).
Proof.
  compile_list_helper runsto_copy.

  eauto using add_sca_pop_adts.
  eauto using AllADTs_chomp, AllADTs_add_in.
Qed.

Lemma compile_pre_push :
  forall {env},
  forall vseq vhead,
  forall init_scas inter_scas final_scas init_adts inter_adts final_adts knowledge head seq,
    vhead <> vseq ->
    refine (@Prog _ env knowledge
                  init_scas final_scas
                  init_adts ([vseq >adt> List (head :: seq)] :: final_adts))
           (phead <- (@Prog _ env knowledge
                            init_scas ([vhead >sca> head]::init_scas)
                            init_adts init_adts);
            ptail <- (@Prog _ env knowledge
                            ([vhead >sca> head]::init_scas) ([vhead >sca> head]::init_scas)
                            init_adts ([vseq >adt> List seq]::inter_adts));
            ppush <- (@Prog _ env knowledge
                            ([vhead >sca> head]::init_scas) inter_scas
                            ([vseq >adt> List seq]::inter_adts)
                            ([vseq >adt> List (head :: seq)]::final_adts));
            pclean <- (@Prog _ env knowledge
                            inter_scas final_scas
                            ([vseq >adt> List (head :: seq)]::final_adts)
                            ([vseq >adt> List (head :: seq)]::final_adts));
            ret (phead; ptail; ppush; pclean)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)
  repeat (constructor; split; intros);
  specialize_states;
  try assumption.
  
  (* RunsTo *)
  intros;
    repeat inversion_facade;
    specialize_states;
    intuition.
Qed.
