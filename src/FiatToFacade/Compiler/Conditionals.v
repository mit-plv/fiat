Require Import FiatToFacade.Compiler.Prerequisites.

Unset Implicit Arguments.

Lemma compile_if_sca :
  forall {av env}
         (vtest: StringMap.key) {vret}
         (test: bool)
         init_knowledge
         init_scas init_adts post_test_adts final_adts
         truecase falsecase,
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> if test then truecase
                                         else falsecase] :: init_scas)
                  init_adts final_adts)
           (ptest  <- (@Prog av env init_knowledge
                             init_scas ([vtest >sca> BoolToW test] :: init_scas)
                             init_adts post_test_adts);
            ptrue  <- (@Prog av env (init_knowledge /\ test = true)
                             ([vtest >sca> BoolToW test] :: init_scas) ([vret >sca>  truecase] :: init_scas)
                             post_test_adts final_adts);
            pfalse <- (@Prog av env (init_knowledge /\ test = false)
                            ([vtest >sca> BoolToW test] :: init_scas) ([vret >sca> falsecase] :: init_scas)
                            post_test_adts final_adts);
            ret (ptest; If vtest = 0 then pfalse else ptrue)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)
  constructor;
  split;
    [ solve [intuition] |
      intros;
        destruct test;
        and_eq_refl; (* Clean up 'true = true' style conditions *) 
        [ apply SafeIfFalse | apply SafeIfTrue ];
        specialize_states;
        scas_adts_mapsto; (* Extract value of vtest *)
        first [ assumption | eapply BoolToW_eval; trivial] ].
  
  (* RunsTo *)
  intros;
    repeat inversion_facade;
    unfold is_true, is_false in *;
    destruct test;
    and_eq_refl;
    specialize_states;
    scas_adts_mapsto;
    eapply BoolToW_eval in maps_to;
    BoolToW_eval_helper; try (eq_transitive; congruence);
    split; assumption.
Qed.

(* FIXME remove 
Lemma compile_if_adt :
  forall {av env}
         (vtest: StringMap.key) {vret}
         (test: bool)
         init_knowledge
         init_scas final_scas init_adts post_test_adts
         truecase falsecase,
    refine (@Prog av env init_knowledge
                  init_scas final_scas
                  init_adts ([vret >sca> if test then truecase
                                         else falsecase] :: init_adts))
           (ptest  <- (@Prog av env init_knowledge
                             init_scas ([vtest >sca> BoolToW test] :: init_scas)
                             init_adts post_test_adts);
            ptrue  <- (@Prog av env (init_knowledge /\ test = true)
                             ([vtest >sca> BoolToW test] :: init_scas) final_scas
                             post_test_adts ([vret >sca> truecase] :: init_adts));
            pfalse <- (@Prog av env (init_knowledge /\ test = false)
                            ([vtest >sca> BoolToW test] :: init_scas) final_scas
                            post_test_adts ([vret >sca> falsecase] :: init_adts));
            ret (ptest; If vtest = 0 then pfalse else ptrue)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)
  constructor;
  split;
    [ solve [intuition] |
      intros;
        destruct test;
        and_eq_refl; (* Clean up 'true = true' style conditions *) 
        [ apply SafeIfFalse | apply SafeIfTrue ];
        specialize_states;
        scas_adts_mapsto; (* Extract value of vtest *)
        first [ assumption | eapply BoolToW_eval; trivial] ].
  
  (* RunsTo *)
  intros;
    repeat inversion_facade;
    unfold is_true, is_false in *;
    destruct test;
    and_eq_refl;
    specialize_states;
    scas_adts_mapsto;
    eapply BoolToW_eval in maps_to;
    BoolToW_eval_helper; try (eq_transitive; congruence);
    split; assumption.
Qed. (* TODO: Exactly the same proof as compile_if_sca *)
 *)

Lemma compile_if_adt :
  forall {av env}
         (vtest: StringMap.key) {vret}
         (test: bool)
         init_knowledge
         init_scas final_scas init_adts post_test_adts final_adts
         ret_type (truecase falsecase: ret_type) wrapper,
    refine (@Prog av env init_knowledge
                  init_scas final_scas
                  init_adts ([vret >adt> wrapper (if test then truecase
                                                  else falsecase)] :: final_adts))
           (ptest  <- (@Prog av env init_knowledge
                             init_scas ([vtest >sca> BoolToW test] :: init_scas)
                             init_adts post_test_adts);
            ptrue  <- (@Prog av env (init_knowledge /\ test = true)
                             ([vtest >sca> BoolToW test] :: init_scas) final_scas
                             post_test_adts ([vret >adt> wrapper truecase] :: final_adts));
            pfalse <- (@Prog av env (init_knowledge /\ test = false)
                            ([vtest >sca> BoolToW test] :: init_scas) final_scas
                            post_test_adts ([vret >adt> wrapper falsecase] :: final_adts));
            ret (ptest; If vtest = 0 then pfalse else ptrue)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)
  constructor;
  split;
    [ solve [intuition] |
      intros;
        destruct test;
        and_eq_refl; (* Clean up 'true = true' style conditions *) 
        [ apply SafeIfFalse | apply SafeIfTrue ];
        specialize_states;
        scas_adts_mapsto; (* Extract value of vtest *)
        first [ assumption | eapply BoolToW_eval; trivial] ].
  
  (* RunsTo *)
  intros;
    repeat inversion_facade;
    unfold is_true, is_false in *;
    destruct test;
    and_eq_refl;
    specialize_states;
    scas_adts_mapsto;
    eapply BoolToW_eval in maps_to;
    BoolToW_eval_helper; try (eq_transitive; congruence);
    split; try assumption.
Qed. (* TODO: Exactly the same proof as compile_if_sca *)

Lemma compile_if_parallel :
  forall {av env}
         (vtest: StringMap.key) {vsca vadt}
         ret_type wrapper
         (test: bool)
         init_knowledge
         init_scas final_scas init_adts post_test_adts final_adts
         scatruecase scafalsecase (adttruecase adtfalsecase: ret_type),
    refine (@Prog av env init_knowledge
                  init_scas ([vsca >sca> (if test then scatruecase
                                          else scafalsecase)] :: final_scas)
                  init_adts ([vadt >adt> wrapper (if test then adttruecase
                                                  else adtfalsecase)] :: final_adts))
           (ptest  <- (@Prog av env init_knowledge
                             init_scas ([vtest >sca> BoolToW test] :: init_scas)
                             init_adts post_test_adts);
            ptrue  <- (@Prog av env (init_knowledge /\ test = true)
                             ([vtest >sca> BoolToW test] :: init_scas)
                             ([vsca >sca> scatruecase] :: final_scas)
                             post_test_adts ([vadt >adt> wrapper adttruecase] :: final_adts));
            pfalse <- (@Prog av env (init_knowledge /\ test = false)
                             ([vtest >sca> BoolToW test] :: init_scas)
                             ([vsca >sca> scafalsecase] :: final_scas)
                             post_test_adts ([vadt >adt> wrapper adtfalsecase] :: final_adts));
            ret (ptest; If vtest = 0 then pfalse else ptrue)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)
  constructor;
  split;
    [ solve [intuition] |
      intros;
        destruct test;
        and_eq_refl; (* Clean up 'true = true' style conditions *) 
        [ apply SafeIfFalse | apply SafeIfTrue ];
        specialize_states;
        scas_adts_mapsto; (* Extract value of vtest *)
        first [ assumption | eapply BoolToW_eval; trivial] ].
  
  (* RunsTo *)
  intros;
    repeat inversion_facade;
    unfold is_true, is_false in *;
    destruct test;
    and_eq_refl;
    specialize_states;
    scas_adts_mapsto;
    eapply BoolToW_eval in maps_to;
    BoolToW_eval_helper; try (eq_transitive; congruence);
    split; try assumption.
Qed. 
