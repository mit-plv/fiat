Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.LaxTerminalFormat.

Section SequenceFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)
  Context {monoid : Monoid T}. (* Target type is a monoid. *)

  Definition sequence_Format
             (format1 format2 : FormatM S T)
    := (fun s env =>
          `(t1, env') <- format1 s env ;
          `(t2, env'') <- format2 s env';
           ret (mappend t1 t2, env''))%comp.

  Definition sequence_Decode
             {S' : Type}
             (decode1 : DecodeM (S' * T) T)
             (decode2 : S' -> DecodeM S T)
    : DecodeM S T
    := (fun t env =>
          match decode1 t env with
          | Some (s', t', env') => decode2 s' t' env
          | None => None
          end).

  Definition sequence_Encode
             (encode1 encode2 : EncodeM S T)
    := (fun s env =>
          `(t1, env') <- encode1 s env ;
          `(t2, env'') <- encode2 s env';
          Some (mappend t1 t2, env'')).

  Notation "x ++ y" := (sequence_Format _ x y) : format_scope .

  Lemma sequeunce_Format_assoc
        (format1 format2 format3 : FormatM S T)
    : forall s env,
      refineEquiv (sequence_Format (sequence_Format format1 format2) format3 s env)
                  (sequence_Format format1 (sequence_Format format2 format3) s env).
  Proof.
    unfold sequence_Format; intros.
    rewrite refineEquiv_bind2_bind.
    eapply refineEquiv_bind; [ reflexivity | ].
    intro; rewrite refineEquiv_bind2_bind.
    symmetry; rewrite refineEquiv_bind2_bind.
    eapply refineEquiv_bind; [ reflexivity | ].
    intro; rewrite refineEquiv_bind2_bind.
    rewrite refineEquiv_bind2_unit.
    eapply refineEquiv_bind; [ reflexivity | ].
    intro; rewrite refineEquiv_bind2_unit; simpl.
    rewrite mappend_assoc; reflexivity.
  Qed.

  Lemma refineEquiv_under_sequence_Format
        (format1 format2 format2' : FormatM S T)
    : (forall s env, refineEquiv (format2 s env) (format2' s env))
      -> forall s env,
        refineEquiv (sequence_Format format1 format2 s env)
                    (sequence_Format format1 format2' s env).
  Proof.
    unfold sequence_Format; intros.
    eapply refineEquiv_bind; [ reflexivity | ].
    intro ab; destruct ab; simpl.
    eapply refineEquiv_bind; [ apply H | reflexivity ].
  Qed.

  Lemma sequence_Format_format_correct_simpl'
      (format1 format2 : FormatM A B)
      (decode1 : DecodeM (A' * B) B)
      (decode2 : A' -> DecodeM A B)
      (decode1_pf : CorrectDecoder_simpl
                      format1 ++
                      (fun data_rest env binxenv =>
                         exists bin', fst binxenv = mappend bin' (snd data_rest) /\
                                      format1 (fst data_rest) env (bin', snd binxenv))
                      decode1)
      (decode2 : A' -> B -> CacheDecode -> option (A * CacheDecode))
      (decode2_pf : forall proj,
          CorrectDecoder_simpl (RestrictFormat format2 (fun data => project data = proj))
                               (decode2 proj))
  : CorrectDecoder_simpl
      (fun (data : A) (env : CacheFormat) =>
         sequence_Format _ (format1 (project data)) (format2 data) env
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(proj, env') <- decode1 bin env;
           decode2 (fst proj) (snd proj) env').
Proof.
  eapply CorrectDecoder_simpl_equiv_format; eauto.
  eapply CorrectDecoder_simpl_equiv_decode; try eassumption.
  eapply CorrectDecoder_simpl_no_inv.
  eapply CorrectDecoder_simpl_strict_equiv.
Abort.

  Lemma CorrectDecoder_Enqueue
    : CorrectDecoder_simpl (Enqueue_Format (decode).
  Proof.
    unfold CorrectDecoder_simpl, FMap_Decode, FMap_Format in *; split; intros.
    { repeat (apply_in_hyp @unfold_computes; destruct_ex; intuition).
      pose proof (g_inverts_f  _ _ _ _ H3 H4).
      rewrite <- unfold_computes in H3.
      eapply H1 in H3; destruct_ex; intuition eauto.
      eexists; rewrite H5; simpl; intuition eauto.
      subst; eauto.
    }
    { apply_in_hyp DecodeBindOpt_inv; destruct_ex; intuition.
      eapply H2 in H3; eauto; injections.
      destruct_ex; eexists; intuition eauto.
      apply unfold_computes.
      eexists; intuition eauto.
    }
  Qed.

Lemma sequence_Format_format_correct
      {A A' B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid B)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (predicate_rest' : A -> B -> Prop)
      (predicate_rest : A' -> B -> Prop)
      (format1 : A' -> CacheFormat -> Comp (B * CacheFormat))
      (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder
              monoid predicate'
              predicate_rest
              format1 decode1 P)
      (pred_pf : forall data, predicate data -> predicate' (project data))
      (predicate_rest_impl :
         forall a' b
                a ce ce' ce'' b' b'',
           computes_to (format1 a' ce) (b', ce')
           -> project a = a'
           -> predicate a
           -> computes_to (format2 a ce') (b'', ce'')
           -> predicate_rest' a b
           -> predicate_rest a' (mappend b'' b))
      (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf : forall proj,
          predicate' proj ->
          cache_inv_Property P P_inv2 ->
          CorrectDecoder monoid
                                  (fun data => predicate data /\ project data = proj)
                                  predicate_rest'
                                  format2
                                  (decode2 proj) P)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      predicate_rest'
      (fun (data : A) (env : CacheFormat) =>
         sequence_Format _ (format1 (project data)) (format2 data)  env
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(proj, rest, env') <- decode1 bin env;
           decode2 proj rest env') P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold sequence_Format, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend b0 ext) env_OK env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections; eauto.
    setoid_rewrite <- mappend_assoc; rewrite H2.
    simpl.
    destruct (fun H'' => proj1 (decode2_pf (project data) (pred_pf _ pred_pm) H1)
                               _ _ _ _ _ ext H4 H (conj pred_pm (eq_refl _)) H'' com_pf');
      intuition; simpl in *; injections.
    eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
    destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ].
    eapply (proj2 (decode2_pf a H5 (proj2 P_inv_pf))) in H2; eauto.
    destruct H2 as [? ?]; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    repeat computes_to_econstructor; eauto.
    simpl; rewrite mappend_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.

Lemma sequence_Format_format_correct_simpl
      {A A' B}
      {cache : Cache}
      {monoid : Monoid B}
      (project : A -> A')
      (format1 : FormatM A' B)
      (format2 : FormatM A B)
      (decode1 : DecodeM (A' * B) B)
      (*oblivious_decoder : forall bs data env bs' env',
          decode1 bs env = Some (data, bs', env') ->
          forall bs'', decode1 (mappend bs bs'') env = Some (data, mappend bs' bs'', env')*)
      (decode1_pf : CorrectDecoder_simpl
                      (fun data_rest env binxenv =>
                         exists bin', fst binxenv = mappend bin' (snd data_rest) /\
                                      format1 (fst data_rest) env (bin', snd binxenv))
                      decode1)
      (decode2 : A' -> B -> CacheDecode -> option (A * CacheDecode))
      (decode2_pf : forall proj,
          CorrectDecoder_simpl (RestrictFormat format2 (fun data => project data = proj))
                               (decode2 proj))
  : CorrectDecoder_simpl
      (fun (data : A) (env : CacheFormat) =>
         sequence_Format _ (format1 (project data)) (format2 data) env
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(proj, env') <- decode1 bin env;
           decode2 (fst proj) (snd proj) env').
Proof.
  split.
  { intros; unfold sequence_Format, Bind2 in *; computes_to_inv;
      destruct v; destruct v0; simpl in *; injections.
    destruct decode1_pf.
    destruct (H1 _ _ c (project data, b0) (mappend b b0) H) as [? [? ?] ].
    apply unfold_computes.
    rewrite unfold_computes in H0; simpl; eauto.
    specialize (decode2_pf (project data)); destruct decode2_pf.
    destruct (H5 c x xenv data b0 H4) as [? [? ?] ].
    unfold RestrictFormat; rewrite unfold_computes; intuition.
    rewrite H3; simpl; rewrite H7; eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 decode1_pf) in Heqo; eauto.
    destruct Heqo as [? [? ?] ].
    apply unfold_computes in H1; intuition; simpl in *;
      destruct_ex; intuition; subst.
    eapply (proj2 (decode2_pf _)) in H0; eauto.
    destruct H0 as [? ?]; destruct_ex; intuition; subst.
    unfold RestrictFormat in H1; apply unfold_computes in H1; intuition.
    rewrite H5.
    unfold sequence_Format; eexists; intuition eauto.
    repeat first [computes_to_econstructor
                  | apply unfold_computes; eauto ]. }
Qed.

Lemma sequence_Format_format_correct_simpl'
      {A A' B}
      {cache : Cache}
      {monoid : Monoid B}
      (project : A -> A')
      (format1 : FormatM A' B)
      (format2 : FormatM A B)
      (decode1 : DecodeM (A' * B) B)
      (*oblivious_decoder : forall bs data env bs' env',
          decode1 bs env = Some (data, bs', env') ->
          forall bs'', decode1 (mappend bs bs'') env = Some (data, mappend bs' bs'', env')*)
      (decode1_pf : CorrectDecoder_simpl
                      (fun data_rest env binxenv =>
                         exists bin', fst binxenv = mappend bin' (snd data_rest) /\
                                      format1 (fst data_rest) env (bin', snd binxenv))
                      decode1)
      (decode2 : A' -> B -> CacheDecode -> option (A * CacheDecode))
      (decode2_pf : forall proj,
          CorrectDecoder_simpl (RestrictFormat format2 (fun data => project data = proj))
                               (decode2 proj))
  : CorrectDecoder_simpl
      (fun (data : A) (env : CacheFormat) =>
         sequence_Format _ (format1 (project data)) (format2 data) env
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(proj, env') <- decode1 bin env;
           decode2 (fst proj) (snd proj) env').
Proof.
  eapply CorrectDecoder_simpl_equiv_format; eauto.
  eapply CorrectDecoder_simpl_equiv_decode; try eassumption.
  eapply CorrectDecoder_simpl_no_inv.
  eapply CorrectDecoder_simpl_strict_equiv.
Abort.

(* For decoding fixed fields that do no depend on the object *)
(* being formatd, e.g. version numbers in an IP packet. This *)
(* allows us to avoid polluting the data invariant with  *)
(* extraneous clauses. *)

(* SUGGESTION: If we're using a deterministic formatr, we *)
(* could compare the binary values of the field instead of *)
(* decoding and comparing. *)

Lemma sequence_Format_format_correct_no_dep
      {A A' B}
      (* Need decideable equality on the type of the fixed field. *)
      (A'_eq_dec : Query_eq A')
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid B)
      (a' : A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (predicate_rest' : A -> B -> Prop)
      (predicate_rest : A' -> B -> Prop)
      (format1 : A' -> CacheFormat -> Comp (B * CacheFormat))
      (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid predicate' predicate_rest
                                    format1 decode1 P)
      (predicate_a' : predicate' a')
      (predicate_rest_impl :
         forall a' b
                a ce ce' ce'' b' b'',
           computes_to (format1 a' ce) (b', ce')
           -> predicate a
           -> computes_to (format2 a ce') (b'', ce'')
           -> predicate_rest' a b
           -> predicate_rest a' (mappend b'' b))
      (decode2 : B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf :
         predicate' a' ->
         cache_inv_Property P P_inv2 ->
         CorrectDecoder monoid
                                 (fun data => predicate data)
                                 predicate_rest'
                                 format2
                                 decode2 P)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      predicate_rest'
      (fun (data : A) (env : CacheFormat) =>
         sequence_Format _ (format1 a') (format2 data)  env
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(a, rest, env') <- decode1 bin env;
           (if A_eq_dec a a' then decode2 rest env' else None)) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold sequence_Format, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (fun H => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend b0 ext) env_OK env_pm predicate_a' H com_pf); intuition; simpl in *; injections.
    eapply predicate_rest_impl; eauto.
    setoid_rewrite <- mappend_assoc; rewrite H2.
    simpl.
    destruct (A_eq_dec a' a'); try congruence.
    subst.
    destruct (fun H => proj1 H6 (*decode2_pf _ (conj (eq_refl _) predicate_a') H1*)
                             _ _ _ _ _ ext H4 H pred_pm pred_pm_rest com_pf');
      intuition; simpl in *; injections.
    eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate;
        destruct (A_eq_dec a a'); try discriminate;
          eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto;
            destruct Heqo; destruct_ex; intuition; subst;
              eapply (proj2 H11 (*decode2_pf a' (conj (eq_refl _) H7) H5)*)) in H1; eauto;
                destruct H1; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    repeat computes_to_econstructor; eauto.
    simpl; rewrite mappend_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.

Lemma CorrectDecoderinish {A B}
  : forall (cache : Cache)
           (monoid : Monoid B)
           (predicate : A -> Prop)
           (rest_predicate : A -> B -> Prop)
           (decode_inv : CacheDecode -> Prop)
           (a : A)
           (b : bool),
    (forall a', predicate a' -> a' = a)
    -> decides b (predicate a)
    -> CorrectDecoder
         monoid
         predicate
         rest_predicate
         (fun a' envE => ret (mempty, envE))
         (fun b' envD => if b then Some (a, b', envD) else None)
         decode_inv.
Proof.
  unfold CorrectDecoder; split; intros.
  - eexists env'; pose proof (H _ H2); subst; find_if_inside;
      simpl in *; intuition eauto; computes_to_inv; injections.
    rewrite mempty_left; eauto.
    eassumption.
  - find_if_inside; injections; try discriminate;
      simpl in *; intuition eauto.
    eexists; eexists; intuition eauto.
    rewrite mempty_left; reflexivity.
Qed.

Lemma decides_and :
  forall b b' P Q,
    decides b P
    -> decides b' Q
    -> decides (andb b b') (P /\ Q).
Proof.
  destruct b; destruct b'; simpl in *; intuition.
Qed.

Lemma decides_assumption :
  forall (P : Prop),
    P -> decides true P.
Proof. simpl in *; intuition. Qed.

Lemma decides_eq_refl {A} :
  forall (a : A), decides true (a = a).
Proof. simpl in *; intuition. Qed.

Lemma decides_dec_eq {A} :
  forall (A_eqb : A -> A -> bool)
         (A_eqb_sound : forall a a', a = a' <-> A_eqb a a' = true)
         (a a' : A), decides (A_eqb a a') (a = a').
Proof.
  simpl in *; intros; pose proof (A_eqb_sound a a');
    destruct (A_eqb a a'); simpl; intuition.
Qed.

Lemma decides_dec_lt
  : forall n n', decides (if (Compare_dec.lt_dec n n') then true else false) (lt n n').
Proof.
  intros; find_if_inside; simpl; eauto.
Qed.

Lemma refine_If_Then_Else_ThenC
  : forall (E B : Type) (monoid : Monoid B) (format1 format2 format3 : E -> Comp (B * E)) (env : E) b,
    refine (((If b Then format1 Else format2) ThenC format3) env)
           (If b Then ((format1 ThenC format3) env) Else ((format2 ThenC format3) env)).
Proof.
  intros; destruct b; reflexivity.
Qed.

Lemma refineEquiv_If_Then_Else_ThenC
  : forall (E B : Type) (monoid : Monoid B) (format1 format2 format3 : E -> Comp (B * E)) (env : E) b,
    refineEquiv (((If b Then format1 Else format2) ThenC format3) env)
                (If b Then ((format1 ThenC format3) env) Else ((format2 ThenC format3) env)).
Proof.
  intros; destruct b; reflexivity.
Qed.
