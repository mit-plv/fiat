Require Import
        Coq.omega.Omega
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.BaseFormats.

Section Word.
  Context {sz : nat}.

  Context {T : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid T}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Fixpoint encode_word' (s : nat) (w : word s) (b' : T) : T :=
    match w with
    | WO => b'
    | WS b s' w' => enqueue_opt b (encode_word' s' w' b')
    end.

  Definition encode_word (w : word sz) (ce : CacheFormat) : T * CacheFormat := (encode_word' sz w mempty, addE ce sz).

  Definition format_word (w : word sz) (ce : CacheFormat) : Comp (T * CacheFormat) :=
    ret (encode_word' sz w mempty, addE ce sz).

  (* Fixpoint format_word' {s : nat} (w : word s) := *)
  (*   match w with *)
  (*   | WO => fun env => ret (mempty, (addE env 0)) *)
  (*   | WS b s' w' => fun env => *)
  (*                     (Bind (format_word' w' env) (fun benv' => *)
  (*                                                    ret (enqueue_opt b (fst benv'), addE (snd benv') 1))) *)
  (*     end. *)

  (* Check (WS true (WS false WO)). *)
  (* Unset Printing Notations. *)
  (* Compute  (natToWord 2 2). *)


(* End Word. *)

(* Section Word'. *)
(*   Context {T : Type}. *)
(*   Context {cache : Cache}. *)
(*   Context {cacheAddNat : CacheAdd cache nat}. *)
(*   Context {monoid : Monoid T}. *)
(*   Context {monoidUnit : QueueMonoidOpt monoid bool}. *)

(*   Variable addE_addE_plus : *)
(*     forall (cd : CacheFormat) (n m : nat), addE (addE cd n) m = addE cd (n + m). *)

(*   Lemma format_word_equiv {sz} : forall (w : word sz) env, *)
(*       refineEquiv (format_word' w env) *)
(*                   (format_word w env). *)
(*   Proof. *)
(*     unfold refineEquiv; split; induction w; simpl; *)
(*       try reflexivity. *)
(*     - unfold format_word; simpl. *)
(*       rewrite IHw. *)
(*       unfold format_word; rewrite Monad.refineEquiv_bind_unit; simpl. *)
(*       rewrite addE_addE_plus; rewrite plus_comm; reflexivity. *)
(*     - unfold format_word; simpl. *)
(*       rewrite <- IHw. *)
(*       unfold format_word; rewrite Monad.refineEquiv_bind_unit; simpl. *)
(*       rewrite addE_addE_plus; rewrite plus_comm; reflexivity. *)
(*   Qed. *)
(* *)


  Fixpoint SW_word {sz} (b : bool) (w : word sz) : word (S sz) :=
    match w with
    | WO => WS b WO
    | WS b' s' w'' => WS b' (SW_word b w'')
    end.

  Fixpoint word_split_hd {sz} (w : word (S sz))
    : bool :=
    match sz return word (S sz) -> bool with
    | 0 => @whd _
    | S n' => fun w => word_split_hd (wtl w)
    end w.

  Fixpoint word_split_tl {sz} (w : word (S sz))
    : word sz :=
    match sz return word (S sz) -> word sz with
    | 0 => fun _ => WO
    | S n' => fun w => WS (whd w) (word_split_tl (wtl w))
    end w.

  Lemma word_split_SW {n}
    : forall (w : word (S n)),
      w = SW_word (word_split_hd w) (word_split_tl w).
  Proof.
    induction n; simpl; intros.
    - shatter_word w; reflexivity.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      rewrite (IHn x0) at 1; reflexivity.
  Qed.

  Fixpoint decode_word' (s : nat) (b : T) {struct s} : option (word s * T) :=
    match s with
    | O => Some (WO, b)
    | S s' =>
      `(c, b') <- dequeue_opt b;
      `(w', b') <- decode_word' s' b';
      Some (SW_word c w', b')
    end.

  Definition decode_word (b : T) (cd : CacheDecode) : option (word sz * T * CacheDecode) :=
    Ifopt decode_word' sz b as decoded Then Some (decoded, addD cd sz) Else None.

  Lemma enqueue_opt_format_word :
    forall n w b b',
      enqueue_opt b (encode_word' n w b') =
      mappend (encode_word' n w b') (enqueue_opt b mempty).
  Proof.
    induction w; simpl; intros; eauto.
    - rewrite <- enqueue_mappend_opt, mempty_right; auto.
    - rewrite !IHw.
      rewrite <- mappend_assoc.
      rewrite <- !enqueue_mappend_opt, !mempty_right.
      rewrite IHw; reflexivity.
  Qed.

  Lemma dequeue_encode_word'_enqueue_opt' :
    forall n w w' b b' ext,
      dequeue_opt w' = Some (b, b')
      -> dequeue_opt (mappend (encode_word' n w w') ext) =
           Some (b, (mappend (encode_word' n w b') ext)).
  Proof.
    induction w; simpl; intros.
    - erewrite dequeue_mappend_opt; eauto using dequeue_head_opt.
    - eapply dequeue_mappend_opt.
      rewrite enqueue_opt_format_word.
      erewrite IHw; eauto.
      rewrite <- enqueue_opt_format_word; reflexivity.
  Qed.

  Corollary dequeue_encode_word'_enqueue_opt :
    forall n w b ext,
      dequeue_opt (mappend (encode_word' n w (enqueue_opt b mempty)) ext) =
      Some (b, (mappend (encode_word' n w mempty) ext)).
  Proof.
    intros; eapply dequeue_encode_word'_enqueue_opt'.
    eapply dequeue_head_opt.
  Qed.

  Lemma dequeue_opt_Some' :
    forall n w ext,
      dequeue_opt (mappend (encode_word' (S n) w mempty) ext)
      = Some (word_split_hd w, (mappend (encode_word' n (word_split_tl w) mempty) ext)).
  Proof.
    induction n; simpl; intros.
    - shatter_word w; simpl in *.
      erewrite dequeue_mappend_opt; eauto using dequeue_head_opt.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      simpl in *.
      rewrite enqueue_opt_format_word.
      rewrite <- mappend_assoc.
      rewrite IHn.
      rewrite enqueue_opt_format_word.
      rewrite <- mappend_assoc; auto.
  Qed.

  Lemma decode_encode_word'
    : forall {n} w ext,
      decode_word' n (mappend (encode_word' n w mempty) ext)
      = Some (w, ext).
  Proof.
    induction n; simpl; intros; try shatter_word w; simpl in *.
    - rewrite mempty_left; reflexivity.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      rewrite enqueue_opt_format_word.
      rewrite <- !mappend_assoc.
      destruct n.
      + shatter_word x0; simpl.
        rewrite mempty_left.
        erewrite dequeue_mappend_opt;
          eauto using dequeue_head_opt.
        simpl.
        rewrite mempty_left; auto.
      + rewrite dequeue_opt_Some'.
        unfold DecodeBindOpt, BindOpt at 1; unfold If_Opt_Then_Else.
        assert (decode_word' (S n)
                   (mappend (encode_word' n (word_split_tl x0) mempty)
                              (mappend (enqueue_opt x mempty) ext))
                = Some (WS x (word_split_tl x0), ext)).
        { simpl.
          pose proof (IHn (WS x (word_split_tl x0)) ext).
          simpl in H.
          rewrite enqueue_opt_format_word in H.
          rewrite <- mappend_assoc in H.
          rewrite H.
          eauto. }
        unfold BindOpt. rewrite H; simpl; rewrite <- (word_split_SW x0); auto.
  Qed.

  Lemma decode_encode_word'_Some
    : forall sz bin data ext,
      decode_word' sz bin = Some (data, ext)
      -> bin = mappend (encode_word' sz data mempty) ext.
  Proof.
    induction sz0; simpl; intros.
    - shatter_word data; simpl; injections.
      rewrite mempty_left; auto.
    - destruct (dequeue_opt bin) as [ [? ?] | ] eqn: ? ;
        simpl in *; try discriminate.
      destruct (decode_word' sz0 t) as [ [? ?] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      apply IHsz0 in Heqo0; subst.
      eapply dequeue_opt_inj; eauto.
      simpl.
      rewrite <- dequeue_encode_word'_enqueue_opt.
      clear; revert ext; induction w; simpl; auto; intros.
      rewrite !enqueue_opt_format_word, <- !mappend_assoc.
      rewrite IHw; reflexivity.
  Qed.

  Theorem Word_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder monoid (fun _ => True)
                              (fun _ _ => True)
                              format_word decode_word P.
  Proof.
    unfold CorrectDecoder, format_word, decode_word; split.
    - intros env env' xenv w w' ext env_OK Eeq _ _ Penc.
      computes_to_inv; injections.
      generalize dependent sz.
      intros; rewrite decode_encode_word'; simpl.
      eexists; split; eauto using add_correct.
    - intros.
      destruct (decode_word' sz bin)
        as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections.
      apply decode_encode_word'_Some in Heqo; subst.
      split; eauto using add_correct.
      eexists; eexists; repeat split.
      eauto using add_correct.
  Qed.

  Lemma decode_word'_le
    : forall (a : word sz) (b' b1 : T),
      decode_word' _ b1 = Some (a, b') -> le_B b' b1.
  Proof.
    intros; apply decode_encode_word'_Some in H; subst.
    unfold le_B.
    rewrite mappend_measure; omega.
  Qed.

  Lemma decode_word_le
    : forall (b1 : T) (cd : CacheDecode) (a : word sz)
             (b' : T) (cd' : CacheDecode),
      decode_word b1 cd = Some (a, b', cd') -> le_B b' b1.
  Proof.
    unfold decode_word.
    intros; destruct (decode_word' sz b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    injections.
    eapply decode_word'_le; eauto.
  Qed.

  Lemma decode_word'_lt
    : forall (a : word (S sz)) (b' b1 : T),
      decode_word' _ b1 = Some (a, b') -> lt_B b' b1.
  Proof.
    simpl; intros; injections; unfold lt_B.
    destruct (dequeue_opt b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    apply measure_dequeue_Some in Heqo; subst.
    destruct (decode_word' sz t) as [ [? ?] | ] eqn: ? ;
        subst; simpl in *; try discriminate.
    eapply decode_word'_le in Heqo0; injections.
    rewrite Heqo.
    unfold le_B in *.
    pose proof (B_measure_gt_0 b).
    omega.
  Qed.

  Lemma decode_word_lt
    : forall (b' : T) (cd : CacheDecode) (a : word (S sz))
             (b1 : T) (cd' : CacheDecode),
      Ifopt decode_word' _ b' as decoded Then Some (decoded, addD cd (S sz)) Else None = Some (a, b1, cd') -> lt_B b1 b'.
  Proof.
    intros; destruct (decode_word' (S sz) b') as [ [? ?] | ] eqn: ? ;
    try eapply decode_word'_lt in Heqo;
      simpl in *; try (subst; discriminate).
    injections.
    unfold lt_B in *.
    omega.
  Qed.

  Definition format_unused_word {S}
    : FormatM S T :=
    Compose_Format format_word (fun _ => {w : word sz | True})%comp.

  Fixpoint monoid_get_word {T}
           {monoid : Monoid T}
           {monoid_opt : QueueMonoidOpt monoid bool}
           (sz : nat)
           (b : T)
    : option (word sz) :=
    match sz with
    | 0 => Some WO
    | S sz' =>
      match dequeue_opt b with
      | Some (c, b') =>
        match monoid_get_word sz' b' with
        | Some w => Some (SW_word c w)
        | _ => None
        end
      | _ => None
      end
    end.

  Definition monoid_dequeue_word
         (sz : nat)
         (b : T)
  : option (word sz * T) := decode_word' sz b.

  Lemma monoid_dequeue_word_eq_decode_word' :
    forall (sz : nat)
           (b : T),
      monoid_dequeue_word sz b = decode_word' sz b.
  Proof.
    reflexivity.
  Qed.

  Lemma monoid_dequeue_encode_word'
        (sz' : nat)
    : forall (w : word sz') (ext : T),
      monoid_dequeue_word sz' (mappend (encode_word' _ w mempty ) ext) = Some (w, ext).
  Proof.
    intros; unfold monoid_dequeue_word.
    apply decode_encode_word'.
  Qed.

  Definition decode_unused_word' (s : nat) (b : T) : option (unit * T) :=
    Ifopt monoid_dequeue_word s b as b' Then Some (tt, snd b') Else None.

  Definition decode_unused_word
    : DecodeM (unit * T) T :=
    Compose_Decode decode_word (fun wt => (tt, snd wt)).

End Word.

Lemma EquivFormat_LaxTerminal {S T}
        {monoid' : Monoid T}
        {cache' : Cache}
  : forall format : FormatM S T,
    EquivFormat (Projection_Format format fst ++ LaxTerminal_Format) (DoneLax format) .
Proof.
  unfold EquivFormat, DoneLax, Projection_Format, Compose_Format, LaxTerminal_Format,
  sequence_Format, ComposeOpt.compose, Bind2;
    split; unfold refine; intros.
  - rewrite unfold_computes in H; destruct_ex; split_and; subst.
    destruct v; destruct s; simpl in *; subst.
    repeat computes_to_econstructor; eauto.
    rewrite unfold_computes; eexists; split; eauto.
    rewrite unfold_computes; eauto.
    simpl; computes_to_econstructor.
  - computes_to_inv; subst.
    rewrite unfold_computes in H; rewrite unfold_computes.
    destruct_ex; destruct v0; eexists; simpl in *; intuition eauto.
    subst; eauto.
Qed.

Add Parametric Morphism
    S T
    (cache : Cache)
    (decode : DecodeM S T)
  : (fun format =>
       @CorrectDecoder_simpl S T cache format decode)
    with signature (EquivFormat ==> impl)
      as format_decode_correct_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder_simpl;
    intuition eauto; intros.
  - eapply H1; eauto; apply H; eauto.
  - destruct (H2 _ _ _ _ _ H0 H3) as [ ? [? ?] ];
      intuition.
    repeat eexists; intuition eauto; apply H; eauto.
Qed.

Theorem unused_word_decode_correct
        {sz : nat}
        {T}
        {monoid : Monoid T}
        {cache : Cache}
        {cacheAddNat : CacheAdd cache nat}
        {monoidUnit : QueueMonoidOpt monoid bool}
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  :
    CorrectDecoder monoid (fun _ => True)
                   (fun _ _ => True)
                   (format_unused_word (sz := sz)) (decode_unused_word (sz := sz)) P.
Proof.
  unfold CorrectDecoder, format_unused_word, decode_unused_word,
  Compose_Format, Compose_Decode; split.
  - intros env env' xenv w w' ext env_OK Eeq _ _ Penc.
    computes_to_inv; injections.
    generalize dependent sz.
    intros; rewrite unfold_computes in Penc; destruct_ex; split_and.
    eapply Word_decode_correct in H0; eauto.
    destruct_ex; split_and; eexists; intuition eauto.
    rewrite H0; destruct w; reflexivity.
  - intros.
    destruct (decode_word bin env')
      as [ [ [? ?] ?] | ] eqn: ?; simpl in *; try discriminate.
    injections.
    eapply Word_decode_correct in Heqo; eauto.
    intuition; destruct_ex; split_and.
    eexists _, _; repeat split; eauto.
    apply unfold_computes; eexists; split; eauto.
Qed.

Lemma compose_unused_correct
      {sz : nat}
      {S T}
      {cache : Cache}
      {cacheAddNat : CacheAdd cache nat}
      {P : CacheDecode -> Prop}
      {P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv2 P))
      (monoid : Monoid T)
      {monoidUnit : QueueMonoidOpt monoid bool}
      (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
      (predicate : S -> Prop)
      (predicate_rest' : S -> T -> Prop)
      (format2 : S -> CacheFormat -> Comp (T * CacheFormat))
      (*predicate_rest_impl :
         forall a' b
                a ce ce' ce'' b' b'',
           computes_to (format1 a' ce) (b', ce')
           -> project a = a'
           -> predicate a
           -> computes_to (format2 a ce') (b'', ce'')
           -> predicate_rest' a b
           -> predicate_rest a' (mappend b'' b)*)
      (decode2 : T -> CacheDecode -> option (S * T * CacheDecode))
      (decode2_pf :
          cache_inv_Property P P_inv2 ->
          CorrectDecoder monoid
                         predicate
                         predicate_rest'
                         format2
                         decode2 P)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      predicate_rest'
      (fun (data : S) (ctx : CacheFormat) =>
         ComposeOpt.compose _ (format_unused_word (sz := sz) data) (format2 data) ctx
      )%comp
      (fun (bin : T) (env : CacheDecode) =>
         `(proj, rest, env') <- decode_unused_word (sz := sz) bin env;
           decode2 rest env') P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold ComposeOpt.compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    injections.
    eapply (unused_word_decode_correct (P := P)) in com_pf; eauto.
    destruct_ex; split_and.
    specialize (decode2_pf P_inv_pf).
    eapply decode2_pf in com_pf'.
    destruct_ex; split_and.
    eexists; eauto.
    rewrite <- mappend_assoc, H0; simpl.
    split; eauto.
    eauto.
    eauto.
    eauto.
    eauto.
  }
  { intros.
    destruct (decode_unused_word bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (unused_word_decode_correct (P := P)) in Heqo; eauto.
    split_and; destruct_ex; split_and.
    specialize (decode2_pf P_inv_pf).
    eapply decode2_pf in H1; eauto.
    split_and; destruct_ex; split_and; subst.
    intuition; eexists _, _; repeat split.
    unfold ComposeOpt.compose; repeat computes_to_econstructor; eauto.
    simpl; rewrite mappend_assoc; reflexivity.
    eassumption.
    eassumption.
  } 
  Grab Existential Variables.
  constructor.
Qed.

Arguments format_unused_word sz {_ _ _ _ _ _}.

Lemma monoid_get_encode_word' {T}
      {monoid : Monoid T}
      {monoid_opt : QueueMonoidOpt monoid bool}
      (sz : nat)
  : forall (w : word sz) (ext : T),
    monoid_get_word sz (mappend (encode_word' _ w mempty) ext) = Some w.
Proof.
  induction sz; simpl; intros; try shatter_word w; simpl in *.
    - reflexivity.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      rewrite enqueue_opt_format_word.
      rewrite <- !mappend_assoc.
      destruct sz.
      + shatter_word x0; simpl.
        rewrite mempty_left.
        erewrite dequeue_mappend_opt;
          eauto using dequeue_head_opt.
      + rewrite dequeue_opt_Some'.
          pose proof (IHsz (WS x (word_split_tl x0)) ext).
          simpl in *.
          rewrite enqueue_opt_format_word in H.
          rewrite <- mappend_assoc in H.
          destruct (dequeue_opt
          (mappend (encode_word' sz (word_split_tl x0) mempty)
                     (mappend (enqueue_opt x mempty) ext))) as [ [? ?] | ];
            simpl in *; try discriminate.
          destruct (monoid_get_word sz t); try discriminate.
          injections.
          rewrite H0.
          simpl.
          rewrite <- (word_split_SW x0); auto.
  Qed.
