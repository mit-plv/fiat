Require Import
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.DomainNameOpt
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BaseFormats
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant.

Require Import
        Bedrock.Word.

Section AlignedList.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Fixpoint align_decode_list {A}
           (A_decode_align : forall n,
               ByteBuffer.t n
               -> CacheDecode
               -> option (A * {n : _ & Vector.t _ n}
                          * CacheDecode))
           (n : nat)
           {sz}
           (v : ByteBuffer.t sz)
           (cd : CacheDecode)
    : option (list A *  {n : _ & Vector.t _ n} * CacheDecode) :=
    match n with
    | 0 => Some (@nil _, existT _ _ v, cd)
    | S s' => `(x, b1, e1) <- A_decode_align sz v cd;
                `(xs, b2, e2) <- align_decode_list A_decode_align s' (projT2 b1) e1;
                Some ((x :: xs)%list, b2, e2)
    end.

  Lemma optimize_align_decode_list
        {A}
        (A_decode :
           ByteString
           -> CacheDecode
           -> option (A * ByteString * CacheDecode))
        (A_decode_align : forall n,
            ByteBuffer.t n
            -> CacheDecode
            -> option (A * {n : _ & Vector.t _ n}
                       * CacheDecode))
        (A_decode_OK :
           forall n (v : Vector.t _ n) cd,
             A_decode (build_aligned_ByteString v) cd =
             Ifopt A_decode_align n v cd as a Then
                                              Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                              Else
                                              None)
    : forall (n : nat)
             {sz}
             (v : ByteBuffer.t sz)
             (cd : CacheDecode),
      decode_list A_decode n (build_aligned_ByteString v) cd =
      Ifopt align_decode_list A_decode_align n v cd as a Then
                                                         Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                                         Else
                                                         None.
  Proof.
    induction n; simpl; intros; eauto.
    rewrite A_decode_OK.
    rewrite (If_Opt_Then_Else_DecodeBindOpt).
    destruct (A_decode_align sz v cd) as [ [ [? [? ?] ] ?]  | ]; simpl; eauto.
    rewrite IHn.
    rewrite (If_Opt_Then_Else_DecodeBindOpt).
    destruct (align_decode_list A_decode_align n t c)
      as [ [ [? [? ?] ] ?]  | ]; simpl; eauto.
  Qed.

  Fixpoint align_format_list {A}
           (A_format_align :
              A
              ->  CacheFormat
              -> {n : _ & ByteBuffer.t n} * CacheFormat)
           (As : list A)
           (ce : CacheFormat)
    : {n : _ & ByteBuffer.t n} * CacheFormat :=
    match As with
    | nil => (existT _ _ (Vector.nil _), ce)
    | a :: As' =>
      let (b, ce') := A_format_align a ce in
      let (b', ce'') := align_format_list A_format_align As' ce' in
      (existT _ _ (append (projT2 b) (projT2 b')), ce'')
    end.

  Lemma optimize_align_format_list
        {A}
        (A_OK : A -> Prop)
        (format_A : A -> CacheFormat -> Comp (ByteString * CacheFormat))
        (A_format_align :
           A
           ->  CacheFormat
           -> {n : _ & ByteBuffer.t n} * CacheFormat)
        (A_format_OK :
           forall a ce,
             A_OK a
             -> refine (format_A a ce)
                    (ret (let (v', ce') := A_format_align a ce in
                          (build_aligned_ByteString (projT2 v'), ce'))))
    : forall (As : list A)
             (ce : CacheFormat),
      (forall a, In a As -> A_OK a)
      -> refine (format_list format_A As ce)
             (let (v', ce') := (align_format_list A_format_align As ce) in
              ret (build_aligned_ByteString (projT2 v'), ce')).
  Proof.
    induction As; simpl; intros; simpl.
    - simpl.
      repeat f_equiv.
      eapply ByteString_f_equal.
      instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := eq_refl _); reflexivity.
    - unfold Bind2.
      rewrite A_format_OK; eauto; simplify with monad laws.
      rewrite IHAs.
      destruct (A_format_align a ce); simpl.
      destruct (align_format_list A_format_align As c);
        simplify with monad laws.
      simpl.
      rewrite <- build_aligned_ByteString_append.
      reflexivity.
      intuition.
  Qed.

  Lemma AlignedFormatListThenC {A}
        (A_OK : A -> Prop)
        format_A
        (encode_A : A -> CacheFormat -> {n : nat & t (word 8) n} * CacheFormat)
    : forall (l : list A) ce (c : _ -> Comp _)
             (v' : _ -> {n : nat & t (word 8) n})
             (ce' : _ -> CacheFormat),
      (forall (a : A) (ce : CacheFormat),
          A_OK a ->
          refine (format_A a ce) (ret (let (v', ce') := encode_A a ce in (build_aligned_ByteString (projT2 v'), ce'))))
      -> (forall v ce'',
             format_list format_A l ce ↝ (v, ce'') ->
             refine (c ce'') (ret (build_aligned_ByteString (projT2 (v' ce'')), ce' ce'')))
      -> (forall a : A, In a l -> A_OK a)
      -> refine (((format_list format_A l)
                    ThenC c) ce)
                (ret (let (v, ce'') := align_format_list encode_A l ce in
                      build_aligned_ByteString
                        (Vector.append (projT2 v) (projT2 (v' ce''))),
                      let (v, ce'') := align_format_list encode_A l ce in
                      ce' ce'')).
  Proof.
    intros.
    etransitivity.
    eapply AlignedFormatThenC.
    rewrite (optimize_align_format_list A_OK format_A encode_A); try eassumption.
    match goal with
      |- context [let (v, c) := ?z in ret (@?b v c)] =>
      rewrite (zeta_inside_ret z _)
    end.
    rewrite zeta_to_fst; simpl.
    instantiate (2 := fun ce => fst (_ ce)).
    instantiate (1 := fun ce => snd (_ ce)).
    simpl; reflexivity.
    intros; eapply H0; eauto.
    simpl.
    rewrite !zeta_to_fst; simpl; reflexivity.
  Qed.

  Fixpoint ListAlignedDecodeM {A} {m}
           (A_decode_align : forall {m}, AlignedDecodeM A m)
           (n : nat)
    : AlignedDecodeM (list A) m :=
    match n with
    | 0 => return (@nil A)
    | S s' => a <- A_decode_align;
                l <- ListAlignedDecodeM (@A_decode_align) s';
              return (a :: l)
    end%AlignedDecodeM%list.

  Lemma AlignedDecodeListM {A C : Type}
        (A_decode : DecodeM (A * _) ByteString)
        (A_decode_align : forall {m}, AlignedDecodeM A m)
        (n : nat)
    : forall (t : list A -> DecodeM (C * _) ByteString)
             (t' : list A -> forall {numBytes}, AlignedDecodeM C numBytes),
      (DecodeMEquivAlignedDecodeM A_decode (@A_decode_align))
      -> (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(l, bs, cd') <- decode_list A_decode n v cd;
                          t l bs cd')
           (fun numBytes => l <- ListAlignedDecodeM (@A_decode_align) n;
                            t' l)%AlignedDecodeM%list.
  Proof.
    induction n; simpl; intros; eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply ReturnAlignedDecodeM_LeftUnit;
                                                      reflexivity | reflexivity ].
    eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: set_evars; erewrite !DecodeBindOpt2_assoc; subst_evars; higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply BindAlignedDecodeM_assoc;
                                                      reflexivity | higher_order_reflexivity ].
    simpl.
    eapply Bind_DecodeMEquivAlignedDecodeM; intros.
    eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: set_evars; erewrite !DecodeBindOpt2_assoc; subst_evars; higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply BindAlignedDecodeM_assoc;
                                                      reflexivity | higher_order_reflexivity ].
    simpl.
    eapply IHn; eauto.
    intros.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [eapply ReturnAlignedDecodeM_LeftUnit | higher_order_reflexivity].
    eapply H0.
  Qed.

  (* Fixpoint list_of_vector_range {A} {sz: nat} n (from: Fin.t (n + sz)) (to: Fin.t sz) (v: Vector.t A (n + sz)) (acc: list A) : list A := *)
  (*   let to' := (eq_rect (sz + n) _ (Fin.L n to) (n + sz) (plus_comm _ _)) in *)
  (*   let acc' := List.cons (Vector.nth v to') acc in *)
  (*   if Fin.eq_dec from to' then acc' *)
  (*   else *)
  (*     match to in Fin.t sz return forall (from: Fin.t (n + sz)) (v: Vector.t A (n + sz)), list A with *)
  (*     | Fin.FS sz pred => *)
  (*       fun from v => @list_of_vector_range A sz (n + 1) *)
  (*                                        (eq_rect (n + S sz) _ from (n + 1 + sz) ltac:(omega)) *)
  (*                                        pred *)
  (*                                        (eq_rect (n + S sz) _ v (n + 1 + sz) ltac:(omega)) *)
  (*                                        acc' *)
  (*     | Fin.F1 _ => *)
  (*       fun _ _ => acc' *)
  (*     end from v. *)

  (* fun (v: ByteBuffer.t m) idx env => *)
  (*   match len with *)
  (*   | 0 => Some ((List.nil, idx), env) *)
  (*   | S len' => *)
  (*     match Fin.of_nat idx m with *)
  (*     | inleft fidx => *)
  (*       let last_idx := idx + len' in *)
  (*       match Fin.of_nat last_idx m with *)
  (*       | inleft flast_idx => Some ((list_of_vector_range 0 fidx flast_idx v [], last_idx), addD env (8 * len)) *)
  (*       | inright _ => None *)
  (*       end *)
  (*     | inright _ => None *)
  (*     end *)
  (*   end. *)

  Definition list_of_bytebuffer_range {sz: nat} (from: nat) (len: nat) (v: ByteBuffer.t sz) : list Core.char :=
    List.firstn len (List.skipn from (Vector.to_list v)).

  Definition CharListAlignedDecodeM {cache : Cache} {cacheAddNat: CacheAdd cache nat} {m : nat} (len: nat) : @AlignedDecodeM cache (list Core.char) m :=
    fun (v: ByteBuffer.t m) idx env =>
      let lastidx := idx + len in
      if NPeano.leb lastidx m then
        Some ((list_of_bytebuffer_range idx len v, lastidx, addD env (8 * len)))
      else
        None.

  Lemma AlignedDecodeCharListM {C : Type}
        (n : nat)
    : forall (t : list Core.char -> DecodeM (C * _) ByteString)
        (t' : list Core.char -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
          (fun v cd => `(l, bs, cd') <- decode_list decode_word n v cd;
                      t l bs cd')
          (fun numBytes => l <- CharListAlignedDecodeM n;
                          t' l)%AlignedDecodeM%list.
  Admitted.

  Lemma AlignedFormatListDoneC {A}
        (A_OK : A -> Prop)
        format_A
        (encode_An : A -> CacheFormat -> nat)
        (encode_A1 : forall a ce,  t (word 8) (encode_An a ce))
        (encode_A2 : A -> CacheFormat -> CacheFormat)
    : forall (l : list A) ce,
      (forall (a : A) (ce : CacheFormat),
          A_OK a
          -> refine (format_A a ce) (ret (build_aligned_ByteString (encode_A1 a ce), encode_A2 a ce)))
      -> (forall a : A, In a l -> A_OK a)
      -> refine (((format_list format_A l) DoneC) ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_format_list (fun a ce => (existT _ _ (encode_A1 a ce), encode_A2 a ce)) l ce))),
                      let (v, ce'') := align_format_list (fun a ce => (existT _ _ (encode_A1 a ce), encode_A2 a ce)) l ce in
                      ce'')).
  Proof.
    intros.
    etransitivity.
    eapply AlignedFormatDoneC.
    rewrite (optimize_align_format_list A_OK format_A (fun a ce => (existT _ _ (encode_A1 a ce), encode_A2 a ce))); try eassumption.
    match goal with
      |- context [let (v, c) := ?z in ret (@?b v c)] =>
      rewrite (zeta_inside_ret z _)
    end.
    rewrite zeta_to_fst; simpl.
    instantiate (2 := fun ce => fst (_ ce)).
    instantiate (1 := fun ce => snd (_ ce)).
    simpl; reflexivity.
    intros; rewrite zeta_to_fst; simpl; reflexivity.
  Qed.

  Fixpoint AlignedEncodeList' {A}
           (A_format_align : forall sz, AlignedEncodeM (S := A) sz)
           (sz : nat)
           v
           idx
           As
           env :=
      match As with
      | nil => if NPeano.ltb idx (S sz) then @ReturnAlignedEncodeM _ (list A) _ v idx nil env else None
      | a :: As' => Ifopt (A_format_align sz v idx a env) as a' Then
                                                                AlignedEncodeList' A_format_align sz (fst (fst a'))
                                                              (snd (fst a'))
                                                              As' (snd a')
                                                              Else None
    end.

  Fixpoint buffer_blit_list' {sz} start (l: list Core.char) (v: ByteBuffer.t sz) :=
    match l with
    | List.nil => v
    | List.cons h t => buffer_blit_list' (S start) t (set_nth' v start h)
    end.

  Definition buffer_blit_list {sz} start (l: list Core.char) (v: ByteBuffer.t sz) :=
    let len := List.length l in
    if NPeano.leb (start + len) sz then
      Some (buffer_blit_list' start l v, len)
    else None.

  Definition AlignedEncodeCharList
    : forall sz, AlignedEncodeM (S := list Core.char) sz :=
    fun sz (v: ByteBuffer.t sz) idx chars env =>
      match buffer_blit_list idx chars v with
      | Some (v', len) =>
        Some ((v', idx + len), addE env (8 * len))
      | None => None
      end.

  Lemma CorrectAlignedEncoderForFormatCharList :
    CorrectAlignedEncoder (format_list (format_word (sz := 8)))
                          AlignedEncodeCharList.
  Admitted.

  Definition AlignedEncodeList {A}
             (A_format_align : forall sz, AlignedEncodeM (S := A) sz)
    : forall sz, AlignedEncodeM (S := list A) sz :=
    AlignedEncodeList' A_format_align.

  Lemma CorrectAlignedEncoderForFormatList {A}
        format_A
        encode_A
    : (CorrectAlignedEncoder format_A encode_A)
      -> CorrectAlignedEncoder (format_list format_A)
                               (@AlignedEncodeList A encode_A).
  Proof.
    unfold CorrectAlignedEncoder; intros.
    eexists ((fix AlignedEncodeList (As : list A) env :=
               match As with
               | nil => Some (mempty, env)
               | a :: As' => `(t1, env') <- projT1 X a env;
                             `(t2, env'') <- AlignedEncodeList As' env';
                             Some (mappend t1 t2, env'')
               end)); split; [ | split ].
    - induction s; intros; simpl; eauto.
      + injections; reflexivity.
      + destruct X as [encode_A' [? [? ?] ] ]; simpl in *.
        destruct (encode_A' a env) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        unfold Bind2.
        rewrite r, refineEquiv_bind_unit; eauto.
        destruct ((fix AlignedEncodeList (As : list A) (env : CacheFormat) {struct As} :
                          option (ByteString * CacheFormat) :=
                          match As with
                          | [] => Some (ByteString_id, env)
                          | a :: As' =>
                              `(t1, env') <- encode_A' a env;
                              `(t2, env'') <- AlignedEncodeList As' env';
                              Some (ByteString_enqueue_ByteString t1 t2, env'')
                          end)) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        rewrite IHs, refineEquiv_bind_unit; simpl; eauto.
        injections; reflexivity.
    - induction s; intros; simpl; eauto.
      + injections; reflexivity.
      + destruct X as [encode_A' [? [? ?] ] ]; simpl in *.
        destruct (encode_A' a env) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        destruct ((fix AlignedEncodeList (As : list A) (env : CacheFormat) {struct As} :
                          option (ByteString * CacheFormat) :=
                          match As with
                          | [] => Some (ByteString_id, env)
                          | a :: As' =>
                              `(t1, env') <- encode_A' a env;
                              `(t2, env'') <- AlignedEncodeList As' env';
                              Some (ByteString_enqueue_ByteString t1 t2, env'')
                          end)) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        injections.
        erewrite padding_ByteString_enqueue_ByteString, e, IHs; eauto.
    - unfold EncodeMEquivAlignedEncodeM; intros.
      pose proof (Append_EncodeMEquivAlignedEncodeM (Basics.compose (projT1 X) fst)
                                                    (Basics.compose (fix AlignedEncodeList (As : list A) env :=
                                                                match As with
                                                                | nil => Some (mempty, env)
                                                                | a :: As' => `(t1, env') <- projT1 X a env;
                                                                              `(t2, env'') <- AlignedEncodeList As' env';
                                                                              Some (mappend t1 t2, env'')
                                                                end) snd)).
      revert env idx. induction s; intros.
      + admit.
      +

        destruct X as [encode_A' [? [? ?] ] ]; simpl in *.
        destruct (encode_A' a env) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        destruct ((fix AlignedEncodeList (As : list A) (env : CacheFormat) {struct As} :
                          option (ByteString * CacheFormat) :=
                          match As with
                          | [] => Some (ByteString_id, env)
                          | a :: As' =>
                              `(t1, env') <- encode_A' a env;
                              `(t2, env'') <- AlignedEncodeList As' env';
                              Some (ByteString_enqueue_ByteString t1 t2, env'')
                          end)) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
  Admitted.
  (*injections.
        revert b0.
        rewrite numBytes_ByteString_enqueue_ByteString; intros.
        destruct (proj1 (e0 env a idx) _ _ Heqo) with
            (v1 := v1) (v := fst (Vector_split _ _ v))
            (v2 := append (snd (Vector_split _ _ v)) v2); split_and.
        eapply e; eauto.
        rewrite ByteString_enqueue_ByteString_assoc in H2.
        eapply (IHs _ (idx + numBytes b) _ m (append v1 (fst (Vector_split _ _ v)))  (snd (Vector_split _ _ v))) in Heqo0;
          destruct_ex; split_and.
        assert (idx + numBytes b + (numBytes b0 + m) =
                idx + (numBytes b + numBytes b0 + m)) by Omega.omega.
        eexists (eq_rect _ _ x0 _ H).
        replace (encode_A (idx + (numBytes b + numBytes b0 + m)) (append v1 (append v v2)) idx a env)
          with (Some (eq_rect _ (fun m => t Core.char (idx + m) )%type x _ (plus_assoc (numBytes b) (numBytes b0) m), idx + numBytes b, c)); simpl.
        split.
        admit.
        admit.
        admit.
        admit.
        eapply e; eauto.
        (*generalize (PeanoNat.Nat.add_assoc (numBytes b) (numBytes b0) m); intros.
        assert (exists (v' : Vector.t _ (numBytes b)), b = build_aligned_ByteString v').
        { eexists (byteString b); destruct b; simpl.
          apply e in Heqo; simpl in Heqo; generalize Heqo front paddingOK; clear; intro.
          rewrite Heqo; intro; shatter_word front; intros.
          eapply byteString_f_equal; simpl; eauto.
          instantiate (1 := eq_refl _); reflexivity. }
        admit. *)
      + revert env idx t env' numBytes' v H H0; induction s; intros.
        * injections.
          simpl.
          rewrite (proj2 (NPeano.Nat.ltb_nlt idx (S numBytes'))); eauto.
          intro.
          rewrite length_ByteString_id in H0.
          Omega.omega.
        * destruct X as [encode_A' [? [? ?] ] ]; simpl in *.
          unfold DecodeBindOpt, BindOpt in H.
          destruct (encode_A' a env) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
          pose proof (proj2 (e0 env a idx)).
          erewrite (proj1 H1); simpl; eauto.
          edestruct (proj1 (e0 env a idx) _ _ Heqo).
          eapply e; eauto.
          admit.
      + revert env idx t env' numBytes' v H H0; induction s; intros.
        * injections; simpl in H0; Omega.omega.
        * simpl.
          shelve.
      + revert env idx numBytes' v H; induction s; intros.
        * discriminate.
        * simpl.
          admit.

  Admitted.
  (*(* injections.
          simpl.
          rewrite (proj2 (NPeano.Nat.ltb_nlt idx (S numBytes'))); eauto.
          intro.
          rewrite length_ByteString_id in H0.
          Omega.omega. *)
        * simpl.
          destruct (encode_A numBytes' v idx a env) as [ [? ?] | ] eqn: ?; simpl; eauto.
          eapply IHs.
          shelve.
          shelve.

        *  simpl; eapply Return_EncodeMEquivAlignedEncodeM.
      + simpl; destruct (X a) as [encode_A' [? [? ?] ] ];
          eapply Append_EncodeMEquivAlignedEncodeM; eauto.
      (*eapply (IHs _ (idx + numBytes b) _ m (append v1 (fst (Vector_split _ _ v)))  (snd (Vector_split _ _ v))) in Heqo0;
          destruct_ex; split_and.
        assert (idx + numBytes b + (numBytes b0 + m) =
                idx + (numBytes b + numBytes b0 + m)) by Omega.omega.
        eexists (eq_rect _ _ x0 _ H).
        replace (encode_A (idx + (numBytes b + numBytes b0 + m)) (append v1 (append v v2)) idx a env)
          with (Some (eq_rect _ (fun m => t Core.char (idx + m) )%type x _ (plus_assoc (numBytes b) (numBytes b0) m), idx + numBytes b, c)); simpl.
        split.
        generalize (PeanoNat.Nat.add_assoc (numBytes b) (numBytes b0) m); intros.

        revert x0 H3 H4.
        clear.
        destruct H.
        rewrite (plus_assoc idx (numBytes b) (numBytes b0)).
        rewrite <- H3.
        erewrite Vector_append_assoc in H3.

        rewrite
        rewrite H.



        destruct Heqo0.
        replace (numBytes (ByteString_enqueue_ByteString b b0)) with
            (numBytes b + numBytes b0) at 1.
        setoid_rewrite numBytes_ByteString_enqueue_ByteString.

        rewrite H1.
        destruct_ex

        injections. *)



      +



  Qed. *) *)

End AlignedList.
