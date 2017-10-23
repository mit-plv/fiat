Require Import
        Fiat.Computation
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Lib2.WordOpt.
Require Import
        Coq.Vectors.Vector
        Bedrock.Word.

Section AlignWord.
  Context {len : nat}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : QueueTransformerOpt transformer bool}.

  Variable addD_addD_plus :
    forall cd n m, addD (addD cd n) m = addD cd (n + m).

  Lemma If_Opt_Then_Else_DecodeBindOpt {A ResultT ResultT'}
    : forall (a_opt : option A)
             (t : A -> option (ResultT * B * CacheDecode))
             (e : option (ResultT * B * CacheDecode))
             (k : _ -> _ -> _ -> option (ResultT' * B * CacheDecode)),
      (`(w, b', cd') <- Ifopt a_opt as a Then t a Else e;
         k w b' cd') =
      (Ifopt a_opt as a Then
                        (`(w, b', cd') <- t a; k w b' cd')
                        Else (`(w, b', cd') <- e; k w b' cd')).
  Proof.
    destruct a_opt; simpl; intros; reflexivity.
  Qed.

  Fixpoint split1' (sz sz' : nat) : word (sz + sz') -> word sz :=
    match sz return word (sz + sz') -> word sz with
    | 0 => fun _ => WO
    | S n' => fun w => SW_word (word_split_hd w)
                               (split1' n' sz' (word_split_tl w))
    end.

  Fixpoint split2' (sz sz' : nat) : word (sz + sz') -> word sz' :=
    match sz return word (sz + sz') -> word sz' with
    | 0 => fun w => w
    | S n' => fun w => split2' n' sz' (word_split_tl w)
    end.

  Lemma CollapseWord {ResultT}
    : forall sz sz' (b : B)
             (cd : CacheDecode)
             (k : _ -> _ -> _ -> _ -> option (ResultT * B * CacheDecode)),
      (`(w, b', cd') <- decode_word (sz:=sz) b cd;
         `(w', b', cd') <- decode_word (sz:=sz') b' cd';
         k w w' b' cd') =
      (`(w , b', cd') <- decode_word (sz:=sz + sz') b cd;
         k (split1' sz sz' w)
           (split2' sz sz' w) b' cd').
  Proof.
    unfold decode_word; repeat setoid_rewrite If_Opt_Then_Else_DecodeBindOpt; simpl.
    induction sz; simpl; intros.
    - rewrite !If_Opt_Then_Else_DecodeBindOpt; simpl.
      rewrite addD_addD_plus; reflexivity.
    - destruct (dequeue_opt b) as [ [? ?] | ]; simpl; eauto.
      pose proof (IHsz sz' b1 (addD cd 1) (fun w => k (SW_word b0 w))).
      destruct (decode_word' sz b1) as [ [? ?] | ]; simpl in *.
      + rewrite !If_Opt_Then_Else_DecodeBindOpt;
          rewrite !If_Opt_Then_Else_DecodeBindOpt in H; simpl in *;
            rewrite !addD_addD_plus in H;
            rewrite !addD_addD_plus; simpl in *.
        rewrite H.
        destruct (decode_word' (sz + sz') b1) as [ [? ?] | ]; simpl; eauto.
        repeat f_equal; clear.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w0; simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w0; simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w0; simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
      + destruct (decode_word' (sz + sz') b1) as [ [? ?] | ]; simpl in *; eauto.
        rewrite addD_addD_plus in H; simpl in *.
        rewrite H; repeat f_equal; clear.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w; simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w; simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w; simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
  Qed.

  Variable addE_addE_plus :
    forall (ce : CacheEncode) (n m : nat), addE (addE ce n) m = addE ce (n + m).

  Lemma encode_word_S {n}
    : forall (w : word (S n)) (bs : B),
      encode_word' (S n) w bs =
      encode_word' n (word_split_tl w) (enqueue_opt (word_split_hd w) bs).
  Proof.
    intros; pose proof (shatter_word_S w); destruct_ex; subst.
    simpl.
    clear; revert x; induction x0; simpl; intros.
    - simpl; reflexivity.
    - rewrite IHx0.
      reflexivity.
  Qed.

  Lemma word_split_hd_SW_word {n}
    : forall b (w : word n), 
      word_split_hd (SW_word b w) = b.
  Proof.
    induction w; simpl; intros; eauto.
  Qed.

  Lemma word_split_tl_SW_word {n}
    : forall b (w : word n), 
      word_split_tl (SW_word b w) = w.
  Proof.
    induction w; simpl; intros; eauto.
    f_equal; eauto.
  Qed.
  
  Lemma CollapseEncodeWord
    : forall {sz sz'} (w : word sz) (w' : word sz') k ce,
      refine (((encode_word_Spec w)
                ThenC (encode_word_Spec w')
                ThenC k) ce)
             (((encode_word_Spec (combine w' w))
                 ThenC k) ce).
  Proof.
    intros; unfold compose, encode_word_Spec, Bind2.
    autorewrite with monad laws.
    simpl; rewrite addE_addE_plus.
    rewrite Plus.plus_comm; f_equiv; intro.
    rewrite transform_assoc.
    destruct a; simpl.
    f_equiv; f_equiv; f_equiv.
    revert sz' w'; induction w; simpl; intros.
    - rewrite transform_id_left.
      generalize transform_id; clear; induction w'; intros.
      + reflexivity.
      + simpl; rewrite IHw'; reflexivity.
    - rewrite !enqueue_opt_encode_word.
      replace (encode_word' (sz' + S n) (combine w' (WS b0 w)) transform_id)
      with (encode_word' (S sz' + n) (combine (SW_word b0 w') w) transform_id).
      + rewrite <- IHw.
        simpl; rewrite encode_word_S.
        rewrite <- transform_assoc, word_split_tl_SW_word, word_split_hd_SW_word.
        f_equal. 
        clear; induction w'.
        * simpl; rewrite transform_id_right; reflexivity.
        * simpl; rewrite !enqueue_opt_encode_word.
          rewrite <- IHw'.
          rewrite transform_assoc; reflexivity.
      + clear; revert n w; induction w'; intros.
        * simpl; eauto.
        * simpl; rewrite <- IHw'; reflexivity.
  Qed.

  Lemma encode_SW_word {n}
    : forall b (w : word n) ce,
          refine (encode_word_Spec (SW_word b w) ce)
                 (`(bs, ce') <- encode_word_Spec w (addE ce 1);
                    ret (transform (enqueue_opt b transform_id) bs, ce')).
  Proof.
    induction n; simpl; intros.
    - shatter_word w; simpl.
      unfold encode_word_Spec; simpl.
      autorewrite with monad laws.
      simpl; rewrite addE_addE_plus; rewrite transform_id_right; reflexivity.
    - pose proof (shatter_word_S w); destruct_ex; subst.
      simpl.
      unfold encode_word_Spec; simpl.
      autorewrite with monad laws; simpl.
      assert (computes_to (`(bs, ce') <- ret (encode_word' n x0 transform_id, addE (addE ce 1) n);
                           ret (transform (enqueue_opt b transform_id) bs, ce'))
                          (transform (enqueue_opt b transform_id) (encode_word' n x0 transform_id), addE (addE ce 1) n)) by repeat computes_to_econstructor.
      pose proof (IHn b x0 ce _ H).
      unfold encode_word_Spec in H0.
      computes_to_inv; inversion H0; subst.
      rewrite H2.
      rewrite enqueue_transform_opt.
      rewrite addE_addE_plus.
      reflexivity.
  Qed.
  
  Lemma If_Opt_Then_Else_DecodeBindOpt_swap {A C ResultT : Type}
    : forall (a_opt : option A)
             (b : B)
             (cd : CacheDecode)
             (dec_c : B -> CacheDecode -> option (C * B * CacheDecode))
             (k : A -> C -> B -> CacheDecode -> option (ResultT * B * CacheDecode)),
      (`(a, b', cd') <- Ifopt a_opt as a Then Some (a, b, cd) Else None;
         `(c, b', cd') <- dec_c b' cd';
         k a c b' cd') =
      (`(c, b', cd') <- dec_c b cd;
         `(a, b', cd') <- Ifopt a_opt as a Then Some (a, b', cd') Else None;
         k a c b' cd').
  Proof.
    destruct a_opt; simpl; intros; eauto.
    destruct (dec_c b cd) as [ [ [? ?] ? ] | ]; reflexivity.
  Qed.

  Lemma If_Then_Else_Bind {sz} {C ResultT : Type}
    : forall (w w' : word sz)
             (b : B)
             (cd : CacheDecode)
             (dec_c : B -> CacheDecode -> option (C * B * CacheDecode))
             (k : C -> B -> CacheDecode -> option (ResultT * B * CacheDecode)),
      (if weq w w' then
         `(c, b', cd') <- dec_c b cd;
           k c b' cd'
       else
         None) =
      (`(c, b', cd') <- dec_c b cd;
         if weq w w' then
           k c b' cd'
         else None).
  Proof.
    intros; find_if_inside; eauto.
    destruct (dec_c b cd) as [ [ [? ?] ? ] | ]; reflexivity.
  Qed.

End AlignWord.

Ltac collapse_word addD_addD_plus :=
  match goal with
  | |- DecodeBindOpt2
         (decode_word (sz := ?sz) ?b ?cd)
         (fun w b' cd' =>
            DecodeBindOpt2 (decode_word (sz := ?sz') b' cd')
                           (fun w' b' cd' => @?k w w' b' cd')) = _ =>
    etransitivity;
    [let H := fresh in
     pose proof (@CollapseWord _ _ _ _ _ addD_addD_plus _ sz sz' b cd k);
     apply H | ]
  end.
