Require Import
        Fiat.BinEncoders.Env.Common.Specs
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
