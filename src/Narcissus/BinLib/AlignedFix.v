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
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedDecoders.

Require Import
        Bedrock.Word.

Section AlignedFix.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Lemma byte_align_Fix_encode {A}
        (lt_A : A -> A -> Prop)
        (wf_lt_A : well_founded lt_A)
    : forall
      (body : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat)
              -> FixComp.funType [A; CacheFormat] (ByteString * CacheFormat))
      (body' : forall r : A,
          (forall r' : A, lt_A r' r -> FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat)) ->
          FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat))

      (refine_body_OK : forall (r : A)
                               (x : A -> CacheFormat  ->
                                    Comp (ByteString * CacheFormat))
                               (y : forall r' : A,
                                   lt_A r' r ->
                                   CacheFormat ->
                                   {n : _ & Vector.t (word 8) n} * CacheFormat),
          (forall (a' : A) (wf_r : lt_A a' r) (ce : CacheFormat),
              refine (x a' ce)
                     (ret (let (v, ce') := y a' wf_r ce in
                           (build_aligned_ByteString (projT2 v), ce'))))
          -> forall ce, refine (body x r ce) (ret (let (v, ce') := body' r y ce in
                                                   (build_aligned_ByteString (projT2 v), ce'))))

      (body_monotone : forall rec rec' : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat),
          FixComp.refineFun rec rec' -> FixComp.refineFun (body rec) (body rec'))
      (body'_monotone : forall (x0 : A)
                               (f
                                  g : {y : A | lt_A y x0} ->
                                      CacheFormat ->
                                      {n : nat & t (word 8) n} * (CacheFormat)),
          (forall y : {y : A | lt_A y x0}, f y = g y) ->
          body' x0 (fun (a' : A) (lt_a' : lt_A a' x0) => f (exist (fun a'0 : A => lt_A a'0 x0) a' lt_a')) =
          body' x0 (fun (a' : A) (lt_a' : lt_A a' x0) => g (exist (fun a'0 : A => lt_A a'0 x0) a' lt_a')))
      (a : A) (ce : CacheFormat),
      refine (FixComp.LeastFixedPointFun.LeastFixedPoint body a ce)
             (ret (let (v, ce') := Fix wf_lt_A _ body' a ce in
                   (build_aligned_ByteString (projT2 v), ce'))).
  Proof.
    intros.
    unfold FixComp.LeastFixedPointFun.LeastFixedPoint, respectful_hetero; intros.
    simpl.
    revert ce; pattern a; eapply (well_founded_ind wf_lt_A).
    simpl; intros.
    pose proof (proj1 (Frame.Is_GreatestFixedPoint (O := @FixComp.LeastFixedPointFun.funDefOps [A; CacheFormat] (ByteString * CacheFormat)) _ (body_monotone))); etransitivity.
    eapply H0; eauto.
    destruct (Fix wf_lt_A
                  (fun _ : A =>
                     CacheFormat ->
                     {n : nat & t (word 8) n} * (CacheFormat)) body' x ce) eqn: ?.
    pose proof (Fix_eq _ _ wf_lt_A _ (fun a rec => body' a (fun a' lt_a' => rec (exist (fun a' => lt_A a' a) a' lt_a')))).
    simpl in H1; unfold Fix_sub, Fix_F_sub in H1; unfold Fix, Fix_F in Heqp.
    rewrite H1 in Heqp; simpl in Heqp; clear H1; eauto.
    etransitivity.
    eapply refine_body_OK.
    instantiate (1 := (fun (a' : A) (_ : lt_A a' x) =>
                         (fix Fix_F_sub (x0 : A) (r : Acc lt_A x0) {struct r} :
                            CacheFormat ->
                            {n : nat & t (word 8) n} * (CacheFormat) :=
                            body' x0 (fun (a'0 : A) (lt_a'0 : lt_A a'0 x0) => Fix_F_sub a'0 (Acc_inv r lt_a'0))) a'
                                                                                                                 (wf_lt_A a'))).
    eapply H; eauto.
    rewrite Heqp; reflexivity.
  Qed.

  Lemma byte_align_Fix_encode_inv {A}
        (A_OK : A -> Prop)
        (lt_A : _ -> _ -> Prop)
        (wf_lt_A : well_founded lt_A)
    : forall
      (body : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat)
              -> FixComp.funType [A; CacheFormat] (ByteString * CacheFormat))
      (body' : forall r : { a : _ & A_OK a},
          (forall r' : { a : _ & A_OK a},
              lt_A r' r
              -> FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat)) ->
          FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat))
      (refine_body_OK : forall (r : { a : _ & A_OK a})
                               (x : A -> CacheFormat ->
                                    Comp (ByteString * CacheFormat))
                               (y : forall r' : { a : _ & A_OK a},
                                   lt_A r' r ->
                                   CacheFormat ->
                                   {n : _ & Vector.t (word 8) n} * CacheFormat),
          (forall (a' : { a : _ & A_OK a}) (wf_r : lt_A a' r) (ce : CacheFormat),
              refine (x (projT1 a') ce)
                     (ret (let (v, ce') := y a' wf_r ce in
                           (build_aligned_ByteString (projT2 v), ce'))))
          -> forall ce, refine (body x (projT1 r) ce) (ret (let (v, ce') := body' r y ce in
                                                            (build_aligned_ByteString (projT2 v), ce'))))

      (body_monotone : forall rec rec' : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat),
          FixComp.refineFun rec rec' -> FixComp.refineFun (body rec) (body rec'))
      (body'_monotone : forall (x0 : { a : _ & A_OK a})
                               (f
                                  g : {y : { a : _ & A_OK a} | lt_A y x0} ->
                                      CacheFormat ->
                                      {n : nat & t (word 8) n} * (CacheFormat)),
          (forall y : {y : { a : _ & A_OK a} | lt_A y x0}, f y = g y) ->
          body' x0 (fun (a' : { a : _ & A_OK a}) (lt_a' : lt_A a' x0) => f (exist (fun a'0 : { a : _ & A_OK a} => lt_A a'0 x0) a' lt_a')) =
          body' x0 (fun (a' : { a : _ & A_OK a}) (lt_a' : lt_A a' x0) => g (exist (fun a'0 : { a : _ & A_OK a} => lt_A a'0 x0) a' lt_a')))
      (a : A) (ce : CacheFormat) (a_OK : A_OK a),
      refine (FixComp.LeastFixedPointFun.LeastFixedPoint body a ce)
             (ret (let (v, ce') := Fix wf_lt_A _ body' (existT _ _ a_OK) ce in
                   (build_aligned_ByteString (projT2 v), ce'))).
  Proof.
    (* 8.4 script *)
    intros.
    unfold FixComp.LeastFixedPointFun.LeastFixedPoint, respectful_hetero; intros.
    simpl.
    replace a with (projT1 (existT _ a a_OK)) at 1.
    revert ce; pattern (existT _ a a_OK); eapply (well_founded_ind wf_lt_A).
    simpl; intros.
    pose proof (proj1 (Frame.Is_GreatestFixedPoint (O := @FixComp.LeastFixedPointFun.funDefOps [A; CacheFormat] (ByteString * CacheFormat)) _ (body_monotone))); etransitivity.
    eapply H0; eauto.
    destruct ( Fix wf_lt_A
                   (fun _ : {a0 : A & A_OK a0} =>
                      CacheFormat ->
                      {n : nat & t (word 8) n} * (CacheFormat)) body' x ce) eqn: ?.
    pose proof (Fix_eq _ _ wf_lt_A _ (fun a rec => body' a (fun a' lt_a' => rec (exist (fun a' => lt_A a' a) a' lt_a')))).
    simpl in H1; unfold Fix_sub, Fix_F_sub in H1; unfold Fix, Fix_F in Heqp.
    rewrite H1 in Heqp; simpl in Heqp; clear H1; eauto.
    etransitivity.
    eapply refine_body_OK.
    instantiate (1 := fun (a' : {a0 : A & A_OK a0}) (_ : lt_A a' x) =>
                        (fix Fix_F_sub (x0 : {a0 : A & A_OK a0}) (r : Acc lt_A x0) {struct r} :
                           CacheFormat ->
                           {n : nat & t (word 8) n} * (CacheFormat) :=
                           body' x0 (fun (a'0 : {a0 : A & A_OK a0}) (lt_a'0 : lt_A a'0 x0) => Fix_F_sub a'0 (Acc_inv r lt_a'0))) a'
                                                                                                                                 (wf_lt_A a')).
    admit. (* works in 8.4: eapply H; eauto. *)
    admit. (* works in 8.4: rewrite Heqp; reflexivity.*)
    reflexivity.
  Qed.

End AlignedFix.
