Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.FixListOpt.
Require Export
        Coq.Lists.List.

(* Commenting out until useful again. *)
(*Section SteppingList.
  Context {A : Type}. (* data type *)
  Context {B : Type}. (* bin type *)
  Context {P : Type}. (* cache pointer type *)
  Context {cache : Cache}.
  Context {cache_inv : CacheDecode -> Prop}.
  Context {transformer : Transformer B}.

  Variable A_halt : A.
  Variable A_halt_dec : forall a, {a = A_halt} + {~ a = A_halt}.
  Variable A_predicate : A -> Prop.
  Variable A_predicate_rest : A -> B -> Prop.
  Variable A_predicate_halt : A_predicate A_halt.
  Variable A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode).
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).
  Variable A_decode_pf : encode_decode_correct_f cache transformer A_predicate A_encode_Spec A_decode cache_inv.
  Variable A_decode_lt
    : forall  (b : B)
              (cd : CacheDecode)
              (a : A)
              (b' : B)
              (cd' : CacheDecode),
      A_decode b cd = Some (a, b', cd')
      -> lt_B b' b.

  Variable P_predicate : P -> Prop.
  Variable P_predicate_dec : forall p, {P_predicate p} + {~ P_predicate p}.
  Variable P_encode_Spec : P -> CacheEncode -> Comp (B * CacheEncode).
  Variable P_decode : B -> CacheDecode -> option (P * B * CacheDecode).
  Variable P_decode_pf : encode_decode_correct_f cache transformer P_predicate P_encode_Spec P_decode cache_inv.
  Variable P_decode_le :
    forall (b1 : B)
           (cd1 : CacheDecode)
           (a : P)
           (b' : B)
           (cd' : CacheDecode),
      P_decode b1 cd1 = Some (a, b', cd') -> le_B b' b1.

  Variable X_encode_Spec : bool -> CacheEncode -> Comp (B * CacheEncode).
  Variable X_decode : B -> CacheDecode -> option (bool * B * CacheDecode).
  Variable X_decode_pf : encode_decode_correct_f cache transformer (fun _ => True) X_encode_Spec X_decode cache_inv.
  Variable X_decode_le :
    forall (b1 : B)
           (cd1 : CacheDecode)
           (a : bool)
           (b' : B)
           (cd' : CacheDecode),
      X_decode b1 cd1 = Some (a, b', cd') -> le_B b' b1.

  Variable cacheAdd : CacheAdd cache (list A * P).
  Variable cacheGet : CacheGet cache (list A) P.
  Variable cachePeek : CachePeek cache P.

  Variable cacheGet_OK :
    forall env p l,
      cache_inv env
      -> getD env p = Some l
      -> forall x,
          In x l
          -> A_predicate x /\ ~ x = A_halt.

  Variable cacheAdd_OK :
    forall env p l,
      cache_inv env
      -> (forall x,
             In x l
             -> A_predicate x /\ ~ x = A_halt)
        -> cache_inv (addD env (l, p)).

  Fixpoint encode_list_step_Spec (l : list A ) (ce : CacheEncode)
    : Comp (B * CacheEncode) :=
    match l with
    | nil => `(b1, e1) <- X_encode_Spec false ce;
             `(b2, e2) <- A_encode_Spec A_halt e1;
             ret (transform b1 b2, e2)
    | cons x l' =>
      match getE ce l with
      | Some position =>
        b <- {b : bool | True};
          If b Then (* Nondeterministically pick whether to use a cached value. *)
           If (P_predicate_dec position)
           Then (`(b1, e1) <- X_encode_Spec true ce;
                `(b2, e2) <- P_encode_Spec position e1;
                  ret (transform b1 b2, e2))
           Else (`(b1, e1) <- X_encode_Spec false ce;
             `(b2, e2) <- A_encode_Spec x e1;
             `(b3, e3) <- encode_list_step_Spec l' e2;
             ret (transform (transform b1 b2) b3, addE e3 (l, peekE ce)))
           Else
           (`(b1, e1) <- X_encode_Spec false ce;
              `(b2, e2) <- A_encode_Spec x e1;
              `(b3, e3) <- encode_list_step_Spec l' e2;
              ret (transform (transform b1 b2) b3, addE e3 (l, peekE ce)))
      | None => `(b1, e1) <- X_encode_Spec false ce;
                     `(b2, e2) <- A_encode_Spec x e1;
                     `(b3, e3) <- encode_list_step_Spec l' e2;
                     ret (transform (transform b1 b2) b3, addE e3 (l, peekE ce))
      end
    end%comp.

  (* Decode now uses a measure on the length of B *)

  Lemma lt_B_trans :
    forall b
           (b1 : {b' : B | le_B b' b})
           (b2 : {b' : B | lt_B b' (` b1)}),
      lt_B (` b2) b.
  Proof.
    intros; destruct b1; destruct b2; simpl in *.
    unfold le_B, lt_B in *; omega.
  Qed.

  Definition decode_list_step (b : B) (cd : CacheDecode):
    option (list A * B * CacheDecode) :=
    Fix well_founded_lt_b
           (fun _ => CacheDecode -> option (list A * B * CacheDecode))
      (fun b rec cd =>
         `(br, b1, e1) <- Decode_w_Measure_le X_decode b cd X_decode_le;
         If br Then
            (`(ps, b2, e2) <- Decode_w_Measure_le P_decode (proj1_sig b1) e1 P_decode_le;
             match getD cd ps  with
             | Some [] => None (* bogus *)
             | Some l => Some (l, proj1_sig b2, e2)
             | None => None (* bogus *)
             end)
            Else
            (`(a , b2, e2) <- Decode_w_Measure_lt A_decode (proj1_sig b1) e1 A_decode_lt;
             If A_halt_dec a Then
                Some (nil, proj1_sig b2, e2)
                Else
                (`(l, b3, e3) <- rec (proj1_sig b2) (lt_B_trans _ _ _) e2;
                 Some (a :: l, b3, addD e3 (a :: l, peekD cd))))) b cd.

  Theorem SteppingList_decode_correct :
    encode_decode_correct_f
      cache transformer
      (fun ls => (forall x, In x ls -> A_predicate x /\ ~ x = A_halt))
      encode_list_step_Spec decode_list_step cache_inv.
  Proof.
    unfold encode_decode_correct_f; split.
    { intros env xenv xenv' l l' ext Eeq Ppredh Penc;
      subst.
      unfold decode_list_step in *; simpl in *.
      generalize dependent l';
        generalize dependent env;
        generalize dependent xenv;
        generalize ext; generalize dependent xenv';
          induction l; intros; simpl in *.
      { unfold Bind2 in *; computes_to_inv; subst.
        destruct v; destruct v0.
        injections.
        destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 ext0) Eeq I Penc) as [? [? ?]]; subst.
        rewrite <- transform_assoc.
        rewrite Coq.Init.Wf.Fix_eq; simpl.
        let H' := fresh in
        destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
          rewrite H'; simpl; clear H'.
          destruct (proj1 A_decode_pf _ _ _ _ _ ext0 H0 A_predicate_halt Penc') as [? [? ?]]; subst.
          let H' := fresh in
          destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (A_halt_dec A_halt); simpl; eexists; eauto.
          congruence.
          intros.
          apply functional_extensionality; intros.
          repeat (f_equal; repeat (apply functional_extensionality; intros)).
      }
      destruct (getE env (a :: l)) eqn: ?.
      rewrite Coq.Init.Wf.Fix_eq; simpl.
      computes_to_inv.
      destruct v; simpl in Penc'.
      { (* Case where the encoder decided to use compression. *)
        destruct (P_predicate_dec p); simpl in Penc';
        unfold Bind2 in Penc'; computes_to_inv; injections;
        subst; destruct v; destruct v0.
        - destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 ext0) Eeq I Penc') as [? [? ?]]; subst.
          rewrite <- transform_assoc; simpl;
            let H' := fresh in
            destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
              rewrite H'; simpl; clear H'.
          destruct (proj1 P_decode_pf _ _ _ _ _ ext0 H0 p0 Penc'') as [? [? ?]];
           let H' := fresh in
            destruct (Decode_w_Measure_le_eq _ _ _ P_decode_le H1) as [? H'];
              rewrite H'; simpl; clear H'.
          eapply get_correct in Heqo; eauto; rewrite Heqo.
          eauto.
        - destruct v1.
          destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 (transform b1 ext0))
                          Eeq I Penc') as [? [? ?]]; subst.
          rewrite <- !transform_assoc; simpl.
          let H' := fresh in
          destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (proj1 A_decode_pf _ _ _ _ _ (transform b1 ext0) H0 (proj1 (Ppredh _ (or_introl _ eq_refl))) Penc'') as [? [? ?]]; subst.
          let H' := fresh in
          destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (A_halt_dec a); simpl.
          elimtype False; apply (proj2 (Ppredh _ (or_introl _ eq_refl)));
            eauto.
          eapply (fun H => IHl H _ ext0) in Penc'''; intros.
          destruct_ex; intuition.
          rewrite H4; simpl.
          eexists; intuition eauto.
          erewrite peek_correct.
          eapply add_correct.
          eauto.
          eauto.
          eapply Ppredh; eauto.
          eauto.
      }
      {
        unfold Bind2 in Penc'; computes_to_inv; injections;
        subst; destruct v; destruct v0; destruct v1.
        - destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 (transform b1 ext0)) Eeq I Penc') as [? [? ?]]; subst.
          rewrite <- !transform_assoc; simpl.
          let H' := fresh in
          destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (proj1 A_decode_pf _ _ _ _ _ (transform b1 ext0) H0 (proj1 (Ppredh _ (or_introl _ eq_refl))) Penc'') as [? [? ?]]; subst.
          let H' := fresh in
          destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (A_halt_dec a); simpl.
          elimtype False; apply (proj2 (Ppredh _ (or_introl _ eq_refl)));
            eauto.
          eapply (fun H => IHl H _ ext0) in Penc'''; intros.
          destruct_ex; intuition.
          rewrite H4; simpl.
          eexists; intuition eauto.
          erewrite peek_correct.
          eapply add_correct.
          eauto.
          eauto.
          eauto.
          eauto.
      }
      intros.
      apply functional_extensionality; intros.
      repeat (f_equal; repeat (apply functional_extensionality; intros)).
      - rewrite Coq.Init.Wf.Fix_eq; simpl.
        unfold Bind2 in Penc; computes_to_inv; injections;
          subst; destruct v; destruct v0; destruct v1;
            simpl in *.
        destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 (transform b1 ext0))
                        Eeq I Penc) as [? [? ?]]; subst.
        rewrite <- !transform_assoc; simpl.
        let H' := fresh in
        destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
          rewrite H'; simpl; clear H'.
        destruct (proj1 A_decode_pf _ _ _ _ _ (transform b1 ext0) H0 (proj1 (Ppredh _ (or_introl _ eq_refl))) Penc') as [? [? ?]]; subst.
        let H' := fresh in
        destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
          rewrite H'; simpl; clear H'.
        destruct (A_halt_dec a); simpl.
        elimtype False; apply (proj2 (Ppredh _ (or_introl _ eq_refl)));
          eauto.
        eapply (fun H => IHl H _ ext0) in Penc''; intros; eauto.
        destruct_ex; intuition.
        rewrite H4; simpl.
        eexists; intuition eauto.
        erewrite peek_correct.
        eapply add_correct.
        eauto.
        eauto.
        intros.
        apply functional_extensionality; intros.
        repeat (f_equal; repeat (apply functional_extensionality; intros)).
    }
    { unfold decode_list_step, encode_list_step_Spec.
      intros env env' xenv' data bin;
        revert env env' xenv' data.
      eapply (@well_founded_induction _ _ well_founded_lt_b) with
      (a := bin); intros.
      rewrite Coq.Init.Wf.Fix_eq in H2; simpl.
      destruct (X_decode x env')
        as [ [ [ [ | ] ?] ?] | ] eqn: Heqo; simpl in *;
        first [eapply (Decode_w_Measure_le_eq' _ _ _ X_decode_le) in Heqo;
               rewrite Heqo in H2; simpl in H2; discriminate
              | let H' := fresh in
                destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le Heqo) as [? H'];
                rewrite H' in H2; simpl in *; clear H'].
      - destruct (P_decode b c)
          as [ [ [ ? ?] ?] | ] eqn: Heqo'; simpl in *;
          first [eapply (Decode_w_Measure_le_eq' _ _ _ P_decode_le) in Heqo';
               rewrite Heqo' in H2; simpl in H2; discriminate
              | let H' := fresh in
                destruct (Decode_w_Measure_le_eq _ _ _ P_decode_le Heqo') as [? H'];
                rewrite H' in H2; simpl in *; clear H'].
        destruct (getD env' p) eqn: ?; simpl in *; try discriminate.
        injections.
        destruct l; try discriminate; injections.
        eapply (proj2 X_decode_pf) in Heqo; destruct Heqo;
          destruct_ex; intuition eauto; subst;
            eapply (proj2 P_decode_pf) in Heqo'; destruct Heqo';
              destruct_ex; intuition eauto; subst.
        rewrite (proj2 (get_correct _ _ _ _ H0) Heqo0).
        eexists; eexists; intuition eauto.
        computes_to_econstructor.
        apply (@PickComputes _ _ true); eauto.
        simpl.
        destruct (P_predicate_dec p).
        repeat computes_to_econstructor; eauto.
        intuition.
        simpl; rewrite transform_assoc; reflexivity.
        pose proof (cacheGet_OK _ _ _ H1 Heqo0 _ H6); intuition.
        pose proof (cacheGet_OK _ _ _ H1 Heqo0 _ H6); intuition.
      - destruct (A_decode b c)
          as [ [ [ ? ?] ?] | ] eqn: Heqo'; simpl in *;
          first [eapply (Decode_w_Measure_lt_eq' _ _ _ A_decode_lt) in Heqo';
                 rewrite Heqo' in H2; simpl in H1; discriminate
                | let H' := fresh in
                  destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt Heqo') as [? H'];
                  rewrite H' in H2; simpl in *; clear H'].
        eapply (proj2 X_decode_pf) in Heqo; eauto;
          destruct Heqo; destruct_ex;
            eauto; subst;
              eapply (proj2 A_decode_pf) in Heqo'; eauto;
                destruct Heqo'; destruct_ex;
                  eauto; subst; split_and; eauto.
        destruct (A_halt_dec a); simpl in *.
        + injections; simpl.
          intuition.
          eexists; eexists; intuition.
          computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
          unfold le_B in x0.
          simpl; rewrite transform_assoc; reflexivity.
          eauto.
        + match type of H2 with
            context [Fix well_founded_lt_b ?P ?f ?b ?c] =>
            destruct (Fix well_founded_lt_b P f b c)
              as [ [ [ ? ?] ?] | ] eqn: ?; simpl in *; try discriminate
          end.
          simpl in H2; injections.
          split.
          * eapply cacheAdd_OK.
            eapply H12 in Heqo; eauto.
            unfold le_B, lt_B in *; omega.
            simpl; intros; intuition subst; eauto.
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eapply H16; eauto.
            unfold le_B, lt_B in *; omega.
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eapply H16; eauto.
            unfold le_B, lt_B in *; omega.
          * destruct (getE env (a :: l)) eqn : ? .
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eexists; eexists; intuition eauto.
            computes_to_econstructor.
            apply (@PickComputes _ _ false); eauto.
            simpl.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            subst; rewrite !transform_assoc; reflexivity.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl.
            erewrite peek_correct; eauto.
            eapply add_correct; eauto.
            unfold le_B, lt_B in *; omega.
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eexists; eexists; intuition eauto.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            subst; rewrite !transform_assoc; reflexivity.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl.
            erewrite peek_correct; eauto.
            eapply add_correct; eauto.
            unfold lt_B, le_B in *; rewrite !transform_measure.
            rewrite transform_measure in x1.
            omega.
      - intros; apply functional_extensionality; intros.
        repeat (f_equal; repeat (apply functional_extensionality; intros)).
        Grab Existential Variables.
        eauto.
    }
  Qed.
End SteppingList. *)
