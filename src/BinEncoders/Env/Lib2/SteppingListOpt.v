Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.FixListOpt.
Require Export
        Coq.Lists.List.

Section SteppingList.
  Context {A : Type}. (* data type *)
  Context {B : Type}. (* bin type *)
  Context {P : Type}. (* cache pointer type *)
  Context {cache : Cache}.
  Context {transformer : Transformer B}.

  Variable fuel : nat.
  Variable A_halt : A.
  Variable A_halt_dec : forall a, {a = A_halt} + {~ a = A_halt}.
  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> B * CacheEncode.
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).
  Variable A_decode_pf : encode_decode_correct_f cache transformer A_predicate A_encode A_decode.

  Variable P_predicate : P -> Prop.
  Variable P_predicate_dec : forall p, {P_predicate p} + {~ P_predicate p}.
  Variable P_encode : P -> CacheEncode -> B * CacheEncode.
  Variable P_decode : B -> CacheDecode -> option (P * B * CacheDecode).
  Variable P_decode_pf : encode_decode_correct_f cache transformer P_predicate P_encode P_decode.

  Variable X_encode : bool -> CacheEncode -> B * CacheEncode.
  Variable X_decode : B -> CacheDecode -> option (bool * B * CacheDecode).
  Variable X_decode_pf : encode_decode_correct_f cache transformer (fun _ => True) X_encode X_decode.

  Variable cacheAdd : CacheAdd cache (list A * P).
  Variable cacheGet : CacheGet cache (list A) P.
  Variable cachePeek : CachePeek cache P.

  Fixpoint encode_list_step (l : list A) (ce : CacheEncode) : B * CacheEncode :=
    match l with
    | nil => let (b1, e1) := X_encode false ce in
             let (b2, e2) := A_encode A_halt e1 in
                 (transform b1 b2, e2)
    | cons x l' =>
      match getE ce l with
      | Some position =>
        if P_predicate_dec position
        then let (b1, e1) := X_encode true ce in
             let (b2, e2) := P_encode position e1 in
                 (transform b1 b2, e2)
        else let (b1, e1) := X_encode false ce in
             let (b2, e2) := A_encode x e1 in
             let (b3, e3) := encode_list_step l' e2 in
                 (transform (transform b1 b2) b3, addE e3 (l, peekE ce))
      | None => let (b1, e1) := X_encode false ce in
                let (b2, e2) := A_encode x e1 in
                let (b3, e3) := encode_list_step l' e2 in
                    (transform (transform b1 b2) b3, addE e3 (l, peekE ce))
      end
    end.

  Fixpoint decode'_list_step (f : nat) (b : B) (cd : CacheDecode) : option (list A * B * CacheDecode) :=
    `(br, b1, e1) <- X_decode b cd;
      If br Then
       `(ps, b2, e2) <- P_decode b1 e1;
        match getD cd ps with
        | Some l => Some (l, b2, e2)
        | None => None (* bogus *)
        end
      Else
        (`(a , b2, e2) <- A_decode b1 e1;
           If A_halt_dec a Then
              Some (nil, b2, e2)
              Else
              match f with
              | O => None (* bogus *)
              | S f' => `(l, b3, e3) <- decode'_list_step f' b2 e2;
                          Some (a :: l, b3, addD e3 (a :: l, peekD cd))
              end).

  Definition decode_list_step := decode'_list_step fuel.

  Theorem SteppingList_decode_correct :
    encode_decode_correct_f
      cache transformer
      (fun ls => A_predicate A_halt /\ |ls| <= fuel /\ (forall x, In x ls -> A_predicate x /\
                                                                             ~ x = A_halt))
      encode_list_step decode_list_step.
  Proof.
    unfold encode_decode_correct_f.
    intros env xenv xenv' l l' ext Eeq [Ppredh [PPredlen PPredA]] Penc;
      subst.
    unfold decode_list_step in *; simpl in *.
    generalize dependent l'; generalize dependent fuel; clear fuel;
      generalize dependent env; 
      generalize dependent xenv; 
      generalize ext; generalize dependent xenv';
    induction l; intros; simpl in *.
    { destruct (X_encode false env) eqn: ?.
      destruct (A_encode A_halt c) eqn: ?.
      inversion Penc; subst; clear Penc.
      destruct (X_decode_pf _ _ _ _ _ (transform b0 ext0) Eeq I Heqp) as [? [? ?]]; subst.
      rewrite <- transform_assoc.
      destruct fuel eqn: ?; subst; simpl in *.
      { rewrite H; simpl.
        destruct (A_decode_pf _ _ _ _ _ ext0 H0 Ppredh Heqp0) as [? [? ?]]; subst.
        rewrite H1.
        simpl.
        destruct (A_halt_dec A_halt); simpl; eexists; eauto.
        congruence.
      }
      { rewrite H; simpl.
        destruct (A_decode_pf _ _ _ _ _ ext0 H0 Ppredh Heqp0) as [? [? ?]]; subst.
        rewrite H1.
        simpl.
        destruct (A_halt_dec A_halt); simpl; eexists; eauto.
        congruence.
      } 
    }
    destruct fuel; try omega; simpl.
    destruct (getE env (a :: l)) eqn: ?.
    - destruct (P_predicate_dec p).
      + destruct (X_encode true env) eqn: ? ;
          destruct (P_encode p c) eqn: ?; intros; injections.
        destruct (X_decode_pf _ _ _ _ _ (transform b0 ext0) Eeq I Heqp1) as [? [? ?]]; subst.
        rewrite <- transform_assoc; rewrite H; simpl.
        destruct (P_decode_pf _ _ _ _ _ ext0 H0 p0 Heqp0) as [? [? ?]];
          subst; rewrite H1; simpl.
        eapply get_correct in Heqo; eauto; rewrite Heqo.
        eauto.
      + destruct (X_encode false env) eqn: ? ;
          destruct (P_encode p c) eqn: ?; intros; injections.
        destruct (A_encode a c) eqn: ?.
        destruct (encode_list_step l c1) eqn: ?.
        injections.
        destruct (X_decode_pf _ _ _ _ _ (transform b1 (transform b2 ext0))
                              Eeq I Heqp0) as [? [? ?]]; subst.
        rewrite <- !transform_assoc; rewrite H; simpl.
        destruct (A_decode_pf _ _ _ _ _ (transform b2 ext0) H0 (proj1 (PPredA _ (or_introl _ eq_refl))) Heqp2) as [? [? ?]]; subst.
        rewrite H1; simpl.
        destruct (A_halt_dec a); simpl.
        elimtype False; apply (proj2 (PPredA _ (or_introl _ eq_refl)));
          eauto.
        eapply (fun H => IHl H _ ext0) in Heqp3; intros.
        destruct_ex; intuition.
        rewrite H4; simpl.
        eexists; intuition eauto.
        erewrite peek_correct.
        eapply add_correct.
        eauto.
        eauto.
        eapply PPredA; eauto.
        eauto.
        omega.
    - destruct (X_encode false env) eqn: ? ;
        destruct (A_encode a c) eqn: ?.
      destruct (encode_list_step l c0) eqn: ?.
      injections.
      destruct (X_decode_pf _ _ _ _ _ (transform b0 (transform b1 ext0))
                            Eeq I Heqp) as [? [? ?]]; subst.
      rewrite <- !transform_assoc; rewrite H; simpl.
      destruct (A_decode_pf _ _ _ _ _ (transform b1 ext0) H0 (proj1 (PPredA _ (or_introl _ eq_refl))) Heqp0) as [? [? ?]]; subst.
      rewrite H1; simpl.
      destruct (A_halt_dec a); simpl.
      elimtype False; apply (proj2 (PPredA _ (or_introl _ eq_refl)));
        eauto.
      eapply (fun H => IHl H _ ext0) in Heqp1; intros.
      destruct_ex; intuition.
      rewrite H4; simpl.
      eexists; intuition eauto.
      erewrite peek_correct.
      eapply add_correct.
      eauto.
      eauto.
      eapply PPredA; eauto.
      eauto.
      omega.
      Grab Existential Variables.
      eauto.
      eauto.
  Qed.
End SteppingList.

