Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.FixList.
Require Export
        Coq.Lists.List.

Section SteppingList.
  Context {A : Type}. (* data type *)
  Context {B : Type}. (* bin type *)
  Context {P : Type}. (* cache pointer type *)
  Context {cache : Cache}.
  Context {monoid : Monoid B}.

  Variable fuel : nat.
  Variable A_halt : A.
  Variable A_halt_dec : forall a, {a = A_halt} + {~ a = A_halt}.
  Variable A_predicate : A -> Prop.
  Variable A_format : A -> CacheFormat -> B * CacheFormat.
  Variable A_decode : B -> CacheDecode -> A * B * CacheDecode.
  Variable A_decode_pf : format_decode_correct monoid A_predicate A_format A_decode.

  Variable P_predicate : P -> Prop.
  Variable P_predicate_dec : forall p, {P_predicate p} + {~ P_predicate p}.
  Variable P_format : P -> CacheFormat -> B * CacheFormat.
  Variable P_decode : B -> CacheDecode -> P * B * CacheDecode.
  Variable P_decode_pf : format_decode_correct monoid P_predicate P_format P_decode.

  Variable X_format : bool -> CacheFormat -> B * CacheFormat.
  Variable X_decode : B -> CacheDecode -> bool * B * CacheDecode.
  Variable X_decode_pf : format_decode_correct monoid (fun _ => True) X_format X_decode.

  Variable cacheAdd : CacheAdd cache (list A * P).
  Variable cacheGet : CacheGet cache (list A) P.
  Variable cachePeek : CachePeek cache P.

  (*Fixpoint format_list_step (l : list A) (ce : CacheFormat) : B * CacheFormat :=
    match l with
    | nil => let (b1, e1) := X_format false ce in
             let (b2, e2) := A_format A_halt e1 in
                 (mappend b1 b2, e2)
    | cons x l' =>
      match getE ce l with
      | Some position =>
        if P_predicate_dec position
        then let (b1, e1) := X_format true ce in
             let (b2, e2) := P_format position e1 in
                 (mappend b1 b2, e2)
        else let (b1, e1) := X_format false ce in
             let (b2, e2) := A_format x e1 in
             let (b3, e3) := format_list_step l' e2 in
                 (mappend (mappend b1 b2) b3, addE e3 (l, peekE ce))
      | None => let (b1, e1) := X_format false ce in
                let (b2, e2) := A_format x e1 in
                let (b3, e3) := format_list_step l' e2 in
                    (mappend (mappend b1 b2) b3, addE e3 (l, peekE ce))
      end
    end.

  Fixpoint decode'_list_step (f : nat) (b : B) (cd : CacheDecode) : list A * B * CacheDecode :=
    let (x1, e1) := X_decode b cd in
    let (br, b1) := x1 in
    match br with
    | true => let (x2, e2) := P_decode b1 e1 in
              let (ps, b2) := x2 in
              match getD cd ps with
              | Some l => (l, b2, e2)
              | None => (nil, b, cd) (* bogus *)
             end
    | false => let (x2, e2) := A_decode b1 e1 in
               let (a, b2) := x2 in
               if A_halt_dec a then
                 (nil, b2, e2)
               else
                 match f with
                 | O => (nil, b, cd) (* bogus *)
                 | S f' => let (x3, e3) := decode'_list_step f' b2 e2 in
                           let (l, b3) := x3 in
                           (a :: l, b3, addD e3 (a :: l, peekD cd))
                 end
    end.

  Definition decode_list_step := decode'_list_step fuel.

  Theorem SteppingList_decode_correct :
    format_decode_correct
      cache monoid
      (fun ls => A_predicate A_halt /\ |ls| <= fuel /\ (forall x, In x ls -> A_predicate x /\
                                                                             ~ x = A_halt))
      format_list_step decode_list_step.
  Proof.
    unfold format_decode_correct.
    intros env env' xenv xenv' l l' bin' ext ext' Eeq [Ppredh [PPredlen PPredA]] Penc Pdec.
    unfold decode_list_step in *; simpl in *.
    generalize dependent l'; generalize dependent fuel; clear fuel;
      generalize dependent env; generalize dependent env';
      generalize dependent xenv; generalize dependent bin';
      generalize ext; generalize dependent ext'; generalize dependent xenv';
    induction l; intros; simpl in *.
    { destruct (X_format false env) eqn: ?.
      destruct (A_format A_halt c) eqn: ?.
      inversion Penc; subst; clear Penc.
      destruct (X_decode (mappend (mappend b b0) ext0) env') as [[? ?] ?] eqn: ?.
      rewrite <- mappend_assoc in Heqp1.
      destruct (X_decode_pf _ _ _ _ _ _ _ _ _ Eeq I Heqp Heqp1) as [? [? ?]]; subst.
      destruct fuel eqn: ?; subst; simpl in *; try rewrite !mappend_assoc in Heqp1.
      { rewrite Heqp1 in Pdec.
        destruct (A_decode (mappend b0 ext0) c0) as [[? ?] ?] eqn: ?.
        destruct (A_decode_pf _ _ _ _ _ _ _ _ _ H Ppredh Heqp0 Heqp2) as [? [? ?]]; subst.
        destruct (A_halt_dec a); inversion Pdec; subst; intuition. }
      { rewrite Heqp1 in Pdec.
        destruct (A_decode (mappend b0 ext0) c0) as [[? ?] ?] eqn: ?.
        destruct (A_halt_dec a); inversion Pdec; subst; clear Pdec.
        destruct (A_decode_pf _ _ _ _ _ _ _ _ _ H Ppredh Heqp0 Heqp2) as [? [? ?]]; intuition.
        destruct (A_decode_pf _ _ _ _ _ _ _ _ _ H Ppredh Heqp0 Heqp2) as [? [? ?]]; congruence. } }
    { destruct fuel as [| fuel']; try solve [ exfalso; intuition; inversion PPredlen ].
      destruct (getE env (a :: l)) eqn: ?.
      { destruct (P_predicate_dec p).
        { destruct (X_format true env) eqn: ?.
          destruct (P_format p c) eqn: ?. simpl in *.
          destruct (X_decode (mappend bin' ext0) env') as [[? ?] ?] eqn: ?.
          destruct (P_decode (mappend b0 ext0) c1) as [[? ?] ?] eqn: ?.
          inversion Penc; subst; clear Penc.
          rewrite <- mappend_assoc in Heqp2.
          destruct (X_decode_pf _ _ _ _ _ _ _ _ _ Eeq I Heqp1 Heqp2) as [? [? ?]]; subst.
          destruct (P_decode_pf _ _ _ _ _ _ _ _ _ H p0 Heqp0 Heqp3) as [? [? ?]]; subst.
          eapply get_correct in Heqo; eauto.
          rewrite Heqp3, Heqo in Pdec.
          inversion Pdec; subst; eauto. }
        { destruct (X_format false env) eqn: ?.
          destruct (A_format a c) eqn: ?.
          destruct (format_list_step l c0) eqn: ?. simpl in *.
          inversion Penc; subst; clear Penc.
          destruct (X_decode (mappend (mappend (mappend b b0) b1) ext0) env')
            as [[? ?] ?] eqn: ?.
          rewrite <- !mappend_assoc in Heqp3.
          destruct (X_decode_pf _ _ _ _ _ _ _ _ _ Eeq I Heqp0 Heqp3) as [? [? ?]]; subst.
          destruct (A_decode (mappend b0 (mappend b1 ext0)) c2) as [[? ?] ?] eqn: ?.
          destruct (A_decode_pf _ _ _ _ _ _ _ _ _ H (proj1 (PPredA _ (or_introl eq_refl)))
                                Heqp1 Heqp4) as [? [? ?]]; subst.
          destruct (A_halt_dec a0).
          { inversion Pdec; subst; clear Pdec.
            exfalso. specialize (PPredA _ (or_introl eq_refl)). intuition congruence. }
          { destruct (decode'_list_step fuel' (mappend b1 ext0) c3) as [[? ?] ?] eqn: ?.
            inversion Pdec; subst; clear Pdec.
            destruct (IHl (fun x H => PPredA x (or_intror H)) _ _ _ _ _ _ _ H0 Heqp2 _
                          (Le.le_S_n _ _ PPredlen) _ Heqp5) as [? [? ?]]; subst.
            intuition eauto.
            erewrite peek_correct; eauto.
            eapply add_correct; eauto. } } }
      { destruct (X_format false env) eqn: ?.
        destruct (A_format a c) eqn: ?.
        destruct (format_list_step l c0) eqn: ?. simpl in *.
        inversion Penc; subst; clear Penc.
        destruct (X_decode (mappend (mappend (mappend b b0) b1) ext0) env')
          as [[? ?] ?] eqn: ?.
        rewrite <- !mappend_assoc in Heqp2.
        destruct (X_decode_pf _ _ _ _ _ _ _ _ _ Eeq I Heqp Heqp2) as [? [? ?]]; subst.
        destruct (A_decode (mappend b0 (mappend b1 ext0)) c2) as [[? ?] ?] eqn: ?.
        destruct (A_decode_pf _ _ _ _ _ _ _ _ _ H (proj1 (PPredA _ (or_introl eq_refl)))
                              Heqp0 Heqp3) as [? [? ?]]; subst.
        destruct (A_halt_dec a0).
        { inversion Pdec; subst; clear Pdec.
          exfalso. specialize (PPredA _ (or_introl eq_refl)). intuition congruence. }
        { destruct (decode'_list_step fuel' (mappend b1 ext0) c3) as [[? ?] ?] eqn: ?.
          inversion Pdec; subst; clear Pdec.
          destruct (IHl (fun x H => PPredA x (or_intror H)) _ _ _ _ _ _ _ H0 Heqp1 _
                        (Le.le_S_n _ _ PPredlen) _ Heqp4) as [? [? ?]]; subst.
          intuition eauto.
          erewrite peek_correct; eauto.
          eapply add_correct; eauto. } } }
  Qed. *)
End SteppingList.
