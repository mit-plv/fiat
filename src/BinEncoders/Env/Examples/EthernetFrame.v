Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import
        Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Definition EthernetFrame :=
  @Tuple <"Destination" :: Vector.t char 6,
          "Source" :: Vector.t char 6,
          "Type" :: BoundedString ["ARP"; "IP"; "RARP"],
          "Data" :: list char>.

Definition EtherTypeCodes : Vector.t (word 16) 3 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0;
   WO~0~1~1~0~0~0~0~0~0~0~0~1~0~0~0~0;
   WO~1~0~1~0~1~1~0~0~0~0~0~1~0~0~0~0
  ].

  Definition transformer : Transformer ByteString := ByteStringTransformer.

  Local Notation "x ++ y" := (transform x y).

Definition composeIf E B
           (transformer : Transformer B)
           (encode1 : E -> Comp (B * E))
           (iComp : Comp bool)
           (encodeT : E -> Comp (B * E))
           (encodeE : E -> Comp (B * E))
  :=
  (fun e0 =>
     `(p, e1) <- encode1 e0;
       b <- iComp;
       If b Then
          `(q, e2) <- encodeT e1;
          ret (transform p q, e2)
       Else (`(q, e2) <- encodeE e1;
            ret (transform p q, e2))
  )%comp.

Lemma composeIf_encode_correct
      {A A' B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_invT P /\ P_invE P))
      (transformer : Transformer B)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate_rest : A' -> B -> Prop)
      (predicate_rest' : A -> B -> Prop)
      (predicate' : A' -> Prop)
      (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (IComp : Comp bool)
      (ICompb : A' -> B -> bool)
      (encodeT : A -> CacheEncode -> Comp (B * CacheEncode))
      (decodeT : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (encodeE : A -> CacheEncode -> Comp (B * CacheEncode))
      (decodeE : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> encode_decode_correct_f
              cache transformer predicate' predicate_rest
              encode1 decode1 P)
      (decodeT_pf : forall proj,
          IComp true ->
          predicate' proj ->
          cache_inv_Property P P_invT ->
          encode_decode_correct_f
            cache transformer
            (fun data => predicate data /\ project data = proj)
            predicate_rest'
            encodeT
            (decodeT proj) P)
      (decodeE_pf : forall proj,
          IComp false ->
          predicate' proj ->
          cache_inv_Property P P_invE ->
          encode_decode_correct_f
            cache transformer
            (fun data => predicate data /\ project data = proj)
            predicate_rest'
            encodeE
            (decodeE proj) P)
      (ICompb_decT :
         forall data env b b' c xenv ext,
           predicate data
           -> encode1 (project data) env ↝ (b, c)
           -> IComp ↝ true
           -> encodeT data c ↝ (b', xenv)
           -> ICompb (project data) (transform b' ext) = true)
      (ICompb_decE :
         forall data env b b' c xenv ext,
           predicate data
           -> encode1 (project data) env ↝ (b, c)
           -> IComp ↝ false
           -> encodeE data c ↝ (b', xenv)
           -> ICompb (project data) (transform b' ext) = false)
      (ICompb_dec :
         forall a b,
           IComp (ICompb a b))
      (predicate_rest_implT : forall a' b b'',
          (IComp true /\
          exists a ce ce' ce'' b' b'',
            computes_to (encode1 a' ce) (b', ce')
            /\ project a = a'
            /\ predicate a
            /\ computes_to (encodeT a ce') (b'', ce'')
            /\ predicate_rest' a b)
          -> predicate_rest a' (transform b'' b))
      (predicate_rest_implE : forall a' b b'',
          (IComp false /\
          exists a ce ce' ce'' b',
            computes_to (encode1 a' ce) (b', ce')
            /\ project a = a'
            /\ predicate a
            /\ computes_to (encodeE a ce') (b'', ce'')
            /\ predicate_rest' a b)
          -> predicate_rest a' (transform b'' b))
      (pred_pf : forall data, predicate data -> predicate' (project data))      
  : encode_decode_correct_f
      cache transformer
      (fun a => predicate a)
      predicate_rest'
      (fun (data : A) (ctx : CacheEncode) =>
         composeIf _ _ _ (encode1 (project data)) IComp (encodeT data) (encodeE data)  ctx
      )%comp
     (fun (bin : B) (env : CacheDecode) =>
        `(proj, rest, env') <- decode1 bin env;
          If (ICompb proj) rest Then
             decodeT proj rest env'
             Else
             decodeE proj rest env'
     ) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext env_pm pred_pm pred_pm_rest com_pf.
    unfold composeIf, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0; simpl in com_pf''.
    - computes_to_inv; destruct v; subst.
      destruct (fun H => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (transform b0 ext) env_pm (pred_pf _ pred_pm) H com_pf); intuition; simpl in *; injections.
      eapply predicate_rest_implT; repeat eexists; intuition eauto.
      pose proof (ICompb_decT _ _ _ _ _ _ ext pred_pm com_pf com_pf' com_pf'').
      destruct (fun H' => proj1 (decodeT_pf (project data) com_pf' (pred_pf _ pred_pm)
                                  H)
                      _ _ _ _ _ ext H3 (conj pred_pm (eq_refl _)) H' com_pf'');
        intuition; simpl in *; injections.
      setoid_rewrite <- transform_assoc; rewrite H2.
      intuition; simpl in *; injections.
      rewrite H5, H7; simpl; eauto.
    - computes_to_inv; destruct v; subst.
      destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (transform b0 ext) env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections.
      eapply predicate_rest_implE; intuition; repeat eexists; intuition eauto.
      pose proof (ICompb_decE _ _ _ _ _ _ ext pred_pm com_pf com_pf' com_pf'').
      destruct (fun H' => proj1 (decodeE_pf (project data) com_pf' (pred_pf _ pred_pm)
                                  H4)
                      _ _ _ _ _ ext H3 (conj pred_pm (eq_refl _)) H' com_pf'');
        intuition; simpl in *; injections.
      setoid_rewrite <- transform_assoc; rewrite H2.
      intuition; simpl in *; injections.
      rewrite H5, H7; simpl; eauto.
  }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    pose proof (ICompb_dec a b) as ICompb'.
    destruct (ICompb a b) eqn: ?; simpl in *.
    - eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto;
        destruct Heqo; destruct_ex; intuition;
          eapply (proj2 (decodeT_pf a ICompb' H7 H3)) in H1; eauto;
            destruct H1; destruct_ex; intuition; subst.
      eexists; eexists; repeat split.
      repeat computes_to_econstructor; eauto.
      simpl; repeat computes_to_econstructor; eauto.
      simpl; rewrite transform_assoc; reflexivity.
      eassumption.
      eassumption.
    - eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto;
        destruct Heqo; destruct_ex; intuition;
          eapply (proj2 (decodeE_pf a ICompb' H7 H8)) in H1; eauto;
            destruct H1; destruct_ex; intuition; subst.
      eexists; eexists; repeat split.
      repeat computes_to_econstructor; eauto.
      simpl; repeat computes_to_econstructor; eauto.
      simpl; rewrite transform_assoc; reflexivity.
      eassumption.
      eassumption.
  }
Qed.

Local Notation "x 'ThenIf' i 'TheniC' t 'ElseiC' e " :=
  (composeIf _ _ _ x i t e) (at level 100, right associativity).

  Definition encode_EthernetFrame_Spec (eth : EthernetFrame) :=
      (encode_Vector_Spec encode_word_Spec eth!"Destination")
        ThenC (encode_Vector_Spec encode_word_Spec eth!"Source")
        ThenIf ({v1042 : bool | True}) (* Support both kinds of frames.*)
        TheniC
        (encode_nat_Spec 16 (length eth!"Data")
           ThenC encode_word_Spec (WO~0~1~0~1~0~1~0~1)
           ThenC encode_word_Spec (WO~0~1~0~1~0~1~0~1)
           ThenC encode_word_Spec (WO~1~1~0~0~0~0~0~0)
           ThenC encode_word_Spec (wzero 24)
           ThenC encode_enum_Spec EtherTypeCodes eth!"Type"
           ThenC encode_list_Spec encode_word_Spec eth!"Data"
           DoneC)
       ElseiC
       encode_enum_Spec EtherTypeCodes eth!"Type"
       ThenC encode_list_Spec encode_word_Spec eth!"Data"
       DoneC.

  Opaque pow2. (* Don't want to be evaluating this. *)

  Ltac apply_compose :=
    intros;
    match goal with
      H : cache_inv_Property ?P ?P_inv |- _ =>
      first [eapply (compose_encode_correct_no_dep H); clear H
            | eapply (compose_encode_correct H); clear H
            | eapply (composeIf_encode_correct H); clear H
            ]
    end.

  Ltac makeEvar T k :=
    let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

  Ltac shelve_inv :=
    let H' := fresh in
    let data := fresh in
    intros data H';
    repeat destruct H';
    match goal with
    | H : ?P data |- ?P_inv' =>
      is_evar P;
      let P_inv' := (eval pattern data in P_inv') in
      let P_inv := match P_inv' with ?P_inv data => P_inv end in
      let new_P_T := type of P in
      makeEvar new_P_T
               ltac:(fun new_P =>
                       unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
    end.    
  
  Theorem decode_list_all_correct_ComposeOpt
      : encode_decode_correct_f
          _ transformer
          (fun a => True)
          (fun _ b => b = transform_id)
          (encode_list_Spec encode_word_Spec)
          (fun (bin : ByteString) (env : CacheDecode) =>
             Some (byteString bin, ByteString_id, tt))
          (fun a => True).
  Proof.
    split.
    {
      intros env env' xenv l l' ext Eeq Ppred Ppred_rest Penc.
      intuition; subst.
      generalize dependent env. generalize dependent env'.
      generalize dependent xenv.
      generalize dependent l'. induction l.
      { intros.
        simpl in *; intuition; computes_to_inv;
          injections; simpl.
        eexists; eauto. }
      { intros; simpl in *.
        unfold Bind2 in Penc; computes_to_inv; subst.
        destruct v; destruct v0; simpl in *.
        injections.
        eapply IHl in Penc'; eauto.
        destruct_ex; intuition; injections.
        pose proof transform_assoc;
          pose proof transform_id_right.
        simpl in H, H0.
        setoid_rewrite <- H.
        setoid_rewrite H0; eexists; intuition; repeat f_equal.
        unfold encode_word_Spec in Penc.
        simpl in Penc.
        admit.
      }
    }
    { admit.
    }
  Qed.

  Ltac solve_data_inv :=
    first [ simpl; intros; exact I
          | shelve_inv ].

  Lemma Vector_predicate_rest_True n
    : forall a' b,
      Vector_predicate_rest (fun (_ : word 8) (_ : ByteString) => True) encode_word_Spec n a' b.
  Proof.
    induction a'; simpl; eauto.
  Qed.

  Ltac finalize_decoder P_inv :=
  (unfold encode_decode_correct_f; intuition eauto);
    [ computes_to_inv; injections; subst; simpl;
      match goal with
        H : Equiv _ ?env |- _ =>
        eexists env; intuition eauto;
        simpl;
        match goal with
          |- ?f ?a ?b ?c = ?P =>
          let P' := (eval pattern a, b, c in P) in
          let f' := match P' with ?f a b c => f end in
          unify f f'; reflexivity
        end
      end
    | injections; eauto
    | eexists _; eexists _;
      intuition eauto; injections; eauto using idx_ibound_eq;
      try match goal with
        |- P_inv ?data => destruct data;
                                 simpl in *; eauto
      end
    ].

  Lemma Check_Integrity {A B C D E F}
        (b_eq_dec : forall b', DecideableEnsembles.DecideableEnsemble (fun b : B => b = b'))
    : forall (a a' : A) (f : A -> B) (b : B) (f' : A -> C -> D -> option F) f'' (c : C) (d : D) (e : E) (P : E -> E -> Prop),
      a = a'
      -> f a = b
      -> (exists e' : E,
          f' a' c d = Some (f'' e') /\ P e e')
      -> exists e' : E,
          If DecideableEnsembles.dec (DecideableEnsemble := b_eq_dec b) (f a') Then f' a' c d Else None = Some (f'' e') /\ P e e'.
  Proof.
    intros.
    rewrite H in H0.
    intros; apply (DecideableEnsembles.dec_decides_P (DecideableEnsemble := b_eq_dec b)) in H0.
    rewrite H0; simpl; intros; eauto.
  Qed.        

  Global Instance Query_eq_nat : DecideableEnsembles.Query_eq nat :=
    {| A_eq_dec := Coq.Arith.Peano_dec.eq_nat_dec |}.

  Definition packet_decoder
    : { decodePlusCacheInv |
        exists P_inv pred,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
        -> encode_decode_correct_f _ transformer pred (fun _ b => b = ByteString_id) encode_EthernetFrame_Spec (fst decodePlusCacheInv) (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
  Proof.
    eexists (_, _); eexists _; eexists _; split; simpl.
    intros.
    apply_compose.
    intro. eapply Vector_decode_correct.
    revert H; eapply Word_decode_correct.
    solve_data_inv.
    intros; apply Vector_predicate_rest_True.
    apply_compose.
    intro. eapply Vector_decode_correct.
    revert H0; eapply Word_decode_correct.
    apply_compose.
    eapply Nat_decode_correct.
    solve_data_inv.
    simpl; intros; exact I.
    apply_compose.
    eapply Word_decode_correct.
    solve_data_inv.
    simpl; intros; exact I.
    apply_compose.
    eapply Word_decode_correct.
    solve_data_inv.
    simpl; intros; exact I.
    apply_compose.
    eapply Word_decode_correct.
    solve_data_inv.
    simpl; intros; exact I.
    apply_compose.
    eapply Word_decode_correct.
    solve_data_inv.
    simpl; intros; exact I.
    apply_compose.
    eapply Enum_decode_correct.
    admit.
    solve_data_inv.
    simpl; intros; exact I.
    apply_compose.
    intros; eapply decode_list_all_correct_ComposeOpt.
    solve_data_inv.
    simpl; intros.
    computes_to_inv; injections.
    pose proof transform_id_left as H'; simpl in H'; rewrite H'; reflexivity.
    simpl; intros.
    unfold encode_decode_correct_f; intuition eauto.
    match goal with
      [H : ?p = ?proj1, H2 : ?f ?p = ?proj2 |-
       exists xenv', ?f' ?proj1 ?b ?env' = Some (?data, ?ext, xenv') /\ Equiv xenv xenv'] =>
      instantiate (1 := fun p b' c => if (DecideableEnsembles.A_eq_dec (f p) proj2) then _ p b' c else None); cbv beta
    end.
    destruct (@DecideableEnsembles.A_eq_dec nat Query_eq_nat 
               (@Datatypes.length char proj3) proj1); try congruence. 
    destruct data as [? [? [? [? [ ] ] ] ] ]; 
      unfold GetAttribute, GetAttributeRaw in *;
      simpl in *.
    computes_to_inv; injections; subst; simpl.
    pose proof transform_id_left as H'; simpl in H'; rewrite H'.
    eexists tt; simpl; intuition eauto.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      try unify f f'; try reflexivity
    end.
    cbv beta in H12.
    destruct (@DecideableEnsembles.A_eq_dec nat Query_eq_nat 
                                              (@Datatypes.length char proj3) proj1); try congruence; subst.
    eexists _; eexists tt;
      intuition eauto; injections; eauto using idx_ibound_eq;
        try match goal with
              |-  ?data => destruct data;
                             simpl in *; eauto
            end.
    destruct env; computes_to_econstructor.
    pose proof transform_id_left as H'; simpl in H'; rewrite H'.
    reflexivity.
    Focus 2.
    apply_compose.
    eapply Enum_decode_correct.
    admit.
    solve_data_inv.
    simpl; intros; exact I.
    apply_compose.
    intros; eapply decode_list_all_correct_ComposeOpt.
    solve_data_inv.
    simpl; intros.
    computes_to_inv; injections.
    pose proof transform_id_left as H'; simpl in H'; rewrite H'; reflexivity.
    simpl; intros.
    unfold encode_decode_correct_f; intuition eauto.
    destruct data as [? [? [? [? [ ] ] ] ] ]; 
      unfold GetAttribute, GetAttributeRaw in *;
      simpl in *.
    computes_to_inv; injections; subst; simpl.
    pose proof transform_id_left as H'; simpl in H'; rewrite H'.
    eexists tt; simpl; intuition eauto.
    match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      try unify f f'; try reflexivity
    end.
    eexists _; eexists tt;
      intuition eauto; injections; eauto using idx_ibound_eq;
        try match goal with
              |-  ?data => destruct data;
                             simpl in *; eauto
            end.
    destruct env; computes_to_econstructor.
    pose proof transform_id_left as H'; simpl in H'; rewrite H'.
    reflexivity.


    

        intros; eapply FixList_decode_correct.
    revert H8; eapply Word_decode_correct.
    solve_data_inv.
    unfold encode_decode_correct_f.

    let H' := fresh in
    let data := fresh in
    let H'' := fresh in
    intros H' data H'';
    repeat destruct H'';
    match goal with
    | H : ?P data |- ?P_inv' =>
      is_evar P;
        let P_inv' := (eval pattern data in P_inv') in
        let P_inv := match P_inv' with ?P_inv data => P_inv end in
        let new_P_T := type of P in
        makeEvar new_P_T
                 ltac:(fun new_P =>
                         try unify P (fun data => new_P data /\ P_inv data)); try apply (Logic.proj2 H)
    end.

    shelve_inv.
    split.
    intros.
    unfold encode_EthernetFrame_Spec in H2.
    unfold compose, Bind2 in H2; computes_to_inv.
    computes_to_inv.
