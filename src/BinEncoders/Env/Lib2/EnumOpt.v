Require Import
        Fiat.Common.BoundedLookup.
Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.WordOpt.
Require Import
        Coq.Vectors.Vector
        Bedrock.Word.

Section Enum.
  Context {len : nat}.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : QueueTransformerOpt transformer bool}.

  Context {sz : nat}.
  Context {ta : t A (S len)}.
  Variable (tb : t (word sz) (S len)).

  Inductive NoDupVector {A}
    : forall {n}, Vector.t A n -> Prop :=
    NoDupVector_nil : NoDupVector (Vector.nil _)
  | NoDupVector_cons : forall (x : A) {n} (l : Vector.t A n),
      ~ Vector.In x l -> NoDupVector l -> NoDupVector (Vector.cons _ x _ l).

  Lemma NoDupVector_invert {A'}
    : forall n (l : Vector.t A' n),
      NoDupVector l
      -> match l with
         | Vector.nil => True
         | Vector.cons a _ l' =>
           ~ Vector.In a l' /\ NoDupVector l'
         end.
  Proof.
    clear; induction 1; eauto.
  Qed.

  Definition encode_enum_Spec (idx : Fin.t _) :
    CacheEncode -> Comp (B * CacheEncode) :=
    encode_word_Spec (nth tb idx).

  Definition encode_enum_Impl (idx : Fin.t _) :
    CacheEncode -> B * CacheEncode :=
    encode_word_Impl (nth tb idx).

  Lemma refine_encode_enum :
    forall idx ce,
      refine (encode_enum_Spec idx ce)
             (ret (encode_enum_Impl idx ce)).
  Proof.
    intros; reflexivity.
  Qed.

  Fixpoint word_indexed {n : nat}
           (w : word sz)
           (t : t (word sz) n) : option (Fin.t n)
    := match t in Vector.t _ n return option (Fin.t n) with
       | nil => None
       | cons w' _ t' =>
         if (weqb w w') then Some (Fin.F1) else
           match word_indexed w t' with
           | Some f => Some (Fin.FS f)
           | None => None
           end
       end.

  Definition decode_enum (b : B)
             (cd : CacheDecode)
    : option (Fin.t _ * B * CacheDecode) :=
    `(w, b', cd') <- decode_word (sz:=sz) b cd;
      Ifopt word_indexed w tb as idx Then
      Some (idx, b', cd')
      Else None.

  Lemma word_indexed_correct :
    forall n (i : Fin.t n) (t : t (word sz) n),
      NoDupVector t
      -> match word_indexed (nth t i) t with
      | Some w' => i = w'
      | None => False
      end.
  Proof.
    clear.
    induction i.
    - intro; pattern n, t; apply Vector.caseS; simpl; intros.
      rewrite (proj2 (weqb_true_iff h h)); eauto.
    - intro; generalize i (IHi (Vector.tl t)); clear.
      pattern n, t; apply Vector.caseS; simpl.
      intros h n0 t0 i; case_eq (word_indexed (nth t0 i) t0); intros;
        apply NoDupVector_invert in H1; intuition subst.
      case_eq (weqb (nth t0 t1) h); intros; eauto.
      apply weqb_true_iff in H0; subst.
      destruct H2; generalize t0 H; clear; induction t1.
      + intro; pattern n, t0; apply Vector.caseS; simpl; intros; econstructor.
      + intro; revert t1 IHt1; pattern n, t0; apply Vector.caseS;
          simpl; intros.
        case_eq (weqb (nth t t1) h); intros; eauto.
        * apply weqb_true_iff in H0; subst; econstructor.
        * rewrite H0 in H.
          econstructor 2; apply IHt1.
          destruct (word_indexed (nth t t1) t); try discriminate.
          f_equal; apply Fin.FS_inj; congruence.
  Qed.

  Theorem Enum_decode_correct
          (tb_OK : NoDupVector tb)
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    : encode_decode_correct_f cache transformer (fun _ => True) (fun _ _ => True) encode_enum_Spec decode_enum P.
  Proof.
    split; unfold encode_enum_Spec, decode_enum.
    { intros env env' xenv c c' ext ? Eeq Ppred Ppred_rest Penc.
      destruct (proj1 (Word_decode_correct P_OK) _ _ _ _ _ ext env_OK Eeq I I Penc) as [? [? ?] ].
      rewrite H; simpl.
      apply (word_indexed_correct _ c) in tb_OK.
      subst; simpl in *.
      destruct (word_indexed (nth tb c) tb);
        intros; simpl in *.
      + eexists; intuition eauto.
        repeat f_equal.
        simpl in H; subst.
        reflexivity.
      + intuition.
    }
    { intros.
      destruct (decode_word bin env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
      destruct (word_indexed w tb) eqn: ? ;
        simpl in *; try discriminate; injections.
      eapply (proj2 (Word_decode_correct P_OK)) in Heqo; eauto;
        destruct Heqo; destruct_ex; intuition; subst.
      simpl.
      unfold encode_word_Spec in *; computes_to_inv; injections.
      unfold encode_word_Spec; repeat eexists; eauto.
      repeat f_equal.
      revert Heqo0; clear.
      remember (S len) as n'; clear len Heqn'.
      revert w tb; induction data.
      - intros w tb; pattern n, tb;
          eapply Vector.caseS; simpl.
        intros; destruct (weqb w h) eqn: ?.
        eapply weqb_true_iff; eauto.
        destruct ( word_indexed w t); try discriminate.
      - intros w tb.
        revert w data IHdata.
        pattern n, tb; eapply Vector.rectS; simpl; intros.
        inversion data.
        intros; destruct (weqb w a) eqn: ?.
        discriminate.
        destruct (word_indexed w v) eqn : ? ; try discriminate.
        eapply IHdata.
        rewrite Heqo.
        f_equal.
        eapply Fin.FS_inj.
        revert Heqo0.
        congruence.
    }
  Qed.
End Enum.

Lemma VectorIn_cons {A} {n}
  : forall (v : Vector.t A n) a a',
    Vector.In a' (Vector.cons _ a _ v) -> a = a' \/ Vector.In a' v.
Proof.
  intros; inversion H; subst; eauto.
  apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto using Peano_dec.eq_nat_dec.
Qed.

Lemma forall_Vector_P {A} (P : A -> Prop) {n}
  : forall v : Vector.t A n,
    Vector.Forall P v
    -> forall idx, P (Vector.nth v idx).
Proof.
  induction v; simpl; intros.
  - inversion idx.
  - revert v IHv H; pattern n, idx; apply Fin.caseS; simpl;
      intros; inversion H; subst; eauto.
    eapply IHv.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto using Peano_dec.eq_nat_dec.
Qed.

Ltac Discharge_NoDupVector :=
  match goal with
  |- NoDupVector _ =>
  repeat econstructor; intro;
  repeat match goal with
         | H : Vector.In _ _ |- _ =>
           first [apply VectorIn_cons in H; destruct H; try discriminate
                 | inversion H]
         end
  end.
