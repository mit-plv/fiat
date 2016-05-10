Require Import
        Fiat.Common.BoundedLookup.
Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.Word.
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
  Context {transformerUnit : TransformerUnit transformer bool}.

  Context {sz : nat}.
  Context {ta : t A (S len)}.
  Variable (tb : t (word sz) (S len)).

  Definition encode_enum (i : BoundedIndex ta) (ce : CacheEncode) : B * CacheEncode :=
    let fin := i.(indexb).(ibound)
    in  encode_word (nth tb fin) ce.

  Definition word_indexed (n : nat) (w : word sz) (t : t (word sz) (S n)) : Fin.t (S n).
    pattern n, t.
    eapply rectS.
    intro. exact Fin.F1.
    intros. destruct (weqb w a).
    - exact Fin.F1.
    - exact (Fin.FS H).
  Defined.

  Definition decode_enum (b : B) (cd : CacheDecode) : BoundedIndex ta * B * CacheDecode.
    destruct (decode_word (sz:=sz) b cd) as [[w b'] cd'].
    refine ({| bindex := _;
               indexb := {| ibound := word_indexed w tb;
                            boundi := _ |} |}, b', cd'); eauto.
  Defined.

  Lemma word_indexed_correct :
    forall n (t : t (word sz) (S n)) (i : Fin.t (S n)),
      word_indexed (nth t i) t = i.
  Proof. (*
    clear.
    intros n t i. revert t. pattern n, i. eapply Fin.rectS.
    - intros. pattern n0, t. eapply caseS. simpl. intros. destruct t0. eauto.
      admit.
    - intros. generalize dependent n0. intro. set (nx := S n0). pattern nx. clearbody nx.

      remember (S n0) as nx. pattern (S n0), t. *)
  Admitted.

  Theorem Enum_decode_correct :
    encode_decode_correct cache transformer (fun _ => True) encode_enum decode_enum.
  Proof.
    unfold encode_decode_correct, encode_enum, decode_enum.
    intros env env' xenv xenv' data data' bin' ext ext' Eeq PPred Penc Pdec.
    destruct (decode_word (transform bin' ext) env') as [[? ?] ?] eqn: ?.
    pose proof (Word_decode_correct _ _ _ _ _ _ _ _ _ Eeq I Penc Heqp).
    inversion Pdec; subst; clear Pdec.
    destruct H as [? [? ?]].
    repeat split; eauto.
    rewrite <- H0. rewrite word_indexed_correct.
    destruct data. destruct indexb. simpl. rewrite <- boundi. reflexivity.
  Qed.
End Enum.