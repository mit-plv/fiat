Require Import BinEncoders.Env.Examples.Dns.
Require Import Bedrock.Memory.
Require Import NArith.

Unset Implicit Arguments.

Definition encode_continue {E B}
           (transformer : Transformer.Transformer B)
           (encode : E -> B * E)
           acc :=
  let (p, e') := encode (snd acc) in
  (Transformer.transform (fst acc) p, e').

Definition compose_acc {E B}
           (transformer : Transformer.Transformer B)
           (encode1 : E -> B * E)
           (encode2 : E -> B * E) e0 :=
  encode_continue transformer encode2 (encode1 e0).

Lemma Compose_compose_acc {E B} :
  forall transformer encode1 encode2 e0,
    @Compose.compose E B transformer encode1 encode2 e0 =
    @compose_acc E B transformer encode1 encode2 e0.
Proof.
  intros; unfold compose_acc, Compose.compose, encode_continue.
  destruct (encode1 _); simpl; destruct (encode2 _); reflexivity.
Qed.

Lemma IList_encode_bools_is_copy:
  forall bits cache,
    (IList.IList_encode' DnsMap.cache Core.btransformer Bool.Bool_encode bits cache) =
    (bits, {| DnsMap.eMap := DnsMap.eMap cache;
              DnsMap.dMap := DnsMap.dMap cache;
              DnsMap.offs := DnsMap.offs cache + (N.of_nat (List.length bits)) |}).
Proof.
  Opaque N.of_nat.
  induction bits; destruct cache; simpl in *.
  + rewrite N.add_0_r; reflexivity.
  + rewrite IHbits; simpl.
    rewrite <- N.add_assoc, N.add_1_l, Nat2N.inj_succ; reflexivity.
    Transparent N.of_nat.
Qed.

Definition EncodeAndPad n length :=
  let encoded := FixInt.encode' n in
  FixInt.pad encoded (length - Datatypes.length encoded).

Lemma FixInt_encode_is_copy {size}:
  forall num cache,
    (FixInt.FixInt_encode (size := size) num cache) =
    (EncodeAndPad (proj1_sig num) size, {| DnsMap.eMap := DnsMap.eMap cache;
                                           DnsMap.dMap := DnsMap.dMap cache;
                                           DnsMap.offs := DnsMap.offs cache + (N.of_nat size) |}).
Proof.
  destruct cache; reflexivity.
Qed.


Definition List16AsWord (ls: {s : list bool | Datatypes.length s = 16}) : W.
Admitted.

Lemma EncodeAndPad_ListAsWord : forall ls, proj1_sig ls = EncodeAndPad (Word.wordToN (List16AsWord ls)) 16.
Admitted.

Lemma NToWord_of_nat:
  forall (sz : nat) (n : nat),
    Word.NToWord _ (N.of_nat n) = Word.natToWord sz n.
Proof.
  intros; rewrite Word.NToWord_nat, Nat2N.id; reflexivity.
Qed.

Lemma NToWord_WordToN:
  forall (sz : nat) (w : Word.word sz),
    Word.NToWord _ (Word.wordToN w) = w.
Proof.
  intros; rewrite Word.NToWord_nat, Word.wordToN_nat, Nat2N.id.
  apply Word.natToWord_wordToNat.
Qed.

Lemma length_of_fixed_length_list :
  forall {size} (ls: {s : list bool | Datatypes.length s = size}),
    List.length (proj1_sig ls) = size.
Proof.
  destruct ls; auto.
Qed.

Lemma FixList_is_IList :
  forall (A bin : Type) (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
    (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
    (xs : list A) (env : Cache.CacheEncode),
    @FixList.FixList_encode' A bin cache transformer A_encode xs env =
    @IList.IList_encode' A bin cache transformer A_encode xs env.
Proof.
  induction xs; simpl; intros.
  + reflexivity.
  + destruct (A_encode _ _).
    rewrite IHxs; reflexivity.
Qed.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.PropertiesOfTelescopes.

Lemma IList_post_transform_TelEq :
  forall {av} {A bin : Type}
    (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
    (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
    (xs : list A) (base : bin) (env : Cache.CacheEncode)
    k__stream (cacheF: Telescope av -> Cache.CacheEncode -> Telescope av) (tenv: Telescope av) ext,
    let fold_on b :=
        List.fold_left (IList.IList_encode'_body cache transformer A_encode) xs (b, env) in
    TelEq ext
      ([[ret (fold_on Transformer.transform_id) as folded]]
         ::[[ k__stream <-- Transformer.transform base (fst folded) as _]] :: cacheF tenv (snd folded))
      ([[ret (fold_on base) as folded]]
         ::[[ k__stream <-- fst folded as _]] :: cacheF tenv (snd folded)).
Proof.
  cbv zeta; intros.
  setoid_rewrite Propagate_anonymous_ret.
  rewrite (IList.IList_encode'_body_characterization _ _ _ _ base).
  destruct (List.fold_left _ _ _); simpl; reflexivity.
Qed.
