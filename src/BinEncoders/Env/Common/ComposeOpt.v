Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose.

Set Implicit Arguments.

Lemma compose_encode_correct A A' B
      (cache : Cache)
      (transformer : Transformer B)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (encode1 : A' -> CacheEncode -> B * CacheEncode)
      (encode2 : A -> CacheEncode -> B * CacheEncode)
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf : encode_decode_correct_f cache transformer predicate' encode1 decode1)
      (pred_pf : forall data, predicate data -> predicate' (project data))
      (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf : forall proj,
          encode_decode_correct_f cache transformer
            (fun data => predicate data /\ project data = proj)
            encode2
            (decode2 proj))
  : encode_decode_correct_f cache transformer predicate
     (fun (data : A) (ctx : CacheEncode) =>
      compose transformer (encode1 (project data)) (encode2 data) ctx)
     (fun (bin : B) (env : CacheDecode) =>
        `(proj, rest, env') <- decode1 bin env;
          decode2 proj rest env').
Proof.
  intros env env' xenv data bin ext env_pm pred_pm com_pf.
  unfold compose in com_pf.
  destruct (encode1 (project data) env) as [b1 e1] eqn: eq1.
  destruct (encode2 data e1) as [b2 e2] eqn: eq2.
  injections.
  destruct (decode1_pf _ _ _ _ _ (transform b2 ext) env_pm (pred_pf _ pred_pm) eq1) as [de [dp dt] ].
  rewrite <- transform_assoc.
  rewrite dp; simpl.
  destruct (decode2_pf (project data) _ _ _ _ _ ext dt (conj pred_pm eq_refl) eq2); intuition eauto.
Qed.
