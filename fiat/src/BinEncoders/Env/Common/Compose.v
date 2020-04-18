Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Definition compose E B
           (transformer : Transformer B)
           (encode1 : E -> B * E)
           (encode2 : E -> B * E) :=
  fun e0 =>
    let (p, e1) := encode1 e0 in
    let (q, e2) := encode2 e1 in
    (transform p q, e2).

Lemma compose_encode_correct A A' B
      (cache : Cache)
      (transformer : Transformer B)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (encode1 : A' -> CacheEncode -> B * CacheEncode)
      (encode2 : A -> CacheEncode -> B * CacheEncode)
      (decode1 : B -> CacheDecode -> A' * B * CacheDecode)
      (decode1_pf : encode_decode_correct cache transformer predicate' encode1 decode1)
      (decode2 : A' -> B -> CacheDecode -> A * B * CacheDecode)
      (decode2_pf : forall proj,
          encode_decode_correct cache transformer
            (fun data => predicate data /\ project data = proj)
            encode2
            (decode2 proj))
  : encode_decode_correct cache transformer (fun a => predicate' (project a) /\ predicate a)
     (fun (data : A) (ctx : CacheEncode) =>
      compose transformer (encode1 (project data)) (encode2 data) ctx)
     (fun (bin : B) (env : CacheDecode) =>
      let (bundle, env') := decode1 bin env in let (proj, rest) := bundle in decode2 proj rest env').
Proof.
  intros env env' xenv xenv' data data' bin ext ext' env_pm pred_pm com_pf.
  unfold compose in com_pf.
  destruct (encode1 (project data) env) as [b1 e1] eqn: eq1.
  destruct (encode2 data e1) as [b2 e2] eqn: eq2.
  destruct (decode1 (transform b1 (transform b2 ext)) env') as [ [d1 r1] e1'] eqn: eq1'.
  destruct (decode1_pf _ _ _ _ _ _ _ _ _ env_pm (proj1 pred_pm) eq1 eq1') as [de [dp dt] ].
  inversion com_pf; subst; clear com_pf.
  rewrite <- transform_assoc. rewrite eq1'.
  destruct (decode2 (project data) (transform b2 ext) e1') as [ [d2 r2] e2'] eqn: eq2'.
  specialize (decode2_pf (project data)  _ _ _ _ _ _ _ _ _ de (conj (proj2 pred_pm) eq_refl) eq2 eq2').
  inversion 1. subst. intuition.
Qed.
