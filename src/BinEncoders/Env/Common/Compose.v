Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Definition compose E
           (transformer : Transformer)
           (encode1 : E -> bin * E)
           (encode2 : E -> bin * E) :=
  fun e0 =>
    let (p, e1) := encode1 e0 in
    let (q, e2) := encode2 e1 in
    (transform p q, e2).

Global Instance compose_decoder A A'
       (cache : Cache)
       (transformer : Transformer)
       (project : A -> A')
       (predicate : A -> Prop)
       (predicate' : A' -> Prop)
       (encode1 : A' -> CacheEncode -> bin * CacheEncode)
       (encode2 : A -> CacheEncode -> bin * CacheEncode)
       (decoder1 : decoder cache transformer predicate' encode1)
       (pred_pf : forall data, predicate data -> predicate' (project data))
       (decoder2 : forall proj,
           decoder cache transformer (fun data => predicate data /\ project data = proj) encode2)
  : decoder cache transformer predicate
            (fun data ctx => compose transformer (encode1 (project data)) (encode2 data) ctx) :=
  { decode := fun bin env => let (bundle, env') := @decode _ _ _ _ _ decoder1 bin env in
                             let (proj, rest) := bundle in
                             @decode _ _ _ _ _ (decoder2 proj) rest env' }.
Proof.
  destruct decoder1 as [decode1 decode1_pf]. simpl.
  intros env env' xenv xenv' data data' bin ext ext' env_pm pred_pm com_pf.
  unfold compose in com_pf.
  destruct (encode1 (project data) env) as [b1 e1] eqn: eq1.
  destruct (encode2 data e1) as [b2 e2] eqn: eq2.
  destruct (decode1 (transform b1 (transform b2 ext)) env') as [[d1 r1] e1'] eqn: eq1'.
  destruct (decode1_pf _ _ _ _ _ _ _ _ _ env_pm (pred_pf _ pred_pm) eq1 eq1') as [de [dp dt]].
  inversion com_pf; subst; clear com_pf.
  rewrite <- transform_assoc. rewrite eq1'.
  destruct (decoder2 (project data)) as [decode2 decode2_pf]. simpl.
  destruct (decode2 (transform b2 ext) e1') as [[d2 r2] e2'] eqn: eq2'.
  specialize (decode2_pf _ _ _ _ _ _ _ _ _ de (conj pred_pm eq_refl) eq2 eq2').
  inversion 1. subst. intuition.
Defined.
