Require Import
        Fiat.Narcissus.Common.Specs.

Set Implicit Arguments.

Definition compose E B
           (monoid : Monoid B)
           (format1 : E -> B * E)
           (format2 : E -> B * E) :=
  fun e0 =>
    let (p, e1) := format1 e0 in
    let (q, e2) := format2 e1 in
    (mappend p q, e2).

Lemma compose_format_correct A A' B
      (cache : Cache)
      (monoid : Monoid B)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (format1 : A' -> CacheFormat -> B * CacheFormat)
      (format2 : A -> CacheFormat -> B * CacheFormat)
      (decode1 : B -> CacheDecode -> A' * B * CacheDecode)
      (decode1_pf : format_decode_correct monoid predicate' format1 decode1)
      (decode2 : A' -> B -> CacheDecode -> A * B * CacheDecode)
      (decode2_pf : forall proj,
          format_decode_correct monoid
            (fun data => predicate data /\ project data = proj)
            format2
            (decode2 proj))
  : format_decode_correct monoid (fun a => predicate' (project a) /\ predicate a)
     (fun (data : A) (ctx : CacheFormat) =>
      compose monoid (format1 (project data)) (format2 data) ctx)
     (fun (bin : B) (env : CacheDecode) =>
      let (bundle, env') := decode1 bin env in let (proj, rest) := bundle in decode2 proj rest env').
Proof.
  intros env env' xenv xenv' data data' bin ext ext' env_pm pred_pm com_pf.
  unfold compose in com_pf.
  destruct (format1 (project data) env) as [b1 e1] eqn: eq1.
  destruct (format2 data e1) as [b2 e2] eqn: eq2.
  destruct (decode1 (mappend b1 (mappend b2 ext)) env') as [ [d1 r1] e1'] eqn: eq1'.
  destruct (decode1_pf _ _ _ _ _ _ _ _ _ env_pm (proj1 pred_pm) eq1 eq1') as [de [dp dt] ].
  inversion com_pf; subst; clear com_pf.
  rewrite <- mappend_assoc. rewrite eq1'.
  destruct (decode2 (project data) (mappend b2 ext) e1') as [ [d2 r2] e2'] eqn: eq2'.
  specialize (decode2_pf (project data)  _ _ _ _ _ _ _ _ _ de (conj (proj2 pred_pm) eq_refl) eq2 eq2').
  inversion 1. subst. intuition.
Qed.
