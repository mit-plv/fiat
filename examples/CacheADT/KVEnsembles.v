Require Import Coq.Sets.Ensembles.

(* Definitions of basic operations on Ensembles of Key/Value pairs. *)

Section KVEnsembles.

  Context {Key : Type}.
  Context {Value : Type}.

  Definition EnsembleInsert  {A} (a : A) (ens : Ensemble A) (a' : A)
  : Prop := a' = a \/ ens a'.

  Definition SubEnsembleInsert {A} (a : A) (ens ens' : Ensemble A)
  : Prop :=
    forall (a' : A), ens' a' -> EnsembleInsert a ens a'.

  Definition EnsembleRemoveKey
             (k : Key)
             (ens : Ensemble (Key * Value))
             (k' : Key * Value)
  : Prop := (fst k' <> k /\ ens k').

  Definition EnsembleReplaceKey
             (k : Key * Value)
             (ens : Ensemble (Key * Value))
             (k' : Key * Value)
  : Prop := k' = k \/
            (EnsembleRemoveKey (fst k) ens k').

  Definition EnsembleUpdateKey
             (k : Key)
             (ens : Ensemble (Key * Value))
             (f : Value -> Value)
             (kv : Key * Value)
  : Prop := ((fst kv) = k /\ exists v, (snd kv) = f v /\ In _ ens (k, v)) \/
            (EnsembleRemoveKey k ens kv).

  Lemma SubEnsembleInsertReplaceKey
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      SubEnsembleInsert kv r (EnsembleReplaceKey kv r).
  Proof.
    unfold SubEnsembleInsert, EnsembleInsert,
    EnsembleReplaceKey, EnsembleRemoveKey; intros; intuition.
  Qed.

  Lemma SubEnsembleInsertRefl
  : forall (kv : Key * Value)
           (r : Ensemble (Key * Value)),
      SubEnsembleInsert kv r r.
  Proof.
    unfold SubEnsembleInsert, EnsembleInsert;
    intros; eauto.
  Qed.

  Definition ValidLookup
             (r : Ensemble (Key * Value))
             (k : Key)
             (v : option Value)
  : Prop := (v = None -> forall v', ~ r (k, v'))
            /\ forall v', v = Some v' -> r (k, v').

  Definition usedKey
             (r : Ensemble (Key * Value))
             (k : Key)
  : Prop := exists v, r (k, v).

End KVEnsembles.
