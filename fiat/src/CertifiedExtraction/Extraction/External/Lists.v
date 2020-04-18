Require Import
        CertifiedExtraction.Extraction.External.Core.
Require Export Bedrock.Platform.Facade.examples.QsADTs.

Lemma CompileEmpty_helper {A}:
  forall (lst : list A) (w : W),
    Programming.propToWord (lst = @nil A) w ->
    ret (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) ↝ w.
Proof.
  unfold Programming.propToWord, IF_then_else in *.
  destruct lst; simpl in *; destruct 1; repeat cleanup; try discriminate; fiat_t.
Qed.

Hint Resolve CompileEmpty_helper : call_helpers_db.

Lemma ListEmpty_helper :
  forall {A} (seq: list A),
    (EqNat.beq_nat (Datatypes.length seq) 0) = match seq with
                                               | nil => true
                                               | _ :: _ => false
                                               end.
Proof.
  destruct seq; reflexivity.
Qed.

Lemma CompileTupleListEmpty_alt_helper {A}:
  forall lst w,
    Programming.propToWord (lst = @nil A) w ->
    ret (bool2w match lst with
                | nil => true
                | _ :: _ => false
                end) ↝ w.
Proof.
  intros * h.
  apply CompileEmpty_helper in h.
  rewrite <- ListEmpty_helper.
  assumption.
Qed.

Hint Resolve CompileTupleListEmpty_alt_helper : call_helpers_db.

Lemma map_eq_nil_iff {A B} (f: A -> B): forall l, map f l = nil <-> l = nil.
Proof.
  destruct l; simpl; split; reflexivity || discriminate.
Qed.

Lemma propToWord_list_empty_map:
  forall A B (lst : list A)
    (x : W) (f : A -> B),
    Programming.propToWord (map f lst = nil) x -> Programming.propToWord (lst = nil) x.
Proof.
  intros.
  unfold Programming.propToWord, IF_then_else in *.
  setoid_rewrite (map_eq_nil_iff f lst) in H; assumption.
Qed.

Hint Resolve propToWord_list_empty_map : call_helpers_db.
