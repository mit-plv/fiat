Require Import Bedrock.Platform.Facade.examples.TuplesF.
Require Import CertifiedExtraction.Utils.
Require Import Bedrock.Memory.

Require Import CertifiedExtraction.Extraction.QueryStructures.Basics.
Require Import CertifiedExtraction.Extraction.QueryStructures.AllOfLength.
Require Import CertifiedExtraction.Extraction.QueryStructures.TupleToListW.
Require Import CertifiedExtraction.Extraction.QueryStructures.Zip2.

Require Import
        Coq.Lists.List
        Coq.Program.Program.

(** Connections of [IndexedEnsemble]s, [Tuple]s, and [GenericTuple W]. *)

Definition IndexedEnsemble_TupleToListW {N} (ensemble: FiatWBag N) : BedrockWBag :=
  fun indexedListW => exists tup, ensemble tup /\ RelatedIndexedTupleAndListW indexedListW tup.

Lemma IndexedEnsemble_TupleToListW_refl :
  forall {N} (tup: FiatWElement N) (ens: FiatWBag N),
    ens tup -> IndexedEnsemble_TupleToListW ens (TupleToListW_indexed tup).
Proof.
  cleanup; red; eauto using RelatedIndexedTupleAndListW_refl.
Qed.

Lemma IndexedEnsemble_TupleToListW_inj_helper:
  forall (N : nat) (e : FiatWBag N) (x : FiatWElement N),
    (IndexedEnsemble_TupleToListW e (IndexedElement_TupleToListW (N := N) x)) <-> e x.
Proof.
  unfold IndexedEnsemble_TupleToListW, RelatedIndexedTupleAndListW;
  repeat match goal with
         | _ => cleanup
         | _ => eassumption
         | _ => progress subst
         | [ x: FiatWElement _ |- _ ] => destruct x
         | [ H: TupleToListW _ = TupleToListW _ |- _ ] => apply TupleToListW_inj in H
         | _ => eexists
         | _ => simpl in *
         end.
Qed.

Lemma lift_eq {A} (f g: A -> Prop) :
  f = g -> (forall x, f x <-> g x).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma IndexedEnsemble_TupleToListW_inj :
  forall {N} (e1 e2: FiatWBag N),
    IndexedEnsemble_TupleToListW e1 = IndexedEnsemble_TupleToListW e2 ->
    e1 = e2.
Proof.
  intros * H; pose proof (lift_eq H); clear H.
  apply Ensembles.Extensionality_Ensembles; unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In.
  repeat cleanup; repeat match goal with
                         | [ H: forall _, _ |- _ ?x ] => specialize (H (IndexedElement_TupleToListW x)); cbv beta in H
                         | [ H: _ |- _ ] => setoid_rewrite IndexedEnsemble_TupleToListW_inj_helper in H
                         end; tauto.
Qed.

Hint Resolve IndexedEnsemble_TupleToListW_inj : inj_db.

Lemma IndexedEnsemble_TupleToListW_length:
  forall (N : nat) (table: FiatWBag N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    AllOfLength_set N (IndexedEnsemble_TupleToListW table).
Proof.
repeat match goal with
       | _ => cleanup
       | _ => progress destruct_conjs
       | _ => progress unfold AllOfLength_set, IndexedEnsemble_TupleToListW,
             RelatedIndexedTupleAndListW, Ensembles.In, GenericTuple in *
       | [ H: _ = _ |- _ ] => rewrite H
       end; auto using TupleToListW_length.
Qed.

Lemma EnsembleIndexedListEquivalence_keepEq_AllOfLength:
  forall {N : nat} {table k default key seq},
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.EnsembleIndexedListEquivalence
      (TuplesF.keepEq eq default (@IndexedEnsemble_TupleToListW N table) k key) seq ->
    AllOfLength_list N seq.
Proof.
  cleanup; eapply EnsembleIndexedListEquivalence_AllOfLength;
  eauto using keepEq_length, IndexedEnsemble_TupleToListW_length.
Qed.

Hint Unfold IndexedEnsembles.EnsembleIndexedListEquivalence
     IndexedEnsembles.UnIndexedEnsembleListEquivalence
     TuplesF.EnsembleIndexedListEquivalence
     TuplesF.UnIndexedEnsembleListEquivalence
     IndexedEnsembles.UnConstrFreshIdx TuplesF.UnConstrFreshIdx : FiatBedrockEquivalences.

Hint Unfold Ensembles.Same_set Ensembles.Included Ensembles.In : Ensembles.

Lemma EnsembleIndexedListEquivalence_TupleToListW_FreshIdx:
  forall (n : nat) (lst : list (FiatWTuple n)) (ens : FiatWBag n),
    TuplesF.EnsembleIndexedListEquivalence
      (IndexedEnsemble_TupleToListW ens) (map TupleToListW lst) ->
    exists bound : nat, IndexedEnsembles.UnConstrFreshIdx ens bound.
Proof.
  repeat match goal with
         | _ => cleanup
         | _ => progress destruct_conjs
         | [ H: context[IndexedEnsemble_TupleToListW ?ens _], H': ?ens ?element |- _ ] =>
           learn (H (TupleToListW_indexed element))
         | _ => progress autounfold with FiatBedrockEquivalences Ensembles in *
         | [  |- exists x, _ ] => eexists
         end; eauto using IndexedEnsemble_TupleToListW_refl.
Qed.


Lemma map_id' :
  forall `{f: A -> A} lst,
    (forall x, List.In x lst -> f x = x) ->
    map f lst = lst.
Proof.
  induction lst; simpl; intros.
  - eauto.
  - f_equal; eauto.
Qed.

Lemma EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv_Characterisation:
  forall (n : nat) (lst : list (FiatWTuple n)) (x : list BedrockWElement),
    map TuplesF.indexedElement x = map TupleToListW lst ->
    map2
      (fun (x0 : BedrockWElement) (y : FiatWTuple n) =>
         TupleToListW_indexed
           {| IndexedEnsembles.elementIndex := TuplesF.elementIndex x0; IndexedEnsembles.indexedElement := y |})
      x lst = x.
Proof.
  unfold TupleToListW_indexed; cleanup; simpl;
  rewrite map2_two_maps, <- H, two_maps_map2;
  apply map_id'; destruct 0; reflexivity.
Qed.

Lemma BedrockWElement_roundtrip:
  forall (b: BedrockWElement),
    {| TuplesF.elementIndex := TuplesF.elementIndex b; TuplesF.indexedElement := TuplesF.indexedElement b |}
    = b.
Proof.
  destruct 0; reflexivity.
Qed.


Lemma IndexedEnsemble_TupleToListW_Characterization :
  forall {N} ens (x: BedrockWElement) (t: FiatWTuple N),
    TuplesF.indexedElement x = TupleToListW t ->
    IndexedEnsemble_TupleToListW (N := N) ens x ->
    ens {| IndexedEnsembles.elementIndex := TuplesF.elementIndex x; IndexedEnsembles.indexedElement := t |}.
Proof.
  cleanup.
  repeat match goal with
         | _ => progress destruct_conjs
         | [ H: TupleToListW _ = TupleToListW _ |- _ ] => apply TupleToListW_inj in H
         | [ H: FiatWElement _ |- _ ] => destruct H
         | [ H: BedrockWElement |- _ ] => destruct H
         | _ => progress unfold IndexedEnsemble_TupleToListW, RelatedIndexedTupleAndListW in H0
         | _ => progress (simpl in *; subst)
         | _ => trivial
         end.
Qed.

Ltac map2_t :=
  match goal with
  | [  |- context[map _ (map2 _ _ _)] ] => unfold map2; rewrite map_map; simpl
  | [  |- context[map ?f (zip2 ?x ?y)] ] => change (map f (zip2 x y)) with (map2 (fun x y => f (x, y)) x y); simpl
  | [ H: In _ (map2 _ _ _) |- _ ] => (unfold map2 in H; rewrite in_map_iff in H)
  | [ H: In (_, _) (zip2 _ _) |- _ ] => learn (in_zip2 _ _ _ _ H)
  | [ H: map _ ?aa = map _ ?bb, H': In (_, _) (zip2 ?aa ?bb) |- _ ] => learn (in_zip2_map_map_eq H H')
  end.

Hint Rewrite
     @map2_fst'
     @map2_snd
     @EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv_Characterisation
  : EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv.

Require Import Coq.Strings.String.

Lemma EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv:
  forall (n : nat) (lst : list (FiatWTuple n)) (ens : FiatWBag n),
    TuplesF.EnsembleIndexedListEquivalence (IndexedEnsemble_TupleToListW ens) (map TupleToListW lst) ->
    IndexedEnsembles.UnIndexedEnsembleListEquivalence ens lst.
Proof.
  repeat match goal with
         | _ => cleanup
         | _ => solve [constructor]
         | _ => progress destruct_conjs
         | _ => progress map2_t

         | [ H: context[IndexedEnsemble_TupleToListW ?ens _] |- context [?ens ?element] ] =>
           specialize (H (TupleToListW_indexed element))
         | [ H: context[IndexedEnsemble_TupleToListW ?ens _], H': ?ens ?element |- _ ] =>
           specialize (H (TupleToListW_indexed element))
         | [ H: ?ens ?element |- _ ] => learn (IndexedEnsemble_TupleToListW_refl element ens H)
         | [ H: map TuplesF.indexedElement ?x = map TupleToListW ?y
             |- map IndexedEnsembles.indexedElement ?var = ?y ] =>
           is_evar var;
             unify var (map2 (fun bedrockElement fiatTuple =>
                                {| IndexedEnsembles.elementIndex := TuplesF.elementIndex bedrockElement;
                                   IndexedEnsembles.indexedElement := fiatTuple |}) x y)
             ; pose "Removing this string will break the match that introduced it (this is Coq bug #3412)"%string
         | [ H: context[In (TupleToListW_indexed ?x) _] |- In ?x _ ] =>
           rewrite <- (Equality.in_map_iff_injective TupleToListW_indexed)
             by (eauto using TupleToListW_indexed_inj)
         | [ H: TuplesF.indexedElement _ = TupleToListW _ |- _ ] => rewrite <- H in *

         | [ H: map _ _ = map _ _ |- _ ] => learn (map_map_sameLength H)
         | _ => progress rewrite BedrockWElement_roundtrip in *
         | _ => progress autounfold with FiatBedrockEquivalences Ensembles in *
         | _ => progress autorewrite with EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv
         | [  |- exists x, _ ] => eexists
         | _ => unfold TupleToListW_indexed in *; simpl in *
         end; apply IndexedEnsemble_TupleToListW_Characterization; try tauto.
Qed.

Lemma ListWToTuple_Truncated_map_keepEq:
  forall (N : nat) (table : FiatWBag N) w,
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    forall (x8 : W) (x9 : list TuplesF.tupl) default,
      TuplesF.EnsembleIndexedListEquivalence
        (TuplesF.keepEq eq default (IndexedEnsemble_TupleToListW table) w x8) x9 ->
      x9 = map TupleToListW (map (ListWToTuple_Truncated N) x9).
Proof.
  cleanup.
  rewrite map_map.
  rewrite map_id'; [ eauto | intros; symmetry; apply ListWToTuple_Truncated_id ].
  apply (EnsembleIndexedListEquivalence_keepEq_AllOfLength H H0); assumption.
Qed.

Lemma EnsembleIndexedListEquivalence_TupleToListW :
  forall n lst ens,
    TuplesF.EnsembleIndexedListEquivalence
      (IndexedEnsemble_TupleToListW ens) (map (TupleToListW (N := n)) lst) ->
    IndexedEnsembles.EnsembleIndexedListEquivalence ens lst.
Proof.
  cleanup.
  split; eauto using EnsembleIndexedListEquivalence_TupleToListW_FreshIdx, EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv.
Qed.

Lemma TuplesF_EnsembleIndexedListEquivalence_EquivEnsembles :
  forall A ens1 ens2,
    Ensembles.Same_set _ ens1 ens2 ->
    forall seq, @TuplesF.EnsembleIndexedListEquivalence A ens1 seq <->
                @TuplesF.EnsembleIndexedListEquivalence A ens2 seq.
Proof.
  intros.
  apply Ensembles.Extensionality_Ensembles in H; rewrite H; reflexivity.
Qed.

Definition FiatWBagEmpty N : FiatWBag N := fun _ => False.

Lemma Empty_lift:
  forall N : nat,
    Empty = IndexedEnsemble_TupleToListW (FiatWBagEmpty N).
Proof.
  intros; apply Ensembles.Extensionality_Ensembles.
  unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In, FiatWBagEmpty, Empty, IndexedEnsemble_TupleToListW; split; intros.
  - exfalso; assumption.
  - repeat cleanup.
Qed.

