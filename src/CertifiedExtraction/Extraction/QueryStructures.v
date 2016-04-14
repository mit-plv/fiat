Require Import Fiat.ADT.Core.
Require Import Bedrock.Platform.Facade.DFModule.
Require Import Fiat.ADTNotation.
Require Import Bedrock.Platform.Facade.CompileUnit2.
Require Import Fiat.Common.i3list.
Require Import Fiat.Common.ilist3.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.

Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import CertifiedExtraction.ADT2CompileUnit.
Check BuildCompileUnit2TSpec.

Definition DecomposeIndexedQueryStructure av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  Decomposei3list _ _ rWrap r.
Arguments DecomposeIndexedQueryStructure _ {_ _} _ _ /.

Definition DecomposeIndexedQueryStructurePost av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r r' : IndexedQueryStructure qs_schema Index) :=
  DecomposePosti3list _ _ rWrap r r'.

Definition DecomposeIndexedQueryStructurePre av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  DecomposePrei3list _ _ rWrap r.

Arguments DecomposeIndexedQueryStructurePost _ _ _ _ _ _ / .
Arguments DecomposeIndexedQueryStructurePre _ _ _ _ _ / .

Require Import Benchmarks.QueryStructureWrappers.

(* FIXME move *)
Lemma bool2w_inj:
  forall v v' : bool, bool2w v = bool2w v' -> v = v'.
Proof.
  destruct v, v'; (discriminate || reflexivity).
Qed.

Instance FacadeWrapper_bool {T : Type} : FacadeWrapper (Value T) bool.
Proof.
  refine {| wrap v := SCA _ (bool2w v) |};
  abstract (intros * H; inversion H; eauto using bool2w_inj).
Defined.

Definition UnpairSigT {A B} (P: A * B -> Type) :
  sigT (fun a => sigT (fun b => P (a, b))) -> sigT P :=
  fun s => let (a, s) := s in
           let (b, s) := s in
           existT P (a, b) s.

Definition UnitSigT (P: unit -> Type) :
  P tt -> sigT P :=
  fun s => existT P tt s.

Ltac _repeat_destruct :=
  match goal with
  | _ => apply UnitSigT
  | [  |- forall idx: Fin.t _, _ ] => eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type; simpl
  (*| [  |- context[@SideStuff] ] => econstructor *)
  | [  |- GoodWrapper _ _ ] => econstructor; reflexivity
  | [  |- prim_prod _ _ ] => split
  | [  |- prod _ _ ] => split
  | [  |- unit ] => constructor
  end.

Ltac repeat_destruct :=
  repeat _repeat_destruct.

(* Definition SchedulerWrappers : { rWrap : _ & @SideStuff QsADTs.ADTValue _ _ _ _ PartialSchedulerImpl
                                                        (DecomposeIndexedQueryStructurePre QsADTs.ADTValue _ _ rWrap) }.
Proof.
  simpl;
  repeat_destruct;
  typeclasses eauto.
Defined. *)

Require Bedrock.Platform.Facade.examples.QsADTs.
Require Bedrock.Platform.Facade.examples.TuplesF.

Ltac fiat_t :=
  repeat (eapply BindComputes || apply PickComputes || apply ReturnComputes || simpl).

Fixpoint TruncateList {A} (a: A) n l :=
  match n, l with
  | 0, _ => nil
  | S n, nil => a :: TruncateList a n nil
  | S n, h :: t => h :: TruncateList a n t
  end.

Lemma TruncateList_length {A} n :
  forall (a: A) (l: list A),
    List.length (TruncateList a n l) = n.
Proof.
  induction n, l; simpl; intuition.
Defined.

Lemma TruncateList_id {A} :
  forall (a: A) (l: list A),
    TruncateList a (List.length l) l = l.
Proof.
  induction l; simpl; auto using f_equal.
Qed.

Definition ListWToTuple_Truncated n l : FiatTuple n :=
  @eq_rect nat _ (fun n => FiatTuple n)
           (ListWToTuple (TruncateList (Word.natToWord 32 0) n l))
           n (TruncateList_length n _ _).


Definition ListWToTuple_Truncated' n (l: list W) : FiatTuple n :=
  match (TruncateList_length n (Word.natToWord 32 0) l) in _ = n0 return FiatTuple n0 with
  | eq_refl => (ListWToTuple (TruncateList (Word.natToWord 32 0) n l))
  end.

Lemma ListWToTuple_Truncated_id n l :
  List.length l = n ->
  l = TupleToListW (ListWToTuple_Truncated' n l).
Proof.
  intros; subst.
  unfold ListWToTuple_Truncated'.
  induction l.
  trivial.
  simpl.

  destruct (TruncateList_length (Datatypes.length l) (Word.natToWord 32 0) l).
  rewrite IHl at 1.
  reflexivity.
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

Definition AllOfLength_set {A} N ens :=
  forall x, Ensembles.In _ ens x -> @List.length A (TuplesF.indexedElement x) = N.

Definition AllOfLength_list {A} N seq :=
  forall x, List.In x seq -> @List.length A x = N.

Lemma keepEq_length:
  forall (N : nat) ens (key k : W),
    AllOfLength_set N ens ->
    AllOfLength_set N (TuplesF.keepEq ens key k).
Proof.
  unfold AllOfLength_set, TuplesF.keepEq, Ensembles.In; cleanup; intuition.
Qed.

Lemma TupleToListW_length':
  forall (N : nat) (tuple : FiatTuple N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    Datatypes.length (TupleToListW tuple) = N.
Proof.
  cleanup;
  erewrite <- Word.wordToNat_natToWord_idempotent;
  eauto using TupleToListW_length.
Qed.

Lemma IndexedEnsemble_TupleToListW_length:
  forall (N : nat) (table: FiatBag N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    AllOfLength_set N (IndexedEnsemble_TupleToListW table).
Proof.
  repeat match goal with
         | _ => cleanup
         | _ => progress destruct_conjs
         | _ => progress unfold AllOfLength_set, IndexedEnsemble_TupleToListW, RelatedIndexedTupleAndListW, Ensembles.In
         | [ H: _ = _ |- _ ] => rewrite H
         end; auto using TupleToListW_length'.
Qed.

Lemma UnIndexedEnsembleListEquivalence_AllOfLength:
  forall (N : nat) A ens seq,
    @TuplesF.UnIndexedEnsembleListEquivalence (list A) ens seq ->
    AllOfLength_set N ens ->
    AllOfLength_list N seq.
Proof.
  repeat match goal with
         | _ => cleanup
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ H: exists _, _ |- _ ] => destruct H
         | [ H: In _ (map _ _) |- _ ] => rewrite in_map_iff in H
         | _ => progress unfold TuplesF.UnIndexedEnsembleListEquivalence,
                AllOfLength_set, AllOfLength_list in *
         end; firstorder.
Qed.

Lemma EnsembleIndexedListEquivalence_AllOfLength:
  forall (N : nat) A ens seq,
    @TuplesF.EnsembleIndexedListEquivalence (list A) ens seq ->
    AllOfLength_set N ens ->
    AllOfLength_list N seq.
Proof.
  unfold TuplesF.EnsembleIndexedListEquivalence; cleanup.
  intuition eauto using UnIndexedEnsembleListEquivalence_AllOfLength.
Qed.

Lemma EnsembleIndexedListEquivalence_keepEq_AllOfLength:
  forall {N : nat} {table k key seq},
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.EnsembleIndexedListEquivalence
      (TuplesF.keepEq (@IndexedEnsemble_TupleToListW N table) k key) seq ->
    AllOfLength_list N seq.
Proof.
  cleanup; eapply EnsembleIndexedListEquivalence_AllOfLength;
  eauto using keepEq_length, IndexedEnsemble_TupleToListW_length.
Qed.

Lemma EmptySet_False :
  forall {A} (x: A), Ensembles.Empty_set _ x <-> False.
Proof.
  firstorder.
Qed.

Ltac EnsembleIndexedListEquivalence_nil_t :=
  repeat match goal with
         | _ => cleanup
         | _ => solve [constructor]
         | _ => progress destruct_conjs
         | _ => progress unfold IndexedEnsembles.EnsembleIndexedListEquivalence,
                IndexedEnsembles.UnIndexedEnsembleListEquivalence,
                TuplesF.EnsembleIndexedListEquivalence,
                TuplesF.UnIndexedEnsembleListEquivalence,
                IndexedEnsemble_TupleToListW,
                Ensembles.Same_set, Ensembles.Included, Ensembles.In in *
         | [  |- exists (_: list ?t), _ ] => exists (@nil t)
         | [ H: map _ _ = nil |- _ ] => apply map_eq_nil in H
         | [ H: context[In _ nil] |- _ ] =>
           setoid_rewrite (fun A a => (fun A => proj1 (neg_false A)) _ (@in_nil A a)) in H
         | [  |- context[Ensembles.Empty_set _ _] ] => setoid_rewrite EmptySet_False
         | [ H: context[Ensembles.Empty_set _ _] |- _ ] => setoid_rewrite EmptySet_False in H
         | _ => firstorder
         end.

Lemma IndexedEnsembles_UnIndexedEnsembleListEquivalence_nil :
  forall A ens, IndexedEnsembles.UnIndexedEnsembleListEquivalence ens (@nil A) <->
                Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.

Lemma IndexedEnsembles_EnsembleIndexedListEquivalence_nil :
  forall A ens, IndexedEnsembles.EnsembleIndexedListEquivalence ens (@nil A) <->
                Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.

Lemma TuplesF_UnIndexedEnsembleListEquivalence_nil :
  forall A ens, TuplesF.UnIndexedEnsembleListEquivalence ens (@nil A) <->
                Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.

Lemma TuplesF_EnsembleIndexedListEquivalence_nil :
  forall A ens,
    TuplesF.EnsembleIndexedListEquivalence ens (@nil A) <->
    Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.

(* Lemma IndexedEnsemble_TupleToListW_empty : *)
(*   forall N ens, *)
(*     Ensembles.Same_set _ (@IndexedEnsemble_TupleToListW N ens) (Ensembles.Empty_set _) -> *)
(*     Ensembles.Same_set _ ens (Ensembles.Empty_set _). *)
(* Proof. *)
(*   repeat match goal with *)
(*          | [ H: context[RelatedIndexedTupleAndListW _ _], x: FiatElement _ |- _ ] => *)
(*            specialize (H (TupleToListW_indexed x)) *)
(*          | _ => progress EnsembleIndexedListEquivalence_nil_t *)
(*          end. *)
(* Qed. *)

Definition TupleToListW_indexed {N} (tup: FiatElement N) :=
  {| TuplesF.elementIndex := IndexedEnsembles.elementIndex tup;
     TuplesF.indexedElement := (TupleToListW (IndexedEnsembles.indexedElement tup)) |}.

Lemma RelatedIndexedTupleAndListW_refl :
  forall {N} tup,
    @RelatedIndexedTupleAndListW N (TupleToListW_indexed tup) tup.
Proof.
  cleanup; red; intuition.
Qed.

Lemma IndexedEnsemble_TupleToListW_refl :
  forall {N} (tup: FiatElement N) (ens: FiatBag N),
    ens tup -> IndexedEnsemble_TupleToListW ens (TupleToListW_indexed tup).
Proof.
  cleanup; red; eauto using RelatedIndexedTupleAndListW_refl.
Qed.

Fixpoint zip2 {A1 A2} (aa1: list A1) (aa2: list A2) :=
  match aa1, aa2 with
  | nil, _ => nil
  | _, nil => nil
  | ha1 :: ta1, ha2 :: ta2 => (ha1, ha2) :: (zip2 ta1 ta2)
  end.

Definition map2 {A1 A2 B} (f: A1 -> A2 -> B) aa1 aa2 :=
  map (fun pair => f (fst pair) (snd pair)) (zip2 aa1 aa2).

Ltac map_length_t :=
  repeat match goal with
         | [ H: cons _ _ = cons _ _ |- _ ] => inversion H; subst; clear H
         | [ H: S _ = S _ |- _ ] => inversion H; subst; clear H
         | _ => progress simpl in *; intros
         | _ => discriminate
         | _ => try f_equal; firstorder
         end.

Lemma map_map_sameLength {A1 A2 B}:
  forall {f g aa1 aa2},
    @map A1 B f aa1 = @map A2 B g aa2 ->
    Datatypes.length aa1 = Datatypes.length aa2.
Proof.
  induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map_snd_zip2 {A1 A2}:
  forall {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    map snd (@zip2 A1 A2 aa1 aa2) = aa2.
Proof.
  induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map_fst_zip2' {A1 A2 B}:
  forall {f: _ -> B} {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    map (fun x => f (fst x)) (@zip2 A1 A2 aa1 aa2) = map f aa1.
Proof.
  induction aa1; destruct aa2; map_length_t.
Qed.

Lemma in_zip2 :
  forall {A B} a b aa bb,
    In (a, b) (@zip2 A B aa bb) ->
    (In a aa /\ In b bb).
Proof. (* This lemma is weak *)
  induction aa; destruct bb;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         | [ aa: list ?a, H: forall _: list ?a, _ |- _ ] => specialize (H aa)
         end.
Qed.

Lemma in_zip2_map :
  forall {A B A' B'} fa fb a b aa bb,
    In (a, b) (@zip2 A B aa bb) ->
    In (fa a, fb b) (@zip2 A' B'  (map fa aa) (map fb bb)).
Proof.
  induction aa; destruct bb;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         end.
Qed.


Lemma zip2_maps_same :
  forall {A A' B'} fa fb aa,
    (@zip2 A' B' (@map A A' fa aa) (map fb aa)) =
    map (fun x => (fa x, fb x)) aa.
Proof.
  induction aa;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         end.
Qed.

Lemma TupleToListW_indexed_inj {N}:
  forall (t1 t2: FiatElement N),
    TupleToListW_indexed t1 = TupleToListW_indexed t2 ->
    t1 = t2.
Proof.
  destruct t1, t2; unfold TupleToListW_indexed; simpl.
  intro eq; inversion eq; subst; clear eq.
  f_equal; intuition.
Qed.

Lemma map2_two_maps:
  forall {A B A' B' C} fa fb g aa bb,
    @map2 A B C (fun a b => g (fa a) (fb b)) aa bb =
    @map2 A' B' C (fun a b => g a b) (map fa aa) (map fb bb).
Proof.
  unfold map2;
  induction aa; destruct bb;
  repeat match goal with
         | _ => progress simpl
         | _ => progress intuition
         | [ H: _ = _ |- _ ] => inversion_clear H
         | [ aa: list ?a, H: forall _: list ?a, _ |- _ ] => specialize (H aa)
         end.
Qed.


Hint Unfold IndexedEnsembles.EnsembleIndexedListEquivalence
     IndexedEnsembles.UnIndexedEnsembleListEquivalence
     TuplesF.EnsembleIndexedListEquivalence
     TuplesF.UnIndexedEnsembleListEquivalence
     IndexedEnsembles.UnConstrFreshIdx TuplesF.UnConstrFreshIdx : FiatBedrockEquivalences.

Hint Unfold Ensembles.Same_set Ensembles.Included Ensembles.In : Ensembles.


Lemma EnsembleIndexedListEquivalence_TupleToListW_FreshIdx:
  forall (n : nat) (lst : list (FiatTuple n)) (ens : FiatBag n),
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


Lemma map2_snd {A1 A2}:
  forall {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    @map2 A1 A2 _ (fun x y => y) aa1 aa2 = aa2.
Proof.
  unfold map2; induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map2_fst {A1 A2}:
  forall {aa1 aa2},
    Datatypes.length aa1 = Datatypes.length aa2 ->
    @map2 A1 A2 _ (fun x y => x) aa1 aa2 = aa1.
Proof.
  unfold map2; induction aa1; destruct aa2; map_length_t.
Qed.

Lemma map2_fst' {A1 A2 B}:
  forall {aa1 aa2} f,
    Datatypes.length aa1 = Datatypes.length aa2 ->
    @map2 A1 A2 B (fun x y => f x) aa1 aa2 = map f aa1.
Proof.
  unfold map2; induction aa1; destruct aa2; map_length_t.
Qed.

Lemma two_maps_map2 :
  forall {A A1 A2 B} f1 f2 f aa,
    (@map2 A1 A2 B f (@map A _ f1 aa) (@map A _ f2 aa)) =
    map (fun x => f (f1 x) (f2 x)) aa.
Proof.
  cleanup; unfold map2. rewrite zip2_maps_same, map_map; reflexivity.
Qed.

Lemma EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv_Characterisation:
  forall (n : nat) (lst : list (FiatTuple n)) (x : list BedrockElement),
    map TuplesF.indexedElement x = map TupleToListW lst ->
    map2
      (fun (x0 : BedrockElement) (y : FiatTuple n) =>
         TupleToListW_indexed
           {| IndexedEnsembles.elementIndex := TuplesF.elementIndex x0; IndexedEnsembles.indexedElement := y |})
      x lst = x.
Proof.
  unfold TupleToListW_indexed; cleanup; simpl;
  rewrite map2_two_maps, <- H, two_maps_map2;
  apply map_id'; destruct 0; reflexivity.
Qed.

Lemma in_zip2_map_map_eq :
  forall {A B A' fa fb a b aa bb},
    @map A A' fa aa = @map B A' fb bb ->
    In (a, b) (@zip2 A B aa bb) ->
    fa a = fb b.
Proof.
  cleanup;
  match goal with
  | [ H: map ?f ?l = map ?g ?l', H': In _ (zip2 ?l ?l') |- _ ] =>
    apply (in_zip2_map f g) in H';
      rewrite <- H, zip2_maps_same, in_map_iff in H';
      destruct_conjs; congruence
  end.
Qed.

Lemma BedrockElement_roundtrip:
  forall (b: BedrockElement),
    {| TuplesF.elementIndex := TuplesF.elementIndex b; TuplesF.indexedElement := TuplesF.indexedElement b |}
    = b.
Proof.
  destruct 0; reflexivity.
Qed.


Lemma IndexedEnsemble_TupleToListW_Characterization :
  forall {N} ens (x: BedrockElement) (t: FiatTuple N),
    TuplesF.indexedElement x = TupleToListW t ->
    IndexedEnsemble_TupleToListW (N := N) ens x ->
    ens {| IndexedEnsembles.elementIndex := TuplesF.elementIndex x; IndexedEnsembles.indexedElement := t |}.
Proof.
  cleanup.
  repeat match goal with
         | _ => progress destruct_conjs
         | [ H: TupleToListW _ = TupleToListW _ |- _ ] => apply TupleToListW_inj in H
         | [ H: FiatElement _ |- _ ] => destruct H
         | [ H: BedrockElement |- _ ] => destruct H
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

Lemma EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv:
  forall (n : nat) (lst : list (FiatTuple n)) (ens : FiatBag n),
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
             ; pose "Removing this string will break the match that introduced it (this is Coq bug #3412)"
         | [ H: context[In (TupleToListW_indexed ?x) _] |- In ?x _ ] =>
           rewrite <- (Equality.in_map_iff_injective TupleToListW_indexed)
             by (eauto using TupleToListW_indexed_inj)
         | [ H: TuplesF.indexedElement _ = TupleToListW _ |- _ ] => rewrite <- H in *

         | [ H: map _ _ = map _ _ |- _ ] => learn (map_map_sameLength H)
         | _ => progress rewrite BedrockElement_roundtrip in *
         | _ => progress autounfold with FiatBedrockEquivalences Ensembles in *
         | _ => progress autorewrite with EnsembleIndexedListEquivalence_TupleToListW_UnIndexedEquiv
         | [  |- exists x, _ ] => eexists
         | _ => unfold TupleToListW_indexed in *; simpl in *
         end; apply IndexedEnsemble_TupleToListW_Characterization; try tauto.
Qed.

Lemma ListWToTuple_Truncated_map_keepEq:
  forall (N : nat) (table : FiatBag N) w,
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    forall (x8 : W) (x9 : list TuplesF.tupl),
      TuplesF.EnsembleIndexedListEquivalence
        (TuplesF.keepEq (IndexedEnsemble_TupleToListW table) w x8) x9 ->
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

Lemma Same_set_pointwise :
  forall A s1 s2,
    Ensembles.Same_set A s1 s2 <-> (forall x, s1 x <-> s2 x).
Proof.
  firstorder.
Qed.

Lemma MakeWordHeading_allWords :
  forall {N} (idx: Fin.t N),
    Domain (MakeWordHeading N) idx = W.
Proof.
  unfold MakeWordHeading; induction idx.
  - reflexivity.
  - unfold Domain in *; simpl in *; assumption.
Defined.

Lemma lt_BinNat_lt:
  forall (p p' : nat),
    lt p p' ->
    BinNat.N.lt (BinNat.N.of_nat p) (BinNat.N.of_nat p').
Proof.
  intros; Nomega.nomega.
Qed.

Lemma BinNat_lt_S:
  forall (p p' : nat),
    BinNat.N.lt (BinNat.N.of_nat p) (BinNat.N.of_nat p') ->
    BinNat.N.lt (BinNat.N.of_nat (S p)) (BinNat.N.of_nat (S p')).
Proof.
  intros; Nomega.nomega.
Qed.

Lemma BinNat_lt_of_nat_S:
  forall (p : nat) (q : BinNums.N),
    BinNat.N.lt (BinNat.N.of_nat (S p)) q ->
    BinNat.N.lt (BinNat.N.of_nat p) q.
Proof.
  intros; Nomega.nomega.
Qed.

Opaque BinNat.N.of_nat.
Lemma selN_GetAttributeRaw:
  forall {N} (tup: @RawTuple (MakeWordHeading N)) (idx: Fin.t N),
    let n := (projT1 (Fin.to_nat idx)) in
    BinNat.N.lt (BinNat.N.of_nat n) (Word.Npow2 32) ->
    let k1 := Word.natToWord 32 n in
    Array.selN (TupleToListW tup) (Word.wordToNat k1) =
    match MakeWordHeading_allWords idx with
    | eq_refl => (GetAttributeRaw tup idx)
    end.
Proof.
  induction idx; simpl in *.
  - reflexivity.
  - destruct (Fin.to_nat idx).
    unfold TupleToListW in *; simpl in *; apply lt_BinNat_lt in l.
    intros.
    rewrite Word.wordToNat_natToWord_idempotent in *
      by auto using BinNat_lt_of_nat_S.
    rewrite IHidx by auto using BinNat_lt_of_nat_S; reflexivity.
Qed.
Transparent BinNat.N.of_nat.

Lemma BinNat_lt_Fin_to_nat:
  forall (N : nat) (idx : Fin.t N),
    BinNat.N.lt (BinNat.N.of_nat (projT1 (Fin.to_nat idx))) (BinNat.N.of_nat N).
Proof.
  intros.
  pose proof (projT2 (Fin.to_nat idx)).
  Nomega.nomega.
Qed.

Lemma Fiat_Bedrock_Filters_Equivalence:
  forall (N : nat) (table : FiatBag N) (key : W) (x9 : list TuplesF.tupl)
         (idx1: Fin.t N)
         (k1 := (Word.natToWord 32 (projT1 (Fin.to_nat idx1)))),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.EnsembleIndexedListEquivalence (TuplesF.keepEq (IndexedEnsemble_TupleToListW table) k1 key) x9 ->
    IndexedEnsembles.EnsembleIndexedListEquivalence
      (IndexedEnsembles.IndexedEnsemble_Intersection
         table
         (fun x0 : FiatTuple N =>
            ((if Word.weq match MakeWordHeading_allWords idx1 in _ = W return W with
                          | eq_refl => GetAttributeRaw x0 idx1
                          end key then true else false) && true)%bool = true))
      (map (ListWToTuple_Truncated N) x9).
Proof.
  intros.
  apply EnsembleIndexedListEquivalence_TupleToListW.
  erewrite <- ListWToTuple_Truncated_map_keepEq by eassumption.

  rewrite TuplesF_EnsembleIndexedListEquivalence_EquivEnsembles; try eassumption.

  unfold IndexedEnsemble_TupleToListW, TuplesF.keepEq, Ensembles.Included,
  Ensembles.In, IndexedEnsembles.IndexedEnsemble_Intersection, Array.sel in *.

  rewrite Same_set_pointwise;
    repeat match goal with
           | _ => cleanup
           | _ => eassumption
           | _ => progress unfold RelatedIndexedTupleAndListW, TuplesF.tupl in *
           | [  |- exists _, _ ] => eexists
           | [ H: exists _, _ |- _ ] => destruct H
           | [  |- context[andb _ true] ] => rewrite Bool.andb_true_r
           | [ H: context[andb _ true] |- _ ] => rewrite Bool.andb_true_r in H
           | [ H: (if ?cond then true else false) = _ |- _ ] => destruct cond; try discriminate; [idtac]
           end.

  - rewrite H4.
    set (IndexedEnsembles.indexedElement x0).

    clear H0.

    unfold k1; rewrite selN_GetAttributeRaw; eauto using BinNat.N.lt_trans, BinNat_lt_Fin_to_nat.
  - rewrite H3.
    unfold k1; rewrite selN_GetAttributeRaw by eauto using BinNat.N.lt_trans, BinNat_lt_Fin_to_nat; simpl.
    destruct (Word.weq _ _); (reflexivity || exfalso; eauto).
Qed.

Lemma CompileTuples2_findFirst :
  forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N (idx1 : Fin.t N) (* FIXME should be generalized *)
         (k1 := (Word.natToWord 32 (projT1 (Fin.to_nat idx1)))) k2
         (table: FiatBag N) (key: W)
         (table':= ( results <- {l : list RawTuple |
                                 IndexedEnsembles.EnsembleIndexedListEquivalence
                                   (IndexedEnsembles.IndexedEnsemble_Intersection
                                      (table)
                                      (fun x0 : RawTuple =>
                                         ((if Word.weq match MakeWordHeading_allWords idx1 in _ = W return W with
                                                       | eq_refl => GetAttributeRaw x0 idx1
                                                       end key then true else false) && true)%bool = true)) l};
                     ret (table, results))
                   : Comp (_ * list (FiatTuple N))),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuples2_findFirst) env ->
    Lifted_MapsTo ext tenv vtable (wrap (FacadeWrapper := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) table) ->
    Lifted_MapsTo ext tenv vkey (wrap key) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    NoDuplicates [[[vret; vtable; vkey]]] ->
    vret ∉ ext ->
    vtable ∉ ext ->
    (* IndexedEnsembles.UnConstrFreshIdx table idx -> *)
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
    {{ tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
           :: [[ (@NTSome QsADTs.ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]]
           :: [[ (@NTSome QsADTs.ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
           :: DropName vret (DropName vtable tenv) }} ∪ {{ ext }} // env.
Proof.
  Ltac facade_cleanup_call ::=  (* FIXME: Added a clear dependent instead of clear *)
       match goal with
       | _ => progress cbv beta iota delta [add_remove_many] in *
       | _ => progress cbv beta iota delta [sel] in *
       | [ H: Axiomatic ?s = Axiomatic ?s' |- _ ] => inversion H; subst; clear dependent H
       | [ H: PreCond ?f _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PreCond] in H
       | [ H: PostCond ?f _ _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PostCond] in H
       | [  |- PreCond ?f _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PreCond]
       | [  |- PostCond ?f _ _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PostCond]
       | [ H: WeakEq ?lhs _ |- _ ] => progress learn_all_WeakEq_remove H lhs
       | [ |- context[ListFacts4.mapM] ] => progress simpl ListFacts4.mapM
       | [ H: context[ListFacts4.mapM] |- _ ] => progress simpl ListFacts4.mapM in H
       | [ H: List.combine ?a ?b = _, H': List.length ?a = List.length ?b |- _ ] => learn (combine_inv a b H' H)
       | [ |-  context[List.split (cons _ _)] ] => simpl
       | [ H: context[List.split (cons _ _)] |- _ ] => may_touch H; simpl in H
       | [ H: List.cons _ _ = List.cons _ _ |- _ ] => inversion H; try subst; clear dependent H
       | _ => GLabelMapUtils.normalize
       | _ => solve [GLabelMapUtils.decide_mapsto_maybe_instantiate]
       | [  |- exists _, _ ] => eexists
       end.

  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  fiat_t.
  5:solve[repeat apply DropName_remove; eauto 1].
  4:solve[simpl; eauto using f_equal, ListWToTuple_Truncated_map_keepEq].
  3:solve[fiat_t].
  2:solve[fiat_t].

  wipe.

  apply Fiat_Bedrock_Filters_Equivalence; assumption.
Qed.

Print Assumptions CompileTuples2_findFirst.

Lemma Lifted_MapsTo_Ext:
  forall `{FacadeWrapper (Value av) A} ext k v tenv,
    StringMap.MapsTo k v ext ->
    @Lifted_MapsTo av ext tenv k (wrap v).
Proof.
  unfold Lifted_MapsTo, LiftPropertyToTelescope.
  SameValues_Facade_t.
Qed.

Lemma Lifted_MapsTo_SCA_not_mapsto_adt:
  forall {av} ext k (v: W) tenv,
    StringMap.MapsTo k (SCA _ v) ext ->
    @Lifted_not_mapsto_adt av ext tenv k.
Proof.
  unfold Lifted_not_mapsto_adt, LiftPropertyToTelescope; intros.
  SameValues_Facade_t.
Qed.

Ltac Lifted_t ::=
     repeat match goal with
            | _ => congruence
            | [  |- _ ∉ _ ] => decide_not_in
            | [  |- StringMap.MapsTo _ _ _ ] => decide_mapsto
            | [  |- NotInTelescope _ _ ] => decide_NotInTelescope
            | [  |- TelEq _ _ _ ] => reflexivity
            | [  |- Lifted_MapsTo _ (Cons (NTSome ?k) _ _) ?k' _ ] => apply Lifted_MapsTo_eq
            | [  |- Lifted_MapsTo _ (Cons (NTSome ?k) _ _) ?k' _ ] => apply Lifted_MapsTo_neq; [ congruence | ]
            | [ H: StringMap.MapsTo ?k _ ?ext |- Lifted_MapsTo ?ext _ ?k _ ] => apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate
            | [  |- Lifted_not_mapsto_adt _ (Cons (NTSome ?k) _ _) ?k' ] => apply Lifted_not_mapsto_adt_eq
            | [  |- Lifted_not_mapsto_adt _ (Cons (NTSome ?k) _ _) ?k' ] => apply Lifted_not_mapsto_adt_neq; [ congruence | ]
            | [  |- Lifted_not_mapsto_adt _ _ _ ] => apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; [ decide_not_in | decide_NotInTelescope ]
            | [ H: StringMap.MapsTo ?k _ ?ext |- Lifted_not_mapsto_adt ?ext _ ?k ] => eapply Lifted_MapsTo_SCA_not_mapsto_adt; decide_mapsto_maybe_instantiate
            | [  |- Lifted_is_true _ _ _ ] => apply Lifted_is_true_eq_MapsTo (* Coercions make precise matching hard *)
            end.

Ltac _PreconditionSet_t_in H ::=
     cbv beta iota zeta delta [PreconditionSet PreconditionSet_helper NoDuplicates NoDuplicates_helper] in H; destruct_ands H.

Lemma CompileTuples2_findFirst_spec :
  forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N
         (idx1 : Fin.t N)
         (k1 := (Word.natToWord 32 (projT1 (Fin.to_nat idx1))))
         k2
         (table: FiatBag N) (key: W)
         (table':= ( results <- {l : list RawTuple |
                                 IndexedEnsembles.EnsembleIndexedListEquivalence
                                   (IndexedEnsembles.IndexedEnsemble_Intersection
                                      (table)
                                      (fun x0 : RawTuple =>
                                         ((if Word.weq match MakeWordHeading_allWords idx1 in _ = W return W with
                                                       | eq_refl => GetAttributeRaw x0 idx1
                                                       end key then true else false) && true)%bool = true)) l};
                     ret (table, results))
                   : Comp (_ * list (FiatTuple N))),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuples2_findFirst) env ->
    StringMap.MapsTo vkey (wrap key) ext ->
    PreconditionSet tenv ext [[[vret; vtable]]] ->
    vret <> vkey ->
    vtable <> vkey ->
    TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
    {{ [[ (@NTSome QsADTs.ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- table as _]] :: tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
           :: [[ (@NTSome QsADTs.ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]]
           :: [[ (@NTSome QsADTs.ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
           :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply generalized CompileTuples2_findFirst; repeat (compile_do_side_conditions || Lifted_t || PreconditionSet_t).
  setoid_rewrite (DropName_NotInTelescope _ _ H12).
  rewrite DropName_Cons_None.
  setoid_rewrite (DropName_NotInTelescope _ _ H10).
  decide_TelEq_instantiate.
Qed.

Lemma CompileWordList_empty_helper:
  forall (N : nat) (lst : list (FiatTuple N)) (x1 : W),
    Programming.propToWord (map TupleToListW lst = nil) x1 -> ret (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) ↝ x1.
Proof.
  unfold Programming.propToWord, IF_then_else in *.
  destruct lst; simpl in *; destruct 1; repeat cleanup; try discriminate; fiat_t.
Qed.

Hint Resolve CompileWordList_empty_helper : call_helpers_db.

Lemma CompileTupleList_Empty:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
         (fpointer : GLabelMap.key) (lst : list _),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) lst) ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_empty) env ->
    {{ tenv }}
      Call vtest fpointer (vlst :: nil)
      {{ [[`vtest <-- (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  rewrite add_remove_comm by congruence.
  rewrite <- add_redundant_cancel by assumption.
  facade_eauto.
Qed.

Lemma CompileTupleList_Empty_spec:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
         (fpointer : GLabelMap.key) (lst : list _),
    vlst <> vtest ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    StringMap.MapsTo vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) lst) ext ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_empty) env ->
    {{ tenv }}
      Call vtest fpointer (vlst :: nil)
      {{ [[`vtest <-- (bool2w (EqNat.beq_nat (Datatypes.length (rev lst)) 0)) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite rev_length.
  apply generalized CompileTupleList_Empty; repeat (compile_do_side_conditions || Lifted_t).
Qed.

Ltac QS_t := match goal with
             | |- not_mapsto_adt _ _ = true => eapply not_In_Telescope_not_in_Ext_not_mapsto_adt; eassumption
             | _ => SameValues_Facade_t_step
             | _ => facade_cleanup_call
             | _ => LiftPropertyToTelescope_t
             | _ => PreconditionSet_t
             end.

Lemma CompileTuple_new_RunsTo_characterization:
  forall (vlen vtup : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fnew : GLabelMap.key) (initial_state st' : State QsADTs.ADTValue) (w: W),
    StringMap.MapsTo vlen (wrap w) initial_state ->
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.Tuple_new) env ->
    RunsTo env (Call vtup fnew [[[vlen]]]) initial_state st' ->
    exists x1, M.Equal st' ([vtup <-- ADT (QsADTs.Tuple x1)]::initial_state) /\ Datatypes.length x1 = Word.wordToNat w.
Proof.
  repeat QS_t.
  reflexivity.
Qed.

Instance QS_WrapBedrockTuple : FacadeWrapper QsADTs.ADTValue (TuplesF.tupl).
Proof.
  refine {| wrap tp := QsADTs.Tuple tp;
            wrap_inj := _ |}; Wrapper_t.
Defined.

Lemma CompileTuple_set_RunsTo_characterization:
  forall (vlen vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fset : GLabelMap.key) (initial_state st' : State QsADTs.ADTValue) (tup: TuplesF.tupl) (val pos: W),
    StringMap.MapsTo v (wrap val) initial_state ->
    StringMap.MapsTo vpos (wrap pos) initial_state ->
    StringMap.MapsTo vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapBedrockTuple))) tup) initial_state ->
    GLabelMap.MapsTo fset (Axiomatic QsADTs.Tuple_set) env ->
    RunsTo env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state st' ->
    M.Equal st' ([vtmp <-- QsADTs.SCAZero]::[vtup <-- ADT (QsADTs.Tuple (Array.upd tup pos val))]::initial_state).
Proof.
  repeat QS_t.
  reflexivity.
Qed.

(* Lemma CompileTuple_set_characterization': *)
(*   forall (vlen vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) N *)
(*     (fset : GLabelMap.key) (initial_state st' : State QsADTs.ADTValue) (tup: FiatTuple N) (val pos: W), *)
(*     StringMap.MapsTo v (wrap val) initial_state -> *)
(*     StringMap.MapsTo vpos (wrap pos) initial_state -> *)
(*     StringMap.MapsTo vtup (wrap tup) initial_state -> *)
(*     GLabelMap.MapsTo fset (Axiomatic QsADTs.Tuple_set) env -> *)
(*     RunsTo env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state st' -> *)
(*     M.Equal st' ([vtmp <-- QsADTs.SCAZero]::[vtup <-- ADT (QsADTs.Tuple (Array.upd (TupleToListW tup) pos val))]::initial_state). *)
(* Proof. *)
(*   repeat QS_t. *)
(*   reflexivity. *)
(* Qed. *)


Lemma CompileTuple_set_Safe:
  forall (vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fset : GLabelMap.key) (initial_state : State QsADTs.ADTValue) (tup: TuplesF.tupl) (val pos: W),
    StringMap.MapsTo v (wrap val) initial_state ->
    StringMap.MapsTo vpos (wrap pos) initial_state ->
    StringMap.MapsTo vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapBedrockTuple))) tup) initial_state ->
    GLabelMap.MapsTo fset (Axiomatic QsADTs.Tuple_set) env ->
    not_mapsto_adt vtmp initial_state = true ->
    Word.wlt pos (IL.natToW (Datatypes.length tup)) ->
    Safe env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call).
Qed.

Lemma CompileTuple_new_Safe:
  forall (vlen vtup : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue))
         (fnew : GLabelMap.key) (initial_state : State QsADTs.ADTValue) (w: W),
    StringMap.MapsTo vlen (wrap w) initial_state ->
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.Tuple_new) env ->
    not_mapsto_adt vtup initial_state = true ->
    ~ Word.wlt w (Word.natToWord 32 2) ->
    Safe env (Call vtup fnew [[[vlen]]]) initial_state.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call).
Qed.

Lemma not_mapsto_adt_eq_SCA:
  forall (av : Type) (k : StringMap.key) (w : W) (fmap : StringMap.t (Value av)),
    not_mapsto_adt k (StringMap.add k (SCA av w) fmap) = true.
Proof.
  eauto using MapsTo_SCA_not_mapsto_adt, StringMap.add_1.
Qed.

Ltac not_mapsto_adt_external_t :=
  PreconditionSet_t;
  repeat match goal with
         | [ H: ?k <> ?s |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] =>
           apply not_mapsto_adt_neq_remove'; [ congruence | ]
         | [ H: ?s <> ?k |- not_mapsto_adt ?k (StringMap.add ?s _ _) = true ] =>
           apply not_mapsto_adt_neq_remove'; [ congruence | ]
         | [  |- not_mapsto_adt ?k (StringMap.add ?k _ _) = true ] =>
           apply not_mapsto_adt_eq_SCA
         end.

(* Remove Hints Bool.trans_eq_bool. *)

Lemma CompileTuple_new :
  forall (v1 v2 v3 o1 o2 o3 vlen vtup vtmp : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
         (val1 val2 val3: W)
         (fnew fset : GLabelMap.key),
    NoDuplicates [[[v1;v2;v3;o1;o2;o3;vtup;vlen;vtmp]]] ->
    StringMap.MapsTo v1 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) val1) ext ->
    StringMap.MapsTo v2 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) val2) ext ->
    StringMap.MapsTo v3 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) val3) ext ->
    StringMap.MapsTo o1 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 0)) ext ->
    StringMap.MapsTo o2 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 1)) ext ->
    StringMap.MapsTo o3 (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 2)) ext ->
    StringMap.MapsTo vlen (wrap (FacadeWrapper := @FacadeWrapper_SCA QsADTs.ADTValue) (Word.natToWord 32 3)) ext ->
    NotInTelescope vtup tenv ->
    NotInTelescope vtmp tenv ->
    vtup ∉ ext ->
    vtmp ∉ ext ->
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.Tuple_new) env ->
    GLabelMap.MapsTo fset (Axiomatic QsADTs.Tuple_set) env ->
    {{ tenv }}
      (Seq (Call vtup fnew (vlen :: nil))
           (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                     (Call vtmp fset (vtup :: o3 :: v3 :: nil)))))
      {{ [[(NTSome (H := WrapInstance (H := QS_WrapTuple)) vtup) <-- ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
           :: [[(NTSome (H := @FacadeWrapper_SCA QsADTs.ADTValue) vtmp) <-- (Word.natToWord 32 0) as _]]
           :: (DropName vtup (DropName vtmp tenv)) }} ∪ {{ ext }} // env.
Proof.
  unfold ProgOk.
  Time repeat repeat match goal with
                     | _ => cleanup
                     | _ => reflexivity
                     | |- Safe _ (Seq _ _) _ => econstructor
                     | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] => inversion' H
                     | _ => eapply SameValues_MapsTo_Ext_State; eassumption
                     | _ => eapply StringMap.add_1; [ congruence ]
                     | _ => eapply StringMap.add_2; [ PreconditionSet_t; congruence | ]
                     | [  |- context[Datatypes.length (Array.upd _ _ _)] ] => rewrite Arrays.upd_length
                     | [ H: RunsTo _ _ _ _ |- _ ] =>
                       eapply CompileTuple_new_RunsTo_characterization in H; [ | clear H; try eassumption.. ]
                     | [ H: RunsTo _ _ _ _ |- _ ] =>
                       eapply CompileTuple_set_RunsTo_characterization in H; [ | clear H; try eassumption.. ]
                     | [  |- Safe _ _ _ ] => eapply CompileTuple_new_Safe
                     | [  |- Safe _ _ _ ] => eapply CompileTuple_set_Safe
                     | [ H: StringMap.Equal ?m1 ?m2 |- StringMap.MapsTo _ _ ?m1 ] => rewrite H
                     | [ H: StringMap.Equal ?m1 ?m2 |- not_mapsto_adt _ _ = _ ] => rewrite H
                     | [ H: StringMap.Equal ?m1 ?m2 |- Safe _ _ ?m1 ] => rewrite H
                     | [ H: ?a = _ |- context[?a] ] => rewrite H
                     | [ |- not_mapsto_adt _ _ = true ] => solve [not_mapsto_adt_external_t; facade_eauto]
                     end.

  repeat StringMap_t.

  Ltac cleanup_StringMap_head :=
    repeat ((rewrite <- add_remove_comm; [ | PreconditionSet_t; congruence ]) ||
                                                                              (rewrite remove_trickle; [ | reflexivity])).

  apply TelEq_swap.

  wipe.                         (* FIXME remove this *)
  repeat match goal with
         | [ H: _ <> _ |- _ ] => clear dependent H
         end.

  (* Notation "[[ 'NTSOME' [ A ]  [ B ]  [ C ]  [ D ]   <--   v 'as' kk ]] :: t" := (Cons (@NTSome A B C D) (Return v) (fun kk => t)) (at level 0). *)

  change QsADTs.SCAZero with (wrap (WrappingType := (Value QsADTs.ADTValue)) (Word.natToWord 32 0)).
  apply SameValues_Pop_Both; [ apply (eq_ret_compute eq_refl) | ].
  cleanup_StringMap_head.

  replace (Array.upd (Array.upd (Array.upd x (Word.natToWord 32 0) val1) (Word.natToWord 32 1) val2)
                     (Word.natToWord 32 2) val3) with [[[val1; val2; val3]]].
  change (ADT (QsADTs.Tuple [[[val1; val2; val3]]])) with
  (wrap (WrappingType := (Value QsADTs.ADTValue)) (ListWToTuple [[[val1; val2; val3]]])).
  apply SameValues_Pop_Both; [ apply (eq_ret_compute eq_refl) | ].
  cleanup_StringMap_head.

  repeat apply DropName_remove; try eassumption.

  do 4 try destruct x as [ | ? x ];
    match goal with
    | [ H: context[Datatypes.length] |- _ ] => simpl in H; try discriminate H
    end.
  reflexivity.
Qed.

Print Assumptions CompileTuple_new.

Ltac side_conditions_fast :=
  repeat match goal with
         | _ => apply CompileDeallocSCA_discretely; [ .. | apply ProgOk_Chomp_Some; intros ]
         | |- NotInTelescope _ _ => simpl; repeat (split; intro; [ congruence | intros ]); eassumption
         | [  |- _ ∉ _ ] => decide_not_in
         end.

Lemma CompileTuple_new_spec :
  forall (v1 v2 v3 o1 o2 o3 vlen vtup vtmp : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
         (val1 val2 val3: W) setup
         (fnew fset : GLabelMap.key),
    NoDuplicates [[[v1;v2;v3;o1;o2;o3;vtup;vlen;vtmp]]] ->
    vlen ∉ ext -> NotInTelescope vlen tenv ->
    o3 ∉ ext -> NotInTelescope o3 tenv ->
    o2 ∉ ext -> NotInTelescope o2 tenv ->
    o1 ∉ ext -> NotInTelescope o1 tenv ->
    v3 ∉ ext -> NotInTelescope v3 tenv ->
    v2 ∉ ext -> NotInTelescope v2 tenv ->
    v1 ∉ ext -> NotInTelescope v1 tenv ->
    NotInTelescope vtup tenv -> NotInTelescope vtmp tenv ->
    vtup ∉ ext ->
    vtmp ∉ ext ->
    GLabelMap.MapsTo (elt:=FuncSpec QsADTs.ADTValue) fnew (Axiomatic QsADTs.Tuple_new) env ->
    GLabelMap.MapsTo (elt:=FuncSpec QsADTs.ADTValue) fset (Axiomatic QsADTs.Tuple_set) env ->
    {{ tenv }}
      setup
      {{ [[`v1 <-- val1 as _]]
           :: [[`v2 <-- val2 as _]]
           :: [[`v3 <-- val3 as _]]
           :: [[`o1 <-- (Word.natToWord 32 0) as _]]
           :: [[`o2 <-- (Word.natToWord 32 1) as _]]
           :: [[`o3 <-- (Word.natToWord 32 2) as _]]
           :: [[`vlen <-- (Word.natToWord 32 3) as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq setup
           (Seq (Call vtup fnew (vlen :: nil))
                (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                     (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                          (Call vtmp fset (vtup :: o3 :: v3 :: nil))))))
      {{ [[`vtup <-- ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
           :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R.
  hoare. hoare. PreconditionSet_t.
  side_conditions_fast.
  computes_to_inv; subst.
  apply generalized CompileTuple_new;
    repeat match goal with
           | _ => congruence
           | _ => decide_not_in
           | _ => decide_mapsto_maybe_instantiate
           | _ => compile_do_side_conditions
           end.
  apply ProgOk_Chomp_Some; try side_conditions_fast. intros.
  PreconditionSet_t; side_conditions_fast; apply CompileSkip.
Qed.

Ltac explode n :=
  match n with
  | 0 => idtac
  | S ?n =>
    compile_do_use_transitivity_to_handle_head_separately;
      [ | apply ProgOk_Chomp_Some; [ | intros; explode n ] ]
  end.

Lemma CompileTuple_Delete:
  forall (vtmp vtup vsize : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
         (fpointer : GLabelMap.key) (tup : FiatTuple N),
    vtup <> vtmp ->
    vtmp ∉ ext ->
    vtup ∉ ext ->
    (* vsize ∉ ext -> *)
    Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTuple (N := N)))) tup) ->
    Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_delete) env ->
    {{ tenv }}
      Call vtmp fpointer (vtup :: vsize :: nil)
      {{ [[`vtmp <-- (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vtup tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; eauto 1.
Qed.


Lemma CompileTuple_Delete_spec:
  forall (vtmp vtup vsize : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
         (fpointer : GLabelMap.key) (tup : FiatTuple N),
    vtup <> vtmp ->
    vtup <> vsize ->
    vsize <> vtmp ->
    vtmp ∉ ext ->
    vtup ∉ ext ->
    vsize ∉ ext ->
    NotInTelescope vtmp tenv ->
    NotInTelescope vtup tenv ->
    NotInTelescope vsize tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_delete) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTuple (N := N)))) vtup) <-- tup as _]] :: tenv }}
      (Seq (Assign vsize (Const (Word.natToWord 32 N))) (Call vtmp fpointer (vtup :: vsize :: nil)))
      {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R; hoare.
  hoare. apply CompileConstant; try compile_do_side_conditions.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros; computes_to_inv; subst; simpl.
  apply generalized CompileTuple_Delete; try (compile_do_side_conditions ||  Lifted_t).
  apply Lifted_MapsTo_Ext; compile_do_side_conditions.
  repeat match goal with
         | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         end.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Qed.

Lemma minFresh_UnConstrFresh :
  forall n table idx,
    TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW (N := n) table) idx ->
    IndexedEnsembles.UnConstrFreshIdx table idx.
Proof.
  unfold TuplesF.minFreshIndex, IndexedEnsembles.UnConstrFreshIdx; intros.
  intuition.
  unfold TuplesF.UnConstrFreshIdx in *.
  assert (IndexedEnsemble_TupleToListW table
                                       {| TuplesF.elementIndex := IndexedEnsembles.elementIndex element;
                                          TuplesF.indexedElement := TupleToListW (IndexedEnsembles.indexedElement element)
                                       |}).
  unfold IndexedEnsemble_TupleToListW; intros; eexists; split; eauto.
  unfold RelatedIndexedTupleAndListW; simpl; intuition.
  apply H1 in H; eauto.
Qed.

Lemma Ensembles_Union_Or:
  forall {A} s1 s2 x,
    @Ensembles.Union A s1 s2 x <-> s1 x \/ s2 x.
Proof.
  split; intros ** H.
  inversion H; firstorder.
  destruct H; [ apply Ensembles.Union_introl | apply Ensembles.Union_intror ]; firstorder.
Qed.

Lemma Ensembles_Singleton_Eq:
  forall {A} x x',
    @Ensembles.Singleton A x x' <-> x = x'.
Proof.
  split; intros ** H; inversion H; firstorder.
Qed.

Lemma minFreshIndex_unique:
  forall {table : BedrockBag} {x y : nat},
    TuplesF.minFreshIndex table x ->
    TuplesF.minFreshIndex table y ->
    x = y.
Proof.
  intros ** [x_ok x_minimal] [y_ok y_minimal].
  specialize (x_minimal y).
  specialize (y_minimal x).
  destruct (Compare_dec.lt_eq_lt_dec x y) as [ [ ? | ? ] | ? ]; intuition.
Qed.

Lemma Fiat_Bedrock_Insert:
  forall (N : nat) (table : FiatBag N) (tuple : FiatTuple N) (x : nat),
    Ensembles.Same_set TuplesF.IndexedElement
                       (TuplesF.insertAt (IndexedEnsemble_TupleToListW table) x (TupleToListW tuple))
                       (IndexedEnsemble_TupleToListW
                          (Ensembles.Add (FiatElement N) table
                                         {| IndexedEnsembles.elementIndex := x; IndexedEnsembles.indexedElement := tuple |})).
Proof.
  intros; rewrite Same_set_pointwise.

  unfold IndexedEnsemble_TupleToListW, TuplesF.insertAt, TuplesF.EnsembleInsert, Ensembles.Add.
  setoid_rewrite Ensembles_Union_Or.
  setoid_rewrite Ensembles_Singleton_Eq.

  unfold RelatedIndexedTupleAndListW.
  repeat match goal with
         | _ => cleanup
         | _ => eassumption
         | [ H: _ \/ _ |- _ ] => destruct H
         | [ H: exists _, _ |- _ ] => destruct H
         | _ => solve [eauto]
                      (* | [  |- exists _, _ ] => solve [eexists; firstorder] *)
         end.

  simpl in *; subst.
  destruct x0; simpl in *; subst; eauto.
Qed.

Lemma CompileTuples2_insert :
  forall vret vtable vtuple fpointer (env: Env QsADTs.ADTValue) ext tenv N k1 k2 idx
    (table: FiatBag N) (tuple: FiatTuple N),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuples2_insert) env ->
    Lifted_MapsTo ext tenv vtable (wrap (FacadeWrapper := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) table) ->
    Lifted_MapsTo ext tenv vtuple (wrap tuple) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    NoDuplicates [[[vret; vtable; vtuple]]] ->
    vret ∉ ext ->
    vtable ∉ ext ->
    vtuple ∉ ext ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW table) idx ->
    {{ tenv }}
      Call vret fpointer (vtable :: vtuple :: nil)
      {{ [[ ( freshIdx <- {freshIdx : nat | IndexedEnsembles.UnConstrFreshIdx table freshIdx};
                ret (Ensembles.Add IndexedEnsembles.IndexedElement table
                                   {| IndexedEnsembles.elementIndex := freshIdx;
                                      IndexedEnsembles.indexedElement := tuple |})) as rep ]]
           :: [[`vret <-- (Word.natToWord 32 0) as _ ]]
           :: [[ (NTSome (H := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) vtable) <-- rep as _ ]]
           :: DropName vtable (DropName vret (DropName vtuple tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
  facade_eauto.
  fiat_t.
  apply minFresh_UnConstrFresh; eauto.
  facade_eauto.
  facade_eauto.

  repeat f_equal.
  apply Ensembles.Extensionality_Ensembles.

  lazymatch goal with
  | [ H: TuplesF.minFreshIndex _ ?x, H': TuplesF.minFreshIndex _ ?y |- _ ] =>
    learn (minFreshIndex_unique H H'); subst
  end.

  apply Fiat_Bedrock_Insert.
  repeat apply DropName_remove; eauto 1.
Qed.

Lemma CompileTuples2_insert_spec :
  forall vtmp vtable vtuple fpointer (env: Env QsADTs.ADTValue) ext tenv N k1 k2 idx
    (table: FiatBag N) (tuple: FiatTuple N),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuples2_insert) env ->
    NoDuplicates [[[vtmp; vtable; vtuple]]] ->
    vtmp ∉ ext ->
    vtable ∉ ext ->
    vtuple ∉ ext ->
    NotInTelescope vtmp tenv ->
    NotInTelescope vtuple tenv ->
    NotInTelescope vtable tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW table) idx ->
    {{ [[ (NTSome (H := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) vtable) <-- table as _ ]]
         :: [[ (NTSome (H := @WrapInstance _ _ QS_WrapTuple) vtuple) <-- tuple as _ ]]
         :: tenv }}
      Call vtmp fpointer (vtable :: vtuple :: nil)
      {{ [[ ( freshIdx <- {freshIdx : nat | IndexedEnsembles.UnConstrFreshIdx table freshIdx};
                ret (Ensembles.Add IndexedEnsembles.IndexedElement table
                                   {| IndexedEnsembles.elementIndex := freshIdx;
                                      IndexedEnsembles.indexedElement := tuple |})) as rep ]]
           :: [[ (NTSome (H := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) vtable) <-- rep as _ ]]
           :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros. PreconditionSet_t.
  apply ProgOk_Remove_Skip_R; hoare.
  apply generalized CompileTuples2_insert; repeat (compile_do_side_conditions || Lifted_t).
  eauto.
  apply ProgOk_Chomp_None; intros.
  repeat match goal with
         | [ H: NotInTelescope ?k ?tenv |- context[DropName ?k ?tenv] ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         | _ => fold @DropName
         end.
  apply CompileDeallocSCA_discretely; repeat (compile_do_side_conditions || decide_NotInTelescope).
  apply CompileSkip.
Qed.

Lemma CompileWordList_pop:
  forall (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) tenv ext
    (fpop : GLabelMap.key) head (tail : list W),
    vlst <> vhead ->
    vhead ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) (head :: tail)) ->
    Lifted_not_mapsto_adt ext tenv vhead ->
    GLabelMap.MapsTo fpop (Axiomatic QsADTs.WordList_pop) env ->
    {{ tenv }}
      Call vhead fpop (vlst :: nil)
    {{ [[`vhead <-- head as _]]::[[(NTSome vlst (H := WrapInstance (H := QS_WrapWordList))) <-- tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileWordList_new:
  forall (vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) tenv ext
    (fnew : GLabelMap.key),
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.WordList_new) env ->
    {{ tenv }}
      Call vlst fnew (nil)
    {{ [[(NTSome vlst (H := WrapInstance (H := QS_WrapWordList))) <-- @nil W as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
  change (ADT (QsADTs.WordList [])) with (wrap (FacadeWrapper := WrapInstance (H := @QS_WrapWordList)) []).
  facade_eauto.
Qed.

(* Lemma CompileTupleList_op: *)
(*   forall {N} (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) tenv ext *)
(*     (fpop : GLabelMap.key) head (tail : list (FiatTuple N)), *)
(*     vlst <> vhead -> *)
(*     vhead ∉ ext -> *)
(*     vlst ∉ ext -> *)
(*     Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := QS_WrapTupleList)) (head :: tail)) -> *)
(*     Lifted_not_mapsto_adt ext tenv vhead -> *)
(*     GLabelMap.MapsTo fpop (Axiomatic TupleList_pop) env -> *)
(*     {{ tenv }} *)
(*       Call vhead fpop (vlst :: nil) *)
(*     {{ [[`vhead <-- head as _]]::[[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <-- tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t); *)
(*   facade_eauto. *)
(* Qed. *)

Lemma ListEmpty_helper :
  forall {A} (seq: list A),
    (EqNat.beq_nat (Datatypes.length seq) 0) = match seq with
                                               | nil => true
                                               | _ :: _ => false
                                               end.
Proof.
  destruct seq; reflexivity.
Qed.

Lemma TupleListEmpty_alt_helper :
  forall {N} x w,
    Programming.propToWord (map (TupleToListW (N := N)) x = nil) w ->
    ret (bool2w match x with
                | nil => true
                | _ :: _ => false
                end) ↝ w.
Proof.
  intros * h.
  apply CompileWordList_empty_helper in h.
  rewrite <- ListEmpty_helper.
  assumption.
Qed.

Hint Resolve TupleListEmpty_alt_helper : call_helpers_db.

Lemma CompileTupleList_Empty_alt:
  forall {N} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
    (fempty : GLabelMap.key) (lst : Comp (list (FiatTuple N))),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env ->
    {{ [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <~~ lst as _]] :: tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <~~ lst as ls]] :: [[`vtest <-- (bool2w match ls with
                                                | nil => true
                                                | _ :: _ => false
                                                end) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileTupleList_Delete:
  forall (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
    (fpointer : GLabelMap.key),
    vlst <> vtmp ->
    vtmp ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) nil) ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_delete) env ->
    {{ tenv }}
      Call vtmp fpointer (vlst :: nil)
    {{ [[`vtmp <-- (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vlst tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileTupleList_Delete_spec:
  forall {N} (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
    (fpointer : GLabelMap.key),
    vlst <> vtmp ->
    vtmp ∉ ext ->
    vlst ∉ ext ->
    NotInTelescope vtmp tenv ->
    NotInTelescope vlst tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.TupleList_delete) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTupleList (N := N)))) vlst) <-- nil as _]] :: tenv }}
      (Call vtmp fpointer (vlst :: nil))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R; hoare.
  apply generalized CompileTupleList_Delete; try (compile_do_side_conditions ||  Lifted_t).
  repeat match goal with
         | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         end.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Qed.

Lemma CompileTupleList_LoopBase :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} (lst: list (FiatTuple N)) init vhead vtest vlst vret fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv (f: Comp A -> FiatTuple N -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic QsADTs.TupleList_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.TupleList_delete) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  unfold DummyArgument; loop_t.

  rewrite TelEq_swap by loop_t;
    eapply (CompileTupleList_Empty_alt (N := N)); loop_t.

  2:eapply (CompileTupleList_Delete_spec (N := N)); loop_t.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.
  simpl.

  eapply CompileWhileTrue; [ loop_t.. | ].

  apply generalized @CompileTupleList_pop; loop_t.
  rewrite <- GLabelMapFacts.find_mapsto_iff; assumption.

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vret; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

  rewrite TelEq_swap.
  apply ProgOk_Remove_Skip_L; hoare.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.
  apply CompileTupleList_Empty_alt; loop_t.

  loop_t.
Qed.

Lemma CompileTupleList_Loop :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} lst init vhead vtest vlst vret fpop fempty fdealloc facadeBody facadeConclude
    env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: Comp A -> FiatTuple N -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  apply @CompileTupleList_LoopBase; eassumption.
Qed.

Lemma CompileTupleList_LoopAlloc :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A} lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
    env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: Comp A -> (FiatTuple N) -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  apply @CompileTupleList_Loop; try eassumption.
Qed.

Lemma CompileWordList_push :
  forall vret vhd vlst fpointer (env: Env QsADTs.ADTValue) ext tenv
    h (t: list W),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.WordList_push) env ->
    Lifted_MapsTo ext tenv vhd (wrap h) ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) t) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    vret <> vlst ->
    vret <> vhd ->
    vhd <> vlst ->
    vhd ∉ ext ->
    vlst ∉ ext ->
    vret ∉ ext ->
    {{ tenv }}
      Call vret fpointer (vlst :: vhd :: nil)
      {{ [[ `vret <-- (Word.natToWord 32 0) as _ ]] :: [[ NTSome (H := WrapInstance (H := QS_WrapWordList)) vlst <-- h :: t as _ ]] :: DropName vlst (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; congruence.
Qed.

Lemma CompileWordList_push_spec :
  forall vtmp vhd vlst fpointer (env: Env QsADTs.ADTValue) ext tenv
    h (t: list W),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.WordList_push) env ->
    PreconditionSet tenv ext [[[vtmp;vhd;vlst]]] ->
    {{ [[ NTSome (H := WrapInstance (H := QS_WrapWordList)) vlst <-- t as _ ]] :: [[ `vhd <-- h as _ ]] :: tenv }}
      Call vtmp fpointer (vlst :: vhd :: nil)
    {{ [[ NTSome (H := WrapInstance (H := QS_WrapWordList)) vlst <-- h :: t as _ ]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R. hoare. PreconditionSet_t.
  apply generalized CompileWordList_push; repeat (compile_do_side_conditions || Lifted_t).
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions; apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  move_to_front vhd; apply CompileDeallocSCA_discretely; try compile_do_side_conditions; apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.
Qed.

Lemma CompileMap_TuplesToWords :
  forall {N} (lst: list (FiatTuple N)) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' (f: FiatTuple N -> W),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (QsADTs.WordList_new)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    GLabelMap.MapsTo fcons (Axiomatic (QsADTs.WordList_push)) env ->
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list (FiatTuple N)) (s': list W),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[NTSome (H := WrapInstance (H := QS_WrapWordList)) vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileTupleList_LoopAlloc; eauto.
  PreconditionSet_t; eauto.

  eapply CompileWordList_new; compile_do_side_conditions.
  setoid_rewrite revmap_fold_comp; eassumption.
  intros.
  rewrite SameValues_Fiat_Bind_TelEq.
  move_to_front vret.
  apply miniChomp'; intros.
  hoare.
  apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.

  apply CompileWordList_push_spec; try compile_do_side_conditions.
Qed.

Lemma CompileTupleList_Loop_ret :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A}
    lst init facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatTuple N) -> A),
    GLabelMap.MapsTo fpop (Axiomatic QsADTs.TupleList_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic QsADTs.TupleList_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic QsADTs.TupleList_delete) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head acc (s: list (FiatTuple N)),
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vret <-- init as _]] :: [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite ret_fold_fold_ret.
  eapply CompileSeq.
  apply CompileTupleList_LoopBase; try compile_do_side_conditions.
  2: apply ProkOk_specialize_to_ret; intros * h; apply ret_fold_fold_ret in h; computes_to_inv; subst; eauto.
  intros; rewrite SameValues_Fiat_Bind_TelEq.
  apply miniChomp'; intros; eauto.
Qed.

Lemma CompileTupleList_LoopAlloc_ret :
  forall {N A} `{FacadeWrapper (Value QsADTs.ADTValue) A}
    lst init facadeInit facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value QsADTs.ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatTuple N) -> A),
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <-- init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc (s: list (FiatTuple N)),
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileTupleList_Loop_ret.
Qed.

Lemma CompileTupleList_DeleteAny_spec:
  forall {N} (vtmp vtmp2 vsize vtest vlst vhead : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext
    (fpop fempty fdealloc ftdealloc : GLabelMap.key) (seq: (list (FiatTuple N))),
    PreconditionSet tenv ext [[[vtmp; vtmp2; vsize; vhead; vtest; vlst]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpop (Axiomatic (QsADTs.TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (QsADTs.TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (QsADTs.TupleList_delete)) env ->
    GLabelMap.MapsTo ftdealloc (Axiomatic (QsADTs.Tuple_delete)) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTupleList (N := N)))) vlst) <-- seq as _]] :: tenv }}
      (Seq (Assign vtmp (Const (Word.natToWord 32 0)))
           (Seq (Seq (Fold vhead vtest vlst fpop fempty (Seq (Assign vsize (Const (Word.natToWord 32 N)))
                                                             (Call vtmp2 ftdealloc [[[vhead; vsize]]])))
                     (Call (DummyArgument vtest) fdealloc [[[vlst]]]))
                Skip))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R.
  apply CompileSeq with ([[ ` vtmp <-- fold_left (fun acc x => acc) seq (Word.natToWord 32 0) as _]]::tenv).
  eapply (CompileTupleList_LoopAlloc_ret (vhead := vhead) (vtest := vtest)); try compile_do_side_conditions.
  apply CompileConstant; try compile_do_side_conditions.
  intros. apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply (CompileTuple_Delete_spec (vtmp := vtmp2) (vsize := vsize)); try compile_do_side_conditions.
  apply CompileSkip.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Defined.

Lemma CompileTuples2_findSecond :
  forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N k1
    (table: FiatBag N) (key: W) (idx2: Fin.t N)
    (k2 := (Word.natToWord 32 (projT1 (Fin.to_nat idx2))))
    (table':= ( results <- {l : list RawTuple |
                          IndexedEnsembles.EnsembleIndexedListEquivalence
                            (IndexedEnsembles.IndexedEnsemble_Intersection
                               table
                               (fun x0 : RawTuple =>
                                  ((if Word.weq match MakeWordHeading_allWords idx2 in _ = W return W with
                                                | eq_refl => GetAttributeRaw x0 idx2
                                                end key then true else false) && true)%bool =
                                  true)) l};
                 ret (table, results))%comp
             : Comp (_ * list (FiatTuple N))),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuples2_findSecond) env ->
    Lifted_MapsTo ext tenv vtable (wrap (FacadeWrapper := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) table) ->
    Lifted_MapsTo ext tenv vkey (wrap key) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    NoDuplicates [[[vret; vtable; vkey]]] ->
    vret ∉ ext ->
    vtable ∉ ext ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
    {{ tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
           :: [[ (@NTSome QsADTs.ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]]
           :: [[ (@NTSome QsADTs.ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
           :: DropName vret (DropName vtable tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
  fiat_t.

  5:solve[repeat apply DropName_remove; eauto 1].
  4:solve[simpl; eauto using f_equal, ListWToTuple_Truncated_map_keepEq].
  3:solve[fiat_t].
  2:solve[fiat_t].

  apply Fiat_Bedrock_Filters_Equivalence; eassumption.
Qed.

Lemma CompileTuples2_findSecond_spec :
  forall vret vtable vkey fpointer (env: Env QsADTs.ADTValue) ext tenv N k1
    (table: FiatBag N) (key: W) (idx2: Fin.t N)
    (k2 := (Word.natToWord 32 (projT1 (Fin.to_nat idx2))))
    (table':= ( results <- {l : list RawTuple |
                          IndexedEnsembles.EnsembleIndexedListEquivalence
                            (IndexedEnsembles.IndexedEnsemble_Intersection
                               table
                               (fun x0 : RawTuple =>
                                  ((if Word.weq match MakeWordHeading_allWords idx2 in _ = W return W with
                                                | eq_refl => GetAttributeRaw x0 idx2
                                                end key then true else false) && true)%bool =
                                  true)) l};
                 ret (table, results))%comp
             : Comp (_ * list (FiatTuple N))),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuples2_findSecond) env ->
    StringMap.MapsTo vkey (wrap key) ext ->
    PreconditionSet tenv ext [[[vret; vtable]]] ->
    vret <> vkey ->
    vtable <> vkey ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.functional (IndexedEnsemble_TupleToListW table) ->
    {{ [[ (@NTSome QsADTs.ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- table as _]] :: tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
    {{ [[ table' as retv ]]
         :: [[ (@NTSome QsADTs.ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]]
         :: [[ (@NTSome QsADTs.ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
         :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply generalized CompileTuples2_findSecond; repeat (compile_do_side_conditions || Lifted_t || PreconditionSet_t).
  setoid_rewrite (DropName_NotInTelescope _ _ H12).
  rewrite DropName_Cons_None.
  setoid_rewrite (DropName_NotInTelescope _ _ H10).
  decide_TelEq_instantiate.
Qed.

Transparent CallBagMethod.
Arguments CallBagMethod : simpl never.
Arguments wrap : simpl never.
Arguments ListWToTuple: simpl never.

Lemma ilist2ToListW_inj :
  forall n el el',
    ilist2ToListW (N := n) el = ilist2ToListW el'
    -> el = el'.
Proof.
  induction n; simpl; eauto.
  - destruct el; destruct el'; reflexivity.
  - destruct el; destruct el'; simpl; intros.
    unfold ilist2.ilist2_tl, ilist2.ilist2_hd in *; simpl in *.
    injections; f_equal.
    eapply IHn; eassumption.
Qed.

Lemma Lift_Ensemble :
  forall n r idx el,
    Ensembles.In (FiatElement n) r
                 {|
                   IndexedEnsembles.elementIndex := idx;
                   IndexedEnsembles.indexedElement := el |}
    <->
    Ensembles.In (BedrockElement) (IndexedEnsemble_TupleToListW r)
                 {|
                   TuplesF.elementIndex := idx;
                   TuplesF.indexedElement := TupleToListW el |}.
Proof.
  split; intros.
  - econstructor; intuition eauto.
    unfold RelatedIndexedTupleAndListW; split; simpl; eauto.
  - destruct H;  unfold RelatedIndexedTupleAndListW in *; intuition.
    simpl in *; subst.
    destruct x; simpl in *; subst.
    unfold TupleToListW in H2.
    apply ilist2ToListW_inj in H2; subst; eauto.
Qed.

Definition BagSanityConditions {N} tbl :=
  TuplesF.functional (IndexedEnsemble_TupleToListW (N := N) tbl)
  /\ exists idx, TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW tbl) idx.

Lemma postConditionAdd:
  forall n (r : FiatBag n) el,
    TuplesF.functional (IndexedEnsemble_TupleToListW r) ->
    IndexedEnsembles.UnConstrFreshIdx r (IndexedEnsembles.elementIndex el) ->
    BagSanityConditions (Ensembles.Add IndexedEnsembles.IndexedElement r el).
Proof.
  split; unfold TuplesF.functional, TuplesF.minFreshIndex; intros; intuition.
  - destruct t1; destruct t2; simpl in *; subst; f_equal.
    destruct H2; destruct H1; intuition.
    destruct H2; destruct H3; subst.
    + unfold TuplesF.tupl in *.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition.
      subst.
      destruct x; destruct x0; simpl in *; subst.
      apply Lift_Ensemble in H2; apply Lift_Ensemble in H1.
      pose proof (H _ _ H1 H2 (eq_refl _)); injections; eauto.
    + destruct H2.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      destruct x0; destruct el; simpl in *; subst.
      unfold TuplesF.UnConstrFreshIdx in H1.
      unfold IndexedEnsembles.UnConstrFreshIdx in H0.
      apply H0 in H1; simpl in *.
      omega.
    + destruct H1.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      destruct x; destruct el; simpl in *; subst.
      unfold IndexedEnsembles.UnConstrFreshIdx in H0.
      apply H0 in H2; simpl in *.
      omega.
    + destruct H2; destruct H1.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      reflexivity.
  - exists (S (IndexedEnsembles.elementIndex el)); split.
    + unfold TuplesF.UnConstrFreshIdx in *; intros.
      destruct H1 as [? [? ? ] ].
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      destruct element; simpl in *; subst.
      * destruct H1.
        destruct x; simpl in *.
        apply H0 in H1; simpl in *; omega.
        destruct H1; omega.
    + intros.
      inversion H1; subst.
      unfold TuplesF.UnConstrFreshIdx in *.
      assert (lt (TuplesF.elementIndex (IndexedElement_TupleToListW el)) (IndexedEnsembles.elementIndex el) ).
      eapply H2.
      econstructor; split.
      unfold Ensembles.Add.
      econstructor 2.
      reflexivity.
      unfold RelatedIndexedTupleAndListW; eauto.
      destruct el; simpl in *; omega.
      unfold TuplesF.UnConstrFreshIdx in *; intros.
      assert (lt (IndexedEnsembles.elementIndex el) idx').
      eapply (H2 {| TuplesF.elementIndex := _;
                    TuplesF.indexedElement := _ |}); simpl.
      unfold IndexedEnsemble_TupleToListW.
      simpl; eexists; split.
      econstructor 2.
      reflexivity.
      unfold RelatedIndexedTupleAndListW; simpl; split; eauto.
      omega.
Qed.

Ltac _compile_CallBagFind :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (Cons (NTSome (H := ?h) ?vdb) (ret (prim_fst ?db)) (fun _ => ?tenv), Cons NTNone ?bf _) =>
              match bf with
              | CallBagMethod Fin.F1 BagFind ?db ?kwd =>
                let vsnd := gensym "snd" in
                let vtmp := gensym "tmp" in
                eapply CompileSeq with ([[bf as retv]]
                                          :: [[(NTSome (H := h) vdb) <-- prim_fst (Refinements.UpdateIndexedRelation
                                                                                 (QueryStructureSchema.QueryStructureSchemaRaw ProcessScheduler.SchedulerSchema)
                                                                                 (icons3 ProcessScheduler.SearchUpdateTerm inil3) db Fin.F1 (fst retv)) as _]]
                                          :: [[`vsnd <-- snd retv as s]]
                                          :: tenv);
                [ match kwd with
                  | (Some ?v, (None, fun _ => true)) =>
                    let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                    match vkwd with
                    | Some ?vkwd => apply (CompileTuples2_findFirst_spec (* FIXME get (Fin.FS Fin.F1) generically *)
                                            (Fin.FS Fin.F1) (vkey := vkwd) _ (table := prim_fst db))
                    end
                  | (None, (Some ?v, fun _ => true)) =>
                    let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                    match vkwd with
                    | Some ?vkwd => apply (CompileTuples2_findSecond_spec (* FIXME get (Fin.F1) generically *)
                                            _ (Fin.F1) (vkey := vkwd) (table := prim_fst db))
                    end
                  end | ]
              end
            end).

Ltac _compile_length :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?pre, Cons ?k (ret (bool2w (EqNat.beq_nat (Datatypes.length (rev ?seq)) 0))) (fun _ => ?pre')) =>
              let vlst := find_fast (wrap (FacadeWrapper := WrapInstance (H := QS_WrapTupleList)) seq) ext in
              match vlst with
              | Some ?vlst => eapply (CompileTupleList_Empty_spec (vlst := vlst))
              end
            end).


Ltac _compile_CallBagInsert := (* FIXME should do the insert in the second branch *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (Cons (NTSome (H := ?h) ?vrep) (ret ?db) (fun _ => ?tenv),
               Cons NTNone ?bm (fun a => Cons ?vret _ (fun _ => Cons (NTSome ?vrep') (ret a) (fun _ => ?tenv')))) =>
              unify vrep vrep';
                match bm with
                | (CallBagMethod _ BagInsert _ (ilist2.icons2 ?a (ilist2.icons2 ?b (ilist2.icons2 ?c ilist2.inil2)))) =>
                  let vtmp := gensym "tmp" in
                  let vtup := gensym "tup" in
                  (* match pre with *)
                  change (ilist2.icons2 a (ilist2.icons2 b (ilist2.icons2 c ilist2.inil2))) with (ListWToTuple [[[a; b; c]]]);
                    apply CompileSeq with (Cons (NTSome (H := h) vrep) (ret db)
                                                (fun _ => Cons (NTSome (H := WrapInstance (H := QS_WrapTuple)) vtup) (ret ((ListWToTuple [[[a; b; c]]]): FiatTuple 3)) (fun _ => tenv)));
                    [ | eapply CompileSeq; [ let vtmp := gensym "vtmp" in eapply (CompileTuples2_insert_spec (vtmp := vtmp)) | ] ]
                end
            end).

Ltac _compile_allocTuple :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?pre, Cons ?k (ret ?tup) (fun _ => ?pre)) =>
              match type of tup with
              | FiatTuple _ =>
                let v1 := gensym "v1" in
                let v2 := gensym "v2" in
                let v3 := gensym "v3" in
                let o1 := gensym "o1" in
                let o2 := gensym "o2" in
                let o3 := gensym "o3" in
                let vlen := gensym "vlen" in
                let vtmp := gensym "vtmp" in
                apply (CompileTuple_new_spec (v1 := "v1") (v2 := "v2") (v3 := "v3") (o1 := "o1") (o2 := "o2") (o3 := "o3") (vlen := "vlen") (vtmp := "vtmp")); try explode 6
              end
            end).

Ltac _compile_destructor_unsafe vtmp tenv tenv' ::=
     let vtmp2 := gensym "tmp'" in
     let vsize := gensym "size" in
     let vtest := gensym "test" in
     let vhead := gensym "head" in
     first [ unify tenv tenv';
             apply (CompileTupleList_DeleteAny_spec (N := 3) (vtmp := vtmp) (vtmp2 := vtmp2) (vsize := vsize)
                                                    (vtest := vtest) (vhead := vhead))
           | eapply CompileSeq;
             [ apply (CompileTupleList_DeleteAny_spec (N := 3) (vtmp := vtmp) (vtmp2 := vtmp2) (vsize := vsize)
                                                      (vtest := vtest) (vhead := vhead)) | ] ].



Lemma CompileConstantBool:
  forall {av} name env (b: bool) ext (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    {{ tenv }}
      (Assign name (Const (bool2w b)))
      {{ [[`name <-- b as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
  change (wrap (bool2w b)) with (wrap (FacadeWrapper := (@FacadeWrapper_bool av)) b).
  facade_eauto.
Qed.

Lemma map_rev_def :
  forall {A B} f seq,
    @map A B f (rev seq) = revmap f seq.
Proof.
  intros; reflexivity.
Qed.

Ltac _compile_map ::= (* ‘_compile_map’ from the stdlib uses generic push-pop methods. *)
     match_ProgOk
     ltac:(fun prog pre post ext env =>
             let vhead := gensym "head" in
             let vhead' := gensym "head'" in
             let vtest := gensym "test" in
             let vtmp := gensym "tmp" in
             match constr:((pre, post)) with
             | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (ret (revmap _ ?seq')) ?tenv') =>
               unify seq seq';
               apply (CompileMap_TuplesToWords (N := 3) seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := vtmp))
             end).

Lemma CompileTuple_Get_helper :
  forall N (idx: (Fin.t N)), (@Vector.nth Type (NumAttr (MakeWordHeading N)) (AttrList (MakeWordHeading N)) idx) = W.
Proof.
  induction idx; eauto.
Defined.

Lemma CompileTuple_get_helper:
  forall (N : nat) (idx : Fin.t N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    IL.goodSize (` (Fin.to_nat idx)).
Proof.
  intros *.
  pose proof (proj2_sig (Fin.to_nat idx)) as h; simpl in h.
  apply NPeano.Nat.le_exists_sub in h; repeat cleanup.
  assert (IL.goodSize N) as h.
  eassumption.
  rewrite H0 in h.
  eapply Arrays.goodSize_plus_r.
  rewrite NPeano.Nat.add_succ_r in h.
  rewrite <- NPeano.Nat.add_succ_l in h.
  eassumption.
Defined.

Lemma CompileTuple_get_helper':
  forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    Word.wlt (Word.natToWord 32 (` (Fin.to_nat idx))) (IL.natToW (Datatypes.length (TupleToListW tup))).
Proof.
  intros. rewrite TupleToListW_length by assumption.
  rewrite Word.wordToNat_natToWord_idempotent by assumption.
  pose proof (proj2_sig (Fin.to_nat idx)) as h; simpl in h.
  apply Arrays.lt_goodSize; try eassumption.
  apply CompileTuple_get_helper; assumption.
Qed.

Hint Resolve CompileTuple_get_helper' : call_helpers_db.

Lemma CompileTuple_get_helper'':
  forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (match CompileTuple_Get_helper idx in (_ = W) return (Vector.nth (MakeVectorOfW N) idx -> W) with
     | eq_refl => fun t : Vector.nth (MakeVectorOfW N) idx => t
     end (ilist2.ith2 tup idx)) = Array.sel (TupleToListW tup) (Word.natToWord 32 (` (Fin.to_nat idx))).
Proof.
  unfold Array.sel.
  intros.
  rewrite Word.wordToNat_natToWord_idempotent by (apply (CompileTuple_get_helper idx); assumption).
  induction idx; simpl; try rewrite IHidx.
  - reflexivity.
  - destruct tup; simpl.
    unfold TupleToListW, ilist2.ilist2_hd, ilist2.ilist2_tl; simpl.
    destruct (Fin.to_nat idx); simpl; reflexivity.
  - apply BinNat.N.lt_succ_l.
    rewrite Nnat.Nat2N.inj_succ in H.
    assumption.
Qed.

Lemma CompileTuple_Get:
  forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
    vtup <> vret ->
    vret ∉ ext ->
    Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTuple (N := N)))) tup) ->
    Lifted_MapsTo ext tenv vpos (wrap (Word.natToWord 32 (proj1_sig (Fin.to_nat idx)))) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_get) env ->
    {{ tenv }}
      Call vret fpointer (vtup :: vpos :: nil)
      {{ [[(NTSome (H := FacadeWrapper_SCA) vret) <--
                                                 (match CompileTuple_Get_helper idx in _ = W return _ -> W with
                                                  | eq_refl => fun t => t
                                                  end) (ilist2.ith2 tup idx) as _]]
           :: (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  rewrite <- CompileTuple_get_helper'' by congruence; reflexivity.
  rewrite <- remove_add_comm by congruence.
  setoid_rewrite <- add_redundant_cancel; try eassumption.
  repeat apply DropName_remove; eauto 1.
Qed.

Lemma CompileTuple_Get_spec:
  forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) (tenv: Telescope QsADTs.ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
    PreconditionSet tenv ext [[[vtup; vret; vpos]]] ->
    vret ∉ ext ->
    vtup ∉ ext ->
    NotInTelescope vret tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.Tuple_get) env ->
    {{ [[ `vtup <-- tup as _ ]] :: tenv }}
      (Seq (Assign vpos (Const (Word.natToWord 32 (proj1_sig (Fin.to_nat idx))))) (Call vret fpointer (vtup :: vpos :: nil)))
    {{ [[ `vtup <-- tup  as _]]
         :: [[(NTSome (H := FacadeWrapper_SCA) vret) <-- (match CompileTuple_Get_helper idx in _ = W return _ -> W with
                                                      | eq_refl => fun t => t
                                                      end) (ilist2.ith2 tup idx) as _]]
         :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  hoare.
  apply CompileConstant; try compile_do_side_conditions.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.

  remember (match CompileTuple_Get_helper idx in (_ = W) return (Vector.nth (AttrList (MakeWordHeading N)) idx -> W) with
      | eq_refl => fun t : Vector.nth (AttrList (MakeWordHeading N)) idx => t
            end (ilist2.ith2 tup idx)). (* Otherwise Coq crashes *)
  setoid_replace tenv with (DropName vret tenv) using relation (@TelStrongEq QsADTs.ADTValue) at 2.
  computes_to_inv;
    subst; apply CompileTuple_Get; repeat (PreconditionSet_t || compile_do_side_conditions || decide_not_in || Lifted_t).
  apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
  apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
  symmetry; apply DropName_NotInTelescope; assumption.
Qed.

Ltac _compile_get :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtmp := gensym "tmp" in
            match constr:((pre, post)) with
            | (Cons (NTSome (H:=?h) ?k) (ret ?tup) ?tenv, Cons (NTSome (H:=?h') ?k') (ret (GetAttributeRaw ?tup' ?idx')) _) =>
              unify tup tup';
                let vpos := gensym "pos" in
                eapply CompileSeq with (Cons (NTSome (H:=h) k) (ret tup)
                                             (fun a => Cons (NTSome (H:=h') k') (ret (ilist2.ith2 tup' idx'))
                                                         (fun _ => tenv a)));
                  [ apply (CompileTuple_Get_spec (N := 3) tup' idx' (vpos := vpos)) |
                    let vtmp := gensym "tmp" in
                    let vsize := gensym "size" in
                    apply (CompileTuple_Delete_spec (vtmp := vtmp) (vsize := vsize)) ]
            end).

Add Parametric Morphism elt
  : (@GLabelMapFacts.UWFacts.WFacts.P.update elt)
    with signature
    (GLabelMap.Equal ==> GLabelMap.Equal ==> GLabelMap.Equal)
      as GLabelMapFacts_UWFacts_WFacts_P_update_morphisn.
Proof.
  apply GLabelMapFacts.UWFacts.WFacts.P.update_m.
Qed.


Add Parametric Morphism av
  : (@RunsTo av)
    with signature
    (GLabelMap.Equal ==> eq ==> StringMap.Equal ==> StringMap.Equal ==> impl)
      as Proper_RunsTo.
Proof.
  unfold impl; intros.
  revert y y1 y2 H0 H1 H.
  induction H2; intros.
  - econstructor; rewrite <- H0, <- H1; eauto.
  - econstructor 2; eauto.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 3; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 4; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 5; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 6; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H1; apply H.
    rewrite <- H1, <- H2; eauto.
  - econstructor 7;
    rewrite <- H2; eauto.
    rewrite <- H1; symmetry; eauto.
  - econstructor 8; eauto.
    rewrite <- H8; eauto.
    rewrite <- H6; eauto.
    rewrite <- H6; eauto.
    rewrite <- H7.
    subst st'; subst st'0; rewrite <- H6; eauto.
  - econstructor 9; eauto.
    rewrite <- H9; eauto.
    rewrite <- H7; eauto.
    rewrite <- H7; eauto.
    eapply IHRunsTo; eauto.
    reflexivity.
    reflexivity.
    subst st'; subst st'0; subst output; rewrite <- H8.
    rewrite <- H7; eauto.
Qed.

Add Parametric Morphism av
  : (@Safe av)
    with signature
    (GLabelMap.Equal ==> eq ==> StringMap.Equal ==> impl)
      as Proper_Safe.
Proof.
  unfold impl; intros.
  rewrite <- H0.
  apply Safe_coind with (R := fun st ext => Safe x st ext); eauto.
  - intros; inversion H2; subst; intuition.
    eapply H4.
    setoid_rewrite H; eauto.
  - intros; inversion H2; subst; intuition.
  - intros; inversion H2; substs; intuition.
    left; intuition eauto.
    subst loop; subst loop1; subst loop2.
    rewrite <- H4.
    eapply H8.
    rewrite H; eauto.
  - intros; inversion H2; substs; intuition.
    eauto.
  - intros; inversion H2; substs; intuition.
    + eexists; intuition eauto.
      left; eexists; intuition eauto.
      rewrite <- H; eauto.
    + eexists; intuition eauto.
      right; eexists; intuition eauto.
      rewrite <- H; eauto.
      eapply H12; eauto.
      rewrite H; eauto.
      eapply H12.
      rewrite H; eauto.
Qed.

Add Parametric Morphism av
  : (@ProgOk av)
with signature
(StringMap.Equal ==> GLabelMap.Equal ==> eq ==> eq ==> eq ==> impl)
  as Proper_ProgOk.
Proof.
  unfold impl; intros; intro; intros; split.
  setoid_rewrite <- H0.
  rewrite <- H in H2.
  eapply H1 in H2; intuition.
  rewrite <- H in H2.
  eapply H1 in H2; intuition.
  rewrite <- H.
  eapply H4.
  rewrite H0.
  eauto.
Qed.

Lemma GLabelMapFacts_map_add_1 : (* This is a hack to transform a rewrite into an apply (setoid-rewrite is too slow). *)
  forall (elt B : Type) (f : elt -> B) (k : GLabelMapFacts.M.key) (v : elt) (m : GLabelMapFacts.M.t elt) m0,
    GLabelMapFacts.M.Equal (GLabelMapFacts.M.map f m) m0 ->
    GLabelMapFacts.M.Equal (GLabelMapFacts.M.map f (m ### k ->> v)) (m0 ### k ->> f v).
Proof.
  intros * H; rewrite GLabelMapFacts.map_add, H; reflexivity.
Qed.

Require Import Fiat.Examples.QueryStructure.ProcessScheduler.

Eval simpl in
  (forall av env P rWrap cWrap dWrap prog,
      (LiftMethod (av := av) env P (DecomposeIndexedQueryStructure _ rWrap) cWrap dWrap prog (Methods PartialSchedulerImpl (Fin.FS (Fin.F1))))).

Require Import
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

Definition coDomainWrappers
           av {n n' : nat}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
  := forall midx : Fin.t n', CodWrapperT av (methCod (Vector.nth methSigs midx)).

Definition domainWrappers
           av {n n' : nat}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
  := forall midx : Fin.t n', DomWrapperT av (methDom (Vector.nth methSigs midx)).

Definition DecomposeRep_well_behaved
           av {n n' : nat}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           (DecomposeRep : Rep adt -> list (Value av)) :=
  forall x x0 : Rep adt,
    is_same_types (DecomposeRep x0)
                  (DecomposeRep x) = true.

Definition Good_bool {av}
  : GoodWrapper av bool.
Proof.
  refine {| gWrap := _;
            gWrapTag := false
         |}; intros; unfold wrap; simpl; eauto.
Defined.

Definition Good_listW
  : GoodWrapper QsADTs.ADTValue (list W).
Proof.
  refine {| gWrap := WrapInstance (H := QS_WrapWordList);
            gWrapTag := true
         |}; intros; unfold wrap; simpl; eauto.
Defined.

Definition Good_BedrockTuple
  : GoodWrapper QsADTs.ADTValue (list W).
Proof.
  refine {| gWrap := WrapInstance (H := QS_WrapBedrockTuple);
            gWrapTag := true
         |}; intros; unfold wrap; simpl; eauto.
Defined.

Definition Good_W {av}
  : GoodWrapper av W.
Proof.
  refine {| gWrap := _;
            gWrapTag := false
         |}; intros; unfold wrap; simpl; eauto.
Defined.

Definition Scheduler_coDomainWrappers
  : coDomainWrappers QsADTs.ADTValue PartialSchedulerImpl.
Proof.
  unfold coDomainWrappers; simpl; repeat_destruct;
  eauto using Good_bool, Good_listW, Good_W.
Defined.

Definition Scheduler_DomainWrappers
  : domainWrappers QsADTs.ADTValue PartialSchedulerImpl.
Proof.
    unfold domainWrappers; simpl; repeat_destruct;
    eauto using Good_bool, Good_listW, Good_W.
Defined.

Definition QueryStructureRepWrapperT
           av (qs_schema : QueryStructureSchema.QueryStructureSchema)
           (qs_schema' := QueryStructureSchema.QueryStructureSchemaRaw
                            qs_schema)
           Index
  := @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema')
                 Schema.RawSchema
                 (fun ns =>
                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                 (fun ns
                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                    @IndexedEnsembles.IndexedEnsemble
                      (@RawTuple (Schema.rawSchemaHeading ns)))
                 (QueryStructureSchema.qschemaSchemas qs_schema') Index.

Definition Scheduler_RepWrapperT Index
  : QueryStructureRepWrapperT QsADTs.ADTValue SchedulerSchema Index.
Proof.
  unfold QueryStructureRepWrapperT; simpl; split.
  apply (@QS_WrapBag2 3 1 0).   (* FIXME generalize *)
  constructor.
Defined.

Definition Scheduler_DecomposeRep_well_behaved av qs_schema Index
(rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

  :=
  (fun r r' : IndexedQueryStructure qs_schema Index =>
     DecomposePrei3list_Agree _ _ rWrap
                              (id r) (id r')).

Definition DecomposeIndexedQueryStructure' av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  Decomposei3list _ _ rWrap (id r).

Definition DecomposeIndexedQueryStructurePost' av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r r' : IndexedQueryStructure qs_schema Index) :=
  DecomposePosti3list _ _ rWrap (id r) (id r').

Definition DecomposeIndexedQueryStructurePre' av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  DecomposePrei3list _ _ rWrap (id r).

Ltac GLabelMap_fast_apply_map :=
  (* This tactic simplifies an expression like [map f (add k1 v1 (add ...))]
     into [add k1 (f v1) (add ...)]. Using setoid_rewrite repeatedly was too
     slow, so it relies on a separate lemma and an evar to do its job. *)
  match goal with (* Not a lazy match: not all [map]s can be removed *)
  | [  |- context[GLabelMap.map ?f ?m] ] =>
    lazymatch type of f with
    | ?elt -> ?elt' =>
      let m' := fresh in
      evar (m' : GLabelMap.t elt');
      (* This block is essentially [setoid_replace (GLabelMap.map f m) m'] with
      relation [@GLabelMap.Equal elt'], but it fails before calling the setoid
      machinery if the relation doesn't actually hold. *)
      let __eq := fresh in
      assert (@GLabelMap.Equal elt' (GLabelMap.map f m) m') as __eq;
      [ unfold m' in *; clear m'; try unfold m;
        solve [repeat apply GLabelMapFacts_map_add_1; apply GLabelMapFacts.map_empty] | ];
      setoid_rewrite __eq; clear __eq
    end
  end.

Ltac _compile_cleanup_env_helper :=
  GLabelMap_fast_apply_map;
  GLabelMap_fast_apply_map;
  reflexivity.

Ltac __compile_cleanup_env :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match env with
            | GLabelMapFacts.UWFacts.WFacts.P.update _ _ =>
              eapply Proper_ProgOk; [ reflexivity | _compile_cleanup_env_helper | reflexivity.. | idtac ];
              match_ProgOk ltac:(fun prog pre post ext env => set env)
            end).

Ltac __compile_prepare_merged_env_for_compile_do_side_conditions :=
  lazymatch goal with
  | [ |- GLabelMap.MapsTo _ _ ?env ] =>
    lazymatch eval unfold env in env with
    | GLabelMapFacts.UWFacts.WFacts.P.update _ _ =>
      unfold env; apply GLabelMapFacts.UWFacts.WFacts.P.update_mapsto_iff; left
    end
  end.

Ltac __compile_pose_query_structure :=
  (* Removing this pose makes the [apply CompileTuples2_findFirst_spec] loop.
     No idea why. *)
  match goal with
  | [ r: IndexedQueryStructure _ _ |- _ ] =>
    match goal with
    | [ r' := _ : IndexedQueryStructure _ _ |- _ ] => fail 1
    | _ => pose r
    end
  end.

Ltac __compile_discharge_bag_side_conditions_step :=
  match goal with
  | _ => cleanup
  | _ => progress injections
  | _ => progress simpl in *
  | _ => progress computes_to_inv
  | _ => progress unfold CallBagMethod in *
  | _ => progress (find_if_inside; simpl in * )
  | [  |- BagSanityConditions (Ensembles.Add _ _ _) ] => apply postConditionAdd
  | [  |- BagSanityConditions _ ] => split; solve [intuition eauto]
  | _ => eassumption
  end.

Ltac __compile_discharge_bag_side_conditions_internal :=
  solve [repeat __compile_discharge_bag_side_conditions_step].

Ltac __compile_discharge_bag_side_conditions :=
  match goal with
  | [  |- TuplesF.functional _ ] => __compile_discharge_bag_side_conditions_internal
  | [  |- TuplesF.minFreshIndex _ _ ] => __compile_discharge_bag_side_conditions_internal
  | [  |- BagSanityConditions _ ] => __compile_discharge_bag_side_conditions_internal
  end.

Ltac __compile_unfold :=
     match goal with
     | _ => progress unfold If_Then_Else in *
     end.

Ltac __compile_start_compiling_module imports :=
  lazymatch goal with
  | [  |- sigT (fun _ => @BuildCompileUnit2TSpec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ] =>
    eexists;
    unfold DecomposeIndexedQueryStructure', DecomposeIndexedQueryStructurePre', DecomposeIndexedQueryStructurePost';
    eapply BuildCompileUnit2T' with (env := imports); try apply eq_refl (* reflexivity throws an Anomaly *)
  | [  |- forall _: (Fin.t _), (sigT _)  ] =>
    eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type; repeat (apply Build_prim_prod || exact tt)
  end.

Ltac __compile_start_compiling_method :=
  lazymatch goal with
  | [  |- sigT (fun (_: Stmt) => _) ] =>
    eexists; repeat match goal with
                    | _ => progress simpl
                    | _ => progress intros
                    | [  |- _ /\ _ ] => split
                    end
  end.

Ltac __compile_decide_NoDup :=
  repeat lazymatch goal with
    | [  |- NoDup _ ] => econstructor
    | [  |- not (List.In _ _) ] => simpl; intuition congruence
    end.

Ltac __compile_start_compiling_step imports :=
  match goal with
  | [ H: BagSanityConditions _ |- _ ] => destruct H as [ ? [ ? ? ] ]
  | _ => __compile_start_compiling_module imports
  | _ => __compile_start_compiling_method
  | _ => __compile_discharge_bag_side_conditions
  | _ => __compile_decide_NoDup
  end.

Ltac __compile_method_step :=
  match goal with
  | _ => __compile_unfold
  | _ => __compile_cleanup_env
  | _ => __compile_pose_query_structure
  | _ => __compile_prepare_merged_env_for_compile_do_side_conditions
  | _ => __compile_discharge_bag_side_conditions
  | _ => _compile_step
  | _ => _compile_CallBagFind
  | _ => _compile_CallBagInsert
  | _ => _compile_length
  | _ => _compile_allocTuple
  | _ => _compile_get
  | _ => apply CompileConstantBool
  | _ => reflexivity
  | _ => progress simpl
  | _ => setoid_rewrite map_rev_def
  end.

Ltac _compile env :=
  repeat __compile_start_compiling_step env;
  repeat __compile_method_step.

Transparent Vector.to_list.

Definition QSEnv_Ax : GLabelMap.t (AxiomaticSpec QsADTs.ADTValue) :=
  (GLabelMap.empty _)
  ### ("ADT", "Tuple_new") ->> (QsADTs.Tuple_new)
  ### ("ADT", "Tuple_delete") ->> (QsADTs.Tuple_delete)
  ### ("ADT", "Tuple_copy") ->> ( QsADTs.Tuple_copy)
  ### ("ADT", "Tuple_get") ->> ( QsADTs.Tuple_get)
  ### ("ADT", "Tuple_set") ->> ( QsADTs.Tuple_set)

  ### ("ADT", "WordList_new") ->> ( QsADTs.WordList_new)
  ### ("ADT", "WordList_delete") ->> ( QsADTs.WordList_delete)
  ### ("ADT", "WordList_pop") ->> ( QsADTs.WordList_pop)
  ### ("ADT", "WordList_empty") ->> ( QsADTs.WordList_empty)
  ### ("ADT", "WordList_push") ->> ( QsADTs.WordList_push)
  ### ("ADT", "WordList_copy") ->> ( QsADTs.WordList_copy)
  ### ("ADT", "WordList_rev") ->> ( QsADTs.WordList_rev)
  ### ("ADT", "WordList_length") ->> ( QsADTs.WordList_length)

  ### ("ADT", "TupleList_new") ->> ( QsADTs.TupleList_new)
  ### ("ADT", "TupleList_delete") ->> ( QsADTs.TupleList_delete)
  ### ("ADT", "TupleList_copy") ->> ( QsADTs.TupleList_copy)
  ### ("ADT", "TupleList_pop") ->> ( QsADTs.TupleList_pop)
  ### ("ADT", "TupleList_empty") ->> ( QsADTs.TupleList_empty)
  ### ("ADT", "TupleList_push") ->> ( QsADTs.TupleList_push)
  ### ("ADT", "TupleList_rev") ->> ( QsADTs.TupleList_rev)
  ### ("ADT", "TupleList_length") ->> ( QsADTs.TupleList_length)

  ### ("ADT", "Tuples0_new") ->> ( QsADTs.Tuples0_new)
  ### ("ADT", "Tuples0_insert") ->> ( QsADTs.Tuples0_insert)
  ### ("ADT", "Tuples0_enumerate") ->> ( QsADTs.Tuples0_enumerate)

  ### ("ADT", "Tuples1_new") ->> ( QsADTs.Tuples1_new)
  ### ("ADT", "Tuples1_insert") ->> ( QsADTs.Tuples1_insert)
  ### ("ADT", "Tuples1_find") ->> ( QsADTs.Tuples1_find)
  ### ("ADT", "Tuples1_enumerate") ->> ( QsADTs.Tuples1_enumerate)

  ### ("ADT", "Tuples2_new") ->> ( QsADTs.Tuples2_new)
  ### ("ADT", "Tuples2_insert") ->> ( QsADTs.Tuples2_insert)
  ### ("ADT", "Tuples2_findBoth") ->> ( QsADTs.Tuples2_findBoth)
  ### ("ADT", "Tuples2_findFirst") ->> ( QsADTs.Tuples2_findFirst)
  ### ("ADT", "Tuples2_findSecond") ->> ( QsADTs.Tuples2_findSecond)
  ### ("ADT", "Tuples2_enumerate") ->> ( QsADTs.Tuples2_enumerate).
