Require Import List Program Ensembles.
Require Import Coq.Lists.SetoidList.
Require Import ADTNotation GeneralBuildADTRefinements QueryQSSpecs QueryStructure.
Require Import SetEq.

Unset Implicit Arguments.

Ltac generalize_all :=
  repeat match goal with 
             [ H : _ |- _ ] => generalize H; clear H
         end.

Section AdditionalDefinitions.
  Open Scope list_scope.

  Definition NonNil {A: Type} (l: list A) :=
    match l with
      | nil => false
      | _  => true
    end.

  Definition dec2bool {A: Type} {P: A -> Prop} (pred: forall (a: A), sumbool (P a) (~ (P a))) :=
    fun (a: A) => 
      match pred a with
        | left _  => true
        | right _ => false
      end.
  
  Definition Box {A: Type} (x: A) := [x].

  Definition Option2Box {A: Type} (xo: option A) :=
    match xo with
      | Some x => [x]
      | None   => []
    end.

  Definition EnsembleListEquivalence {A: Type} (ensemble: A -> Prop) (seq: list A) :=
    forall x, In _ ensemble x <-> List.In x seq.
End AdditionalDefinitions.

Section AdditionalLogicLemmas.
  Lemma or_false :
    forall (P: Prop), P \/ False <-> P.
  Proof.
    tauto.
  Qed.
End AdditionalLogicLemmas.


Section AdditionalListLemmas.   
  Lemma map_id : 
    forall {A: Type} (seq: list A),
      (map (fun x => x) seq) = seq.
  Proof.
    intros A seq; induction seq; simpl; congruence.
  Qed.      

  Lemma filter_comm :
    forall {A: Type} (pred1 pred2: A -> bool), 
    forall (seq: list A),
      List.filter pred1 (List.filter pred2 seq) =
      List.filter pred2 (List.filter pred1 seq).
  Proof.
    intros A pred1 pred2 seq; 
    induction seq as [ | hd tl];
    [ simpl 
    | destruct (pred1 hd) eqn:eq1; 
      destruct (pred2 hd) eqn:eq2; 
      repeat progress (simpl; 
                       try rewrite eq1; 
                       try rewrite eq2)
    ]; congruence.
  Qed.

  Lemma InA_In:
    forall (A : Type) (x : A) (l : list A),
      InA eq x l -> List.In x l.
  Proof.
    intros ? ? ? H; 
    induction H; 
    simpl;
    intuition.
  Qed.

  Lemma not_InA_not_In : 
    forall {A: Type} l eqA (x: A), 
      Equivalence eqA ->
      not (InA eqA x l) -> not (List.In x l).
  Proof.
    intros A l;
    induction l;
    intros ? ? equiv not_inA in_l;
    simpl in *;
    
    [ trivial
    | destruct in_l as [eq | in_l];
      subst;
      apply not_inA;
      pose proof equiv as (?,?,?);
      eauto using InA_cons_hd, InA_cons_tl, (In_InA equiv)
    ].
  Qed.

  Lemma NoDupA_stronger_than_NoDup : 
    forall {A: Type} (seq: list A) eqA, 
      Equivalence eqA ->
      NoDupA eqA seq -> NoDup seq.
  Proof.
    intros ? ? ? ? nodupA;
    induction nodupA;
    constructor;
    [ apply (not_InA_not_In _ _ _ _ H0)
    | trivial].
  (* Alternative proof: red; intros; apply (In_InA (eqA:=eqA)) in H2; intuition. *)
  Qed.

  Lemma add_filter_nonnil_under_app :
    forall {A: Type} (seq: list (list A)),
      fold_right (app (A := A)) [] seq = 
      fold_right (app (A := A)) [] (List.filter NonNil seq).
  Proof.
    intros; induction seq; simpl; 
    [ | destruct a; simpl; rewrite IHseq]; 
    trivial.
  Qed.
  
(*
  Require Import Notations QueryQSSpecs.
  Local Open Scope QuerySpec_scope.
  Lemma filter_nonnil_plus_where_is_just_filter :
    forall {A B: Type} {P: A -> Prop} (seq: list A),
    forall (pred: forall (a: A), sumbool (P a) (~ (P a))) (extraction: A -> B),
      List.filter NonNil (map (fun p => 
                                 Where (pred p) 
                                       [extraction p]) seq) =
      map Box
          (map extraction (List.filter (dec2bool pred) seq)).
    intros; induction seq; simpl;
    [ | unfold dec2bool; destruct (pred a); subst; rewrite IHseq];
    trivial.
  Qed.
*)

  Lemma box_plus_app_is_identity :
    forall {A: Type} (seq: list A),
      fold_right (app (A := A)) [] (map Box seq) = seq. 
  Proof.
    intros A seq; induction seq; simpl; congruence.
  Qed.

  Lemma in_Option2Box :
    forall {A: Type} (xo: option A) (x: A),
      List.In x (Option2Box xo) <-> xo = Some x. 
  Proof.
    intros A xo x; destruct xo; simpl; try rewrite or_false; intuition; congruence.
  Qed.          
End AdditionalListLemmas.

Section AdditionalComputationLemmas.
  Lemma eq_ret_compute : 
    forall (A: Type) (x y: A), x = y -> ret x ↝ y.
  Proof.
    intros; subst; apply ReturnComputes; trivial.
  Qed.
  
  Lemma refine_eqA_into_ret :
    forall {A: Type} {eqA: list A -> list A -> Prop},
      Reflexive eqA ->
      forall (comp : Comp (list A)) (impl result: list A),
        comp = ret impl -> (
          comp ↝ result ->
          eqA result impl 
        ).
  Proof.
    intros; subst; inversion_by computes_to_inv; subst; trivial. 
  Qed.
End AdditionalComputationLemmas.

Ltac refine_eq_into_ret :=
  match goal with
    | [ H : _ _ _ ↝ _ |- ?eq _ _ ] => 
      generalize H; 
        clear H;
        apply (refine_eqA_into_ret _)
  end.    

Ltac hone_observer' name :=
  hone' observer name using _;
  [ simpl;
    unfold refine; 
    intros;
    unfold Query_For, Query_Where, 
    Query_In, Query_Return, qsHint, 
    In, qsSchemaHint;
    constructor;
    intros;
    constructor;
    intros;
    repeat subst;
    constructor;
    generalize_all | ].

(* TODO: This could probably inconjunction with pull_definition to
avoid the case disjunction in there, but I'm not sure how to allow
unification to proceed: it seems that only a let inside of the
instantiation pattern will do.  *)
Ltac uncurry_evar :=
  instantiate (1 := (fun x => _ (fst x) (snd x)));
  simpl.

Ltac pull_definition :=
  match goal with
    | [ |- ?f (?db1, (?db2, ?db3)) ?params = ret ?body ] =>
      instantiate (1 := fun db params => let (db1, db23) := db in let (db2, db3) := db23 in ret _)
    | [ |- ?f (?db1, ?db2) ?params = ret ?body ] =>
      instantiate (1 := fun db params => let (db1, db2) := db in ret _)
    | [ |- ?f ?db ?params = ret ?body ] => 
      instantiate (1 := fun db params => ret (_ db params)) 
  end;
  simpl;
  exists.

Section AdditionalQueryLemmas.
  Lemma refine_ensemble_into_list_with_extraction :
    forall {A B: Type} (la: list A) (ens: A -> Prop) (lb: list B)  
           (cond_prop: A -> Prop) (cond: A -> bool) 
           (extraction: A -> B),
      (forall a, (cond_prop a <-> cond a = true)) -> 
      (EnsembleListEquivalence ens la) -> 
      ((forall (b: B), List.In b lb <-> (exists a0, ens a0 /\ cond_prop a0 /\ extraction a0 = b)) <->
       (SetEq lb (map extraction (List.filter cond la)))).
  Proof.
    unfold SetEq, EnsembleListEquivalence.

    intros.
    split; intros.
    rewrite in_map_iff.
    destruct (H1 x) as [H1' H1''].

    split; intros.

    specialize (H1' H2).
    destruct H1' as [a1 ?].
    eexists.
    rewrite filter_In, <- H.
    rewrite <- H0.
    instantiate (1 := a1); tauto.

    destruct H2 as [x' H2].
    rewrite filter_In, <- H in H2.
    apply H1''.
    exists x'.
    rewrite H0; tauto.


    rewrite H1.
    rewrite in_map_iff.
    split; intro HH; 
    destruct HH as [x HH];
    exists x;
    try rewrite filter_In in *;
    try rewrite H0, H in *;
    try rewrite <- H0 in *;
    tauto.
  Qed.

  Lemma refine_ensemble_into_list : 
    forall {A: Type},
    forall (la: list A) (ens: A -> Prop) (lb: list A)  
           (cond_prop: A -> Prop) (cond: A -> bool),
      (forall a, (cond_prop a <-> cond a = true)) -> 
      (EnsembleListEquivalence ens la) ->
      ((forall (b : A), List.In b lb <-> ens b /\ cond_prop b) <->
       (SetEq lb (List.filter cond la))).
  Proof.
    unfold EnsembleListEquivalence.
    intros A la ens lb cond_prop cond H H0.
 
    pose proof (refine_ensemble_into_list_with_extraction la ens lb cond_prop cond (fun x => x) H H0).
    simpl in H1.

    rewrite map_id in H1.
    destruct H1 as [H1 H1'].

    split; intros HH;
    [ apply H1 | specialize (H1' HH) ].

    intros.
    specialize (HH b).
    rewrite HH.
    split; intros.
    exists b; intuition.
    destruct H2 as [a0 H2]; intuition; subst; tauto.

    unfold SetEq in HH.
    intros b; specialize (HH b).
    rewrite HH.
    
    rewrite filter_In, H, H0.
    intuition.
  Qed.
End AdditionalQueryLemmas.

Section AdditionalSetEqLemmas.
  Lemma SetUnion_Or : 
    forall {A: Type} 
           {ens1 ens2: A -> Prop}
           {seq1 seq2: list A},
      EnsembleListEquivalence ens1 seq1 ->
      EnsembleListEquivalence ens2 seq2 ->
      EnsembleListEquivalence (fun x => ens1 x \/ ens2 x) (SetUnion seq1 seq2).
  Proof.
    unfold EnsembleListEquivalence, SetUnion, In;
    intros A ens1 ens2 seq1 seq2 eq1 eq2 x;
    specialize (eq1 x);
    specialize (eq2 x);
    rewrite in_app_iff;
    tauto.
  Qed.      

  Lemma equiv_EnsembleListEquivalence:
    forall {A: Type} {seq ens1 ens2},
      (forall (x: A), ens1 x <-> ens2 x) ->
      EnsembleListEquivalence ens1 seq ->
      EnsembleListEquivalence ens2 seq.
  Proof.
    intros A ? ? ? equiv;
    unfold EnsembleListEquivalence;
    intros same_1 x; 
    specialize (equiv x); 
    specialize (same_1 x); 
    intuition.
  Qed.
End AdditionalSetEqLemmas.
