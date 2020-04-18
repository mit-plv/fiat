Require Import Coq.Strings.String Coq.Arith.Arith
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.ListImplementation
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples
        Fiat.QueryStructure.Implementation.Operations.General.EmptyRefinements
        Fiat.Common.List.ListFacts.

Ltac is_sumbool expr :=
  match type of expr with
    | (sumbool _ _) => idtac
    | _ => fail
  end.

Ltac unfold_functions expr :=
  match expr with
    | appcontext [ ?f _ ] => unfold f
  end.

Ltac destruct_ifs_inside conditional :=
  match conditional with
    | context [ if ?sub_conditional then _ else _ ] => destruct_ifs_inside sub_conditional
    | _ => first [ is_sumbool conditional; destruct conditional | progress unfold_functions conditional ]
  end.

Ltac destruct_ifs :=
  intros;
  repeat (match goal with
            | [ |- ?body ] =>
              destruct_ifs_inside body
          end; simpl in *).

Ltac prove_extensional_eq :=
  clear;
  unfold ExtensionalEq;
  destruct_ifs; first [ solve [intuition] | solve [exfalso; intuition] | idtac ].

Example ifs_destruction :
  forall w x y z,
    (if (if string_dec w x then true else false) then (if eq_nat_dec y z then false else true) else (if eq_nat_dec z y then true else false)) = (if (if eq_nat_dec y z then true else false) then (if string_dec x w then false else true) else (if string_dec x w then true else false)).
Proof.
  destruct_ifs; intuition.
Qed.

Ltac autoconvert func :=
  match goal with
    | [ src := cons ?head ?tail |- list _ ] =>
      refine (func head _ :: _);
        [ solve [ eauto with * ] | clear src;
                            set (src := tail);
                            autoconvert func ]
    | [ src := nil |- list _ ] => apply []
    | _ => idtac
  end.

(* [mkIndex] builds a [BagPlusProof] record packaging an indexed
   with all its operations and proofs of correctness. *)

Ltac mkIndex heading attributes' :=
  set (src := attributes');
  assert (list (@ProperAttribute heading)) as decorated_source by autoconvert (@CheckType heading);
  apply (@NestedTreeFromAttributesAsCorrectBagPlusProof heading decorated_source).


 Tactic Notation "lift" "list" "property" constr(prop) "as" ident(name) :=
  pose proof prop as name;
  setoid_rewrite EnsembleIndexedListEquivalence_lift_property in name;
  [ | eassumption].

Tactic Notation "call" "eapply" constr(hypothesis) "after" tactic1(preprocessor) :=
  first [ preprocessor; eapply hypothesis | eapply hypothesis ].

Tactic Notation
       "rewrite" "filter" "over" reference(indexed_storage)
       "using" "search" "term" constr(keyword) :=
  match goal with
    | [ H: EnsembleBagEquivalence ?bag_plus ?table ?storage
        |- appcontext [ filter ?filter1 (benumerate ?storage) ] ] =>
      let temp := fresh in
      let filter2 := constr:(bfind_matcher (Bag := BagPlus indexed_storage)
                                           keyword) in
          assert (ExtensionalEq filter1 filter2) as temp by prove_extensional_eq;
            rewrite (filter_by_equiv filter1 filter2 temp);
            clear temp
      end.

Tactic Notation
       "rewrite" "dependent" "filter" constr(filter1)
       "over" reference(indexed_storage)
       "using" "dependent" "search" "term" constr(keyword) :=
  let temp := fresh in
  let filter2 := constr:(fun x => bfind_matcher (Bag := BagPlus indexed_storage) (keyword x)) in
  assert (forall x, ExtensionalEq (filter1 x) (filter2 x)) as temp by prove_extensional_eq;
    setoid_rewrite (filter_by_equiv_meta filter1 filter2 temp);
    clear temp.


(* The following tactic is useful when we have a set of hypotheses
     of the form

     H0 : In DB tuple
     H  : tupleAgree tuple <COL :: x, ...> COL
     H' : forall tuple', In DB tuple' -> (tuple'!COL <> x)

     which essentially means that we have a tuple that's in the DB and
     matches another one on the COL column, and an hypothesis H' that
     guarantees that such a match is in fact impossible. In that case,
     it's essentially enough to call exfalso, which this tactic does
 *)

Tactic Notation "prove" "trivial" "constraints" :=
  unfold decides, not in *;
  intros;
  match goal with
    | [ H: tupleAgree _ _ (?column :: _) |- _ ] =>
      specialize (H column);
        exfalso;
        match goal with
          | [ H': _ |- _] =>
            eapply H';
              try eassumption;
              call eapply H after symmetry;
              simpl;
              auto
        end
  end.

Definition ID {A} := fun (x: A) => x.

Lemma ens_red {heading}
      {BagType TSearchTerm TUpdateTerm} :
  forall (y_is_bag: Bag BagType (@Tuple heading) TSearchTerm TUpdateTerm) x y,
    @EnsembleIndexedListEquivalence (@Tuple heading) x (benumerate (Bag := y_is_bag) y) =
    (ID (fun y => EnsembleIndexedListEquivalence x (benumerate y))) y.
Proof.
  intros; reflexivity.
Qed.

Lemma EnsembleBagEquivalence_pick_new_index {heading} :
  forall storage (ens : Ensemble (@IndexedTuple heading)) seq,
    EnsembleBagEquivalence storage ens seq ->
    exists bound, UnConstrFreshIdx ens bound.
Proof.
  intros * (indexes & equiv) ** ;
  eapply EnsembleIndexedListEquivalence_pick_new_index; eauto.
  apply indexes.
Qed.

Lemma refine_bag_update_other_table :
  forall (db_schema : QueryStructureSchema) (qs : UnConstrQueryStructure db_schema)
         (index1 index2 : Fin.t _) bag_store store Rel,
    EnsembleBagEquivalence bag_store (GetUnConstrRelation qs index2) store ->
    index1 <> index2 ->
      EnsembleBagEquivalence bag_store
                             (GetUnConstrRelation
                                (UpdateUnConstrRelation qs index1 Rel) index2)
                             store.
Proof.
  intros; rewrite get_update_unconstr_neq; eauto.
Qed.

Ltac refine_bag_update_other_table :=
  match goal with
    | [ |- appcontext [
               EnsembleBagEquivalence
                 ?bag
                 (GetUnConstrRelation
                    (UpdateUnConstrRelation ?qs ?index1 ?Rel) ?index2) ] ] =>
      apply (@refine_bag_update_other_table _ qs index1 index2 bag);
        [ eauto | intuition discriminate ]
  end.

(* Workaround Coq's algorithms not being able to infer ther arguments to refineEquiv_pick_pair *)
Ltac refineEquiv_pick_pair_benumerate :=
  setoid_rewrite refineEquiv_pick_pair;
  unfold ID; cbv beta.

Ltac snd_bdelete_correct search_term :=
  match goal with
      H : EnsembleBagEquivalence ?bag_plus (GetUnConstrRelation ?Rel' ?Ridx) ?bag
      |- EnsembleBagEquivalence
           ?bag_plus
           (GetUnConstrRelation
              (UpdateUnConstrRelation
                 ?Rel ?Ridx
                 (EnsembleDelete (GetUnConstrRelation ?Rel' ?Ridx) ?DeletedTuples))
              ?Ridx) _ =>
      eapply (@bdeletePlus_correct_DB_snd _ Rel Ridx bag_plus bag H DeletedTuples _ search_term);
        prove_extensional_eq
  end.

Ltac binsert_correct_DB :=
  match goal with
    | [ H: EnsembleBagEquivalence ?bag_plus
                                  (GetUnConstrRelation ?qs ?index)
                                  ?store,
        H0 : UnConstrFreshIdx (GetUnConstrRelation ?qs ?index) ?bound |- _ ] =>
      solve [ simpl; apply (binsertPlus_correct_DB qs index bag_plus store H _ bound H0) ]
  end.

(*Lemma refine_Perm_map
      {TItem A}
      {BagPl : BagPlusProof TItem}
:
  forall search_term b f,
    refine {l' : list A |
            Permutation
              (map f (filter (bfind_matcher (Bag := BagPlus BagPl) search_term)
                             (benumerate (Bag := BagPlus BagPl) b))) l' }
           {l' : list A |
            Permutation
              (map f (bfind (Bag := BagPlus BagPl) b search_term)) l' }.
    Admitted.

Tactic Notation "replace" "filter" "enumerate" constr(storage) :=
    match goal with
        |- context[map ?f (filter (bfind_matcher ?search_term)
                                  (benumerate ?bag))] =>
        rewrite (@refine_Perm_map _ _ storage search_term bag f)
    end. *)
