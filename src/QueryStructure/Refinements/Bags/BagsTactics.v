Require Import QueryStructureNotations.
Require Import ListImplementation.
Require Import BagsInterface.
Require Import AdditionalLemmas.

Ltac prove_observational_eq :=
  clear;
  vm_compute;
  intros;
  repeat match goal with
           | [ |- context[ if ?cond then _ else _ ] ] =>
             let eqn := fresh "eqn" in
             destruct cond eqn:eqn;
               subst;
               vm_compute;
               rewrite ?collapse_ifs_bool, ?collapse_ifs_dec;
               intuition
         end.

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
    | [ (*TODO: storage: BagType ?ind, *) H: EnsembleIndexedListEquivalence ?table (benumerate ?storage) 
        |- appcontext [ filter ?filter1 (benumerate ?storage) ] ] => 
      let temp := fresh in 
      let filter2 := constr:(bfind_matcher (Bag := BagProof indexed_storage) keyword) in
      assert (ObservationalEq filter1 filter2) as temp by prove_observational_eq;
        rewrite (filter_by_equiv filter1 filter2 temp);
        clear temp
  end.

Tactic Notation 
       "rewrite" "dependent" "filter" constr(filter1)
       "over" reference(indexed_storage) 
       "using" "dependent" "search" "term" constr(keyword) :=
  let temp := fresh in
  let filter2 := constr:(fun x => bfind_matcher (Bag := BagProof indexed_storage) (keyword x)) in
  assert (forall x, ObservationalEq (filter1 x) (filter2 x)) as temp by prove_observational_eq;
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
