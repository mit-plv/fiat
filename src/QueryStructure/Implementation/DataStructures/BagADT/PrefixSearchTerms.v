Require Import
        ADTSynthesis.QueryStructure.Specification.Representation.Heading
        ADTSynthesis.QueryStructure.Specification.Representation.Tuple
        ADTSynthesis.Common
        ADTSynthesis.Common.BoolFacts
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.List.Prefix
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation
        Coq.Bool.Bool.

Section PrefixSearchTerm.
  Context {A : Type}.
  Context {A_eq_dec : forall a b : A, {a = b} + {a <> b}}.

  Context {Heading : Heading}.
  Definition Tuple := @Tuple Heading.

  Context {Field : Tuple -> list A}.

  Global Instance DecideablePrefix_f {T} (f : T -> list A) {n}
  : DecideableEnsemble (fun tup => prefix_prop (f tup) n) :=
    {| dec n' :=  @prefix_bool _ A_eq_dec (f n') n;
       dec_decides_P n' := prefix_bool_eq (f n') n|}.

  Global Instance DecideablePrefix_b {X} (f : X -> list A) {n}
  : DecideableEnsemble (fun tup => prefix_prop n (f tup)) :=
    {| dec n' :=  @prefix_bool _ A_eq_dec n (f n');
       dec_decides_P n' := prefix_bool_eq n (f n')|}.

  Record PrefixSearchTerm := { pst_index : list A;
                               pst_filter : Tuple -> bool }.

  Definition PrefixSearchTermMatcher
             (search_term : PrefixSearchTerm) (t : Tuple) :=
    @prefix_bool _ A_eq_dec (Field t) (pst_index search_term) && pst_filter search_term t.

  Definition PrefixSearchUpdateTerm :=
    {| BagSearchTermType := PrefixSearchTerm;
       BagMatchSearchTerm := PrefixSearchTermMatcher;
       BagUpdateTermType := Tuple -> Tuple;
       BagApplyUpdateTerm := fun f x => f x |}.
End PrefixSearchTerm.

Ltac PrefixSearchTermFinder' idx :=
  generalize dependent idx;
  let a' := fresh in let ha := fresh in
    match goal with
      | |- forall a, _ = PrefixSearchTermMatcher ?st (@?h a) =>
        intros a'; remember (h a') as ha; generalize ha
    end;
    match goal with
      (* case prefix match *)
      | |- forall a, prefix_bool _ ?t && @?f a =
                     PrefixSearchTermMatcher ?st a =>
        instantiate (1 := {| pst_index := t; pst_filter := f |}); reflexivity
    end.
Ltac AdjustAndRec terminal term :=
  let aterm := fresh in
  first [
      (* if we get the exact match, we're done !*)
      assert (aterm : terminal = term) by reflexivity; clear aterm |
        match term with
          | ?left && ?right =>
            first [
                (* if the left term is the exact match, also done! *)
                assert (aterm : left = terminal) by reflexivity; clear aterm |
                (* if the right term is the exact match, just need to switch! *)
                assert (aterm : right = terminal) by reflexivity; clear aterm;
                replace (left && right) with
                (right && left) by apply andb_comm |
                (* now try recursively on the left term *)
                (AdjustAndRec terminal left);
                  match goal with
                    | |- context [ (terminal && ?rem) && right ] =>
                      replace ((terminal && rem) && right) with
                      (terminal && (rem && right)) by apply andb_assoc
                  end |
                (* and now the right term *)
                (AdjustAndRec terminal right);
                  match goal with
                    | |- context [ left && (terminal && ?rem) ] =>
                      replace (left && (terminal && rem)) with
                      (terminal && (left && rem)) by apply andb_permute
                  end ]
        end ].
Ltac AdjustAnd terminal ensure_and :=
  match goal with
    | |- ?filter = _ => AdjustAndRec terminal filter
  end;
  match ensure_and with
    | true =>
      match goal with
        | |- _ && _ = _ => idtac
        | |- ?x = _ => rewrite <- (andb_true_r x)
      end
    | false => idtac
  end.
Ltac PrefixSearchTermFinder :=
  let idx := fresh in
  intros idx;
    match goal with
      | |- context [ @prefix_bool _ ?dec ?n ?n' ] =>
          AdjustAnd (@prefix_bool _ dec n n') true; PrefixSearchTermFinder' idx
    end.