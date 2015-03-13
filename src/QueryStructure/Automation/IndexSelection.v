Require Import Coq.Sorting.Mergesort Coq.Structures.Orders
        Coq.Arith.Arith
        Coq.Structures.OrderedType Coq.Structures.OrderedTypeEx
        Coq.Strings.String Coq.FSets.FMapAVL
        ADTSynthesis.Common.String_as_OT
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Implementation.Operations.

Module AttrCountOrder <: TotalLeBool.
  Definition t := prod (prod string string) nat.

  (* Largest element first *)
  Definition leb (x y : t) :=
    leb (snd y) (snd x).

  Theorem leb_total : forall a1 a2 : t, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    destruct a1; destruct a2; unfold leb; simpl.
    case_eq (Compare_dec.leb n n0); intuition.
    case_eq (Compare_dec.leb n0 n); intuition.
    apply leb_iff_conv in H; apply leb_iff_conv in H0.
    omega.
  Qed.

End AttrCountOrder.

Module PairOfString_As_OT := (PairOrderedType String_as_OT String_as_OT).

Module RelationAttributeCounter := FMapAVL.Make PairOfString_As_OT.
Module Import AttrCountSort := Sort AttrCountOrder.

Definition IncrementAttrCount
           (idx : string * string)
           (cnt : RelationAttributeCounter.t nat)
: RelationAttributeCounter.t nat :=
  match RelationAttributeCounter.find idx cnt with
    | Some n => RelationAttributeCounter.add idx (S n) cnt
    | _ => RelationAttributeCounter.add idx 1 cnt
  end.

Definition CountAttributes (l : list (string * string))
: list (string * string * nat)  :=
  sort (RelationAttributeCounter.elements
          (fold_right IncrementAttrCount
                      (RelationAttributeCounter.empty nat)
                      l)).

Definition GetIndexes
           (qs_schema : QueryStructureSchema)
           (indices : list (string * string * nat))
: list (list string) :=
  map (fun ns : NamedSchema =>
         map (fun index => snd (fst index))
             (filter (fun index => if (string_dec (fst (fst index)) (relName ns))
                                   then true
                                   else false)
                     indices))
      (qschemaSchemas qs_schema).

Ltac QueryAttributes ClauseAttributes QueryBody k :=
  match QueryBody with
    | @UnConstrQuery_In _ ?qsSchema _ {|bindex := ?Ridx |} ?QueryBody' => (* Initial "Naked" Case *)
      let QueryBody'' := eval cbv beta in (fun tup : @Tuple (GetHeading qsSchema Ridx) => QueryBody' tup) in
          QueryAttributes ClauseAttributes
                          QueryBody'' k  (* Simply recurse under binder *)
    | fun tups : ?A =>
        @UnConstrQuery_In _ ?qsSchema _ {| bindex := ?Ridx |}
                          (@?f tups) => (* Already Under binder *)
      let join := eval cbv beta in
      (fun joinedtups : prod A (@Tuple (GetHeading qsSchema Ridx)) =>
         f (fst joinedtups) (snd joinedtups)) in
          pose "foo2"; QueryAttributes ClauseAttributes join k
    | fun tups => Where (@?P tups) (@?QueryBody' tups) =>
      pose P;
        let attrs := ClauseAttributes P in
        QueryAttributes ClauseAttributes QueryBody'
                        ltac:(fun attrs' => k (app attrs attrs'))
    | _ => k (@nil (prod string string))
  end.

Ltac TermAttributes Term :=
  match Term with
    | fun tups => @GetAttribute _ (@?f tups) {|bindex := ?Aidx |} =>
      match type of f
      with _ -> @Tuple (GetHeading _ ?Ridx) =>
           (* This match works because of the explicit types
                provided in QueryAttributes*)
           constr:([(Ridx, Aidx)])
      end
    | _ => constr:(@nil (prod string string))
  end.

Ltac ClauseAttributes WhereClause TermAttributes k :=
  match WhereClause with
    | fun tups => @?C1 tups /\ @?C2 tups =>
      ClauseAttributes C1 TermAttributes
                       ltac:(fun attrs1 =>
                               ClauseAttributes C2 TermAttributes
                                                ltac:(fun attrs2 =>
                                                        k (app attrs2 attrs1)))
    | fun tups => @?C1 tups = @?C2 tups =>
      let attrs1 := TermAttributes C1 in
      let attrs2 := TermAttributes C2 in
      k (app attrs1 attrs2)
    | _ => k (@nil (prod string string))
  end.

Ltac MethodAttributes meth l :=
  hone method meth;
  [ match goal with
        |- context[For ?Q] =>
        QueryAttributes
          ltac:(fun wc => ClauseAttributes wc TermAttributes ltac:(fun a => a))

                 Q ltac:(fun attrs => let attrs' := eval simpl in attrs in
                                          unify l attrs')
      | _ => unify l (@nil (prod string string))
    end; finish honing | ].

Ltac MethodsAttributes' meths l :=
  match meths with
    | cons ?meth ?meths' =>
      makeEvar (list (prod string string))
               ltac:(fun l1 =>
                       makeEvar (list (prod string string))
                                ltac:(fun l2 =>
                                        unify l (app l1 l2);
                                      MethodAttributes meth l1;
                                      MethodsAttributes' meths' l2))
    | nil => unify l (@nil (prod string string))
  end.

Ltac GenerateIndexesFor meths k :=
  match goal with
      |- Sharpened
           (@BuildADT (UnConstrQueryStructure ?qs_schema) _ _ _ _) =>
      makeEvar (list (prod string string))
               ltac:(fun l =>
                       MethodsAttributes' meths l;
                     let l' := eval compute in
                     (GetIndexes qs_schema (CountAttributes l)) in
                         k l')
  end.

Ltac GenerateIndexesForAll k :=
  match goal with
      |- Sharpened
           (@BuildADT (UnConstrQueryStructure ?qs_schema) _ ?methSigs _ _) => let meths := eval compute in (map methID methSigs) in
                                                                                  GenerateIndexesFor meths k
  end.
