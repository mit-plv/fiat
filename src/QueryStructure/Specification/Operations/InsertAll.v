Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Sets.Ensembles
        Coq.Arith.Arith
        Fiat.Computation.Core
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.Common.StringBound
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Computation.FoldComp
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildADTSig
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure.

Lemma refine_flip A (a : Comp A) B (b : Comp B) C (z : A -> B -> Comp C) :
  refineEquiv (x <- a; y <- b; z x y)
              (y <- b; x <- a; z x y).
Proof.
  intros.
  Local Transparent Bind.
  unfold Bind.
  unfold refineEquiv.
  unfold refine.
  Local Transparent computes_to.
  unfold computes_to.
  unfold Ensembles.In.
  split;
  intros x H;
  do 2 destruct H;
  do 2 destruct H0;
  exists x1;
  split; trivial;
  exists x0;
  split; trivial.
Qed.

Definition QSInsertType qs_schema QS:=
    QS qs_schema ->
    forall Ridx : Fin.t (numRawQSschemaSchemas
                           (QueryStructureSchemaRaw qs_schema)),
      @RawTuple
        (@GetNRelSchemaHeading
           (numRawQSschemaSchemas (QueryStructureSchemaRaw qs_schema))
           (qschemaSchemas (QueryStructureSchemaRaw qs_schema)) Ridx) ->
      Comp (QS qs_schema  * bool).

Definition StatefulInsertAll {qsSchema A S QS}
         (r : QS qsSchema)
         (idx : BoundedIndex (QSschemaNames qsSchema))
         (st : S) (As : list A)
         (insertComp : QSInsertType qsSchema QS)
         (rowFunc : A -> S -> Comp (_ * S))
         (failure : A -> S -> Comp S) :
  Comp (QS qsSchema * S) :=
  foldComp (fun (acc : QS _ * S) a =>
              let (r, st) := acc in
              p <- rowFunc a st;
              let (newRow, st') := p in
              res  <- insertComp r (ibound (indexb idx)) newRow;
              let (r, b) := res in
              st'' <- If b
                      Then ret st'
                      Else failure a st';
              ret (r, st'')) (r, st) As.

Lemma DropConstraints_StatefulInsertAll {qsSchema A S}
      (r_o : QueryStructure qsSchema)
      (r_n : UnConstrQueryStructure qsSchema)
      (idx : BoundedIndex (QSschemaNames qsSchema))
      (st : S) (As : list A)
      (insertComp : QSInsertType qsSchema QueryStructure)
      (insertComp' : QSInsertType qsSchema UnConstrQueryStructure)
      (rowFunc : A -> S -> Comp (_ * S))
      (failure : A -> S -> Comp S)
      ResultT
      (k : QueryStructure qsSchema * S -> Comp ResultT)
      (k' : UnConstrQueryStructure qsSchema * S -> Comp ResultT) :
   (forall r_o r_n st, DropQSConstraints_AbsR r_o r_n
                         -> refine (k (r_o, st)) (k' (r_n, st)))
     -> DropQSConstraints_AbsR r_o r_n
     -> (forall r_o r_n,
            DropQSConstraints_AbsR r_o r_n
            -> forall_relation2 (fun _ _ => refine)
                             (fun idx tup =>
                                x <- insertComp r_o idx tup;
                                y <- { x' | DropQSConstraints_AbsR (fst x) x'};
                                ret (y, snd x))
                             (insertComp' r_n))
     -> refine (r_o' <- StatefulInsertAll r_o idx st As insertComp
                                          rowFunc failure;
                k r_o')
               (r_n' <- StatefulInsertAll r_n idx st As insertComp'
                                          rowFunc failure;
                k' r_n').
Proof.
  intros.
  apply FoldComp.refine_foldComp_invariant'
    with (P:=fun p p' => DropQSConstraints_AbsR (fst p) (fst p')
                      /\ snd p = snd p').
  - intros ?? H2 ?.
    destruct z, z', H2.
    simpl in H2, H3.
    subst.
    simplify with monad laws.
    f_equiv.
    intros [tup st'].
    specialize (H1 q u H2 (ibound (indexb idx)) tup).
    simpl in H1.
    rewrite <- H1.
    rewrite !refineEquiv_bind_bind.
    f_equiv.
    intros [r b].
    autorewrite with monad laws.
    rewrite refine_flip.
    simpl.
    f_equiv.
    intros st''.
    rewrite refineEquiv_pick_pair.
    f_equiv.
    intros u'.
    refine pick eq.
    autorewrite with monad laws.
    reflexivity.
  - intros.
    destruct st_n, st_n', H2.
    simpl in H2, H3.
    subst.
    apply H.
    exact H2.
  - simpl.
    split; intros; auto.
Qed.
