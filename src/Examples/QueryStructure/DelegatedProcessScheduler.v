Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.

Definition State := W.
Definition SLEEPING : State := Word.natToWord 32 0.
Definition RUNNING : State  := Word.natToWord 32 1.

Instance : Query_eq (Word.word n) :=
  { A_eq_dec := @Word.weq n }.
Opaque Word.weq.

Definition SchedulerSchema :=
  Query Structure Schema [
          relation "Processes" has schema
          <"pid" :: W, "state" :: State, "cpu" :: W>
          where (UniqueAttribute ``"pid")
  ] enforcing [].

Definition SchedulerSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure SchedulerSchema,

    Def Constructor0 "Init" : rep := empty,,
    Def Method0 "foo" (r : rep) : rep := ret r

    (*Def Method2 "Spawn" (r : rep) (new_pid cpu : W) : rep * bool :=
      Insert (<"pid" :: new_pid, "state" :: SLEEPING, "cpu" :: cpu> : RawTuple) into r!"Processes",

    Def Method1 "Enumerate" (r : rep) (state : State) : rep * list W :=
      procs <- For (p in r!"Processes")
               Where (p!"state" = state)
               Return (p!"pid");
      ret (r, procs),

    Def Method1 "GetCPUTime" (r : rep) (id : W) : rep * list W :=
        proc <- For (p in r!"Processes")
                Where (p!"pid" = id)
                Return (p!"cpu");
      ret (r, proc) *)
              }%methDefParsing.

Record DelegationADT (Sig : ADTSig)
  : Type
  := Build_SharpenedUnderDelegates
       { DelegateeIDs : nat;
         DelegateeSigs : Fin.t DelegateeIDs -> ADTSig;
         DelegatedImplementation :
           forall (DelegateeReps : Fin.t DelegateeIDs -> Type)
                  (DelegateeConsImpls :
                     forall idx (cidx : ConstructorIndex (DelegateeSigs idx)),
                       constructorType (DelegateeReps idx) (ConstructorDom _ cidx))
                  (DelegateMethImpls :
                     forall idx (midx : MethodIndex (DelegateeSigs idx)),
                       methodType (DelegateeReps idx)
                                  (fst (MethodDomCod _ midx))
                                  (snd (MethodDomCod _ midx))),
             ADT Sig;
         DelegateeSpecs : forall idx, ADT (DelegateeSigs idx) }.

Definition refinedUnderDelegates
           (Sig : ADTSig)
           (spec : ADT Sig)
           (dadt : DelegationADT Sig)
  := forall
    (DelegateReps : Fin.t (DelegateeIDs dadt) -> Type)
    (DelegateConsImpls : forall idx (cidx : ConstructorIndex (DelegateeSigs dadt idx)),
        constructorType (DelegateReps idx) (ConstructorDom _ cidx))
    (DelegateMethImpls : forall idx (midx : MethodIndex (DelegateeSigs dadt idx)),
        methodType (DelegateReps idx)
                   (fst (MethodDomCod _ midx))
                   (snd (MethodDomCod _ midx)))
    (DelegateImpls := fun idx => {| Rep := DelegateReps idx;
                                    Constructors := DelegateConsImpls idx;
                                    Methods := DelegateMethImpls idx |})
    (ValidImpls
     : forall idx : Fin.t (DelegateeIDs dadt),
        refineADT (DelegateeSpecs dadt idx)
                  (DelegateImpls idx)),
    refineADT spec
              (DelegatedImplementation dadt DelegateReps DelegateConsImpls DelegateMethImpls).

Definition refinedUnderDelegatesStep
           (Sig : ADTSig)
           (spec adt' : ADT Sig)
           (dadt : DelegationADT Sig)
           (refine_spec : refineADT spec adt')
           (refine_adt' : refinedUnderDelegates adt' dadt)
  : refinedUnderDelegates spec dadt.
      unfold refinedUnderDelegates; intros.
      eapply transitivityT; eauto.
Defined.

Axiom foo : forall T, T.

Lemma Notation_Friendly_refinedUnderDelegates
           (RepT : Type)
           {DelegateIDs n n'}
           (consSigs : Vector.t consSig n)
           (methSigs : Vector.t methSig n')
           (consDefs : ilist consSigs)
           (methDefs : ilist methSigs)
           (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
           (rep : (Fin.t DelegateIDs -> Type) -> Type)
           (refinedConstructors :
              forall
                (DelegateReps : Fin.t DelegateIDs -> Type)
                (DelegateConsImpls : forall idx (cidx : ConstructorIndex (DelegateSigs idx)),
                    constructorType (DelegateReps idx) (ConstructorDom _ cidx))
                (DelegateMethImpls : forall idx (midx : MethodIndex (DelegateSigs idx)),
                    methodType (DelegateReps idx)
                               (fst (MethodDomCod _ midx))
                               (snd (MethodDomCod _ midx))),
                ilist
                  (B := fun Sig : consSig => constructorType (rep DelegateReps) (consDom Sig))
                  consSigs)
           (refinedMethods :
              forall
                (DelegateReps : Fin.t DelegateIDs -> Type)
                (DelegateConsImpls : forall idx (cidx : ConstructorIndex (DelegateSigs idx)),
                    constructorType (DelegateReps idx) (ConstructorDom _ cidx))
                (DelegateMethImpls : forall idx (midx : MethodIndex (DelegateSigs idx)),
                    methodType (DelegateReps idx)
                               (fst (MethodDomCod _ midx))
                               (snd (MethodDomCod _ midx))),
                ilist
                  (B := fun Sig : methSig =>
                          methodType
                            (rep DelegateReps)
                            (methDom Sig)
                            (methCod Sig)) methSigs)
           (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
           (cAbsR :
              forall
                (DelegateReps : Fin.t DelegateIDs -> Type)
                (DelegateConsImpls : forall idx (cidx : ConstructorIndex (DelegateSigs idx)),
                    constructorType (DelegateReps idx) (ConstructorDom _ cidx))
                (DelegateMethImpls : forall idx (midx : MethodIndex (DelegateSigs idx)),
                    methodType (DelegateReps idx)
                               (fst (MethodDomCod _ midx))
                               (snd (MethodDomCod _ midx)))
                (DelegateImpls := fun idx => {| Rep := DelegateReps idx;
                                                 Constructors := DelegateConsImpls idx;
                                                 Methods := DelegateMethImpls idx |})
                (ValidImpls
                 : forall idx : Fin.t DelegateIDs,
                    refineADT (DelegateSpecs idx)
                              (DelegateImpls idx)),
                RepT -> rep DelegateReps -> Prop)
           (constructorsRefinesSpec :
              forall
                (DelegateReps : Fin.t DelegateIDs -> Type)
                (DelegateConsImpls : forall idx (cidx : ConstructorIndex (DelegateSigs idx)),
                    constructorType (DelegateReps idx) (ConstructorDom _ cidx))
                (DelegateMethImpls : forall idx (midx : MethodIndex (DelegateSigs idx)),
                    methodType (DelegateReps idx)
                               (fst (MethodDomCod _ midx))
                               (snd (MethodDomCod _ midx)))
                (DelegateImpls := fun idx => {| Rep := DelegateReps idx;
                                                 Constructors := DelegateConsImpls idx;
                                                 Methods := DelegateMethImpls idx |})
                (ValidImpls
                 : forall idx : Fin.t DelegateIDs,
                    refineADT (DelegateSpecs idx)
                              (DelegateImpls idx)),
                Iterate_Dep_Type_BoundedIndex
                  (fun idx =>
                     @refineConstructor
                       (RepT)
                       (rep DelegateReps)
                       (cAbsR _ _ _ ValidImpls)
                       (consDom (Vector.nth consSigs idx))
                       (getConsDef consDefs idx)
                       (ith (refinedConstructors
                               DelegateReps
                               DelegateConsImpls
                               DelegateMethImpls) idx)))
           (methodsRefinesSpec :
              forall
                (DelegateReps : Fin.t DelegateIDs -> Type)
                (DelegateConsImpls : forall idx (cidx : ConstructorIndex (DelegateSigs idx)),
                    constructorType (DelegateReps idx) (ConstructorDom _ cidx))
                (DelegateMethImpls : forall idx (midx : MethodIndex (DelegateSigs idx)),
                    methodType (DelegateReps idx)
                               (fst (MethodDomCod _ midx))
                               (snd (MethodDomCod _ midx)))
                (DelegateImpls := fun idx => {| Rep := DelegateReps idx;
                                                 Constructors := DelegateConsImpls idx;
                                                 Methods := DelegateMethImpls idx |})
                (ValidImpls
                 : forall idx : Fin.t DelegateIDs,
                    refineADT (DelegateSpecs idx)
                              (DelegateImpls idx)),
                Iterate_Dep_Type_BoundedIndex
                  (fun idx =>
                     @refineMethod
                       (RepT)
                       (rep DelegateReps)
                       (cAbsR _ _ _ ValidImpls)
                       (methDom (Vector.nth methSigs idx))
                       (methCod (Vector.nth methSigs idx))
                       (getMethDef methDefs idx)
                       (ith (refinedMethods
                               DelegateReps
                               DelegateConsImpls
                               DelegateMethImpls) idx)))
  : refinedUnderDelegates
      (BuildADT (Rep := RepT) consDefs methDefs)
      {|
        DelegateeSigs := DelegateSigs;
        DelegatedImplementation :=
          fun DelegateReps DelegateConsImpls DelegateMethImpls =>
            BuildADT (Rep := rep DelegateReps)
                     (imap (@Build_consDef _) (refinedConstructors DelegateReps DelegateConsImpls DelegateMethImpls))
                     (imap (@Build_methDef _) (refinedMethods DelegateReps DelegateConsImpls DelegateMethImpls));
        DelegateeSpecs := DelegateSpecs |}.
Proof.
  unfold refinedUnderDelegates; simpl; intros.
  eapply (@refinesADT _ (BuildADT (Rep := RepT) consDefs methDefs)
                      (BuildADT (Rep := rep (fun idx => DelegateReps idx)) _ _)
                      (cAbsR DelegateReps _ _ ValidImpls)).
  - intros.
    unfold Constructors; simpl.
    rewrite <- ith_imap; eauto.
    eapply (Lookup_Iterate_Dep_Type
                  _ (constructorsRefinesSpec _ _ _ ValidImpls) idx).
      - intros.
        unfold Methods; simpl.
        rewrite <- ith_imap; eauto.
        eapply (Lookup_Iterate_Dep_Type
                 _ (methodsRefinesSpec _ _ _  ValidImpls) idx).
Defined.

(* Sharpen_w_Delegates constructs a refinement of an ADT whose *)
(* representation is parameterized over some abstract models of state. *)
Definition
  Sharpen_w_Delegates
  (* The fixed set of 'abstract' types in the ADT's *)
  (* representation. *)
  (DelegateIDs : nat)
  (AbstractReps : Fin.t DelegateIDs -> Type)

  (* The parameterized representation type. Intuitively, *)
  (* this relation swaps in 'concrete' types for the *)
  (* abstract ones, i.e. lists for sets. The type's *)
  (* parametricity is witnessed by FunctorRepT. *)
  (pRepT : (Fin.t DelegateIDs -> Type) -> Type)

  (* The initial representation type. *)
  (RepT := pRepT AbstractReps)

  (* The constructors and methods of the ADT being *)
  (* sharpened. *)
  {n n'}
  (consSigs : Vector.t consSig n)
  (methSigs : Vector.t methSig n')
  (consDefs : ilist (B := consDef (Rep := RepT)) consSigs)
  (methDefs : ilist (B := methDef (Rep := RepT)) methSigs)


  (* The signatures of each delegate's constructors *)
  (* and methods in terms of the abstract representation *)
  (* types. *)
  (numDelegateConstructors : Fin.t DelegateIDs -> nat)
  (DelegateConstructorSigs
   : forall (idx : Fin.t DelegateIDs),
      Vector.t consSig (numDelegateConstructors idx))
  (numDelegateMethods : Fin.t DelegateIDs -> nat)
  (DelegateMethodSigs
   : forall (idx : Fin.t DelegateIDs),
      Vector.t methSig (numDelegateMethods idx))
  (DelegateSigs := fun idx =>
                     BuildADTSig
                       (DelegateConstructorSigs idx)
                       (DelegateMethodSigs idx))

  (* The specifications of each delegate's constructors *)
  (* and methods in terms of the abstract representation *)
  (* types. *)
  (DelegateConstructorSpecs
   : forall (idx : Fin.t DelegateIDs),
      ilist (B := consDef (Rep := AbstractReps idx))
            (DelegateConstructorSigs idx))
  (DelegateMethodSpecs
   : forall (idx : Fin.t DelegateIDs),
      ilist (B := methDef (Rep := AbstractReps idx))
            (DelegateMethodSigs idx))
  (DelegateSpecs := fun idx =>
                      BuildADT
                        (DelegateConstructorSpecs idx)
                        (DelegateMethodSpecs idx))

  (* An abstraction relation between the original representation *)
  (* and the abstract representation (generally equality). This is *)
  (* generically lifted to a relation between the original *)
  (* representation and the concrete representation. *)
  (pAbsR : forall (A B : Fin.t DelegateIDs -> Type),
      (forall idx, A idx -> B idx -> Prop)
      -> pRepT A -> pRepT B -> Prop)
  (cAbsR :=
     fun DelegateReps' DelegateConsImpls' DelegateMethImpls'
         (DelegateImpls' := fun idx => {| Rep := DelegateReps' idx;
                                         Constructors := DelegateConsImpls' idx;
                                         Methods := DelegateMethImpls' idx |})
         (ValidImpls'
          : forall idx : Fin.t DelegateIDs,
             refineADT (DelegateSpecs idx)
                       (DelegateImpls' idx))
         r_o r_n =>
       pAbsR _ _ (fun idx => AbsR (ValidImpls' idx)) r_o r_n)

  cConstructors
  cMethods
  cConstructorsRefinesSpec
  cMethodsRefinesSpec

  (* The implementations of each delegate. *)
  (ConcreteReps : Fin.t DelegateIDs -> Type)
  (DelegateImpls : forall idx,
      ADT (DelegateSigs idx))
  (ValidImpls
   : forall idx : Fin.t DelegateIDs,
      refineADT (DelegateSpecs idx)
                (DelegateImpls idx))

  := @Notation_Friendly_refinedUnderDelegates
       RepT _ _ _
       consSigs methSigs
       consDefs methDefs
       DelegateSigs pRepT
       cConstructors
       cMethods
       DelegateSpecs cAbsR
       cConstructorsRefinesSpec
       cMethodsRefinesSpec.

Fixpoint Iterate_Dep_Type_AbsR {n}
         (A B : Fin.t n -> Type)
         (AB_AbsR : forall idx, A idx -> B idx -> Prop)
         (a : Iterate_Dep_Type_BoundedIndex A)
         (b : Iterate_Dep_Type_BoundedIndex B)
  : Prop :=
  match n as n' return
        forall (A B : Fin.t n' -> Type)
               (AB_AbsR : forall idx, A idx -> B idx -> Prop),
          Iterate_Dep_Type_BoundedIndex A
          -> Iterate_Dep_Type_BoundedIndex B
          -> Prop with
  | S n' => fun A B AB_AbsR a b =>
              AB_AbsR _ (prim_fst a) (prim_fst b)
              /\ Iterate_Dep_Type_AbsR (fun n' => A (Fin.FS n'))
                                       (fun n' => B (Fin.FS n'))
                                       (fun n' => AB_AbsR (Fin.FS n'))
                                       (prim_snd a)
                                       (prim_snd b)
  | _ => fun _ _ _ _ _ => True
  end A B AB_AbsR a b.

Fixpoint UnConstryQueryStructure_Abstract_AbsR'
         {n}
         {qsSchema}
         (r_o : ilist2 (B := (fun ns : RawSchema => RawUnConstrRelation (rawSchemaHeading ns))) qsSchema)
         (r_n : Iterate_Dep_Type_BoundedIndex
                  (fun idx : Fin.t n=>
                     @IndexedEnsemble
                       (@RawTuple
                          (rawSchemaHeading (Vector.nth qsSchema idx)))))
  : Prop :=
  match qsSchema as qsSchema return
        forall
          (r_o : ilist2 (B := (fun ns : RawSchema => RawUnConstrRelation (rawSchemaHeading ns))) qsSchema)
          (r_n : Iterate_Dep_Type_BoundedIndex
                   (fun idx : Fin.t _ =>
                      @IndexedEnsemble
                        (@RawTuple
                           (rawSchemaHeading (Vector.nth qsSchema idx))))), Prop with
  | Vector.cons sch _ qsSchema' =>
    fun r_o r_n =>
      ilist2_hd r_o = prim_fst r_n
      /\ UnConstryQueryStructure_Abstract_AbsR'
           (prim_snd r_o)
           (prim_snd r_n)
  | Vector.nil  => fun _ _ => True
  end r_o r_n.

Definition UnConstryQueryStructure_Abstract_AbsR
           {qsSchema}
           (r_o : UnConstrQueryStructure qsSchema)
           (r_n : Iterate_Dep_Type_BoundedIndex _)
  := UnConstryQueryStructure_Abstract_AbsR' r_o r_n.

Lemma UpdateUnConstrRelation_Abstract_AbsR {qsSchema}
  : forall (r_o : UnConstrQueryStructure qsSchema)
           (r_n : Iterate_Dep_Type_BoundedIndex _),
    UnConstryQueryStructure_Abstract_AbsR r_o r_n
    -> forall idx R,
      UnConstryQueryStructure_Abstract_AbsR
        (UpdateUnConstrRelation r_o idx R)
        (Update_Iterate_Dep_Type idx _ r_n R).
Proof.
  intros.
  destruct qsSchema; simpl in *.
  unfold UnConstryQueryStructure_Abstract_AbsR in *.
  unfold UnConstrQueryStructure in r_o; simpl in *.
  unfold UpdateUnConstrRelation; simpl.
  simpl; clear qschemaConstraints.
  generalize dependent qschemaSchemas; intro.
  revert idx; induction qschemaSchemas; simpl; intros.
  - inversion idx.
  - generalize dependent idx.
    intro; intro.
    generalize dependent qschemaSchemas.
    pattern n, idx.
    lazymatch goal with
    | [ |- ?P _ idx ] =>
      simpl; eapply (@Fin.caseS P); simpl; intros; intuition
    end.
Qed.

Ltac UpdateUnConstrRelation_Abstract :=
  match goal with
    H : UnConstryQueryStructure_Abstract_AbsR ?r_o ?r_n
    |- context [{ r_n | UnConstryQueryStructure_Abstract_AbsR
                          (UpdateUnConstrRelation ?r_o ?idx ?R) r_n }] =>
    refine pick val _;
      [ | apply (UpdateUnConstrRelation_Abstract_AbsR r_o r_n H idx R); eauto]
  end.

Ltac PickUnchangedRep :=
  match goal with
    |- context [Pick (fun r_n => @?R r_n)] =>
    match goal with
      H : ?R' ?r_n |- _ => unify R R'; refine pick val r_n; [ | apply H]
    end
  end.

Lemma GetUnConstrRelation_Abstract_AbsR {qsSchema}
  : forall (r_o : UnConstrQueryStructure qsSchema)
           (r_n : Iterate_Dep_Type_BoundedIndex _),
    UnConstryQueryStructure_Abstract_AbsR r_o r_n
    -> forall idx,
      GetUnConstrRelation r_o idx = Lookup_Iterate_Dep_Type _ r_n idx.
Proof.
  intros.
  destruct qsSchema; simpl in *.
  unfold UnConstryQueryStructure_Abstract_AbsR in *.
  unfold UnConstrQueryStructure in r_o; simpl in *.
  unfold GetUnConstrRelation; simpl.
  simpl; clear qschemaConstraints.
  generalize dependent qschemaSchemas; intro.
  revert idx; induction qschemaSchemas; simpl; intros.
  - inversion idx.
  - generalize dependent idx.
    intro.
    generalize dependent qschemaSchemas.
    pattern n, idx.
    lazymatch goal with
    | [ |- ?P _ idx ] =>
      simpl; eapply (@Fin.caseS P); simpl; intros; intuition
    end.
Qed.

Ltac GetUnConstrRelation_Abstract :=
  match goal with
    H : UnConstryQueryStructure_Abstract_AbsR ?r_o ?r_n
    |- context [GetUnConstrRelation ?r_o ?idx] =>
    rewrite (GetUnConstrRelation_Abstract_AbsR r_o r_n H idx)
  end.


Lemma refine_UpdateUnConstrRelationInsertC
      {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx : Fin.t (numRawQSschemaSchemas qsSchema))
           (tup : IndexedElement),
    refine (UpdateUnConstrRelationInsertC qs Ridx tup)
           (ret
              (UpdateUnConstrRelation qs Ridx
                                      (EnsembleInsert tup (GetUnConstrRelation qs Ridx)))).
Proof.
  reflexivity.
Qed.

Lemma refine_UpdateUnConstrRelationDeleteC
      {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema)
           (Ridx : Fin.t (numRawQSschemaSchemas qsSchema))
           (deletedTuples : Ensemble RawTuple),
    refine (UpdateUnConstrRelationDeleteC qs Ridx deletedTuples)
           (ret
              (UpdateUnConstrRelation
                 qs Ridx
                 (EnsembleDelete (GetUnConstrRelation qs Ridx) deletedTuples))).
Proof.
  reflexivity.
Qed.


Ltac parameterize_query_structure :=
        repeat first
               [ simplify with monad laws; cbv beta; simpl
               | rewrite refine_UpdateUnConstrRelationDeleteC
               | rewrite refine_UpdateUnConstrRelationInsertC
               | rewrite refine_If_Then_Else_Bind
               | GetUnConstrRelation_Abstract
               | UpdateUnConstrRelation_Abstract
               | progress unfold QSDeletedTuples
               | PickUnchangedRep].

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac Iterate_Dep_Type_BoundedIndex_evar n T k :=
  match n with
  | 0 => k tt
  | S ?n' =>
    Iterate_Dep_Type_BoundedIndex_evar
      n' (fun n' => T (Fin.FS n'))
      ltac:(fun b =>
              makeEvar
                (T Fin.F1)
                ltac:(fun a =>
                        k ({| prim_fst := a;
                              prim_snd := b |})))
  end.

Ltac make_Vector_of_evar n T k :=
  match n with
  | 0 => k (@Vector.nil T)
  | S ?n' => make_Vector_of_evar
               n' T
               ltac:(fun l =>
                       makeEvar
                         T
                         ltac:(fun a => k (@Vector.cons T a n' l)))
  end.

Ltac ilist_of_evar' n C B As k :=
  match n with
  | 0 => k (fun (c : C) => @inil _ (B c))
  | S ?n' =>
    makeEvar (forall c : C, B c (Vector.hd As))
             ltac:(fun b =>
                     ilist_of_evar'
                       n' C B (Vector.tl As)
                       ltac:(fun Bs' => k (fun c => icons (a := Vector.hd As) (b c) (Bs' c))))
  end.

Ltac ilist_of_evar_dep2 n C D1 D2 B As k :=
  match n with
  | 0 => k (fun (c : C) (d1 : D1 c) (d2 : D2 c) => @inil _ (B c))
  | S ?n' =>
    makeEvar (forall (c : C) (d1 : D1 c) (d2 : D2 c), B c (Vector.hd As))
             ltac:(fun b =>
                           ilist_of_evar_dep2 n'
                                             C D1 D2 B (Vector.tl As)
                                             ltac:(fun Bs' => k (fun (c : C) (d1 : D1 c) (d2 : D2 c) => icons (a := Vector.hd As) (b c d1 d2) (Bs' c d1 d2))))
  end.

Ltac FullySharpenEachMethod_w_Delegates
     DelegateIDs'
     AbstractReps
     dRepT
     dAbsR :=
  match goal with
    |- refinedUnderDelegates (@BuildADT ?Rep' ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs) _ =>
(* We build a bunch of evars in order to decompose the goal *)
    (* into a single subgoal for each constructor. *)
    let DelegateIDs := (eval compute in DelegateIDs') in
    make_Vector_of_evar DelegateIDs nat
                        ltac:(fun numDelegateConstructors' =>
        let numDelegateConstructors := constr:(Vector.nth numDelegateConstructors') in
    make_Vector_of_evar DelegateIDs nat
      ltac:(fun numDelegateMethods' =>
        let numDelegateMethods := constr:(Vector.nth numDelegateMethods') in
    Iterate_Dep_Type_BoundedIndex_evar DelegateIDs
                (fun (idx : Fin.t DelegateIDs)=>
                   Vector.t consSig (numDelegateConstructors idx))
      ltac:(fun DelegateConstructorSigs' =>
    Iterate_Dep_Type_BoundedIndex_evar DelegateIDs
                (fun (idx : Fin.t DelegateIDs)=>
                   Vector.t methSig (numDelegateMethods idx))
      ltac:(fun DelegateMethodSigs' =>
        let DelegateConstructorSigs :=
            constr:(Lookup_Iterate_Dep_Type
                      (fun (idx : Fin.t DelegateIDs)=>
                         Vector.t consSig (numDelegateConstructors idx))
                      DelegateConstructorSigs') in
        let DelegateMethodSigs :=
            constr:(Lookup_Iterate_Dep_Type
                      (fun (idx : Fin.t DelegateIDs)=>
                         Vector.t methSig (numDelegateMethods idx))
                      DelegateMethodSigs') in
        let DelegateSigs :=
            constr:(fun idx =>
                      BuildADTSig (DelegateConstructorSigs idx) (DelegateMethodSigs idx)) in
    Iterate_Dep_Type_BoundedIndex_evar DelegateIDs
                          (fun (idx : Fin.t DelegateIDs) =>
                             ilist (B := consDef (Rep := AbstractReps idx))
                                   (DelegateConstructorSigs idx))
      ltac:(fun DelegateConstructorSpecs' =>
    Iterate_Dep_Type_BoundedIndex_evar DelegateIDs
                (fun (idx : Fin.t DelegateIDs) =>
                  ilist (B := methDef (Rep := AbstractReps idx))
                        (DelegateMethodSigs idx))
      ltac:(fun DelegateMethodSpecs' =>
        let DelegateConstructorSpecs :=
            constr:(Lookup_Iterate_Dep_Type
                      (fun (idx : Fin.t DelegateIDs) =>
                         ilist (B := consDef (Rep := AbstractReps idx))
                               (DelegateConstructorSigs idx))
                      DelegateConstructorSpecs') in
        let DelegateMethodSpecs :=
            constr:(Lookup_Iterate_Dep_Type
                      (fun (idx : Fin.t DelegateIDs) =>
                         ilist (B := methDef (Rep := AbstractReps idx))
                               (DelegateMethodSigs idx))
                      DelegateMethodSpecs') in
        let DelegateSpecs :=
            constr:(fun idx =>
                      BuildADT
                        (DelegateConstructorSpecs idx)
                        (DelegateMethodSpecs idx)) in
        ilist_of_evar_dep2
          n
          (Fin.t DelegateIDs' -> Type)
          (fun DelegateReps =>
             forall idx cidx,
               constructorType (DelegateReps idx)
                               (ConstructorDom (DelegateConstructorSigs idx)) cidx))
          (fun DelegateReps =>
             forall idx midx,
               methodType (DelegateReps idx)
                          (fst (MethodDomCod (DelegateMethodSigs idx)) midx)
                          (snd (MethodDomCod (DelegateMethodSigs idx idx)) midx))
          (fun (DelegateReps : Fin.t DelegateIDs' -> Type)
               (DelegateConsImpls : forall idx (cidx : ConstructorIndex (DelegateSigs idx)),
                   constructorType (DelegateReps idx) (ConstructorDom _ cidx))
               (DelegateMethImpls : forall idx (midx : MethodIndex (DelegateSigs idx)),
                    methodType (DelegateReps idx)
                               (fst (MethodDomCod _ midx))
                               (snd (MethodDomCod _ midx)))
               (Sig : consSig) =>
             constructorType
               (dRepT DelegateReps)
               (consDom Sig))
        consSigs
        ltac:(fun cCons =>
        ilist_of_evar'
          n'
          (forall idx : Fin.t DelegateIDs,
              ADT (DelegateSigs idx))
          (fun (DelegateImpls : forall idx, ADT (DelegateSigs idx))
                    (Sig : methSig) =>
                  methodType
                    (dRepT (fun idx => Rep (DelegateImpls idx)))
                    (methDom Sig)
                    (methCod Sig)
          )
        methSigs
        ltac:(fun cMeths =>
        eapply (@Sharpen_w_Delegates
                          DelegateIDs AbstractReps dRepT n n'
                          consSigs methSigs
                          consDefs methDefs
                          numDelegateConstructors
                          DelegateConstructorSigs
                          numDelegateMethods
                          DelegateMethodSigs
                          (*DelegateConstructorSpecs
                          DelegateMethodSpecs
                          dAbsR
                          cCons
                          cMeths *)
           ))))))))
  end; try (simpl; repeat split; intros; subst).

(* Determines if a term [r_o] is an abstract piece of state. *)
Ltac identify_Abstract_Rep_Use r_o AbstractReps k :=
  first [unify r_o (AbstractReps Fin.F1);
          match type of AbstractReps with
          | Fin.t ?n -> _ => k (@Fin.F1 (n - 1))
          end
        | identify_Abstract_Rep_Use r_o (fun n => AbstractReps (Fin.FS n))
                                    ltac:(fun n => k (Fin.FS n))].

(* Crawls through the goal to identify any occurences of abstract *)
(* state. (Uber generic, albeit super inefficient. *)
Ltac find_Abstract_Rep AbstractReps k :=
  match goal with
    |- context [?r_o] =>
    identify_Abstract_Rep_Use
      ltac:(type of r_o)
             AbstractReps ltac:(k r_o)
  end.

Definition
  Implement_Abstract_Operation
  (* The 'abstract' ADT's representation type. *)
  (AbstractRep : Type)

  (* The signatures of each delegate's constructors *)
  (* and methods in terms of the abstract representation *)
  (* types. *)
  (numDelegateConstructors : nat)
  (DelegateConstructorSigs
   : Vector.t consSig numDelegateConstructors)
  (numDelegateMethods : nat)
  (DelegateMethodSigs
   : Vector.t methSig numDelegateMethods)
  (DelegateSigs := BuildADTSig
                     DelegateConstructorSigs
                     DelegateMethodSigs)

  (* The specifications of each delegate's constructors *)
  (* and methods in terms of the abstract representation *)
  (* types. *)
  (DelegateConstructorSpecs
   : ilist (B := @consDef AbstractRep) DelegateConstructorSigs)
  (DelegateMethodSpecs
   : ilist (B := methDef (Rep := AbstractRep)) DelegateMethodSigs)
  (DelegateSpecs := BuildADT
                      DelegateConstructorSpecs
                      DelegateMethodSpecs)

  (* The concrete ADT implementation's type. *)
  (ConcreteRep : Type)
  (DelegateImpl : ADT DelegateSigs)
  (ValidImpl
   : refineADT DelegateSpecs
               DelegateImpl)
  : forall midx
           (c : methodType
                  (AbstractRep)
                  (fst (MethodDomCod DelegateSigs midx))
                  (snd (MethodDomCod DelegateSigs midx))),
    c = (Methods DelegateSpecs midx)
    -> refineMethod (AbsR ValidImpl)
                    c
                    (Methods DelegateImpl midx).
Proof.
  intros; subst.
  apply (ADTRefinementPreservesMethods ValidImpl midx).
Qed.

Fixpoint observerType' (rep : Type) (dom : list Type) (cod : option Type)
         {struct dom} : Type :=
  match dom with
  | [] =>
    match cod with
    | Some cod' => Comp cod'
    | None => Comp unit
    end
  | d :: dom' => d -> observerType' rep dom' cod
  end.

Definition observerType (rep : Type)
           (dom : list Type)
           (cod : option Type) :=
  rep -> observerType' rep dom cod.

Fixpoint liftObserverToMethod'
         (rep : Type)
         (dom : list Type)
         (cod : option Type)
         (observer : observerType' rep dom cod)
         (r : rep)
         {struct dom}
  : methodType' rep dom cod :=
  match dom as dom' return
        observerType' rep dom' cod
        -> methodType' rep dom' cod
  with
  | [] =>
    match cod as cod' return
          observerType' rep [ ] cod'
          -> methodType' rep [ ] cod' with
    | Some cod' => fun observer => r' <- observer; ret (r, r')
    | None => fun observer => r' <- observer; ret r
    end
  | D :: dom' =>
    fun observer' (d : D) =>
      liftObserverToMethod' dom' cod (observer' d) r
  end observer.

Definition liftObserverToMethod
           (rep : Type)
           (dom : list Type)
           (cod : option Type)
           (observer : observerType rep dom cod) :=
  fun r => liftObserverToMethod' dom cod (observer r) r.

Definition refineObserver {oldRep newRep}
           (AbsR : oldRep -> newRep -> Prop)
           (dom : list Type) (cod : option Type)
           (oldObserver : observerType oldRep dom cod)
           (newMethod : methodType newRep dom cod) :=
  refineMethod AbsR (liftObserverToMethod oldObserver) newMethod.

Lemma refineObserverTrans {oldRep newRep}
  : forall (AbsR : oldRep -> newRep -> Prop)
           (dom : list Type) (cod : option Type)
           (oldObserver : observerType oldRep dom cod)
           (oldMethod : methodType oldRep dom cod)
           (newMethod : methodType newRep dom cod),
    refineObserver eq oldObserver oldMethod
    -> refineMethod AbsR oldMethod newMethod
    -> refineObserver AbsR oldObserver newMethod.
Proof.
  unfold refineObserver; induction dom; simpl.
  - destruct cod; intros.
    + setoid_rewrite <- H0; eauto.
      setoid_rewrite <- H; eauto.
      repeat setoid_rewrite refineEquiv_bind_bind; f_equiv.
      intro.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      intros v Comp_v; computes_to_inv; subst; repeat computes_to_econstructor.
      eauto.
    + setoid_rewrite <- H0; eauto.
      rewrite <- H by eauto.
      repeat setoid_rewrite refineEquiv_bind_bind; f_equiv.
      intro.
      intros v Comp_v; computes_to_inv; subst; repeat computes_to_econstructor;
      eauto.
  - intros.
    eapply IHdom with
    (oldObserver := fun r_o => oldObserver r_o d)
      (oldMethod := fun r_o => oldMethod r_o d)
      (newMethod := fun r_n => newMethod r_n d);
      intros; subst; eauto.
    unfold refineMethod; intros; eapply H; eauto.
    unfold refineMethod; intros; eauto.
Qed.

Lemma refineObserverLift {oldRep}
  : forall (dom : list Type) (cod : option Type)
           (oldObserver : observerType oldRep dom cod),
    refineObserver eq oldObserver (liftObserverToMethod oldObserver).
Proof.
  unfold refineObserver, liftObserverToMethod; induction dom; simpl.
  - destruct cod; intros.
    + rewrite H by eauto.
      intros v Comp_v; computes_to_inv; subst; simpl; eauto.
    + rewrite H by eauto.
      intros v Comp_v; computes_to_inv; subst; simpl; eauto.
  - intros.
    eapply IHdom with
    (oldObserver := fun r_o => oldObserver r_o d);
      intros; subst; eauto.
Qed.

Definition
  Implement_Abstract_Observer
  (* The 'abstract' ADT's representation type. *)
  (AbstractRep : Type)

  (* The signatures of each delegate's constructors *)
  (* and methods in terms of the abstract representation *)
  (* types. *)
  (numDelegateConstructors : nat)
  (DelegateConstructorSigs
   : Vector.t consSig numDelegateConstructors)
  (numDelegateMethods : nat)
  (DelegateMethodSigs
   : Vector.t methSig numDelegateMethods)
  (DelegateSigs := BuildADTSig
                     DelegateConstructorSigs
                     DelegateMethodSigs)

  (* The specifications of each delegate's constructors *)
  (* and methods in terms of the abstract representation *)
  (* types. *)
  (DelegateConstructorSpecs
   : ilist (B := @consDef AbstractRep) DelegateConstructorSigs)
  (DelegateMethodSpecs
   : ilist (B := methDef (Rep := AbstractRep)) DelegateMethodSigs)
  (DelegateSpecs := BuildADT
                      DelegateConstructorSpecs
                      DelegateMethodSpecs)

  (* The delegate ADT implementation. *)
  (DelegateImpl : ADT DelegateSigs)
  (ValidImpl
   : refineADT DelegateSpecs DelegateImpl)
  : forall midx
           (c : observerType
                  (AbstractRep)
                  (fst (MethodDomCod DelegateSigs midx))
                  (snd (MethodDomCod DelegateSigs midx))),
    refineObserver eq c (Methods DelegateSpecs midx)
    -> refineObserver (AbsR ValidImpl)
                      c
                      (Methods DelegateImpl midx).
Proof.
  intros; subst.
  eapply refineObserverTrans; eauto.
  eapply (ADTRefinementPreservesMethods ValidImpl midx).
Qed.

Opaque UpdateUnConstrRelationInsertC.
Opaque UpdateUnConstrRelationDeleteC.

Ltac doOne srewrite_fn drills_fn finish_fn :=
  first [srewrite_fn | drills_fn | finish_fn].

Ltac find_AbsR qschema DelegateImpls ValidImpls :=
  find_Abstract_Rep
    (fun idx : Fin.t (numRawQSschemaSchemas qschema) =>
       @IndexedEnsemble (@RawTuple (rawSchemaHeading (Vector.nth (qschemaSchemas qschema) idx))))
    ltac:(fun r_o n =>
            (* Synthesize a similar concrete representation type [r_n'] *)
            (* using an evar. If this fails, we don't have a candidate for*)
            (* operation conversion. *)
            makeEvar (Rep (DelegateImpls n))
                     ltac:(fun r_n' =>
                             let AbsR_r_o := fresh in
                             assert (AbsR (ValidImpls n) r_o r_n')
                               as AbsR_r_o by intuition eauto);
          (* Generalize the refineADT proof for the concrete representation*)
          (* type [r_n'] so that we can add a new method to its spec. *)
          let ValidImplT' := (type of (ValidImpls n)) in
          let ValidImplT := (eval simpl in ValidImplT') in
          pose (ValidImpls n : ValidImplT)
         ).

Ltac identify_Observer qschema :=
  find_Abstract_Rep
    (fun idx : Fin.t (numRawQSschemaSchemas qschema) =>
       @IndexedEnsemble (@RawTuple (rawSchemaHeading (Vector.nth (qschemaSchemas qschema) idx))))
    ltac:(fun r_o n =>
            match goal with
              |- refine _ (?f ?x) /\ _ =>
              match type of f with
              | Rep (_ (_ ?idx)) -> _ => unify idx n
                end; unify x r_o
            end; split; [ finish honing | solve [intuition eauto]  ] ).

(*Lemma refine_under_bind_constructor
      {DelegateIDs}
      (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
      (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
      (DelegateImpls : forall idx, ADT (DelegateSigs idx))
      (ValidImpls
       : forall idx : Fin.t DelegateIDs,
          refineADT (DelegateSpecs idx)
                    (DelegateImpls idx))
      {B : Type}
  : forall idx
           (c : Comp (Rep (DelegateSpecs idx)))
           (d : Comp (Rep (DelegateImpls idx)))
           (x : Rep (DelegateSpecs idx) -> Comp B)
           (y : Rep (DelegateImpls idx) -> Comp B),
    refineConstructor (AbsR (ValidImpls idx)) (dom := []) c d
    -> (forall r_o r_n, AbsR (ValidImpls idx) r_o r_n ->
                        refine (x r_o) (y r_n))
    -> refine (a <- c; x a) (a <- d; y a).
Proof.
  intros; intuition.
  simpl in H; rewrite <- H.
  autorewrite with monad laws.
  eapply refine_under_bind_both; try reflexivity.
  intros.
  intros v Comp_v; computes_to_inv; subst.
  eapply H0; eauto.
Qed.

Lemma refine_under_bind_method
      {DelegateIDs}
      (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
      (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
      (DelegateImpls : forall idx, ADT (DelegateSigs idx))
      (ValidImpls
       : forall idx : Fin.t DelegateIDs,
          refineADT (DelegateSpecs idx)
                    (DelegateImpls idx))
      {A B : Type}
  : forall idx
           (c : Comp A)
           (c' : Rep (DelegateSpecs idx) -> Comp A)
           (d : Rep (DelegateImpls idx) -> Comp (Rep (DelegateImpls idx) * A))
           (x : A -> Comp B)
           (x' : Rep (DelegateSpecs idx) -> A -> Comp B)
           (y : Rep (DelegateImpls idx) -> A -> Comp B)
           (r_o : Rep (DelegateSpecs idx))
           (r_n : Rep (DelegateImpls idx)),
    (refine c (c' r_o)
     /\ AbsR (ValidImpls idx) r_o r_n)
    -> (forall a, refine (x a) (x' r_o a))
    -> refineMethod (AbsR (ValidImpls idx)) (dom := []) (cod := Some A) (liftObserverToMethod (dom := []) (cod := Some A) c') (d)
    -> (forall a r_o r_n, AbsR (ValidImpls idx) r_o r_n ->
                          refine (x' r_o a) (y r_n a))
    -> refine (a <- c; x a) (a <- d r_n; y (fst a) (snd a)).
Proof.
  intros; intuition.
  setoid_rewrite H3.
  unfold refineObserver, liftObserverToMethod in H1; simpl in H1.
  setoid_rewrite <- H1; intuition eauto.
  autorewrite with monad laws.
  eapply refine_under_bind_both; try reflexivity.
  intros.
  eapply H1 in H4.
  repeat setoid_rewrite refineEquiv_bind_bind in H4.
  repeat setoid_rewrite refineEquiv_bind_unit in H4.
  simpl in *.
  rewrite H0.
  intros v Comp_v; computes_to_inv; subst.
  eapply H2; eauto.
Qed.

Lemma refine_under_bind_Pick_AbsR
      {DelegateIDs}
      (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
      (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
      (DelegateImpls : forall idx, ADT (DelegateSigs idx))
      (ValidImpls
       : forall idx : Fin.t DelegateIDs,
          refineADT (DelegateSpecs idx)
                    (DelegateImpls idx))
      {B : Type}
  : forall idx
           (c : Rep (DelegateSpecs idx))
           (c' : Rep (DelegateSpecs idx) -> Rep (DelegateSpecs idx))
           (d : Rep (DelegateImpls idx) -> Comp (Rep (DelegateImpls idx)))
           (x : Rep (DelegateImpls idx) -> Comp B)
           (y : Rep (DelegateImpls idx) -> Comp B)
           (r_o : Rep (DelegateSpecs idx))
           (r_n : Rep (DelegateImpls idx)),
    (refine (ret c) (ret (c' r_o))
     /\ AbsR (ValidImpls idx) r_o r_n)
    -> refineMethod (AbsR (ValidImpls idx)) (dom := []) (cod := None) (fun r_o => ret (c' r_o)) d
    -> (forall r_o r_n, AbsR (ValidImpls idx) r_o r_n ->
                          refine (x r_n) (y r_n))
    -> refine (a <- { r_n' | AbsR (ValidImpls idx) c r_n' }; x a) (a <- d r_n; y a).
Proof.
  intros; intuition.
  simpl in H0.
  setoid_rewrite <- H0; eauto.
  autorewrite with monad laws.
  specialize (H2 _ (ReturnComputes _)); computes_to_inv; subst.
  eapply refine_under_bind_both; try reflexivity; intros.
  computes_to_inv; subst.
  eauto.
Qed.

Lemma refine_under_bind_Pick_AbsR'
      {DelegateIDs}
      (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
      (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
      (DelegateImpls : forall idx, ADT (DelegateSigs idx))
      (ValidImpls
       : forall idx : Fin.t DelegateIDs,
          refineADT (DelegateSpecs idx)
                    (DelegateImpls idx))
      {B : Type}
  : forall idx
           (c : Rep (DelegateSpecs idx))
           (d : Comp (Rep (DelegateImpls idx)))
           (x : Rep (DelegateImpls idx) -> Comp B)
           (y : Rep (DelegateImpls idx) -> Comp B),
    refineConstructor (AbsR (ValidImpls idx)) (dom := []) (ret c) d
    -> (forall r_o r_n, AbsR (ValidImpls idx) r_o r_n ->
                          refine (x r_n) (y r_n))
    -> refine (a <- { r_n' | AbsR (ValidImpls idx) c r_n' }; x a) (a <- d; y a).
Proof.
  intros; intuition.
  simpl in *.
  setoid_rewrite <- H; eauto.
  autorewrite with monad laws.
  eapply refine_under_bind_both; try reflexivity; intros.
  eapply H0.
  computes_to_inv; subst.
  eauto.
Qed.

Lemma refineObserver_cons
      {Rep_o Rep_n : Type}
      (AbsR' : Rep_o -> Rep_n -> Prop)
  : forall dom cod
           (sig := {| methID := "tmp";
                      methDom := dom;
                      methCod := cod |})
           (c : observerType Rep_o (methDom sig) (methCod sig))
           n'
           (methSigs' : Vector.t methSig n')
           (methDefs_o : ilist (B := methDef) methSigs')
           methDefs_n,
    (forall idx, refineMethod AbsR'
                              (ith (icons {| methBody := liftObserverToMethod c |}
                                          (l := methSigs') methDefs_o) idx)
                              (methDefs_n idx))
    -> refineMethod AbsR' (liftObserverToMethod c)
                      (methDefs_n Fin.F1).
Proof.
  intros; eauto.
  eapply (H (Fin.F1)).
Qed.

Lemma refineMethod_cons_dom
      {Rep_o Rep_n D : Type}
      (d : D)
      (AbsR' : Rep_o -> Rep_n -> Prop)
  : forall dom cod
           (c : D -> methodType Rep_o dom cod)
           (c' : methodType Rep_n (D :: dom) cod),
    refineMethod (dom := D :: dom) AbsR'
                 (fun i d => c d i)
                 c'
    -> refineMethod AbsR' (c d) (fun i => c' i d).
Proof.
  unfold refineMethod; simpl; intros.
  eapply H; eauto.
Qed. *)

Lemma refineEquiv_pick_prim_prod:
  forall (A B : Type) (PA : A -> Prop) (PB : B -> Prop),
    refineEquiv {x : prim_prod A B | PA (prim_fst x) /\ PB (prim_snd x)}
                (a <- {a : A | PA a};
                 b <- {b : B | PB b};
                 ret {| prim_fst := a; prim_snd :=  b |}).
Proof.
  split; intros;
  intros v Comp_v; computes_to_inv; subst; repeat computes_to_econstructor; simpl;
  intuition eauto.
  destruct v; simpl; computes_to_econstructor.
Qed.

Ltac find_evar_in_ilist MethDefs MethSigs k :=
  first [ is_evar MethDefs;
          k (fun n => @Fin.F1 n) MethDefs (MethSigs)
        |
        let MethDefs' := (eval simpl in (prim_snd MethDefs)) in
        let MethSigs' := (eval simpl in (Vector.tl MethSigs)) in
        find_evar_in_ilist
          MethDefs'
          MethSigs'
          ltac:(fun idx MethDefs'' MethSigs'' =>
                  k (fun n => @Fin.FS _ (idx n))
                    MethDefs'' MethSigs'') ].
(*
Ltac insert_constructor_into_delegates
     ConstructorSigs
     ConstructorDefs
     ValidConstructors
     newIndex :=
     (* Now insert the goal into the list of constructors *)
     match goal with
       |- @refineConstructor ?RepSpec ?RepImpl ?AbsR ?dom ?r _ =>
       let RepSpec' := (eval simpl in RepSpec) in
       makeEvar nat
           ltac:(fun n'' =>
       makeEvar (Vector.t consSig n'')
           ltac:(fun consSigs' =>
        makeEvar (ilist (B := @consDef RepSpec') consSigs')
           ltac:(fun consDefs' =>
                    unify ConstructorSigs
                         (Vector.cons
                            _
                            {| consID := "tmp";
                               consDom := dom |}
                            _
                            consSigs');
                 (* This can cause stack overflows later on if RepSpec isn't simpled *)
                 unify ConstructorDefs
                       (icons (@Build_consDef RepSpec' {| consID := "tmp";
                                                          consDom := dom |} r) (l := consSigs') consDefs');
                 apply (ValidConstructors (newIndex n''))
                  )))
  end.

Ltac delegate_to_constructor ValidImpls' :=
  let ValidImpls := (eval simpl in ValidImpls') in
  match type of ValidImpls with
  | forall idx : ?consIndex', refineConstructor _ (@?ConstructorSpecs' idx) (@?ConstructorImpls' idx) =>
    (* Get the list of constructors definitions and signatures *)
    let ConstructorSpecs := (eval simpl in ConstructorSpecs') in
    let ConstructorSigs := (match ConstructorSpecs with
                       | fun idx =>
                           consBody (@ith ?A ?B ?m ?consSigs' ?consDefs' idx) =>
                         consSigs'
                       end) in
    let ConstructorDefs := (match ConstructorSpecs with
                       | fun idx =>
                           consBody (@ith ?A ?B ?m ?consSigs' ?consDefs' idx) =>
                         eval simpl in consDefs'
                       end) in
    find_evar_in_ilist
      ConstructorDefs
      ConstructorSigs
      ltac:(fun idx ConstructorDefs'' ConstructorSigs'' =>
              insert_constructor_into_delegates
                ConstructorSigs'' ConstructorDefs'' ValidImpls idx)
  end.

Ltac insert_method_into_delegates
     MethodSigs
     MethodDefs
     ValidMethods
     newIndex :=
     (* Now insert the goal into the list of methods *)
     match goal with
       |- @refineMethod ?RepSpec ?RepImpl ?AbsR ?dom ?cod ?r _ =>
       makeEvar nat
           ltac:(fun n'' =>
       makeEvar (Vector.t methSig n'')
           ltac:(fun methSigs' =>
        makeEvar (ilist (B := @methDef RepSpec) methSigs')
           ltac:(fun methDefs' =>
                    unify MethodSigs
                         (Vector.cons
                            _
                            {| methID := "tmp";
                               methDom := dom;
                               methCod := cod |}
                            _
                            methSigs');
                 let mDef := constr:(@Build_methDef RepSpec {| methID := "tmp";
                               methDom := dom;
                               methCod := cod |} r) in
                 let methDefs'' :=
                     (eval simpl in (icons mDef (l := methSigs') methDefs')) in
                 try unify MethodDefs methDefs'';
                 eapply (ValidMethods (newIndex n''))
                  )))
  end.


Ltac delegate_to_method ValidImpls' :=
  let ValidImpls := (eval simpl in ValidImpls') in
  match type of ValidImpls with
  | forall idx : ?methIndex', refineMethod _ (@?MethodSpecs' idx) (@?MethodImpls' idx) =>
    (* Get the evar for the number of methods *)
    let MethodSpecs := (eval simpl in MethodSpecs') in
    let numMeths := (match MethodSpecs with
                     | fun idx =>
                         methBody (@ith ?A ?B ?m ?methSigs' ?methDefs' idx) =>
                       m
                     end) in
    (* Get the list of methods definitions and signatures *)
    let MethodSpecs := (eval simpl in MethodSpecs') in
    let MethodSigs := (match MethodSpecs with
                       | fun idx =>
                           methBody (@ith ?A ?B ?m ?methSigs' ?methDefs' idx) =>
                         methSigs'
                       end) in
    let MethodDefs := (match MethodSpecs with
                       | fun idx =>
                           methBody (@ith ?A ?B ?m ?methSigs' ?methDefs' idx) =>
                         eval simpl in methDefs'
                       end) in
    find_evar_in_ilist
      MethodDefs
      MethodSigs
      ltac:(fun idx MethodDefs'' MethodSigs'' =>
              insert_method_into_delegates
                MethodSigs'' MethodDefs'' ValidImpls idx)
  end.

Lemma flatten_CompList_Return_f {A B: Type}
  : forall (f : A -> B) (l : list A),
    refine (FlattenCompList.flatten_CompList (map (fun a => Query_Return (f a)) l)) (ret (map f l)).
Proof.
  induction l; simpl; eauto.
  - reflexivity.
  - setoid_rewrite IHl.
    unfold Query_Return; simplify with monad laws.
    reflexivity.
Qed. *)


Definition SharpenedScheduler :
  {adt' : _ & refinedUnderDelegates SchedulerSpec adt'}.
Proof.
  eexists; unfold SchedulerSpec.
  simpl; pose_string_hyps; pose_heading_hyps.
  eapply refinedUnderDelegatesStep.
  hone representation using (@DropQSConstraints_AbsR SchedulerSchema).
  - eapply Constructor_DropQSConstraints.
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  (*- doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing). *)
  - (*hone method StringId0.
    { setoid_rewrite UniqueAttribute_symmetry.
      setoid_rewrite (@refine_uniqueness_check_into_query' SchedulerSchema Fin.F1 _ _ _ _).
      simpl.
      setoid_rewrite refine_For_rev.
      setoid_rewrite refine_Count.
      subst.
      simplify with monad laws.
      repeat doOne ltac:(first [
                             rewrite !refine_if_If
                           | rewrite refine_If_Then_Else_Duplicate])
                          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    } *)
    hone representation using (@FiniteTables_AbsR SchedulerSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + repeat doOne simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    (*+ repeat doOne simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + repeat doOne simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing). *)
    + hone representation using (@UnConstryQueryStructure_Abstract_AbsR SchedulerSchema).
      * simplify with monad laws.
        refine pick val (imap2 rawRel (Build_EmptyRelations (qschemaSchemas SchedulerSchema))).
        finish honing.
        unfold UnConstryQueryStructure_Abstract_AbsR; simpl; intuition.
      * doAny parameterize_query_structure
              rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      (** doAny parameterize_query_structure
              rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      * doAny parameterize_query_structure
              rewrite_drill ltac:(repeat subst_refine_evar; try finish honing). *)
      * eapply reflexivityT.
  -

    Set Printing Universes.
    Print IterateBoundedIndex.

Definition Sharpen_w_Delegates'
     : forall (DelegateIDs : nat) (AbstractReps : Fin.t DelegateIDs -> Type)
         (pRepT : (Fin.t DelegateIDs -> Type) -> Type)
         (n n' : nat) (consSigs : Vector.t consSig n)
         (methSigs : Vector.t methSig n') (consDefs : ilist consSigs)
         (methDefs : ilist methSigs)
         (numDelegateConstructors : Fin.t DelegateIDs -> nat)
         (DelegateConstructorSigs : forall idx : Fin.t DelegateIDs,
                                    Vector.t consSig
                                      (numDelegateConstructors idx))
         (numDelegateMethods : Fin.t DelegateIDs -> nat)
         (DelegateMethodSigs : forall idx : Fin.t DelegateIDs,
                               Vector.t methSig (numDelegateMethods idx))
         (cConstructors : forall DelegateReps : Fin.t DelegateIDs -> Type,
                          (forall (idx : Fin.t DelegateIDs)
                             (cidx : ConstructorIndex
                                       ((fun idx0 : Fin.t DelegateIDs =>
                                         DecADTSig
                                           ((fun idx1 : Fin.t DelegateIDs =>
                                             BuildADTSig
                                               (DelegateConstructorSigs idx1)
                                               (DelegateMethodSigs idx1))
                                              idx0)) idx)),
                           constructorType (DelegateReps idx)
                             (ConstructorDom
                                ((fun idx0 : Fin.t DelegateIDs =>
                                  DecADTSig
                                    ((fun idx1 : Fin.t DelegateIDs =>
                                      BuildADTSig
                                        (DelegateConstructorSigs idx1)
                                        (DelegateMethodSigs idx1)) idx0)) idx)
                                cidx)) ->
                          (forall (idx : Fin.t DelegateIDs)
                             (midx : MethodIndex
                                       ((fun idx0 : Fin.t DelegateIDs =>
                                         DecADTSig
                                           ((fun idx1 : Fin.t DelegateIDs =>
                                             BuildADTSig
                                               (DelegateConstructorSigs idx1)
                                               (DelegateMethodSigs idx1))
                                              idx0)) idx)),
                           methodType (DelegateReps idx)
                             (fst
                                (MethodDomCod
                                   ((fun idx0 : Fin.t DelegateIDs =>
                                     DecADTSig
                                       ((fun idx1 : Fin.t DelegateIDs =>
                                         BuildADTSig
                                           (DelegateConstructorSigs idx1)
                                           (DelegateMethodSigs idx1)) idx0))
                                      idx) midx))
                             (snd
                                (MethodDomCod
                                   ((fun idx0 : Fin.t DelegateIDs =>
                                     DecADTSig
                                       ((fun idx1 : Fin.t DelegateIDs =>
                                         BuildADTSig
                                           (DelegateConstructorSigs idx1)
                                           (DelegateMethodSigs idx1)) idx0))
                                      idx) midx))) ->
                          ilist (B := consDef (Rep := pRepT AbstractReps)) consSigs)
         (cMethods : forall DelegateReps : Fin.t DelegateIDs -> Type,
                     (forall (idx : Fin.t DelegateIDs)
                        (cidx : ConstructorIndex
                                  ((fun idx0 : Fin.t DelegateIDs =>
                                    DecADTSig
                                      ((fun idx1 : Fin.t DelegateIDs =>
                                        BuildADTSig
                                          (DelegateConstructorSigs idx1)
                                          (DelegateMethodSigs idx1)) idx0))
                                     idx)),
                      constructorType (DelegateReps idx)
                        (ConstructorDom
                           ((fun idx0 : Fin.t DelegateIDs =>
                             DecADTSig
                               ((fun idx1 : Fin.t DelegateIDs =>
                                 BuildADTSig (DelegateConstructorSigs idx1)
                                   (DelegateMethodSigs idx1)) idx0)) idx)
                           cidx)) ->
                     (forall (idx : Fin.t DelegateIDs)
                        (midx : MethodIndex
                                  ((fun idx0 : Fin.t DelegateIDs =>
                                    DecADTSig
                                      ((fun idx1 : Fin.t DelegateIDs =>
                                        BuildADTSig
                                          (DelegateConstructorSigs idx1)
                                          (DelegateMethodSigs idx1)) idx0))
                                     idx)),
                      methodType (DelegateReps idx)
                        (fst
                           (MethodDomCod
                              ((fun idx0 : Fin.t DelegateIDs =>
                                DecADTSig
                                  ((fun idx1 : Fin.t DelegateIDs =>
                                    BuildADTSig
                                      (DelegateConstructorSigs idx1)
                                      (DelegateMethodSigs idx1)) idx0)) idx)
                              midx))
                        (snd
                           (MethodDomCod
                              ((fun idx0 : Fin.t DelegateIDs =>
                                DecADTSig
                                  ((fun idx1 : Fin.t DelegateIDs =>
                                    BuildADTSig
                                      (DelegateConstructorSigs idx1)
                                      (DelegateMethodSigs idx1)) idx0)) idx)
                              midx))) -> ilist (B := methDef (Rep := pRepT AbstractReps)) methSigs) zeke,
      refinedUnderDelegates (BuildADT (Rep := pRepT AbstractReps) consDefs methDefs)
                            zeke.
  admit.
Defined.

Ltac ilist_of_evar_nodep n B As k :=
  match n with
  | 0 => k (@inil _ B)
  | S ?n' =>
    makeEvar (B (Vector.hd As))
             ltac:(fun b =>
                     ilist_of_evar_nodep
                       n' B (Vector.tl As)
                       ltac:(fun Bs' => k (icons (a := Vector.hd As) b Bs')))
  end.

Ltac FullySharpenEachMethod_w_Delegates'
     DelegateIDs'
     AbstractReps
     dRepT
     dAbsR :=
  match goal with
    |- refinedUnderDelegates (@BuildADT ?Rep' ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs) _ =>
(* We build a bunch of evars in order to decompose the goal *)
    (* into a single subgoal for each constructor. *)
    let DelegateIDs := (eval compute in DelegateIDs') in
    make_Vector_of_evar DelegateIDs nat
      ltac:(fun numDelegateConstructors' =>
        let numDelegateConstructors := constr:(Vector.nth numDelegateConstructors') in
    make_Vector_of_evar DelegateIDs nat
      ltac:(fun numDelegateMethods' =>
        let numDelegateMethods := constr:(Vector.nth numDelegateMethods') in
    ilist_of_evar_nodep DelegateIDs
       (fun numCons => Vector.t consSig numCons)
       numDelegateConstructors'
       ltac:(fun DelegateConstructorSigs' =>
    ilist_of_evar_nodep DelegateIDs
       (fun numMeths => Vector.t methSig numMeths)
       numDelegateMethods'
       ltac:(fun DelegateMethodSigs' =>
         let DelegateConstructorSigs :=
             constr:(ith DelegateConstructorSigs') in
         let DelegateMethodSigs :=
             constr:(ith DelegateMethodSigs') in
         let DelegateSigs :=
             constr:(fun idx =>
                       BuildADTSig (DelegateConstructorSigs idx) (DelegateMethodSigs idx)) in
    makeEvar (i2list (fun (idx : nat)
                          (consSigs : Vector.t consSig idx) =>
                        ilist (B := consDef (Rep :=
    (*Iterate_Dep_Type_BoundedIndex_evar DelegateIDs
                          (fun (idx : Fin.t DelegateIDs) =>
                             ilist (B := consDef (Rep := AbstractReps idx))
                                   (DelegateConstructorSigs idx))
      (*ltac:(fun DelegateConstructorSpecs' =>
    Iterate_Dep_Type_BoundedIndex_evar DelegateIDs
                (fun (idx : Fin.t DelegateIDs) =>
                  ilist (B := methDef (Rep := AbstractReps idx))
                        (DelegateMethodSigs idx))
      ltac:(fun DelegateMethodSpecs' =>
        let DelegateConstructorSpecs :=
            constr:(Lookup_Iterate_Dep_Type
                      (fun (idx : Fin.t DelegateIDs) =>
                         ilist (B := consDef (Rep := AbstractReps idx))
                               (DelegateConstructorSigs idx))
                      DelegateConstructorSpecs') in
        let DelegateMethodSpecs :=
            constr:(Lookup_Iterate_Dep_Type
                      (fun (idx : Fin.t DelegateIDs) =>
                         ilist (B := methDef (Rep := AbstractReps idx))
                               (DelegateMethodSigs idx))
                      DelegateMethodSpecs') in
        let DelegateSpecs :=
            constr:(fun idx =>
                      BuildADT
                        (DelegateConstructorSpecs idx)
                        (DelegateMethodSpecs idx)) in
        ilist_of_evar_dep2
          n
          (Fin.t DelegateIDs' -> Type)
          (fun DelegateReps =>
             forall idx cidx,
               constructorType (DelegateReps idx)
                               (consDom (Vector.nth (DelegateConstructorSigs idx) cidx)))
          (fun DelegateReps =>
             forall idx midx,
               methodType (DelegateReps idx)
                          (methDom (Vector.nth (DelegateMethodSigs idx) midx))
                          (methCod (Vector.nth (DelegateMethodSigs idx) midx)))
          (fun (DelegateReps : Fin.t DelegateIDs' -> Type)
               (Sig : consSig) =>
             constructorType
               (dRepT DelegateReps)
               (consDom Sig))
        consSigs
        ltac:(fun cCons =>
        ilist_of_evar_dep2
          n'
          (Fin.t DelegateIDs' -> Type)
          (fun DelegateReps =>
             forall idx cidx,
               constructorType (DelegateReps idx)
                               (consDom (Vector.nth (DelegateConstructorSigs idx) cidx)))
          (fun DelegateReps =>
             forall idx midx,
               methodType (DelegateReps idx)
                          (methDom (Vector.nth (DelegateMethodSigs idx) midx))
                          (methCod (Vector.nth (DelegateMethodSigs idx) midx)))
          (fun (DelegateReps : Fin.t DelegateIDs' -> Type)
               (Sig : methSig) =>
             methodType
               (dRepT DelegateReps)
               (methDom Sig)
               (methCod Sig))
        methSigs
        ltac:(fun cMeths => *) *)
        eapply (@Sharpen_w_Delegates
                          DelegateIDs AbstractReps dRepT n n'
                          consSigs methSigs
                          consDefs methDefs
                          numDelegateConstructors
                          DelegateConstructorSigs
                          numDelegateMethods
                          DelegateMethodSigs
                          _
                          _
                          _
                          _
                          _
                          (*DelegateConstructorSpecs
                          DelegateMethodSpecs
                          dAbsR
                          cCons
                          cMeths *)
           )))))
  end; try (simpl; repeat split; intros; subst).
FullySharpenEachMethod_w_Delegates'
      1
      (fun idx : Fin.t (numRawQSschemaSchemas SchedulerSchema) =>
         @IndexedEnsemble (@RawTuple (rawSchemaHeading (Vector.nth (qschemaSchemas SchedulerSchema) idx))))
      (@Iterate_Dep_Type_BoundedIndex 1)
      (@foo ).
repeat instantiate (1 := foo _).
admit.
repeat instantiate (1 := foo _).
admit.
exact nat.
apply foo.
Grab Existential Variables.
apply foo.

Defined.

eapply Sharpen_w_Delegates.
apply foo.
apply foo.
apply foo.
apply foo.
Grab Existential Variables.
apply foo.
apply foo.
apply foo.
apply foo.
apply foo.
apply foo.
apply foo.
apply foo.
apply foo.
apply foo.

Defined.
FullySharpenEachMethod_w_Delegates'
      1
      (fun idx : Fin.t (numRawQSschemaSchemas SchedulerSchema) =>
         @IndexedEnsemble (@RawTuple (rawSchemaHeading (Vector.nth (qschemaSchemas SchedulerSchema) idx))))
      (@Iterate_Dep_Type_BoundedIndex 1)
      (@foo ).
Set Printing Universes.
Grab Existential Variables.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
Defined.

repeat instantiate (1 := foo _).
admit.

admit.
Grab Existential Variables.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
Set Printing Universes.
Defined.



Set Printing Universes.
eapply foo.
Grab Existential Variables.
repeat instantiate (1 := foo _).
eapply foo.
eapply foo.
eapply foo.
eapply foo.
eapply foo.
Defined.
admit.
exact (inil).
exact (inil).
Defined.

FullySharpenEachMethod_w_Delegates'
      1
      (fun idx : Fin.t (numRawQSschemaSchemas SchedulerSchema) =>
         @IndexedEnsemble (@RawTuple (rawSchemaHeading (Vector.nth (qschemaSchemas SchedulerSchema) idx))))
      (@Iterate_Dep_Type_BoundedIndex 1)
      (@Iterate_Dep_Type_AbsR 1).

simplify with monad laws.
    refine pick val (foo _).
    finish honing.
    eapply foo.
    { simplify with monad laws.
      refine pick val _ ; eauto.
      finish honing.
    }
    exact nat.
    eapply reflexivityT.
    Grab Existential Variables.
    exact inil.
    exact inil.
Defined.

Grab Existential Variables.
repeat instantiate (1 := foo _).
Print Universes.
admit.











    {
      etransitivity.
      simplify with monad laws; simpl.
      match goal with
        |- context [@Pick _ (fun r : prim_prod ?A ?B => @?P r /\ ?Q)] =>
        setoid_rewrite (fun P => @refineEquiv_pick_prim_prod A B P (fun _ => True))
      end.

      refine pick val (foo (DelegateReps Fin.F1)).
      simplify with monad laws.
      refine pick val tt; eauto.
      simplify with monad laws.
      finish honing.
      apply foo.
      finish honing.
    }
    { simplify with monad laws.
      refine pick val _ ; eauto.
      finish honing.
    }
    exact nat.
    eapply reflexivityT.
    Grab Existential Variables.
    exact inil.
    exact inil.
Defined.
    simplify with mona

      Lemma refine_under_bind_Pick_AbsR'
      {DelegateIDs}
      (DelegateSigs : Fin.t DelegateIDs -> ADTSig)
      (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
      (DelegateImpls : forall idx, ADT (DelegateSigs idx))
      (ValidImpls
       : forall idx : Fin.t DelegateIDs,
          refineADT (DelegateSpecs idx)
                    (DelegateImpls idx))
      {B : Type}
  : forall idx
           (c : Rep (DelegateSpecs idx))
           (d : Comp (Rep (DelegateImpls idx)))
           (x : Rep (DelegateImpls idx) -> Comp B)
           (y : Rep (DelegateImpls idx) -> Comp B),
    refineConstructor (AbsR (ValidImpls idx)) (dom := []) (ret c) d
    -> (forall r_o r_n, AbsR (ValidImpls idx) r_o r_n ->
                          refine (x r_n) (y r_n))
    -> refine (a <- { r_n' | AbsR (ValidImpls idx) c r_n' }; x a) (a <- d; y a).
Proof.
Admitted.
      eapply (refine_under_bind_Pick_AbsR' _ _ _ ValidImpls Fin.F1).

Ltac insert_constructor_into_delegates
     ConstructorSigs
     ConstructorDefs
     ValidConstructors
     newIndex :=
     simpl;
     (* Now insert the goal into the list of constructors *)
     match goal with
       |- @refineConstructor ?RepSpec ?RepImpl ?AbsR ?dom ?r _ =>
       let RepSpec' := (eval simpl in RepSpec) in
       makeEvar nat
           ltac:(fun n'' =>
       makeEvar (Vector.t consSig n'')
           ltac:(fun consSigs' =>
        makeEvar (ilist (B := @consDef RepSpec') consSigs')
           ltac:(fun consDefs' =>
                    unify ConstructorSigs
                         (Vector.cons
                            _
                            {| consID := "tmp";
                               consDom := dom |}
                            _
                            consSigs');
                 (* This can cause stack overflows later on if RepSpec isn't simpled *)
                 unify ConstructorDefs
                       (icons (@Build_consDef RepSpec' {| consID := "tmp";
                                                          consDom := dom |} r) (l := consSigs') consDefs');
                 apply (ValidConstructors (newIndex n''))
                  )))
  end.

Ltac delegate_to_constructor ValidImpls' :=
  let ValidImpls := (eval simpl in ValidImpls') in
  match type of ValidImpls with
  | forall idx : ?consIndex', refineConstructor _ (@?ConstructorSpecs' idx) (@?ConstructorImpls' idx) =>
    (* Get the list of constructors definitions and signatures *)
    let ConstructorSpecs := (eval simpl in ConstructorSpecs') in
    let ConstructorSigs := (match ConstructorSpecs with
                       | fun idx =>
                           consBody (@ith ?A ?B ?m ?consSigs' ?consDefs' idx) =>
                         consSigs'
                       end) in
    let ConstructorDefs := (match ConstructorSpecs with
                       | fun idx =>
                           consBody (@ith ?A ?B ?m ?consSigs' ?consDefs' idx) =>
                         eval simpl in consDefs'
                       end) in
    find_evar_in_ilist
      ConstructorDefs
      ConstructorSigs
      ltac:(fun idx ConstructorDefs'' ConstructorSigs'' =>
              insert_constructor_into_delegates
                ConstructorSigs'' ConstructorDefs'' ValidImpls idx)
  end.
Arguments refineConstructor : simpl never.

delegate_to_constructor (ADTRefinementPreservesConstructors (ValidImpls Fin.F1)).
      simpl; intros; setoid_rewrite (refine_pick_val (a := tt)); eauto;
      simplify with monad laws.
      finish honing.
      finish honing.
    }
    { simplify with monad laws.
      refine pick val _ ; eauto.
      finish honing.
    }
    exact nat.
    eapply reflexivityT.
    Grab Existential Variables.
    exact inil.
    exact inil.
Defined.



    {
    Arguments refineMethod : simpl never.
    simplify with monad laws; simpl.
    etransitivity.
    intros; eapply (refine_under_bind_method _ _ _ ValidImpls); simpl; try eauto.
    identify_Observer SchedulerSchema.


    intros; finish honing.
    delegate_to_method (ADTRefinementPreservesMethods (ValidImpls Fin.F1)).

    simpl; intros.
    rewrite !refine_For.
    Transparent QueryResultComp.
    simplify with monad laws.
    eapply (refine_under_bind_method _ _ _ ValidImpls); simpl; try eauto.
    identify_Observer SchedulerSchema.
    intros; finish honing.
    match goal with
      |- refineMethod ?AbsR' (dom := ?Dom) (cod := ?Cod) ?meth_o ?meth_n =>
      let meth_o' := (eval pattern d in meth_o) in
      let meth_o'' := match meth_o' with ?f _ => f end in
      apply (@refineMethod_cons_dom _ _ _ d AbsR' Dom Cod meth_o'');
        simpl
    end.
    match goal with
      |- refineMethod ?AbsR' (dom := ?Dom) (cod := ?Cod) ?meth_o ?meth_n =>
      let meth_o' := (eval pattern d0 in meth_o) in
      let meth_o'' := match meth_o' with ?f _ => f end in
      eapply (@refineMethod_cons_dom _ _ _ d0 AbsR' Dom Cod meth_o'')
    end.
    clear; simpl in *.
    delegate_to_method (ADTRefinementPreservesMethods (ValidImpls Fin.F1)).
    (* rewrite causing stack overflows out the wazzoo. *)
    (* mysteriously, this is no longer happening. *)
    simpl; intros.
    rewrite flatten_CompList_Return; simplify with monad laws.
    rewrite refine_Permutation_Reflexivity; simplify with monad laws.
    rewrite refine_If_Then_Else_Bind.
    etransitivity; apply refine_If_Then_Else.
    simplify with monad laws; simpl.
    set_evars.
    match goal with
      |- context [@Pick _ (fun r : prim_prod ?A ?B => @?P r /\ ?Q)] =>
      setoid_rewrite (fun P => @refineEquiv_pick_prim_prod A B P (fun _ => True))
    end.
    simplify with monad laws.
    (* Need a refine_under_bind_mutator variant here. *)
    eapply (refine_under_bind_Pick_AbsR _ _ _ ValidImpls Fin.F1).
    Show Existentials.
    identify_Observer SchedulerSchema.
    simpl.
    match goal with
      |- refineMethod ?AbsR' (dom := ?Dom) (cod := ?Cod) ?meth_o ?meth_n =>
      let meth_o' := (eval pattern d in meth_o) in
      let meth_o'' := match meth_o' with ?f _ => f end in
      apply (@refineMethod_cons_dom _ _ _ d AbsR' Dom Cod meth_o'');
        simpl
    end.
    match goal with
      |- refineMethod ?AbsR' (dom := ?Dom) (cod := ?Cod) ?meth_o ?meth_n =>
      let meth_o' := (eval pattern d0 in meth_o) in
      let meth_o'' := match meth_o' with ?f _ => f end in
      eapply (@refineMethod_cons_dom _ _ _ d0 AbsR' Dom Cod meth_o'')
    end.
    match goal with
      |- refineMethod ?AbsR' (dom := ?Dom) (cod := ?Cod) ?meth_o ?meth_n =>
      let meth_o' := (eval pattern a in meth_o) in
      let meth_o'' := match meth_o' with ?f _ => f end in
      eapply (@refineMethod_cons_dom _ _ _ a AbsR' Dom Cod meth_o'')
    end.
    simpl in *.
    delegate_to_method (ADTRefinementPreservesMethods (ValidImpls Fin.F1)).
    simpl.
    intros; refine pick val tt; eauto; simplify with monad laws.
    finish honing.

    simplify with monad laws.
    set_evars.
    match goal with
      |- context [@Pick _ (fun r : prim_prod ?A ?B => @?P r /\ ?Q)] =>
      setoid_rewrite (fun P => @refineEquiv_pick_prim_prod A B P (fun _ => True))
    end.
    simplify with monad laws.
    simpl; refine pick val _; intuition eauto.
    simplify with monad laws.
    intros; refine pick val tt; eauto; simplify with monad laws.
    finish honing.

    finish honing.
    finish honing.
    finish honing.
    }

    {
    Arguments refineMethod : simpl never.
    simplify with monad laws; simpl.
    etransitivity.
    rewrite !refine_For.
    Transparent QueryResultComp.
    simplify with monad laws.
    eapply (refine_under_bind_method _ _ _ ValidImpls); simpl; try eauto.
    identify_Observer SchedulerSchema.
    intros; finish honing.
    match goal with
      |- refineMethod ?AbsR' (dom := ?Dom) (cod := ?Cod) ?meth_o ?meth_n =>
      let meth_o' := (eval pattern d in meth_o) in
      let meth_o'' := match meth_o' with ?f _ => f end in
      apply (@refineMethod_cons_dom _ _ _ d AbsR' Dom Cod meth_o'');
        simpl
    end.
    clear; simpl in *.
    delegate_to_method (ADTRefinementPreservesMethods (ValidImpls Fin.F1)).
    (* rewrite causing stack overflows out the wazzoo. *)
    (* mysteriously, this is no longer happening. *)
    simpl; intros.

    rewrite flatten_CompList_Return_f; simplify with monad laws.
    rewrite refine_Permutation_Reflexivity; simplify with monad laws.
    set_evars.
    match goal with
      |- context [@Pick _ (fun r : prim_prod ?A ?B => @?P r /\ ?Q)] =>
      setoid_rewrite (fun P => @refineEquiv_pick_prim_prod A B P (fun _ => True))
    end.
    simplify with monad laws.
    simpl; refine pick val _; intuition eauto.
    simplify with monad laws.
    simpl; refine pick val tt; intuition eauto.
    simplify with monad laws.
    finish honing.
    finish honing.
    }

    {
    Arguments refineMethod : simpl never.
    simplify with monad laws; simpl.
    etransitivity.
    rewrite !refine_For.
    Transparent QueryResultComp.
    simplify with monad laws.
    eapply (refine_under_bind_method _ _ _ ValidImpls); simpl; try eauto.
    identify_Observer SchedulerSchema.
    intros; finish honing.
    match goal with
      |- refineMethod ?AbsR' (dom := ?Dom) (cod := ?Cod) ?meth_o ?meth_n =>
      let meth_o' := (eval pattern d in meth_o) in
      let meth_o'' := match meth_o' with ?f _ => f end in
      apply (@refineMethod_cons_dom _ _ _ d AbsR' Dom Cod meth_o'');
        simpl
    end.
    clear; simpl in *.
    delegate_to_method (ADTRefinementPreservesMethods (ValidImpls Fin.F1)).
    (* rewrite causing stack overflows out the wazzoo. *)
    (* mysteriously, this is no longer happening. *)
    simpl; intros.

    rewrite flatten_CompList_Return_f; simplify with monad laws.
    rewrite refine_Permutation_Reflexivity; simplify with monad laws.
    set_evars.
    match goal with
      |- context [@Pick _ (fun r : prim_prod ?A ?B => @?P r /\ ?Q)] =>
      setoid_rewrite (fun P => @refineEquiv_pick_prim_prod A B P (fun _ => True))
    end.
    simplify with monad laws.
    simpl; refine pick val _; intuition eauto.
    simplify with monad laws.
    simpl; refine pick val tt; intuition eauto.
    simplify with monad laws.
    finish honing.
    finish honing.
    }
    idtac.
    exact nat.
    eapply reflexivityT.
    Grab Existential Variables.
    exact inil.
    exact inil.
    (* Universe Inconsistency :( *)
    (* /Probably/ need to define a variant delegate ADT definition that doesn't *)
    (* package ADT reps inside the record, as we do with computation ADTs at the moment. *)
Defined.

Time Definition PartialSchedulerImpl : ADT _ :=
  Eval simpl in (fst (projT1 SharpenedScheduler)).
Print PartialSchedulerImpl.

Time Definition SchedulerImplSpecs :=
  Eval simpl in (Sharpened_DelegateSpecs (snd (projT1 SharpenedScheduler))).
Print SchedulerImplSpecs.

Print MostlySharpened.

Lemma GetRelation_Empty_eq  :
  forall MySchema R,
    GetRelation (QSEmptySpec MySchema) R = (Empty_set _).
Proof.
  intros; unfold GetRelation, QSEmptySpec.
  rewrite Build_EmptyRelation_IsEmpty; reflexivity.
Qed.

Lemma GetUnConstrRelation_Empty_eq  :
  forall MySchema R,
    GetUnConstrRelation (DropQSConstraints (QSEmptySpec MySchema)) R = (Empty_set _).
Proof.
  intros; rewrite GetRelDropConstraints; apply GetRelation_Empty_eq.
Qed.

Lemma wones_max :
  forall n w, ~ Word.wlt (Word.wones n) w.
Proof.
  admit.
Qed.

Lemma wones_eq :
  forall n w, ~ Word.wlt w (Word.wones n) -> w = Word.wones n.
Proof.
  admit.
Qed.

Lemma wlt_S :
  forall n w,
    Word.wlt w (Word.wplus (Word.natToWord n 1) w).
Proof.
  admit.
Qed.

Lemma wlt_trans :
  forall n (w w' w'' : Word.word n),
    Word.wlt w w'
    -> Word.wlt w' w''
    -> Word.wlt w w''.
Proof.
  admit.
Qed.

Lemma refine_If_Opt_Then_Else_cond {A B}
  : forall (c : option B) (e e': Comp A) (t t' : B -> Comp A),
    (forall b, c = Some b -> refine (t b) (t' b))
    -> (c = None -> refine e e')
    -> refine (Ifopt c as b' Then t b' Else e)
              (Ifopt c as b' Then t' b' Else e').
Proof.
  intros; destruct c; simpl in *; eauto.
Qed.

Definition If_OptC_Then_Else {A B : Type}
           (i : Ensemble A)
           (t : A -> Comp B)
           (e : Comp B) :=
  b <- {b | (forall b', b = Some b' -> i b') /\
            ((forall b', ~ i b') -> b = None)};
  If_Opt_Then_Else b t e.

Locate "Ifopt _ as _ Then _ Else _".

Definition GetRelationBnd
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : BoundedIndex (QSschemaNames QSSchema))
  : @IndexedEnsemble (@RawTuple (GetNRelSchemaHeading (qschemaSchemas QSSchema) (ibound (indexb idx)))) := @GetRelation QSSchema qs (ibound (indexb idx)).

Notation "'IfoptC' i 'as' a 'Then' t 'Else' e" :=
  (If_OptC_Then_Else (fun a => i) (fun a => t) e) (at level 90).

(* This scheduler variant allows new processes to be inserted, requiring a cache. *)
Definition SpawningSchedulerSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure SchedulerSchema,

    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "Spawn" (r : rep) (cpu : W) : rep * bool :=
      IfoptC (forall proc, IndexedEnsemble_In (GetRelationBnd r ``"Processes") proc
                           -> (new_pid <> proc!"pid")) as new_pid
      Then Insert (<"pid" :: new_pid, "state" :: SLEEPING, "cpu" :: cpu> : RawTuple) into r!"Processes"
      Else ret (r, false),

    Def Method1 "Enumerate" (r : rep) (state : State) : rep * list W :=
      procs <- For (p in r!"Processes")
               Where (p!"state" = state)
               Return (p!"pid");
      ret (r, procs),

    Def Method1 "GetCPUTime" (r : rep) (id : W) : rep * list W :=
        proc <- For (p in r!"Processes")
                Where (p!"pid" = id)
                Return (p!"cpu");
      ret (r, proc)
              }%methDefParsing.

(*Definition SpawningSharpenedScheduler :
  MostlySharpened SchedulerSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  {
    (* The tactics don't handle insertions inside of conditionals, so we instead manually *)
    (* drill inside the conditional and apply the tactic. *)
    unfold If_OptC_Then_Else.
    simplify with monad laws.
    etransitivity.
    eapply refine_under_bind; intros.
    set_evars; setoid_rewrite refine_If_Opt_Then_Else_Bind.
    unfold H2; apply refine_If_Opt_Then_Else.
    - intro; set_evars.
      drop_constraints_from_insert.
    - simplify with monad laws.
      simpl; refine pick val _; eauto.
      simplify with monad laws; finish honing.
    - simpl.
      unfold GetRelationBnd.
      rewrite <- GetRelDropConstraints; rewrite H.
      finish honing.
  }
  (* The next step is to cache the current pid. *)
  hone representation using
       (ADTCache.cachedRep_AbsR ((fun (r : UnConstrQueryStructure SchedulerSchema) max_pid =>
             match max_pid with
             | Some pid =>
               forall proc, IndexedEnsemble_In (GetUnConstrRelation r Fin.F1) proc
                            -> (Word.wlt (sz := 32) (GetAttributeRaw proc Fin.F1) pid)
             | None =>
               ~ exists pid,
                 forall proc, IndexedEnsemble_In (GetUnConstrRelation r Fin.F1) proc
                              -> (Word.wlt (GetAttributeRaw proc Fin.F1) pid)
             end)));
    [ setoid_rewrite ADTCache.refine_pick_cachedRep .. | ].
  - apply refine_under_bind; intros.
    computes_to_inv; subst.
    refine pick val (Some (Word.natToWord 32 0)).
    simplify with monad laws; finish honing.
    setoid_rewrite GetUnConstrRelation_Empty_eq.
    unfold IndexedEnsemble_In; intros; destruct_ex; inversion H0.
    - unfold If_OptC_Then_Else.
    simplify with monad laws.
    rewrite (proj1 H0).
    refine pick val (ADTCache.cachedVal r_n).
    simplify with monad laws.
    setoid_rewrite refine_If_Opt_Then_Else_Bind.
    unfold H; eapply refine_If_Opt_Then_Else_cond; set_evars.
    + intros.
      simplify with monad laws.
      repeat setoid_rewrite refine_if_If.
      setoid_rewrite refine_If_Then_Else_Bind.
      unfold H1.
      apply refine_under_bind; intros.
      eapply refine_under_bind; intros.
      apply refine_If_Then_Else.
      setoid_rewrite refine_if_If.
      rewrite refine_If_Then_Else_Bind.
      apply refine_If_Then_Else.
      simplify with monad laws.
      simpl.
      * refine pick val (match ADTCache.cachedVal r_n with
                       | Some v =>
                         if (Word.wlt_dec v (Word.wones _)) then
                           Some (Word.wplus (Word.natToWord 32 1) v)
                         else None
                       | None => None
                       end).
        simplify with monad laws.
        finish honing.
        rewrite H2.
        find_if_inside.
        intros; unfold IndexedEnsemble_In in H5; destruct_ex.
        rewrite get_update_unconstr_eq in H5.
        destruct H5; subst; eauto.
        injection H5; intros; subst.
        unfold GetAttributeRaw, ith2, Vector.caseS, AttrList,
        ilist2_hd, prim_fst, icons2.
        apply wlt_S.
        eapply wlt_trans.
        destruct H0.
        rewrite H2 in H6.
        eapply H6.
        rewrite H0.
        econstructor; unfold In; eauto.
        apply wlt_S.
        intro; destruct_ex.
        eapply wones_max with (n := 32).
        apply wones_eq in n; erewrite <- n.
        eapply (H5 (icons2 _ (icons2 SLEEPING (icons2 d inil2)))).
        econstructor.
        rewrite get_update_unconstr_eq.
        econstructor; reflexivity.
      * simplify with monad laws; simpl.
        refine pick val (Some b).
        simplify with monad laws; finish honing.
        destruct H0; subst; rewrite H2 in H5; eauto.
      * simplify with monad laws; simpl.
        refine pick val (Some b).
        simplify with monad laws; finish honing.
        destruct H0; subst; rewrite H2 in H5; eauto.
    + intros.
      simplify with monad laws; simpl.
      refine pick val None.
      simplify with monad laws; finish honing.
      destruct H0; subst; rewrite H2 in H3; eauto.
    + destruct H0; subst.
      revert H1; case_eq (ADTCache.cachedVal r_n); intros.
      * split.
        { intros; injections; intuition eauto; subst.
          apply H1 in H3; subst.
          eapply Word.eq_le; try eassumption.
          reflexivity. }
        { intros. exfalso; eapply (H2 w).
          intros.
          apply H1 in H3.
          intro; subst.
          eapply Word.eq_le; try eassumption.
          reflexivity. }
      * split.
        { intros; discriminate. }
        { reflexivity. }
  - simplify with monad laws.
    destruct H0; subst.
    unfold H; apply refine_under_bind; intros.
    refine pick val _; eauto.
    simplify with monad laws; finish honing.
  - simplify with monad laws.
    destruct H0; subst.
    unfold H; apply refine_under_bind; intros.
    refine pick val _; eauto.
    simplify with monad laws; finish honing.
  (* Now we implement the various set operations using BagADTs. *)
  (* Again, our tactics don't play nicely with the cache in the spec, so *)
  (* we have to manually massage the goals to get things in the right form. *)
  (* A little more tactic support in the caching refinement should make this *)
  (* much nicer. *)
  - let attrlist := constr:({)|
      prim_fst := [ ("EqualityIndex", Fin.F1);
                    ( "EqualityIndex", Fin.FS (@Fin.F1 1) ) ];
      prim_snd := () |} in
    let sch' := eval simpl in (qschemaSchemas SchedulerSchema) in
        makeIndex' sch' attrlist
                   ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                          ltac:(LastCombineCase5 BuildLastEqualityIndex)
                   ltac:(fun l =>
                           pose_string_hyps; pose_heading_hyps;
                         let index := fresh "Index" in
                         pose l as index;
                         simpl in index;
                         pose_string_hyps_in index; pose_heading_hyps_in index;
                         pose_search_term_in index;
                         pose_SearchUpdateTerms_in index).
    hone representation using (fun r_o r_n => @DelegateToBag_AbsR SchedulerSchema Index (ADTCache.origRep r_o) (ADTCache.origRep r_n) /\ ADTCache.cachedVal r_o = ADTCache.cachedVal r_n).
    + simplify with monad laws.
      refine pick pair.
      initializer.
      make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex

    + simplify with monad laws; simpl.
      refine pick val (Some w).
      simplify with monad laws; finish honing.
      eauto.
    + cbv beta.

      intro; destruct_ex.
      simpl.
      rewrite get_update_unconstr_eq in H6; destruct H6.
      destruct H5; subst; eauto.
      injection H5; intros; subst.
      apply n.
      unfold GetAttributeRaw, ith2, Vector.caseS, AttrList,
      ilist2_hd, prim_fst, icons2 in H7.
      rewrite H0 in H4; injection H4; intros; subst.
      eauto.


    eapply n.
    rewrite H0 in H4; injection H4; intros; subst.


    admit.

    simpl.

    simpl GetAttributeRaw.


    pose @get_update_unconstr_iff. in H6.
    unfold GetUnConstrRelation in H6; simpl.
    simpl in H6.
    setoid_rewrite refine_if_If.
    apply refine_under_bind; intros.
    refine pick val (ADTCache.cachedVal r_n).
    simplify with monad laws.
    finish honing.
    rewrite H0; intros; eapply H1.
    etransitivity.
    eapply refine_Pick_If_Then_Opt.


with
                     | Some v =>
                       if (Word.wlt_dec v (Word.wones _)) then
                         Some (Word.wplus v (Word.natToWord 32 1))
                       else None
                     | None => None
                     end).

    try match goal with
        H0 := _,
        H1 : ADTCache.cachedRep_AbsR _ _ _ |- _ =>
              let H' := fresh in
              destruct H1 as [H' ?]; rewrite H' in *;
              subst H0; apply refine_under_bind
      end.
      Focus 2.
  match goal with
        H0 := _,
        H1 : ADTCache.cachedRep_AbsR _ _ _ |- _ =>
              let H' := fresh in
              destruct H1 as [H' ?]; rewrite H' in *;
              subst H0
      end.
  destruct H0; subst.

  eapply refine_under_bind.
  etransitivity; [apply refine_under_bind | ] .. | ].
  Print LoadPath.
  Focus 2.
  etransitivity.
  apply refine_under_bind.
  unfold H.
  eapply refine_under_bind.
  apply refine_under_bind; intros.
  rewrite (@refine_pick_val _ (Some (Word.natToWord 32 0))).

  Ltac addCache cacheSpec' :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_refine_All with (AbsR := _);
    [ repeat (first [eapply refine_Constructors_nil
                    | eapply refine_Constructors_cons;
                      [ intros;
                        eapply ADTCache.refine_addCacheToConstructor_step with (cacheSpec := cacheSpec');
                        simpl; intros;
                        match goal with
                        |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E) => is_evar E; let H := fresh in set (H := E)
                        | _ => idtac
                        end | ] ])
    | repeat (first [eapply refine_Methods_nil
                    | eapply refine_Methods_cons;
                      [ intros;
                        eapply ADTCache.refine_addCacheToMethod_step with (cacheSpec := cacheSpec');
                        unfold ADTCache.addCacheToMethod; simpl; intros;
                        match goal with
                        |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _) => is_evar E; let H := fresh in set (H := E)
                          | _ => idtac
                        end | ]
                    ])]
  | ].
  addCache (fun (r : QueryStructure SchedulerSchema) max_pid =>
             match max_pid with
             | Some pid =>
               forall proc, IndexedEnsemble_In (GetRelation r Fin.F1) proc
                            -> (Word.wlt (sz := 32) (GetAttributeRaw proc Fin.F1) pid)
             | None => ~ exists pid proc,
                   IndexedEnsemble_In (GetRelation r Fin.F1) proc
                   /\ (GetAttributeRaw proc Fin.F1) <> pid
             end).
  Focus 2.
  unfold refineMethod_eq; simpl; intros.
  eapply addCacheToConstructor


  (exists b', i b' /\ b = Some b') /\
            ((forall b', ~ i b') -> b = None)}


  hone method "Spawn".
  { simpl in *|-.


    Locate Ltac start_honing_QueryStructure'.

  Print UnConstrQueryStructure.

  Definition DelegateToBag_AbsR'
             (qs_schema : RawQueryStructureSchema)
             (r_o r_n : UnConstrQueryStructure qs_schema) :=
    forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
      Same_set _ (GetUnConstrRelation r_o idx)
               (GetUnConstrRelation r_n idx).

  eapply FullySharpened_Finish.
  Print refineADT.
  eapply SharpenFully with (cAbsR := DelegateToBag_AbsR' _).
  econstructor.
  hone representation using (@DelegateToBag_AbsR sch index))


  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics). *)
  master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics).

Time Defined.
(* 1336MB *)
Time Definition MessagesImpl : ComputationalADT.cADT MessagesSig :=
  Eval simpl in (projT1 SharpenedMessages).
Print MessagesImpl. *)
