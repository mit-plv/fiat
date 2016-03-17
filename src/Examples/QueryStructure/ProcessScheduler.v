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
  QueryADTRep SchedulerSchema {
    Def Constructor0 "Init" : rep := empty,

    Def Method2 "Spawn" (r : rep) (new_pid cpu : W) : rep * bool :=
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
      ret (r, proc)
              }%methDefParsing.

Record DelegationADT (Sig : ADTSig)
  : Type
  := Build_SharpenedUnderDelegates
       { DelegateeIDs : nat;
         DelegateeSigs : Fin.t DelegateeIDs -> ADTSig;
         DelegatedImplementation :
           forall (DelegateImpls : forall idx,
                      ADT (DelegateeSigs idx)),
             ADT Sig;
         DelegateeSpecs : forall idx, ADT (DelegateeSigs idx) }.

Definition refinedUnderDelegates
           (Sig : ADTSig)
           (spec : ADT Sig)
           (adt : DelegationADT Sig)
  := forall (DelegateImpls : forall idx,
                ADT (DelegateeSigs adt idx))
            (ValidImpls
             : forall idx : Fin.t (DelegateeIDs adt),
                refineADT (DelegateeSpecs adt idx)
                          (DelegateImpls idx)),
    refineADT spec
              (DelegatedImplementation adt DelegateImpls).

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
                (DelegateImpls : forall idx, ADT (DelegateSigs idx)),
                ilist
                  (B := fun Sig : consSig =>
                          constructorType
                            (rep (fun idx => Rep (DelegateImpls idx)))
                            (consDom Sig)) consSigs)
           (refinedMethods :
              forall (DelegateImpls : forall idx, ADT (DelegateSigs idx)),
                ilist
                  (B := fun Sig : methSig =>
                          methodType
                            (rep (fun idx => Rep (DelegateImpls idx)))
                            (methDom Sig)
                            (methCod Sig)) methSigs)
           (DelegateSpecs : forall idx, ADT (DelegateSigs idx))
           (cAbsR :
              forall
                (DelegateImpls : forall idx, ADT (DelegateSigs idx))
                (ValidImpls
                 : forall idx : Fin.t DelegateIDs,
                    refineADT (DelegateSpecs idx)
                              (DelegateImpls idx)),
                RepT -> rep (fun idx => Rep (DelegateImpls idx)) -> Prop)
           (constructorsRefinesSpec :
              forall
                (DelegateImpls : forall idx, ADT (DelegateSigs idx))
                (ValidImpls
                 : forall idx : Fin.t DelegateIDs,
                    refineADT (DelegateSpecs idx)
                              (DelegateImpls idx)),
                Iterate_Dep_Type_BoundedIndex
                  (fun idx =>
                     @refineConstructor
                       (RepT)
                       (rep (fun idx => Rep (DelegateImpls idx)))
                       (cAbsR _ ValidImpls)
                       (consDom (Vector.nth consSigs idx))
                       (getConsDef consDefs idx)
                       (ith (refinedConstructors DelegateImpls) idx)))
           (methodsRefinesSpec :
              forall
                (DelegateImpls : forall idx, ADT (DelegateSigs idx))
                (ValidImpls
                 : forall idx : Fin.t DelegateIDs,
                    refineADT (DelegateSpecs idx)
                              (DelegateImpls idx)),
                Iterate_Dep_Type_BoundedIndex
                  (fun idx =>
                     @refineMethod
                       (RepT)
                       (rep (fun idx => Rep (DelegateImpls idx)))
                       (cAbsR _ ValidImpls)
                       (methDom (Vector.nth methSigs idx))
                       (methCod (Vector.nth methSigs idx))
                       (getMethDef methDefs idx)
                       (ith (refinedMethods DelegateImpls) idx)))
  : refinedUnderDelegates
      (BuildADT consDefs methDefs)
      {|
        DelegateeSigs := DelegateSigs;
        DelegatedImplementation :=
          fun DelegateImpls =>
            BuildADT (Rep := rep (fun idx => Rep (DelegateImpls idx)))
                     (imap (@Build_consDef _) (refinedConstructors DelegateImpls))
                     (imap (@Build_methDef _) (refinedMethods DelegateImpls));
        DelegateeSpecs := DelegateSpecs |}.
      unfold refinedUnderDelegates; simpl; intros.
      eapply (@refinesADT _ (BuildADT (Rep := RepT) consDefs methDefs)
                          (BuildADT (Rep := rep (fun idx => Rep (DelegateImpls idx))) _ _)
                          (cAbsR DelegateImpls ValidImpls)).
      - intros.
        unfold Constructors; simpl.
        rewrite <- ith_imap; eauto.
        eapply (Lookup_Iterate_Dep_Type
                  _ (constructorsRefinesSpec DelegateImpls ValidImpls) idx).
      - intros.
        unfold Methods; simpl.
        rewrite <- ith_imap; eauto.
        eapply (Lookup_Iterate_Dep_Type
                 _ (methodsRefinesSpec DelegateImpls ValidImpls) idx).
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
     fun DelegateImpls'
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

  := Notation_Friendly_refinedUnderDelegates
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
Admitted.

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
Admitted.

Ltac GetUnConstrRelation_Abstract :=
  match goal with
    H : UnConstryQueryStructure_Abstract_AbsR ?r_o ?r_n
    |- context [GetUnConstrRelation ?r_o ?idx] =>
    rewrite (GetUnConstrRelation_Abstract_AbsR r_o r_n H idx)
  end.

Ltac parameterize_query_structure :=
        repeat first
               [ simplify with monad laws; cbv beta; simpl
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
        ilist_of_evar'
          n
          (forall idx : Fin.t DelegateIDs,
              ADT (DelegateSigs idx))
          (fun (DelegateImpls : forall idx, ADT (DelegateSigs idx))
                    (Sig : consSig) =>
                  constructorType
                    (dRepT (fun idx => Rep (DelegateImpls idx)))
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
                          DelegateConstructorSpecs
                          DelegateMethodSpecs
                          dAbsR
                          cCons
                          cMeths

           )))))))))
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

Fixpoint refineObserver' {oldRep newRep}
         (AbsR : oldRep -> newRep -> Prop)
         (dom : list Type)
         (cod : option Type) {struct dom} :=
  match
    dom as dom'
    return
    (observerType' oldRep dom' cod
     -> methodType' newRep dom' cod
     -> Prop)
  with
  | [] =>
    match cod as cod' return
          (observerType' oldRep [] cod' -> methodType' newRep [] cod' -> Prop)
    with
    | Some cod' =>
      fun oldObserver newMethod =>
        refine oldObserver
               (r <- newMethod; ret (snd r))
    | None =>
      fun oldObserver newMethod =>
        refine oldObserver (r <- newMethod; ret tt)
    end
  | D :: dom' =>
    fun oldObserver newMethod =>
      forall d : D, refineObserver' AbsR dom' cod (oldObserver d) (newMethod d)
  end.

Definition refineObserver {oldRep newRep}
           (AbsR : oldRep -> newRep -> Prop)
           (dom : list Type) (cod : option Type)
           (oldObserver : observerType oldRep dom cod)
           (newMethod : methodType newRep dom cod) :=
  forall (r_o : oldRep) (r_n : newRep),
    AbsR r_o r_n
    -> refineObserver' AbsR dom cod (oldObserver r_o) (newMethod r_n).

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
    + rewrite H by eauto.
      setoid_rewrite <- H0; eauto.
      repeat setoid_rewrite refineEquiv_bind_bind; f_equiv.
      intro.
      setoid_rewrite refineEquiv_bind_unit; simpl.
      intros v Comp_v; computes_to_inv; subst; computes_to_econstructor.
    + rewrite H by eauto.
      setoid_rewrite <- H0; eauto.
      repeat setoid_rewrite refineEquiv_bind_bind; f_equiv.
      intro.
      intros v Comp_v; computes_to_inv; subst; computes_to_econstructor.
  - intros.
    eapply IHdom with
    (oldObserver := fun r_o => oldObserver r_o d)
      (oldMethod := fun r_o => oldMethod r_o d)
      (newMethod := fun r_n => newMethod r_n d);
      intros; subst; eauto.
    unfold refineMethod; intros; eapply H0; eauto.
Qed.

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
      destruct v1; eauto.
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

Definition SharpenedScheduler :
  {adt' : _ & refinedUnderDelegates SchedulerSpec adt'}.
Proof.
  eexists; unfold SchedulerSpec.
  simpl; pose_string_hyps; pose_heading_hyps.
  eapply refinedUnderDelegatesStep.
  eapply SharpenStep;
    [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl | ]
          ])]
      end | ].
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone method StringId0.
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
    }
    hone representation using (@FiniteTables_AbsR SchedulerSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + repeat doOne simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + repeat doOne simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + repeat doOne simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + hone representation using (@UnConstryQueryStructure_Abstract_AbsR SchedulerSchema).
      * simplify with monad laws.
        refine pick val (imap2 rawRel (Build_EmptyRelations (qschemaSchemas SchedulerSchema))).
        finish honing.
        unfold UnConstryQueryStructure_Abstract_AbsR; simpl; intuition.
      * Transparent UpdateUnConstrRelationInsertC.
        Transparent UpdateUnConstrRelationDeleteC.
        doAny parameterize_query_structure
              rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      * doAny parameterize_query_structure
              rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      * doAny parameterize_query_structure
              rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      * eapply reflexivityT.
  - simpl.
    FullySharpenEachMethod_w_Delegates
      1
      (fun idx : Fin.t (numRawQSschemaSchemas SchedulerSchema) =>
         @IndexedEnsemble (@RawTuple (rawSchemaHeading (Vector.nth (qschemaSchemas SchedulerSchema) idx))))
      (@Iterate_Dep_Type_BoundedIndex 1)
      (@Iterate_Dep_Type_AbsR 1).
    Focus 2.

simplify with monad laws; simpl.
etransitivity.
apply refine_under_bind_both.

Ltac find_AbsR DelegateImpls ValidImpls :=
find_Abstract_Rep
  (fun idx : Fin.t (numRawQSschemaSchemas SchedulerSchema) =>
     @IndexedEnsemble (@RawTuple (rawSchemaHeading (Vector.nth (qschemaSchemas SchedulerSchema) idx))))
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

find_AbsR DelegateImpls ValidImpls.


    match goal with
      H : refineADT (@BuildADT ?Rep ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs)
                _
  |- refine ?c ?H0 =>
  makeEvar nat
    ltac:(fun n'' =>
  makeEvar (Vector.t methSig n'')
     ltac:(fun methSigs' =>
  makeEvar (ilist (B := @methDef Rep) methSigs')
           ltac:(fun methDefs' =>
                   unify methSigs
                         (@Vector.cons methSig {| methID := "foo";
                              methDom := @nil Type;
                              methCod := Some (nat : Type) |} n'' methSigs');
             unify methDefs
                   (@icons methSig
                           (@methDef Rep)
                           {| methID := "foo";
                              methDom := @nil Type;
                              methCod := Some (nat : Type) |}
                           n'' methSigs'
                           (@Build_methDef Rep {| methID := "foo";
                              methDom := @nil Type;
                              methCod := Some (nat : Type) |}
                                           (fun (r_o : Rep) =>
                                              idx <- { idx | UnConstrFreshIdx r_o idx};
                                            ret (r_o, idx)))
                           methDefs');
             apply (@Implement_Abstract_Observer Rep
                                                  n consSigs (S n'')
                                                 methSigs
                                                 consDefs
                                                 methDefs
                                                 _
                                                 (ValidImpls (Fin.F1))
                                                 (Fin.F1)
                                                 _
                                                 (refineObserverLift _)
                                                 
                  )
         ); eauto))
end.
intros.
rewrite !refine_For.
Transparent QueryResultComp.

simplify with monad laws.
apply refine_under_bind_both.
find_AbsR DelegateImpls ValidImpls.

apply r0.
simpl in r0.
Check (r0 _ (refineObserverLift _)).
unfold refineObserver in r0; simpl in r0.



  (* Now we implement the various set operations using BagADTs. *)
  - make_simple_indexes
      {|
        prim_fst := [ ("EqualityIndex", Fin.F1);
                      ( "EqualityIndex", Fin.FS (@Fin.F1 1) ) ];
        prim_snd := () |}
      ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
             ltac:(LastCombineCase5 BuildLastEqualityIndex).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + setoid_rewrite refine_For_rev; simplify with monad laws.
      plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + setoid_rewrite refine_For_rev; simplify with monad laws.
      plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + hone method "Spawn".
      { subst; simplify with monad laws.
        unfold GetAttributeRaw at 1.
        simpl; unfold ilist2_hd at 1; simpl.
        unfold H1; apply refine_under_bind.
        intros; set_evars.
        setoid_rewrite refine_pick_eq'; simplify with monad laws.
        rewrite app_nil_r, map_map; simpl.
        unfold ilist2_hd; simpl; rewrite map_id.
        repeat setoid_rewrite refine_If_Then_Else_Bind.
        repeat setoid_rewrite refineEquiv_bind_unit; simpl.
        setoid_rewrite refineEquiv_bind_bind.
        setoid_rewrite refineEquiv_bind_unit.
        rewrite (CallBagFind_fst H0); simpl.
        finish honing.
      }
      hone method "Enumerate".
      { subst; simplify with monad laws.
        unfold H1; apply refine_under_bind.
        intros; set_evars; simpl in *.
        rewrite (CallBagFind_fst H0).
        setoid_rewrite refine_pick_eq'; simplify with monad laws.
        simpl; rewrite app_nil_r, map_map, <- map_rev.
        unfold ilist2_hd; simpl.
        finish honing.
      }
      hone method "GetCPUTime".
      { subst; simplify with monad laws.
        unfold H1; apply refine_under_bind.
        intros; set_evars; rewrite (CallBagFind_fst H0); simpl in *.
        setoid_rewrite refine_pick_eq'; simplify with monad laws.
        simpl; rewrite app_nil_r, map_map, <- map_rev.
        unfold ilist2_hd; simpl.
        finish honing.
      }
      simpl.
      eapply reflexivityT.
  - unfold CallBagFind, CallBagInsert.
    pose_headings_all;
      match goal with
      | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
        FullySharpenQueryStructure Schema Indexes
      end.
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
  QueryADTRep SchedulerSchema {
    Def Constructor0 "Init" : rep := empty,

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
