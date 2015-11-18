Require Import Fiat.Examples.QueryStructure.ProcessScheduler.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Examples
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.

Parameter TSearchTerm : Type.
Parameter TAcc : Type.
Definition av := (list W + TSearchTerm + TAcc)%type.

Definition MyEnvListsB : Env (list W + TSearchTerm + TAcc) :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("listW", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("listW", "push!") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("listW", "pop!") ->> (Axiomatic (List_pop W))
    ### ("listW", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("listW", "empty?") ->> (Axiomatic (List_empty W))
    ### ("search", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor TSearchTerm))
    ### ("acc", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor TAcc)).

(* Ltac compile_destructor := *)
(*   match_ProgOk *)
(*     ltac:(fun prog pre post ext env => *)
(*             let vtmp := gensym "tmp" in *)
(*             match constr:(pre, post) with *)
(*             | (Cons _ _ (fun _ => ?tenv), ?tenv) => *)
(*               apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) *)
(*             | (Cons _ ?v (fun _ => ?tenv), ?tenv') => *)
(*               match tenv' with *)
(*               | context[v] => fail 1 *)
(*               | _ => eapply CompileSeq; [ apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) | ] *)
(*               end *)
(*             end. *)

Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation Fiat.QueryStructure.Automation.Common Fiat.QueryStructure.Specification.Representation.Schema.
Require Import Coq.Vectors.Fin.

(* Notation "'BIND' !! A !! B !! C" := (@Bind A B C) (at level 1). *)
(* Notation "x { A } <- y ; z" := (Bind y (fun x: A => z)) (at level 1). *)

Definition FinToWord {N: nat} (n: Fin.t N) :=
  Word.natToWord 32 (proj1_sig (Fin.to_nat n)).

Definition FitsInW {N: nat} (n: Fin.t N) :=
  Word.wordToNat (FinToWord n) = proj1_sig (Fin.to_nat n).

Set Printing All.
Set Printing Depth 1000.
Print PartialSchedulerImpl.
Unset Printing All.

Definition Type1 := IndexedQueryStructure
                     (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                     (@icons3 _
                              (fun sch : RawHeading => SearchUpdateTerms sch) heading 0
                              (VectorDef.nil RawHeading) SearchUpdateTerm
                              (@inil3 _ (fun sch : RawHeading => SearchUpdateTerms sch))).

Definition Type2 := (Type1 * list (Domain heading (@FS 2 (@FS 1 (@F1 0)))))%type.

Definition Method2 :=
          (fun
           (r_n : IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))
           (d
            d0 : Word.word
                   (S
                      (S
                         (S
                            (S
                               (S
                                  (S
                                     (S
                                        (S
                                           (S
                                              (S
                                                 (S
                                                  (S
                                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) =>
         @Bind
           (prod
              (@IndexedEnsembles.IndexedEnsemble
                 (@RawTuple
                    (@Build_RawHeading (S (S (S O)))
                       (Vector.cons Type W (S (S O))
                          (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
              (list
                 (@RawTuple
                    (@Build_RawHeading (S (S (S O)))
                       (Vector.cons Type W (S (S O))
                          (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))))
           (prod
              (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                    (VectorDef.nil RawHeading) SearchUpdateTerm 
                    (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
           (@CallBagMethod (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
              (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                 (VectorDef.nil RawHeading) SearchUpdateTerm 
                 (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) 
              (@F1 O)
              (@BagFind
                 (@Build_RawHeading (S (S (S O)))
                    (Vector.cons Type W (S (S O))
                       (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                 (@ilist3_hd RawSchema (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns)) 
                    (S O)
                    (Vector.cons RawSchema
                       (Build_RawSchema
                          (@Build_RawHeading (S (S (S O)))
                             (Vector.cons Type W (S (S O))
                                (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                          (@None
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                              Prop))
                          (@Some
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                              @RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                              Prop)
                             (@UniqueAttribute
                                (@BuildHeading (S (S (S O)))
                                   (Vector.cons Attribute
                                      (Build_Attribute
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String 
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString))) W)
                                      (S (S O))
                                      (Vector.cons Attribute
                                         (Build_Attribute
                                            (String 
                                               (Ascii.Ascii true true false false true true true false)
                                               (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                            ProcessScheduler.State) 
                                         (S O)
                                         (Vector.cons Attribute
                                            (Build_Attribute
                                               (String 
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) W)
                                            O (Vector.nil Attribute)))))
                                (@BoundedLookup.Build_BoundedIndex string 
                                   (S (S (S O)))
                                   (Vector.cons string
                                      (String (Ascii.Ascii false false false false true true true false)
                                         (String (Ascii.Ascii true false false true false true true false)
                                            (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                      (S (S O))
                                      (Vector.cons string
                                         (String (Ascii.Ascii true true false false true true true false)
                                            (String 
                                               (Ascii.Ascii false false true false true true true false)
                                               (String 
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                         (S O)
                                         (Vector.cons string
                                            (String 
                                               (Ascii.Ascii true true false false false true true false)
                                               (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                            (Vector.nil string))))
                                   (String (Ascii.Ascii false false false false true true true false)
                                      (String (Ascii.Ascii true false false true false true true false)
                                         (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                   (@BoundedLookup.Build_IndexBound string 
                                      (S (S (S O)))
                                      (String (Ascii.Ascii false false false false true true true false)
                                         (String (Ascii.Ascii true false false true false true true false)
                                            (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                      (Vector.cons string
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String 
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                         (S (S O))
                                         (Vector.cons string
                                            (String 
                                               (Ascii.Ascii true true false false true true true false)
                                               (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                            (S O)
                                            (Vector.cons string
                                               (String 
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                               (Vector.nil string)))) 
                                      (@F1 (S (S O)))
                                      (@eq_refl string
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String 
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString)))))))))
                       O (Vector.nil RawSchema))
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))) r_n
              (@pair (option (Domain heading (@F1 (S (S O)))))
                 (prod (option (Domain heading (@FS (S (S O)) (@F1 (S O))))) (@RawTuple heading -> bool))
                 (@Some (Domain heading (@F1 (S (S O)))) d)
                 (@pair (option (Domain heading (@FS (S (S O)) (@F1 (S O))))) 
                    (@RawTuple heading -> bool) (@None (Domain heading (@FS (S (S O)) (@F1 (S O)))))
                    (fun _ : @RawTuple heading => true))))
           (fun
              a : prod
                    (@IndexedEnsembles.IndexedEnsemble
                       (@RawTuple
                          (@Build_RawHeading (S (S (S O)))
                             (Vector.cons Type W (S (S O))
                                (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                    (list
                       (@RawTuple
                          (@Build_RawHeading (S (S (S O)))
                             (Vector.cons Type W (S (S O))
                                (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) =>
            @Common.If_Then_Else
              (Comp
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool))
              (EqNat.beq_nat
                 (@Datatypes.length (@RawTuple heading)
                    (@rev (@RawTuple heading)
                       (@snd
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a)))
                 O)
              (@Bind
                 (@IndexedEnsembles.IndexedEnsemble
                    (@RawTuple
                       (@Build_RawHeading (S (S (S O)))
                          (Vector.cons Type W (S (S O))
                             (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
                 (@CallBagMethod (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) 
                    (@F1 O)
                    (@BagInsert
                       (@Build_RawHeading (S (S (S O)))
                          (Vector.cons Type W (S (S O))
                             (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                       (@ilist3_hd RawSchema (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns)) 
                          (S O)
                          (Vector.cons RawSchema
                             (Build_RawSchema
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                                (@None
                                   (@RawTuple
                                      (@Build_RawHeading 
                                         (S (S (S O)))
                                         (Vector.cons 
                                            Type W 
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                                    Prop))
                                (@Some
                                   (@RawTuple
                                      (@Build_RawHeading 
                                         (S (S (S O)))
                                         (Vector.cons 
                                            Type W 
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                                    @RawTuple
                                      (@Build_RawHeading 
                                         (S (S (S O)))
                                         (Vector.cons 
                                            Type W 
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                                    Prop)
                                   (@UniqueAttribute
                                      (@BuildHeading 
                                         (S (S (S O)))
                                         (Vector.cons Attribute
                                            (Build_Attribute
                                               (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                               W) (S (S O))
                                            (Vector.cons Attribute
                                               (Build_Attribute
                                                  (String 
                                                  (Ascii.Ascii true true false false true true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                                  ProcessScheduler.State) 
                                               (S O)
                                               (Vector.cons Attribute
                                                  (Build_Attribute
                                                  (String 
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) W)
                                                  O 
                                                  (Vector.nil Attribute)))))
                                      (@BoundedLookup.Build_BoundedIndex string 
                                         (S (S (S O)))
                                         (Vector.cons string
                                            (String 
                                               (Ascii.Ascii false false false false true true true false)
                                               (String 
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                            (S (S O))
                                            (Vector.cons string
                                               (String 
                                                  (Ascii.Ascii true true false false true true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                               (S O)
                                               (Vector.cons string
                                                  (String 
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                                  (Vector.nil string))))
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String 
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                         (@BoundedLookup.Build_IndexBound string 
                                            (S (S (S O)))
                                            (String 
                                               (Ascii.Ascii false false false false true true true false)
                                               (String 
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                            (Vector.cons string
                                               (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                               (S (S O))
                                               (Vector.cons string
                                                  (String 
                                                  (Ascii.Ascii true true false false true true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                                  (S O)
                                                  (Vector.cons string
                                                  (String 
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                                  (Vector.nil string)))) 
                                            (@F1 (S (S O)))
                                            (@eq_refl string
                                               (String 
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String 
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))))))))
                             O (Vector.nil RawSchema))
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))))
                    (Refinements.UpdateIndexedRelation 
                       (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n 
                       (@F1 O)
                       (@fst
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a))
                    (@ilist2.icons2 Type (@id Type) W 
                       (S (S O)) (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))) d
                       (@ilist2.icons2 Type (@id Type) ProcessScheduler.State 
                          (S O) (Vector.cons Type W O (Vector.nil Type)) SLEEPING
                          (@ilist2.icons2 Type (@id Type) W O (Vector.nil Type) d0 (@ilist2.inil2 Type (@id Type))))))
                 (fun
                    u : @IndexedEnsembles.IndexedEnsemble
                          (@RawTuple
                             (@Build_RawHeading (S (S (S O)))
                                (Vector.cons Type W 
                                   (S (S O))
                                   (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))) =>
                  @Return
                    (prod
                       (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
                    (@pair
                       (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool
                       (Refinements.UpdateIndexedRelation 
                          (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))
                          (Refinements.UpdateIndexedRelation 
                             (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                             (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                                (VectorDef.nil RawHeading) SearchUpdateTerm
                                (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n 
                             (@F1 O)
                             (@fst
                                (@IndexedEnsembles.IndexedEnsemble
                                   (@RawTuple
                                      (@Build_RawHeading 
                                         (S (S (S O)))
                                         (Vector.cons 
                                            Type W 
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                                (list
                                   (@RawTuple
                                      (@Build_RawHeading 
                                         (S (S (S O)))
                                         (Vector.cons 
                                            Type W 
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                                a)) (@F1 O) u) true)))
              (@Return
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
                 (@pair
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool
                    (Refinements.UpdateIndexedRelation 
                       (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n 
                       (@F1 O)
                       (@fst
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a))
                    false)))).

Definition MethodOfInterest :=
  (fun
              (r_n : IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) 
              (d : ProcessScheduler.State) =>
            @Bind (prod (@IndexedEnsembles.IndexedEnsemble (@RawTuple heading)) (list (@RawTuple heading)))
              (prod
                 (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))
                 (list
                    (Word.word
                       (S
                          (S
                             (S
                                (S
                                   (S
                                      (S
                                         (S
                                            (S
                                               (S
                                                  (S
                                                  (S
                                                  (S
                                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))
              (@CallBagMethod (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                    (VectorDef.nil RawHeading) SearchUpdateTerm 
                    (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) 
                 (@F1 O)
                 (@BagFind heading
                    (@ilist3_hd RawSchema (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns)) 
                       (S O)
                       (Vector.cons RawSchema
                          (Build_RawSchema heading 
                             (@None (@RawTuple heading -> Prop))
                             (@Some (@RawTuple heading -> @RawTuple heading -> Prop) (@UniqueAttribute heading0 BStringId0))) O
                          (Vector.nil RawSchema))
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))) r_n
                 (@pair (option (Domain heading (@F1 (S (S O))))) 
                    (prod (option ProcessScheduler.State) (@RawTuple heading -> bool)) 
                    (@None (Domain heading (@F1 (S (S O)))))
                    (@pair (option ProcessScheduler.State) 
                       (@RawTuple heading -> bool) 
                       (@Some ProcessScheduler.State d) 
                       (fun _ : @RawTuple heading => true))))
              (fun a : prod (@IndexedEnsembles.IndexedEnsemble (@RawTuple heading)) (list (@RawTuple heading)) =>
               @Return
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) 
                    (list W))
                 (@pair
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) 
                    (list W)
                    (Refinements.UpdateIndexedRelation 
                       (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n 
                       (@F1 O)
                       (@fst
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading 
                                   (S (S (S O)))
                                   (Vector.cons Type W 
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a))
                    (@map (@RawTuple heading) (Domain heading (@F1 (S (S O))))
                       (fun x : @RawTuple heading => @GetAttributeRaw heading x (@F1 (S (S O))))
                       (@rev (@RawTuple heading)
                          (@snd
                             (@IndexedEnsembles.IndexedEnsemble
                                (@RawTuple
                                   (@Build_RawHeading 
                                      (S (S (S O)))
                                      (Vector.cons 
                                         Type W (S (S O))
                                         (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                             (list
                                (@RawTuple
                                   (@Build_RawHeading 
                                      (S (S (S O)))
                                      (Vector.cons 
                                         Type W (S (S O))
                                         (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                             a)))))).

Print Type1.

Definition av' := (list W + Type1 +
                  (@IndexedEnsembles.IndexedEnsemble
                     (@RawTuple heading)) +
                  (list (@RawTuple heading)) +
                  (@RawTuple heading))%type.

Definition MyEnvListsC : Env av' :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("listW", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("listW", "push!") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("listW", "pop!") ->> (Axiomatic (List_pop W))
    ### ("listW", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("listW", "empty?") ->> (Axiomatic (List_empty W))
    ### ("listT", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list (@RawTuple heading)) nil))
    ### ("listT", "push!") ->> (Axiomatic (FacadeImplementationOfMutation_ADT _ (list (@RawTuple heading)) cons))
    ### ("listT", "pop!") ->> (Axiomatic (List_pop (@RawTuple heading)))
    ### ("listT", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (list (@RawTuple heading))))
    ### ("listT", "empty?") ->> (Axiomatic (List_empty (@RawTuple heading)))
    ### ("IndexedEnsemble", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor IndexedEnsembles.IndexedEnsemble))
    ### ("RawTuple", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (@RawTuple heading))).

Check MethodOfInterest.

Ltac _compile_CallGetAttribute :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (Cons (NTSome ?vsrc) (ret ?src) ?tenv,
               Cons (NTSome ?vtarget) (ret (GetAttributeRaw ?src ?index)) ?tenv') =>
              let vindex := gensym "index" in
              eapply CompileSeq with ([[`vindex <-- FinToWord index as _]]
                                        :: [[`vsrc <-- src as src]]
                                        :: (tenv src));
                [ | match_ProgOk
                      ltac:(fun prog' _ _ _ _ =>
                              unify prog' (Call vtarget ("ext", "GetAttribute")
                                                (vsrc :: vindex :: nil))) ]
            end).

Ltac _compile_CallBagFind :=
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             match constr:(pre, post) with
             | (Cons (NTSome ?vdb) (ret ?db) (fun _ => Cons (NTSome ?vd) (ret ?d) ?tenv),
                Cons NTNone (CallBagMethod ?id BagFind ?db (Some ?d, _)) ?tenv') =>
               let vsnd := gensym "snd" in
               let vtmp := gensym "tmp" in
               match post with
               | Cons NTNone ?bf _ =>
                 eapply CompileSeq with ([[bf as retv]]
                                           :: [[`vdb <-- Refinements.UpdateIndexedRelation
                                                (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                (icons3 SearchUpdateTerm inil3) db F1 (fst retv)
                                                as _]]
                                           :: [[`vsnd <-- snd retv as s]]
                                           :: [[`vd <-- d as _]]
                                           :: (tenv d));
                   [ match_ProgOk
                       ltac:(fun prog' _ _ _ _ =>
                               unify prog' (Call (DummyArgument vtmp) ("ext", "BagFind")
                                                 (vsnd :: vdb :: vd :: nil))) (* FIXME *) | ]
               end
             end).

Ltac _compile_CallBagInsert :=
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             match constr:(pre, post) with
             | (Cons ?vdb (ret ?db) (fun _ => ?tenv),
                Cons NTNone ?bm (fun a => Cons ?vdb' (@?rel a) (fun _ => ?tenv'))) =>
               unify vdb vdb';
                 match constr:(vdb, bm, rel) with
                 | (NTSome ?vdb', CallBagMethod ?id BagInsert ?db _, (fun a => ret (Refinements.UpdateIndexedRelation _ _ ?db' ?id a))) =>
                   unify db db';
                     let vtmp := gensym "tmp" in
                     apply CompileSeq with (Cons NTNone bm (fun a => Cons vdb (rel a) (fun _ => tenv))); (* FIXME hardcoded var names *)
                       [ match_ProgOk
                           ltac:(fun prog' _ _ _ _ =>
                                   unify prog' (Call (DummyArgument "tmp") ("ext", "BagInsert") (vdb' :: "d" :: "d0" :: nil))) | ]
                 end
             end).

Arguments wrap : simpl never.

Example random_test_with_adt :
  Facade program implementing ( x <- Random;
                                ret (if IL.weqb x 0 then
                                       (Word.natToWord 32 1) :: nil
                                     else
                                       x :: nil)) with MyEnvW.
Proof.
  Time compile_step.
  repeat (_compile_step || _compile_random).
Defined.

Eval compute in (extract_facade random_test_with_adt).

(* Require Import Utf8 FIXME remove *)

Definition Remembered {A} (a : A) := a.

Ltac set_remember v :=
  let vv := fresh in
  change v with (Remembered v);
    set (vv := Remembered v) in *.

Ltac set_values tenv :=
  lazymatch tenv with
  | context[Cons _ ?v ?tail] =>
    try match v with
        | ret ?v  => set_remember v
        | _ => set_remember v
        end;
      try set_values tail
  | _ => idtac
  end.

Ltac unset_values :=
  repeat match goal with
         | [ H := Remembered _ |- _ ] => unfold H in *; clear H
         | _ => unfold Remembered in *
         end.

Example other_test_with_adt''':
  sigT (fun prog => forall (searchTerm: TSearchTerm) (init: TAcc),
            {{ [[`"search" <-- searchTerm as _]] :: [[`"init" <-- init as _]] :: (@Nil av) }}
              prog
            {{ [[`"ret" <~~  ( seq <- {s: list W | True };
                             fold_left (fun acc elem =>
                                          acc <- acc;
                                          { x: W | Word.wlt (Word.wplus acc elem) x })
                                       seq (ret (Word.natToWord 32 0: W))) as _]] :: (@Nil av) }} ∪ {{ StringMap.empty (Value av) }} // MyEnvListsB).
Proof.
  econstructor; intros.

  (* repeat setoid_rewrite SameValues_Fiat_Bind_TelEq. *)

  _compile.

  eapply ProgOk_Transitivity_Name' with "seq".
  instantiate (1 := Skip).       (* FIXME alloc *)
  admit.
  compile_miniChomp.

  _compile.
  compile_loop.

  _compile.
  _compile.
  _compile.

  compile_do_extend_scalar_lifetime.
  _compile.

  compile_miniChomp.
  _compile.

  instantiate (1 := Skip); admit.
Defined.

Eval compute in (extract_facade other_test_with_adt''').

Example other_test_with_adtB'' `{FacadeWrapper av (list W)}:
    sigT (fun prog => forall seq: list W, {{ [[`"arg1" <-- seq as _ ]] :: Nil }}
                                    prog
                                  {{ [[`"ret" <-- (List.fold_left (@Word.wminus 32) seq 0) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvLists).
Proof.
  econstructor; intros.
  Print Ltac compile_loop.
  repeat (compile_step || compile_loop).
  let fop := translate_op Word.wminus in
  apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions.
Defined.

Example compile2 :
  sigT (fun prog => forall r_n d d0,
            {{ [[`"r_n" <-- r_n as _ ]] :: [[`"d" <-- d as _]] :: [[`"d0" <-- d0 as _]] :: Nil }}
              prog
            {{ [[Method2 r_n d d0 as retv]] :: [[`"r_n" <-- fst retv as _]] :: [[`"ret" <-- bool2w (snd retv) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvListsC).
Proof.
  eexists; intros.
  unfold Method2, Common.If_Then_Else.

  Time repeat _compile_step.
  admit.
  instantiate (1 := Call "test" ("list", "Empty") ("snd" :: nil)) (* FIXME *); admit.
  admit.
Time Defined.

Eval compute in (extract_facade compile2).

Print Method2.

Example compile :
  sigT (fun prog => forall (r_n : Type1) (d : W),
            {{ [[`"r_n" <-- r_n as _ ]] :: [[`"d" <-- d as _]] :: Nil }}
              prog
            {{ [[MethodOfInterest r_n d as retv]] :: [[`"r_n" <-- fst retv as _]] :: [[`"ret" <-- snd retv as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvListsC).
Proof.
  eexists; intros.
  unfold MethodOfInterest.

  Ltac _compile_CallBagFind ::=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:(pre, post) with
              | (Cons (NTSome ?vdb) (ret ?db) (fun _ => Cons (NTSome ?vd) (ret ?d) ?tenv),
                 Cons NTNone (CallBagMethod ?id BagFind ?db _) ?tenv') =>
                let vsnd := gensym "snd" in
                let vtmp := gensym "tmp" in
                match post with
                | Cons NTNone ?bf _ =>
                  eapply CompileSeq with ([[bf as retv]]
                                            :: [[`vdb <-- Refinements.UpdateIndexedRelation
                                                 (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                 (icons3 SearchUpdateTerm inil3) db F1 (fst retv)
                                                 as _]]
                                            :: [[`vsnd <-- snd retv as s]]
                                            :: [[`vd <-- d as _]]
                                            :: (tenv d));
                    [ match_ProgOk
                        ltac:(fun prog' _ _ _ _ =>
                                unify prog' (Call (DummyArgument vtmp) ("ext", "BagFind")
                                                  (vsnd :: vdb :: vd :: nil))) (* FIXME *) | ]
                end
              end).

  Lemma map_rev_def :
    forall {A B} f seq,
      @map A B f (rev seq) = revmap f seq.
  Proof.
    intros; reflexivity.
  Qed.

  Time repeat (_compile_step || setoid_rewrite map_rev_def).
  admit.
  admit.
Defined.

Opaque DummyArgument.
Definition compiled := Eval compute in (extract_facade compile).

Example other_test_with_adt''''' :
    sigT (fun prog => forall seq seq', {{ [[`"arg1" <-- seq as _ ]] :: [[`"arg2" <-- seq' as _]] :: Nil }}
                                 prog
                               {{ [[`"arg1" <-- (rev_append seq seq') as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvW).
Proof.
  econstructor; intros.
Abort.



  Lemma ProgOk_Transitivity_Cons_B :
    forall {av} env ext t1 t1' t2 prog1 prog2 k (v: Comp (Value av)),
      {{ t1 }}                            prog1     {{ [[Some k <~~ v as kk]] :: t1' kk }}     ∪ {{ ext }} // env ->
      {{ [[Some k <~~ v as kk]] :: t1' kk }} prog2     {{ [[Some k <~~ v as kk]] :: t2 kk }} ∪ {{ ext }} // env ->
      {{ t1 }}                      Seq prog1 prog2 {{ [[Some k <~~ v as kk]] :: t2 kk }} ∪ {{ ext }} // env.
  Proof.
    eauto using CompileSeq.
  Qed.

  (* This is a well-behaved version of ProgOk_Transitivity_Cons, but it is not
     very useful, as the side goal that it creates are in a form in which one
     would want to apply transitivity again. *)
  Lemma ProgOk_Transitivity_Cons_Drop :
    forall {av} env ext t1 t2 prog1 prog2 k (v: Comp (Value av)),
      {{ t1 }}                     prog1      {{ [[Some k <~~ v as _]]::(DropName k t1) }}     ∪ {{ ext }} // env ->
      {{ [[Some k <~~ v as _]]::(DropName k t1) }}      prog2      {{ [[Some k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
      {{ t1 }}                Seq prog1 prog2 {{ [[Some k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env.
  Proof.
    SameValues_Facade_t.
  Qed.