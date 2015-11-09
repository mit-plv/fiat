Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Examples
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.Extraction.

Require Import Fiat.Examples.QueryStructure.ProcessScheduler.

Definition MyEnvLists `{FacadeWrapper av (list W)} : Env av :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("list", "nil") (Axiomatic (FacadeImplementationOfConstructor nil)))
       ((GLabelMap.add ("list", "push") (Axiomatic (FacadeImplementationOfMutation cons)))
          ((GLabelMap.add ("list", "pop") (Axiomatic List_pop))
             ((GLabelMap.add ("list", "delete") (Axiomatic (FacadeImplementationOfDestructor)))
                ((GLabelMap.add ("list", "empty?") (Axiomatic List_empty))
                   (GLabelMap.empty (FuncSpec _))))))).

Example other_test_with_adt'' `{FacadeWrapper av (list W)}:
    sigT (fun prog => forall seq: list W, {{ [[`"arg1" <-- seq as _ ]] :: Nil }}
                                    prog
                                  {{ [[`"ret" <-- (List.fold_left (@Word.wminus 32) seq 0) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvLists).
Proof.
  econstructor; intros.
  repeat (compile_step || compile_loop).
  let fop := translate_op Word.wminus in
  apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions.
Defined.

Print Assumptions other_test_with_adt''. (* FIXME *)

Opaque Word.wordToNat.
Opaque Word.natToWord.

Eval compute in (extract_facade other_test_with_adt'').

Eval cbv beta iota zeta delta [extract_facade Fold proj1_sig sig_of_sigT other_test_with_adt'' WrapOpInExpr] in (extract_facade other_test_with_adt'').

Definition fold_comp {TAcc TElem} (f: Comp TAcc -> TElem -> Comp TAcc) seq init :=
  List.fold_left (fun (acc: Comp TAcc) (elem: TElem) =>
                    ( f acc elem )%comp)
                 seq init.

Require Import
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

(* Opaque WrapInstance.            (* FIXME simpl never? *) *)

Lemma CompileLoop :
  forall `{FacadeWrapper av (list W)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp W -> W -> Comp W),
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (A := list W))) env ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    vhead ∉ ext ->
    NotInTelescope vhead tenv ->
    vtest <> vret ->
    vtest <> vlst ->
    vtest <> vhead ->
    vret <> vlst ->
    vret <> vhead ->
    vlst <> vhead ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp W) (s: Comp (list W)),
        {{ [[`vhead <-- head as _]] :: [[`vlst <~~ s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vlst <~~ s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <~~ (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil))))
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  Require Import FacadeLoops.
  loop_t.

  rewrite TelEq_swap by loop_t;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply CompileCallFacadeImplementationOfDestructor; loop_t.

  rewrite (TelEq_swap _ NTNone) by loop_t.

  apply miniChomp'; loop_t.

  clear dependent facadeInit;
  generalize dependent init;
  generalize dependent lst;
  induction vv; loop_t.

  rewrite TelEq_swap by loop_t.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized CompileCallPop; loop_t.

  apply CompileCallEmpty_spec; loop_t.

  loop_t.
Qed.

Lemma CompileLoop' :
  forall {A} `{FacadeWrapper av (list W)} `{FacadeWrapper av A}
    (lst: Comp (list W)) init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp A -> W -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (A := list W))) env ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    vhead ∉ ext ->
    NotInTelescope vhead tenv ->
    vtest <> vret ->
    vtest <> vlst ->
    vtest <> vhead ->
    vret <> vlst ->
    vret <> vhead ->
    vlst <> vhead ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A) (s: Comp (list W)),
        {{ [[`vhead <-- head as _]] :: [[`vlst <~~ s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vlst <~~ s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <~~ (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil))))
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  loop_t.

  rewrite TelEq_swap by loop_t;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply (CompileCallFacadeImplementationOfDestructor (A := list W)); loop_t.

  loop_unify_with_nil_t.
  
  rewrite (TelEq_swap _ NTNone) by loop_t.

  apply miniChomp'; loop_t.

  clear dependent facadeInit;
  generalize dependent init;
  generalize dependent lst;
  induction vv; loop_t.

  rewrite TelEq_swap by loop_t.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized CompileCallPop; loop_t.

  apply CompileCallEmpty_spec; loop_t.

  loop_t.
Qed.

Lemma CompileLoop_strong :
  forall `{FacadeWrapper av (list W)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
    env (ext: StringMap.t (Value av)) tenv tenv' (f: Comp W -> W -> Comp W),
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (A := list W))) env ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    vhead ∉ ext ->
    NotInTelescope vhead tenv ->
    vtest <> vret ->
    vtest <> vlst ->
    vtest <> vhead ->
    vret <> vlst ->
    vret <> vhead ->
    vlst <> vhead ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv }}
      facadeConclude
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp W) (s: Comp (list W)),
        {{ [[`vhead <-- head as _]] :: [[`vlst <~~ s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vlst <~~ s as _]] :: [[`vtest <-- (bool2w false) as _]] :: [[`vret <~~ (f acc head) as _]] :: tenv }} ∪ {{ ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call vtest fdealloc (vlst :: nil)))) facadeConclude)
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  eapply CompileSeq;
    [ apply CompileLoop | eassumption ];
    assumption.
Qed.

Parameter TSearchTerm : Type.
Parameter TAcc : Type.
Definition av := (list W + TSearchTerm + TAcc)%type.

Definition MyEnvListsB : Env (list W + TSearchTerm + TAcc) :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("list", "nil") (Axiomatic (FacadeImplementationOfConstructor (@nil W))))
       ((GLabelMap.add ("list", "push!") (Axiomatic (FacadeImplementationOfMutation (@cons W))))
          ((GLabelMap.add ("list", "pop!") (Axiomatic List_pop))
             ((GLabelMap.add ("list", "delete!") (Axiomatic (FacadeImplementationOfDestructor (A := list W))))
                ((GLabelMap.add ("list", "empty?") (Axiomatic List_empty))
                   ((GLabelMap.add ("search", "delete!") (Axiomatic (FacadeImplementationOfDestructor (A := TSearchTerm))))
                      ((GLabelMap.add ("acc", "delete!") (Axiomatic (FacadeImplementationOfDestructor (A := TAcc))))
                         (GLabelMap.empty (FuncSpec _))))))))).

Example other_test_with_adt''':
  sigT (fun prog => forall (searchTerm: TSearchTerm) (init: TAcc),
            {{ [[`"search" <-- searchTerm as _]] :: [[`"init" <-- init as _]] :: (@Nil av) }}
              prog
            {{ [[`"ret" <~~  ( seq <- {s: list W | True };
                             fold_comp (fun acc elem =>
                                          acc <- acc;
                                          { x: W | Word.wlt (Word.wplus acc elem) x })
                                       seq (ret (Word.natToWord 32 0: W))) as _]] :: (@Nil av) }} ∪ {{ StringMap.empty (Value av) }} // MyEnvListsB).
Proof.
  Unset Ltac Debug.
  econstructor; intros.

  repeat setoid_rewrite SameValues_Fiat_Bind_TelEq.

  eapply ProgOk_Transitivity_Name' with "seq".

  instantiate (1 := Skip).       (* FIXME alloc *)
  admit.

  let av := av_from_ext (StringMap.empty (Value av)) in
  let fpop := find_function_pattern_in_env
               (fun w => (Axiomatic (List_pop (av := av) (H := w)))) MyEnvListsB in
  let fempty := find_function_pattern_in_env
                 (fun w => (Axiomatic (List_empty (av := av) (H := w)))) MyEnvListsB in
  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        (A := list W) (av := av) (H := w)))) MyEnvListsB in
  let vtest := gensym "test" in
  let vhead := gensym "head" in
  apply (CompileLoop_strong (vtest := vtest) (vhead := vhead) (fpop := fpop) (fempty := fempty) (fdealloc := fdealloc));
    try compile_do_side_conditions.

  repeat compile_step.
  repeat compile_step.

  eapply CompileSeq.
  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        (A := TSearchTerm) (av := av) (H := w)))) MyEnvListsB in
  let vtmp := gensym "tmp" in
  apply (CompileCallFacadeImplementationOfDestructor (fpointer := fdealloc) (vtmp := vtmp));
    try compile_do_side_conditions.

  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        (A := TAcc) (av := av) (H := w)))) MyEnvListsB in
  let vtmp := gensym "tmp" in
  apply (CompileCallFacadeImplementationOfDestructor (fpointer := fdealloc) (vtmp := vtmp));
    try compile_do_side_conditions.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  apply miniChomp.
  intros.
  rewrite Propagate_anonymous_ret.

  instantiate (1 := Skip).
  admit.
Defined.

Eval compute in (extract_facade other_test_with_adt''').

Lemma SameValues_Fiat_Bind_TelEq_Pair :
  forall {av A1 A2 B} key compA compB tail ext,
    TelEq ext
          (Cons (av := av) key (@Bind (A1 * A2) B compA compB) tail)
          (Cons NTNone compA (fun a => Cons NTNone (ret (fst a)) (fun a1 => Cons NTNone (ret (snd a)) (fun a2 => Cons key (compB (a1, a2)) tail)))).
Proof.
  unfold TelEq;
  repeat match goal with
         | _ => progress subst
         | _ => progress SameValues_Fiat_t_step
         | _ => rewrite <- surjective_pairing in *
         end.
Qed.

(* Example other_test_with_adt'''' A: *)
(*   sigT (fun prog => forall (searchTerm: TSearchTerm) (init: TAcc), *)
(*             {{ [[`"search" <-- searchTerm as _]] :: [[`"init" <-- init as _]] :: (@Nil av) }} *)
(*               prog *)
(*             {{ [[`"ret" <~~  ( seq <- {s: (A * list W) | True }; *)
(*                              ret (snd seq)) as _]] :: (@Nil av) }} ∪ {{ StringMap.empty (Value av) }} // MyEnvListsB). *)
(* Proof. *)
(*   Unset Ltac Debug. *)
(*   econstructor; intros. *)

(*   rewrite SameValues_Fiat_Bind_TelEq_Pair. *)
(*   simpl. *)


Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation Fiat.QueryStructure.Automation.Common Fiat.QueryStructure.Specification.Representation.Schema.
Require Import Coq.Vectors.Fin.
Print PartialSchedulerImpl.

Definition Type1 := IndexedQueryStructure 
                     (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                     (@icons3 _ 
                              (fun sch : RawHeading => SearchUpdateTerms sch) heading 0 
                              (VectorDef.nil RawHeading) SearchUpdateTerm 
                              (@inil3 _ (fun sch : RawHeading => SearchUpdateTerms sch))).

Definition Type2 := (Type1 * list (Domain heading (@FS 2 (@FS 1 (@F1 0)))))%type.

Definition MethodOfInterest := fun (r_n : Type1) (d : W) =>
                                (a <- @CallBagMethod 
                                   (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                        (@icons3 _ 
                                           (fun sch : RawHeading => SearchUpdateTerms sch) heading 0 
                                           (VectorDef.nil RawHeading) SearchUpdateTerm 
                                           (@inil3 _ (fun sch : RawHeading => SearchUpdateTerms sch))) 
                                        (@F1 0)
                                        (@BagFind heading
                                           (@ilist3_hd RawSchema 
                                              (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns)) 1
                                              (Vector.cons RawSchema
                                                 {|
                                                 rawSchemaHeading := heading;
                                                 attrConstraints := @None (@RawTuple heading -> Prop);
                                                 tupleConstraints := @Some 
                                                  (@RawTuple heading -> @RawTuple heading -> Prop) 
                                                  (@FunctionalDependency_P heading [@FS 2 (@FS 1 (@F1 0)); @FS 2 (@F1 1)] [@F1 2]) |} 0 
                                                 (Vector.nil RawSchema))
                                              (@icons3 _ 
                                                 (fun sch : RawHeading => SearchUpdateTerms sch) heading 0 
                                                 (VectorDef.nil RawHeading) SearchUpdateTerm 
                                                 (@inil3 _ (fun sch : RawHeading => SearchUpdateTerms sch))))) r_n
                                        (@Some W d, (@None (Domain heading (@FS 2 (@F1 1))), fun _ : @RawTuple heading => true));
                                 ret
                                   (r_n,
                                   @map (@RawTuple heading) 
                                     (Domain heading (@FS 2 (@FS 1 (@F1 0))))
                                     (fun x : @RawTuple heading =>
                                      @GetAttributeRaw heading
                                        (@ilist2.ilist2_hd RawHeading 
                                           (@RawTuple) 1 
                                           (VectorDef.cons RawHeading heading 0 (VectorDef.nil RawHeading))
                                           (@ilist2.icons2 RawHeading (@RawTuple) heading 0 (VectorDef.nil RawHeading) x (@ilist2.inil2 RawHeading (@RawTuple))))
                                        (@FS 2 (@FS 1 (@F1 0)))) 
                                     (@snd (@IndexedEnsembles.IndexedEnsemble (@RawTuple heading)) (list (@RawTuple heading)) a)))%comp : Comp Type2.

Definition av' := (list W + Type1 + Type2)%type.

Definition MyEnvListsC : Env av' :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("list", "nil") (Axiomatic (FacadeImplementationOfConstructor (@nil W))))
       ((GLabelMap.add ("list", "push!") (Axiomatic (FacadeImplementationOfMutation (@cons W))))
          ((GLabelMap.add ("list", "pop!") (Axiomatic List_pop))
             ((GLabelMap.add ("list", "delete!") (Axiomatic (FacadeImplementationOfDestructor (A := list W))))
                ((GLabelMap.add ("list", "empty?") (Axiomatic List_empty))
                   (GLabelMap.empty (FuncSpec _))))))).

Check MethodOfInterest.

Example compile :
  sigT (fun prog => forall (r_n : Type1) (d : W),
            {{ [[`"r_n" <-- r_n as _ ]] :: [[`"d" <-- d as _]] :: Nil }}
              prog
            {{ [[MethodOfInterest r_n d as retv]] :: [[`"r_n" <-- fst retv as _]] :: [[`"ret" <-- snd retv as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvListsC).
Proof.
  eexists; intros.
  unfold MethodOfInterest.

  (* Notation "'BIND' !! A !! B !! C" := (@Bind A B C) (at level 1). *)
  (* Notation "x { A } <- y ; z" := (Bind y (fun x: A => z)) (at level 1). *)
  rewrite SameValues_Fiat_Bind_TelEq_Pair.
  setoid_rewrite Propagate_anonymous_ret at 3; simpl.

  Eval simpl in (@CallBagMethod (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
           (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
              (VectorDef.nil RawHeading) SearchUpdateTerm 
              (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) 
           (@F1 O)
           (@BagFind heading
              (@ilist3_hd RawSchema (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns)) 
                 (S O)
                 (Vector.cons RawSchema
                    (Build_RawSchema heading (@None (@RawTuple heading -> Prop))
                       (@Some (@RawTuple heading -> @RawTuple heading -> Prop)
                          (@FunctionalDependency_P heading
                             (@cons (t (S (S (S O)))) 
                                (@FS (S (S O)) (@FS (S O) (@F1 O)))
                                (@cons (t (S (S (S O)))) (@FS (S (S O)) (@F1 (S O))) (@nil (t (S (S (S O)))))))
                             (@cons (t (S (S (S O)))) (@F1 (S (S O))) (@nil (t (S (S (S O))))))))) O 
                    (Vector.nil RawSchema))
                 (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O 
                    (VectorDef.nil RawHeading) SearchUpdateTerm 
                    (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))) r_n
           (@pair (option W) (prod (option (Domain heading (@FS (S (S O)) (@F1 (S O))))) (@RawTuple heading -> bool)) 
              (@Some W d)
              (@pair (option (Domain heading (@FS (S (S O)) (@F1 (S O))))) 
                 (@RawTuple heading -> bool) (@None (Domain heading (@FS (S (S O)) (@F1 (S O))))) 
                 (fun _ : @RawTuple heading => true)))).

  Eval simpl in ((fix methodType' (rep : Type) (dom : list Type) (cod : option Type) {struct dom} : 
        Type :=
          match dom with
          | nil => match cod with
                  | Some cod' => Comp (rep * cod')
                  | None => Comp rep
                  end
          | d :: dom' => d -> methodType' rep dom' cod
          end)
         (Core.Rep
            (BagADT.BagSpec (BagMatchSearchTerm (ith3 (icons3 SearchUpdateTerm inil3) F1))
               (BagApplyUpdateTerm (ith3 (icons3 SearchUpdateTerm inil3) F1)))) 
         []
         (snd
            (ADTSig.MethodDomCod
               (BuildADTSig.DecADTSig
                  (BagADT.BagSig RawTuple (BagSearchTermType (ith3 (icons3 SearchUpdateTerm inil3) F1))
                     (BagUpdateTermType (ith3 (icons3 SearchUpdateTerm inil3) F1)))) BagFind))).

  
  eapply ProgOk_Transitivity_Cons; repeat compile_step.
  Focus 2. eapply ProgOk_Transitivity_Name' with "fst"; repeat compile_step.
  Focus 2. eapply ProgOk_Transitivity_Name' with "snd"; repeat compile_step.
  Focus 2. 


  
  simpl.
  eapply ProgOk_Transitivity_Cons.



  
  f_equal.
  unfold Type2.
  compute.
  specialize (H (@NTSome _ _ "ret" (@WrapInstance av' Type2 (@FacadeWrapper_Right (sum (list W) Type1) Type2 Type2 (@FacadeWrapper_Self Type2))))).

  
  compile_step.
  
  Eval compute in (Core.Rep
          (BagADT.BagSpec (BagMatchSearchTerm (ith3 (icons3 SearchUpdateTerm inil3) F1))
             (BagApplyUpdateTerm (ith3 (icons3 SearchUpdateTerm inil3) F1)))).

  Set Printing Implicit.
  Unset Printing Notations.
  
  Eval compute in (CallBagMethod (qs_schema := QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema) F1 BagFind r_n (Some d, (None, fun _ : RawTuple => true))).
  Eval compute in ((fix methodType' (rep : Type) (dom : list Type) (cod : option Type) {struct dom} : 
        Type :=
          match dom with
          | nil => match cod with
                  | Some cod' => Comp (rep * cod')
                  | None => Comp rep
                  end
          | d :: dom' => d -> methodType' rep dom' cod
          end)
         (Core.Rep
            (BagADT.BagSpec (BagMatchSearchTerm (ith3 (icons3 SearchUpdateTerm inil3) F1))
               (BagApplyUpdateTerm (ith3 (icons3 SearchUpdateTerm inil3) F1)))) 
         []
         (snd
            (ADTSig.MethodDomCod
               (BuildADTSig.DecADTSig
                  (BagADT.BagSig RawTuple (BagSearchTermType (ith3 (icons3 SearchUpdateTerm inil3) F1))
                     (BagUpdateTermType (ith3 (icons3 SearchUpdateTerm inil3) F1)))) BagFind))).
  compile_step.
  forall ,
    


Example other_test_with_adt'' :
    sigT (fun prog => forall seq seq', {{ [[`"arg1" <-- seq as _ ]] :: [[`"arg2" <-- seq' as _]] :: Nil }}
                                 prog
                               {{ [[`"arg1" <-- (rev_append seq seq') as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvW).
Proof.
  econstructor; intros.

  compile_step.
  compile_step.
  compile_step.
  compile_random.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_random.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  

  compile_step.
  Fail fail.
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
 
