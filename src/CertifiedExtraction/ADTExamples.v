Require Import Fiat.Examples.QueryStructure.ProcessScheduler.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Examples
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.Extraction.

Definition MyEnvLists `{FacadeWrapper av (list W)} : Env av :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("list", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("list", "push") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("list", "pop") ->> (Axiomatic (List_pop W))
    ### ("list", "delete") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("list", "empty?") ->> (Axiomatic (List_empty W)).

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
Opaque nat_as_constant nat_as_word string_as_var.

Eval compute in (extract_facade other_test_with_adt'').

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

Require Import FacadeLoops.

Lemma CompileLoop :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp A' -> A -> Comp A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: Comp (list A)),
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

  2:eapply CompileCallFacadeImplementationOfDestructor; loop_t.

  rewrite (TelEq_swap _ NTNone).

  apply miniChomp'; loop_t.

  clear dependent facadeInit;
  generalize dependent init;
  generalize dependent lst;
  induction vv; loop_t.

  rewrite TelEq_swap.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized @CompileCallPop; loop_t.

  apply CompileCallEmpty_spec; loop_t.

  loop_t.
Qed.

Lemma CompileLoop_strong :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
    env (ext: StringMap.t (Value av)) tenv tenv' (f: Comp A' -> A -> Comp A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <~~ lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv }}
      facadeConclude
    {{ [[lst as ls]] :: [[`vret <~~ (fold_comp f ls init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: Comp (list A)),
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
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("listW", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("listW", "push!") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("listW", "pop!") ->> (Axiomatic (List_pop W))
    ### ("listW", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("listW", "empty?") ->> (Axiomatic (List_empty W))
    ### ("search", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor TSearchTerm))
    ### ("acc", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor TAcc)).

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
               (fun w => (Axiomatic (List_pop (av := av) _ (H := w)))) MyEnvListsB in
  let fempty := find_function_pattern_in_env
                 (fun w => (Axiomatic (List_empty (av := av) _ (H := w)))) MyEnvListsB in
  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        (list W) (av := av) (H := w)))) MyEnvListsB in
  let vtest := gensym "test" in
  let vhead := gensym "head" in
  apply (CompileLoop_strong (vtest := vtest) (vhead := vhead) (fpop := fpop) (fempty := fempty) (fdealloc := fdealloc));
    try compile_do_side_conditions.

  repeat compile_step.
  repeat compile_step.

  eapply CompileSeq.
  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        TSearchTerm (av := av) (H := w)))) MyEnvListsB in
  let vtmp := gensym "tmp" in
  apply (CompileCallFacadeImplementationOfDestructor (fpointer := fdealloc) (vtmp := vtmp));
    try compile_do_side_conditions.

  let fdealloc := find_function_pattern_in_env
                   (fun w => (Axiomatic (FacadeImplementationOfDestructor
                                        TAcc (av := av) (H := w)))) MyEnvListsB in
  let vtmp := gensym "tmp" in
  apply (CompileCallFacadeImplementationOfDestructor (fpointer := fdealloc) (vtmp := vtmp));
    try compile_do_side_conditions.

  compile_step.
  apply CompileDeallocSCA_discretely. (* FIXME compile_do_extend_scalar_lifetime should consider Word.word 32 *)
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

Definition revmap {A B} f := fun seq => @map A B f (rev seq).

Lemma CompileMap_helper:
  forall (A A' : Type) (f : A -> A') (a : A) (vv : list A) (base : list A'),
    revmap f (a :: vv) ++ base = revmap f vv ++ f a :: base.
Proof.
  unfold revmap; intros; simpl.
  rewrite map_rev.
  rewrite map_app.
  simpl.
  rewrite <- app_assoc.
  simpl.
  rewrite <- map_rev.
  reflexivity.
Qed.

Ltac defunctionalize_evar :=
  match goal with
  | [  |- context[?e] ] =>
    is_evar e;
      match type of e with
      | ?a -> ?b => let ee := fresh in
                  evar (ee: b);
                    unify e (fun _:a => ee);
                    unfold ee in *;
                    clear ee
      end
  end.

Ltac move_to_front var :=
  repeat lazymatch goal with
    | [  |- context[Cons ?k _ (fun _ => Cons (@NTSome _ _ var _) _ _)] ] =>
      setoid_rewrite (TelEq_swap k (@NTSome _ _ var _)) at 1
    end.

Lemma CompileMap_ADT :
  forall {av A A'} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list A')} `{FacadeWrapper av A} `{FacadeWrapper av A'}
    (base: list A') (lst: Comp (list A)) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody env (ext: StringMap.t (Value av)) (tenv: Telescope av) (f: A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list A') base)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_ADT A' (list A') cons)) env ->
    PreconditionSet tenv ext ([[[vhead; vhead'; vtest; vlst; vret; vtmp]]]) ->
    (forall head (s: list A) (s': list A'),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Fold vhead vtest vlst fpop fempty
                  (Seq facadeBody
                       (Call vtmp fcons (vret :: vhead' :: nil))))
            (Call vtest fdealloc (vlst :: nil))))
    {{ [[lst as ls]] :: [[`vret <-- (revmap f ls) ++ base as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  loop_t.

  eapply (CompileCallFacadeImplementationOfConstructor (A := list A') (adt := base)); loop_t.

  rewrite TelEq_swap;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply (CompileCallFacadeImplementationOfDestructor (A := list A)); loop_t.

  loop_unify_with_nil_t.
  rewrite (TelEq_swap _ NTNone).

  apply miniChomp'; loop_t.

  clear dependent falloc;
  generalize dependent lst;
    generalize dependent base;
    induction vv; loop_t.

  rewrite TelEq_swap.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized (CompileCallPop (A := A)); loop_t.

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vret; apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

  move_to_front vhead'.
  move_to_front vret.
  apply CompileCallFacadeImplementationOfMutation_ADT; try compile_do_side_conditions.

  move_to_front vlst.
  apply CompileCallEmpty_spec; loop_t.

  rewrite CompileMap_helper.
  loop_t.
Qed.

Lemma CompileMap_ADT_strong :
  forall {av A A'} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list A')} `{FacadeWrapper av A} `{FacadeWrapper av A'}
    (lst: Comp (list A)) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list A') nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_ADT A' (list A') cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[lst as ls]] :: [[`vret <-- (revmap f ls) as _]] :: tenv }}
      facadeCoda
    {{ [[lst as ls]] :: [[`vret <-- (revmap f ls) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list A'),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      (Seq
         (Seq
            (Call vret falloc nil)
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil))))
          facadeCoda)
    {{ [[lst as ls]] :: [[`vret <-- (revmap f ls) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  setoid_rewrite (app_nil_end (revmap f _)).
  apply CompileMap_ADT; eauto.
Qed.

Lemma CompileMap_SCA:
  forall {av A} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list W)} `{FacadeWrapper av A}
    (base: list W) (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody env (ext: StringMap.t (Value av)) (tenv: Telescope av) (f: A -> W),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list W) base)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons)) env ->
    PreconditionSet tenv ext ([[[vhead; vhead'; vtest; vlst; vret; vtmp]]]) ->
    (forall head (s: list A) (s': list W),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Fold vhead vtest vlst fpop fempty
                  (Seq facadeBody
                       (Call vtmp fcons (vret :: vhead' :: nil))))
            (Call vtest fdealloc (vlst :: nil))))
    {{ [[`vret <-- (revmap f lst) ++ base as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  loop_t.

  eapply (CompileCallFacadeImplementationOfConstructor (A := list W) (adt := base)); loop_t.

  rewrite TelEq_swap;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply (CompileCallFacadeImplementationOfDestructor (A := list A)); loop_t.

  loop_unify_with_nil_t.
  loop_t.

  clear dependent falloc;
    generalize dependent base;
    induction lst; loop_t.

  rewrite TelEq_swap.

  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; loop_t.

  apply generalized (CompileCallPop (A := A)); loop_t.

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vret; apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

  move_to_front vhead'.
  move_to_front vret.
  apply CompileCallFacadeImplementationOfMutation_SCA; try compile_do_side_conditions.

  move_to_front vlst.
  apply CompileCallEmpty_spec; loop_t.

  rewrite CompileMap_helper.
  loop_t.
Qed.

Lemma CompileMap_SCA_strong :
  forall {av A} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list W)} `{FacadeWrapper av A}
    (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> W),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list W) nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list W),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Seq
            (Call vret falloc nil)
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil))))
          facadeCoda)
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  setoid_rewrite (app_nil_end (revmap f _)).
  apply CompileMap_SCA; eauto.
Qed.

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

Definition av' := (list W + Type1 + Type2 + (@IndexedEnsembles.IndexedEnsemble
                                              (@RawTuple heading)) + (list (@RawTuple heading)) + (@RawTuple heading))%type.

Check MethodOfInterest.

(* Notation "'BIND' !! A !! B !! C" := (@Bind A B C) (at level 1). *)
(* Notation "x { A } <- y ; z" := (Bind y (fun x: A => z)) (at level 1). *)

Lemma ProgOk_Transitivity_Name_Pair :
  forall {av A1 A2} `{FacadeWrapper av A1} `{FacadeWrapper av A2} {ext env}
    vfst vsnd tenv tenv' (pair: Comp (A1 * A2)) prog d1 d2,
    {{ tenv }}
      prog
    {{ [[pair as p]] :: [[`vfst <-- fst p as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env ->
    {{ [[pair as p]] :: [[`vfst <-- fst p as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }}
      d1
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env ->
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[`vsnd <-- snd p as p2]] :: tenv' p1 p2 }}
      d2
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[ret (snd p) as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env ->
    {{ tenv }}
      Seq prog (Seq d1 d2)
    {{ [[pair as p]] :: [[ret (fst p) as p1]] :: [[ret (snd p) as p2]] :: tenv' p1 p2 }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.

About List_pop.

Lemma CompileDeallocADT_discretely : (* TODO create a specialized version that hardcodes the deallocation call *)
  forall {av A} {env ext} (k: NameTag av A) comp tenv tenv' prog dealloc,
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      prog
      {{ [[k <~~ comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as kk]] :: tenv' kk }}
      dealloc
      {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env ->
    {{ [[k <~~ comp as kk]] :: tenv kk }}
      (Seq prog dealloc)
      {{ [[comp as kk]] :: tenv' kk }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.

Lemma CompileDeallocADT_discretely' : (* TODO create a specialized version that hardcodes the deallocation call *)
  forall {av A} {env ext} (k: NameTag av A) v tenv tenv' prog dealloc,
    {{ [[k <-- v as _]] :: tenv }}
      prog
    {{ [[k <-- v as _]] :: tenv' }} ∪ {{ext}} // env ->
    {{ [[k <-- v as _]] :: tenv' }}
      dealloc
    {{ tenv' }} ∪ {{ext}} // env ->
    {{ [[k <-- v as _]] :: tenv }}
      (Seq prog dealloc)
    {{ tenv' }} ∪ {{ext}} // env.
Proof.
  repeat hoare.
Qed.

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

Example compile :
  sigT (fun prog => forall (r_n : Type1) (d : W),
            {{ [[`"r_n" <-- r_n as _ ]] :: [[`"d" <-- d as _]] :: Nil }}
              prog
            {{ [[MethodOfInterest r_n d as retv]] :: [[`"r_n" <-- fst retv as _]] :: [[`"ret" <-- snd retv as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvListsC).
Proof.
  eexists; intros.
  unfold MethodOfInterest.

  rewrite SameValues_Fiat_Bind_TelEq.
  setoid_rewrite Propagate_anonymous_ret; simpl.

  move_to_front "r_n".
  compile_step.
  compile_step.
  compile_step.

  Ltac compile_CallBagFind :=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:(pre, post) with
              | (Cons (NTSome ?kd) (ret ?d) ?tenv,
                 Cons NTNone (CallBagMethod ?id BagFind ?v (Some ?d, ?r)) ?tenv') =>
                let vfst := gensym "fst" in
                let vsnd := gensym "snd" in
                let vtmp := gensym "tmp" in
                match post with
                | Cons NTNone ?v _ =>
                  eapply CompileSeq with ([[v as vv]]
                                            :: [[`vfst <-- fst vv as f]]
                                            :: [[`vsnd <-- snd vv as s]]
                                            :: [[ret d as dd]]
                                            :: (tenv dd));
                    [ match_ProgOk
                        ltac:(fun prog' _ _ _ _ =>
                                unify prog' (Call (DummyArgument vtmp) ("ext", "BagFind")
                                                  (vfst :: vsnd :: "r_n" :: kd :: nil))) (* FIXME *) | ]
                end
              end).

  compile_CallBagFind.
  admit.

  apply ProgOk_Chomp_None.
  compile_step.

  apply CompileDeallocADT_discretely'.
  compile_step.
  compile_step.

  setoid_rewrite Propagate_anonymous_ret.

  match goal with
  | [  |- appcontext[@map ?a ?b] ] => replace (@map a b) with (@revmap a b) by admit
  end.

  let vhead := gensym "head" in
  let vhead' := gensym "head'" in
  let vtest := gensym "test" in
  let vtmp := gensym "tmp" in
  apply (CompileMap_SCA_strong (snd v0) (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := DummyArgument vtmp)); try compile_do_side_conditions.

  compile_step.
  compile_step.
  compile_step.

  Definition FinToWord {N: nat} (n: Fin.t N) :=
    Word.natToWord 32 (proj1_sig (Fin.to_nat n)).

  Definition FitsInW {N: nat} (n: Fin.t N) :=
    Word.wordToNat (FinToWord n) = proj1_sig (Fin.to_nat n).

  assert (FitsInW (@FS 2 (@FS 1 (@F1 0)))) by reflexivity.

  compile_do_use_transitivity_to_handle_head_separately.

  apply CompileSeq with ([[`"index" <-- FinToWord (@FS 2 (@FS 1 (@F1 0))) as _]] :: [[ ` "head" <-- head as _]] :: Nil).

  compile_step.                 (* FIXME shouldn't extend SCA lifespan *)
  apply CompileSkip. (* FIXME fast-track compile_step this to just apply CompileSkip *)
  instantiate (1 := Call "head'" ("ext", "GetAttribute") ("head" :: "index" :: nil)).
  admit.

  compile_step.
  compile_step.
  compile_step.
  let tmp := gensym "tmp" in     (* FIXME prove  deallocation lemma specific to the ret case. *)
  apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument tmp)); try compile_do_side_conditions.

  let tmp := gensym "tmp" in     (* FIXME prove  deallocation lemma specific to the ret case. *)
  apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument tmp)); try compile_do_side_conditions.
Defined.

Opaque DummyArgument.
Eval compute in (extract_facade compile).

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
