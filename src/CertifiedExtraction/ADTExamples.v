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

Require Import
        CertifiedExtraction.Extraction.AllInternal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

(* Opaque WrapInstance.            (* FIXME simpl never? *) *)

Require Import FacadeLoops.

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
  repeat
    lazymatch goal with         (* `at 1' prevents setoid_rewrite from modifying evars *)
    | [  |- context[Cons ?k _ (fun _ => Cons var _ _)] ] =>
      setoid_rewrite (TelEq_swap k var) at 1
    | [  |- context[Cons ?k _ (fun _ => Cons (@NTSome _ _ var _) _ _)] ] =>
      setoid_rewrite (TelEq_swap k (@NTSome _ _ var _)) at 1
    end.

Lemma CompileLoop :
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper (Value av) A'} `{FacadeWrapper av (list A)}
    lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody env (ext: StringMap.t (Value av)) tenv (f: Comp A' -> A -> Comp A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vhead <-- head as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  unfold DummyArgument; loop_t.

  rewrite TelEq_swap by loop_t;
    eapply CompileCallEmpty_spec; loop_t.

  2:eapply CompileCallFacadeImplementationOfDestructor; loop_t.

  loop_unify_with_nil_t.

  loop_t.
  clear dependent facadeInit;
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
  apply CompileWhileFalse_Loop; loop_t.

  eapply CompileWhileTrue; [ loop_t.. | ].

  apply generalized @CompileCallPop; loop_t.

  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

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
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A') (s: list A),
        {{ [[`vhead <-- head as _]] :: [[`vret <~~ acc as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Seq facadeInit (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))) facadeConclude)
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  eapply CompileSeq;
    [ apply CompileLoop | eassumption ];
    assumption.
Qed.

Definition revmap {A B} f := fun seq => @map A B f (rev seq).

Lemma revmap_fold_helper:
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

Lemma revmap_fold_strong :
  forall {A B} (f: A -> B) (seq: list A) (base: list B),
    fold_left (fun acc elem => f elem :: acc) seq base = (@revmap A B f seq) ++ base.
Proof.
  induction seq; simpl; intros.
  - reflexivity.
  - rewrite revmap_fold_helper; eauto.
Qed.

Lemma revmap_fold :
  forall {A B} (f: A -> B) (seq: list A),
    fold_left (fun acc elem => f elem :: acc) seq nil = @revmap A B f seq.
Proof.
  intros.
  rewrite <- (app_nil_r (revmap f seq)).
  apply revmap_fold_strong.
Qed.

Lemma revmap_fold_comp_strong :
  forall {A B} (f: A -> B) (seq: list A) base,
    Monad.equiv
      (fold_left (fun cacc elem => (acc <- cacc; ret (f elem :: acc))%comp) seq base)
      ( b <- base;
        ret ((@revmap A B f seq) ++ b)).
Proof.
  intros; etransitivity.
  2: apply Monad.computes_under_bind; intros; rewrite <- revmap_fold_strong; apply SetoidMorphisms.equiv_refl.

  generalize dependent base; induction seq; simpl;
  [ | setoid_rewrite IHseq ];
  split; intros; computes_to_inv; subst; eauto using BindComputes.
Qed.

Lemma revmap_fold_comp :
  forall {A B} (f: A -> B) (seq: list A),
    Monad.equiv
      (fold_left (fun cacc elem => (acc <- cacc; ret (f elem :: acc))%comp) seq (ret nil))
      (ret (@revmap A B f seq)).
Proof.
  intros.
  rewrite <- (app_nil_r (revmap f seq)).
  rewrite revmap_fold_comp_strong.
  split; intros; computes_to_inv; subst; eauto using BindComputes.
Qed.

Lemma CompileMap_ADT_strong :
  forall {av A A'} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list A')} `{FacadeWrapper av A} `{FacadeWrapper av A'}
    (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> A'),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list A') nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_ADT A' (list A') cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list A'),
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
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileLoop_strong; eauto.
  PreconditionSet_t; eauto.
  eapply (CompileCallFacadeImplementationOfConstructor (A := list A')); loop_t.
  setoid_rewrite revmap_fold_comp; eassumption.
  intros.
  rewrite SameValues_Fiat_Bind_TelEq.
  move_to_front vret.
  apply miniChomp'; intros.
  hoare.
  apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.
  apply CompileCallFacadeImplementationOfMutation_ADT; compile_do_side_conditions.
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
                          (Call (DummyArgument vtmp) fcons (vret :: vhead' :: nil))))
               (Call (DummyArgument vtest) fdealloc (vlst :: nil))))
          facadeCoda)
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileLoop_strong; eauto.
  PreconditionSet_t; eauto.
  eapply (CompileCallFacadeImplementationOfConstructor (A := list W)); loop_t.
  setoid_rewrite revmap_fold_comp; eassumption.
  intros.
  rewrite SameValues_Fiat_Bind_TelEq.
  move_to_front vret.
  apply miniChomp'; intros.
  hoare.
  apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.
  apply CompileCallFacadeImplementationOfMutation_SCA; unfold DummyArgument; compile_do_side_conditions.
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

Ltac compile_loop :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtest := gensym "test" in
            let vhead := gensym "head" in
            match constr:(pre, post) with
            | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (List.fold_left _ ?seq _) ?tenv') =>
              apply (CompileLoop_strong (vtest := vtest) (vhead := vhead)); try compile_do_side_conditions
            | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (ret (List.fold_left _ ?seq _)) ?tenv') =>
              (* FIXME rename and generalize to different tenvs *)
              apply (FacadeLoops.CompileLoop CompileLoop_strong (vtest := vtest) (vhead := vhead)); try compile_do_side_conditions
            end).

Ltac compile_destructor :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtmp := gensym "tmp" in
            match constr:(pre, post) with
            | (Cons _ _ (fun _ => ?tenv), ?tenv) =>
              apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp))
            | (Cons _ ?v (fun _ => ?tenv), ?tenv') =>
              match tenv' with
              | context[v] => fail 1
              | _ => eapply CompileSeq; [ apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) | ]
              end
            end; try compile_do_side_conditions).

Ltac compile_miniChomp :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons NTNone ?v ?tenv' =>
              match pre with
              | context[Cons ?k v _] =>
                move_to_front k;
                  apply miniChomp'
              end
            end).

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

  repeat setoid_rewrite SameValues_Fiat_Bind_TelEq.

  (* FXIME compile_do_alloc should use Transitivity_Name' *)
  eapply ProgOk_Transitivity_Name' with "seq".

  instantiate (1 := Skip).       (* FIXME alloc *)
  admit.

  compile_miniChomp.
  compile_step.
  compile_loop.
  compile_step.

  repeat compile_step.

  compile_destructor.
  compile_destructor.

  compile_step.
  repeat setoid_rewrite SameValues_Fiat_Bind_TelEq.

  compile_do_extend_scalar_lifetime.
  compile_step.
  compile_step.
  (* FIXME compile_do_alloc shouldn't be called here. *)
  compile_miniChomp.
  compile_step.
  compile_step.

  instantiate (1 := Skip).
  admit.
Defined.

Opaque DummyArgument.

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

Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation Fiat.QueryStructure.Automation.Common Fiat.QueryStructure.Specification.Representation.Schema.
Require Import Coq.Vectors.Fin.

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

Definition FinToWord {N: nat} (n: Fin.t N) :=
  Word.natToWord 32 (proj1_sig (Fin.to_nat n)).

Definition FitsInW {N: nat} (n: Fin.t N) :=
  Word.wordToNat (FinToWord n) = proj1_sig (Fin.to_nat n).

Ltac compile_chomp :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match pre with    (* FIXME could be generalized beyond the first binding *)
            | Cons ?k ?v ?tenv =>
              match post with
              | Cons k v _ => fail 1
              | context[Cons k v _] => move_to_front k
              end
            end).

Ltac compile_dealloc_useless :=  (* FIXME used? *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match pre with
            | Cons ?k ?v ?tenv =>
              match post with
              | context[k] => fail 1 "k appears in conclusion"
              | context[v] => fail 1 "v appears in conclusion"
              | _ => apply CompileDeallocSCA_discretely
              | _ => apply CompileDeallocADT_discretely
              | _ => apply CompileDeallocADT_discretely'
              end
            end).

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

Ltac _compile_map :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vhead := gensym "head" in
            let vhead' := gensym "head'" in
            let vtest := gensym "test" in
            let vtmp := gensym "tmp" in
            match constr:(pre, post) with
            | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (ret (revmap _ ?seq')) ?tenv') =>
              unify seq seq';
                first [
                    apply (CompileMap_SCA_strong seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := DummyArgument vtmp)) |
                    apply (CompileMap_ADT_strong seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := DummyArgument vtmp)) ];
                try compile_do_side_conditions
            end).


  Ltac facade_if_helper ::=     (* Add an eauto 3 to prevent spurious existentials from popping up *)
  match goal with
  | H:is_true ?st (isTrueExpr ?k),
    H':StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st
    |- _ => learn (is_true_isTrueExpr H H')
  | H:is_false ?st (isTrueExpr ?k),
    H':StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st
    |- _ => learn (is_false_isTrueExpr H H')
  | _ => solve
  [ eauto 3 using isTrueExpr_is_false, isTrueExpr_is_true  with SameValues_db ]
  | _ => solve
  [ eauto using isTrueExpr_is_false, isTrueExpr_is_true  with SameValues_db ]
  end.

Lemma CompileIf :
  forall {av A} k tmp (gallinaTest: bool) (gallinaT gallinaF: Comp A) facadeTest facadeT facadeF
    env (ext: StringMap.t (Value av)) tenv tenv',
    tmp ∉ ext ->
    NotInTelescope tmp tenv ->
    {{ tenv }}
      facadeTest
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::tenv }}
      facadeT
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::[[k <~~ gallinaT as v]]::tenv' v }} ∪ {{ ext }} // env ->
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::tenv }}
      facadeF
    {{ [[`tmp <-- (bool2w gallinaTest) as _]]::[[k <~~ gallinaF as v]]::tenv' v }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq facadeTest (DFacade.If (isTrueExpr tmp) facadeT facadeF))
    {{ [[k <~~ if gallinaTest then gallinaT else gallinaF as v]]::tenv' v }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  repeat (SameValues_Facade_t_step || facade_if_helper).
Qed.

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

Lemma SameValues_remove_SCA:
  forall (av0 : Type) (tenv' : Telescope av0)
    (ext : StringMap.t (Value av0)) (k : StringMap.key)
    (final_state : State av0) (x : W),
    StringMap.MapsTo k (wrap x) final_state ->
    StringMap.remove (elt:=Value av0) k final_state ≲ tenv' ∪ ext ->
    final_state ≲ tenv' ∪ ext.
Proof.
  induction tenv'; simpl; intros.
  - rewrite (add_redundant_cancel H).
    rewrite <- add_remove_cancel; try reflexivity.
    apply WeakEq_pop_SCA.
    apply StringMap.remove_1; reflexivity.
    assumption.
  - destruct key; repeat cleanup.
    + eauto.
    + SameValues_Fiat_t.
      StringMap_t.
      rewrite remove_mapsto_iff in *.
      cleanup.
      StringMap_t.
      repeat cleanup.
      eapply H.
      2: rewrite remove_remove_comm; eauto.
      rewrite remove_mapsto_iff in *; eauto.
Qed.

Hint Resolve SameValues_remove_SCA : SameValues_db.

Lemma CompileDeallocSCA_discretely :
  forall {av} (tenv tenv': Telescope av) ext env k (v: Comp W) prog,
    k ∉ ext ->
    NotInTelescope k tenv ->
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ [[`k <~~ v as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as _]] :: tenv }} prog {{ tenv' }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

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

Ltac _compile_chomp :=         (* This is a weak version of the real compile_chomp, which is too slow *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (Cons ?k ?v ?tenv, Cons ?k' ?v' ?tenv') =>
              unify k k'; unify v v';
              match k with
              | NTNone => apply ProgOk_Chomp_None
              | _ => apply ProgOk_Chomp_Some
              end
            end).

Ltac tenv_mentions env v :=
  first [ match env with
          | context[?vv] => first [ is_evar vv; fail 1
                                 | unify v vv; fail 2 ]
          | _ => idtac
          end; fail 1 | idtac ].

Ltac tenv_mentions_fast env v :=
  lazymatch v with
  | ?f => match env with context[f] => idtac end
  | ?f ?a => match env with context[f ?a'] => unify a a' end
  | ?f ?a ?b => match env with context[f ?a' ?b'] => unify a a'; unify b b' end
  | ?f ?a ?b ?c => match env with context[f ?a' ?b' ?c'] => unify a a'; unify b b'; unify c c' end
  | ?f ?a ?b ?c ?d => match env with context[f ?a' ?b' ?c' ?d'] => unify a a'; unify b b'; unify c c'; unify d d' end
  end.

Ltac _compile_destructor_unsafe vtmp tenv tenv' :=
  (apply CompileDeallocSCA_discretely ||
   first [ unify tenv tenv';
           apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp))
         | eapply CompileSeq;
           [ apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) | ] ]);
  try compile_do_side_conditions.

Ltac _compile_destructor :=
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             let vtmp := gensym "tmp" in
             match pre with
             | Cons _ ?v (fun _ => ?tenv) =>
               match tenv with
               | context[post] => _compile_destructor_unsafe vtmp tenv post
               | _ => unify tenv post; _compile_destructor_unsafe vtmp tenv post
               | _ => lazymatch v with
                 | ret ?vv => first [ tenv_mentions_fast post vv; fail 1
                                   | _compile_destructor_unsafe vtmp tenv post ]
                 | ?vv => first [ tenv_mentions_fast post vv; fail 1
                               | _compile_destructor_unsafe vtmp tenv post ]
                 end
               end
             end).

Ltac _compile_skip :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, ?tenv') => not_evar tenv; not_evar tenv'; unify tenv tenv'; apply CompileSkip
            end).

Ltac _compile_if :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (_, Cons _ (if _ then _ else _) _) =>
              let vtmp := gensym "test" in
              apply (CompileIf (tmp := "test"))
            end).

Ltac __compile_prepare_chomp tenv tenv' :=
  match tenv with
  | Cons ?k ?v _ =>
    match tenv' with
    | Cons ?k' ?v' _ =>
      unify k k'; unify v v';
      fail 1 (* Nothing to do: can already chomp *)
    | Cons _ _ (fun _ => ?tail) =>
      unify tenv tail; idtac;
      fail 1 (* This is a job for deallocation, not chomping *)
    | context[Cons k v _] =>
      move_to_front k
    end
  end.

Ltac _compile_prepare_chomp :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            is_evar prog;
            first [ __compile_prepare_chomp pre post
                  | __compile_prepare_chomp post pre ]).

Arguments wrap : simpl never.

Ltac useless_binder term :=
  lazymatch term with
  | (fun _ => ?body) => let capture := body in idtac
  end.

Ltac _compile_rewrite :=
  (* setoid_rewrite at the speed of light *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | context[Cons ?k (ret _) ?tail] =>
              first [ useless_binder tail; fail 1 |
                      match k with
                      | NTSome _ => setoid_rewrite Propagate_ret
                      | NTNone => setoid_rewrite Propagate_anonymous_ret
                      end ]
            | context[Cons _ (Bind _ _) _] => setoid_rewrite SameValues_Fiat_Bind_TelEq
            end).

Ltac _compile_step :=
  match goal with
  | _ => progress subst; idtac "progress subst"
  | _ => progress intros; idtac "progress intros"
  | _ => progress computes_to_inv; idtac "progress computes_to_inv"
  | _ => _compile_rewrite; idtac "_compile_rewrite"
  | _ => compile_do_side_conditions; idtac "compile_do_side_conditions"
  | _ => _compile_skip; idtac "_compile_skip"
  | _ => _compile_map; idtac "_compile_map"
  | _ => _compile_CallBagFind; idtac "_compile_CallBagFind"
  | _ => _compile_CallBagInsert; idtac "_compile_CallBagInsert"
  | _ => _compile_CallGetAttribute; idtac "_compile_CallGetAttribute"
  | _ => _compile_destructor; idtac "_compile_destructor"
  | _ => _compile_chomp; idtac "_compile_chomp"
  | _ => _compile_prepare_chomp; idtac "_compile_prepare_chomp"
  | _ => _compile_if; idtac "_compile_if"
  | _ => compile_simple; idtac "compile_simple"
  | _ => progress simpl; idtac "progress simpl"
  end.

Ltac _compile :=
  repeat _compile_step.

Ltac _compile_random :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, Cons NTNone Random ?tenv') =>
              let vrandom := gensym "random" in
              apply ProgOk_Transitivity_Name with vrandom;
                [ call_tactic_after_moving_head_binding_to_separate_goal
                    ltac:(apply CompileCallRandom) | apply miniChomp' ] (* FIXME do deallocation here *)
            end).

Ltac compile_do_side_conditions_internal ::=
  repeat cleanup; PreconditionSet_t;
   match goal with
   | _ => exact I
   | |- _ <> _ => discriminate 1
   | |- _ ∉ _ => decide_not_in
   | |- NotInTelescope _ _ => decide_NotInTelescope
   | |- StringMap.find _ _ = Some _ => decide_mapsto_maybe_instantiate
   | |- StringMap.MapsTo _ _ _ => decide_mapsto_maybe_instantiate
   | |- GLabelMap.MapsTo _ _ _ =>
         GLabelMapUtils.decide_mapsto_maybe_instantiate
   end.

Example random_test_with_adt :
  Facade program implementing ( x <- Random;
                                ret (if IL.weqb x 0 then
                                       (Word.natToWord 32 1 : W) :: nil
                                     else
                                       x :: nil)) with MyEnvW.
Proof.
  Time compile_step.
  repeat (_compile_random || compile_mutation_alloc || compile_constructor || _compile_step || match_ProgOk compile_rewrite).
  (* FIXME try the side conditions before subst and computes_to_inv? *)
Defined.

Eval compute in (extract_facade random_test_with_adt).

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

(* Ltac _compile_destructor ::= *)
(*      match_ProgOk *)
(*      ltac:(fun prog pre post ext env => *)
(*              let vtmp := gensym "tmp" in *)
(*              match pre with *)
(*              | Cons _ ?v (fun _ => ?tenv) => *)
(*                match tenv with *)
(*                | context[post] => _compile_destructor_unsafe vtmp tenv post *)
(*                | _ => unify tenv post; _compile_destructor_unsafe vtmp tenv post *)
(*                | _ => ( set_values tail; *)
(*                        lazymatch v with *)
(*                        | ret ?vv => tenv_not_mentions post vv; _compile_destructor_unsafe vtmp tenv post *)
(*                        | ?vv => tenv_not_mentions post vv; _compile_destructor_unsafe vtmp tenv post *)
(*                        end; *)
(*                        unset_values) *)
(*                end *)
(*              end). *)

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

  _compile_step.
  _compile_step.
  _compile_step.
  
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.

  
  Time repeat (_compile_step || change (ilist2.ilist2_hd (ilist2.icons2 head ilist2.inil2)) with head).
  admit.
  admit.
Defined.

Opaque DummyArgument.
Eval compute in (extract_facade compile).

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