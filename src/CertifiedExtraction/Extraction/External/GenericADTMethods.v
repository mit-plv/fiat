Require Import
        Coq.Lists.List
        CertifiedExtraction.Extraction.BasicTactics
        CertifiedExtraction.Extraction.External.Core.

Definition FacadeImplementationOfMutation `{FacadeWrapper av A} (fAA: W -> A -> A) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists (w: W) (x: A), args = (wrap x) :: (wrap w) :: nil;
      PostCond := fun args ret => exists (w: W) (x: A), args = (wrap x, Some (wrap (fAA w x))) :: (wrap w, None) :: nil /\ ret = wrap (Word.natToWord 32 0)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfConstructor  `{FacadeWrapper av A} (fAA: A) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ ret = (wrap fAA)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfCopy `{FacadeWrapper av A} : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x: A, args = (wrap x) :: nil;
      PostCond := fun args ret => exists x: A, args = (wrap x, Some (wrap x)) :: nil /\ ret = (wrap x)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfDestructor `{FacadeWrapper av A} : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x: A, args = (wrap x) :: nil;
      PostCond := fun args ret => exists x: A, args = (wrap x, None) :: nil /\ ret = wrap (Word.natToWord 32 0)
    |}; spec_t.
Defined.

Lemma SameValues_Mutation_helper:
  forall (av : Type) (vsrc vret : StringMap.key)
    (ext : StringMap.t (Value av)) (tenv : Telescope av)
    (initial_state : State av) (x : Value av),
    vret <> vsrc ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    StringMap.MapsTo vsrc x initial_state ->
    initial_state ≲ tenv ∪ ext ->
    [vsrc <-- x]::M.remove vret initial_state ≲ tenv ∪ ext.
Proof.
  intros;
  rewrite <- remove_add_comm, <- add_redundant_cancel by congruence;
  facade_eauto.
Qed.

Hint Resolve SameValues_Mutation_helper : call_helpers_db.

Lemma CompileCallFacadeImplementationOfCopy:
  forall `{FacadeWrapper av A} {env},
  forall fpointer vsrc,
    GLabelMap.MapsTo fpointer (Axiomatic FacadeImplementationOfCopy) env ->
    forall vret (adt: A) (ext: StringMap.t (Value av)) (tenv: Telescope av),
      vret <> vsrc ->
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      StringMap.MapsTo vsrc (wrap adt) ext ->
      {{ tenv }}
        (Call vret fpointer (vsrc :: nil))
      {{ [[ vret <-- adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end.
  facade_eauto.
  facade_eauto.
  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation:
  forall `{H : FacadeWrapper av A}
    (env : GLabelMap.t (FuncSpec av)) (fADT : W -> A -> A)
    (fpointer : GLabelMap.key) (varg vtmp : StringMap.key) 
    (SCAarg : W) (ADTarg : A) (tenv : Telescope av),
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation fADT)) env ->
    forall (vret : StringMap.key) (ext : StringMap.t (Value av)),
      vret <> varg ->
      vtmp <> varg ->
      vtmp <> vret ->
      vret ∉ ext ->
      vtmp ∉ ext ->
      varg ∉ ext ->
      @NotInTelescope av vret tenv ->
      @NotInTelescope av vtmp tenv ->
      @NotInTelescope av varg tenv ->
      {{ [[vret <-- ADTarg as _]]::[[varg <-- SCAarg as _]]::tenv }}
        Call vtmp fpointer (vret :: varg :: nil)
      {{ [[vret <-- fADT SCAarg ADTarg as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end.

  facade_eauto.
  facade_eauto.
  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_Alloc:
  forall `{FacadeWrapper av A} {env} fADT,
  forall fpointer varg vtmp (SCAarg: W) (ADTarg: A) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation fADT)) env ->
    forall vret ext pSCA pADT,
      vret <> varg ->
      vtmp <> varg ->
      vtmp <> vret ->
      vret ∉ ext ->
      vtmp ∉ ext ->
      varg ∉ ext ->
      @NotInTelescope av vret tenv ->
      @NotInTelescope av vtmp tenv ->
      @NotInTelescope av varg tenv ->
      {{ tenv }}
        pSCA
      {{ [[ varg <-- SCAarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ varg <-- SCAarg as _]] :: tenv }}
        pADT
      {{ [[ varg <-- SCAarg as _]] :: [[ vret <-- ADTarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq pSCA (Seq pADT (Call vtmp fpointer (vret :: varg :: nil)))
      {{ [[ vret <-- (fADT SCAarg ADTarg) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  rewrite TelEq_swap by congruence;
  eauto using CompileCallFacadeImplementationOfMutation.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_Replace:
  forall `{FacadeWrapper av A} {env} fADT,
  forall fpointer varg vtmp (SCAarg: W) (ADTarg: A) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation fADT)) env ->
    forall vret ext pSCA,
      vret <> varg ->
      vtmp <> varg ->
      vtmp <> vret ->
      vret ∉ ext ->
      vtmp ∉ ext ->
      varg ∉ ext ->
      NotInTelescope vret tenv ->
      NotInTelescope vtmp tenv ->
      NotInTelescope varg tenv ->
      {{ [[ vret <-- ADTarg as _]] :: tenv }}
        pSCA
      {{ [[ vret <-- ADTarg as _]] :: [[ varg <-- SCAarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ vret <-- ADTarg as _]] :: tenv }}
        Seq pSCA (Call vtmp fpointer (vret :: varg :: nil))
      {{ [[ vret <-- (fADT SCAarg ADTarg) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  eauto using CompileCallFacadeImplementationOfMutation.
Qed.

Lemma CompileCallFacadeImplementationOfConstructor:
  forall `{FacadeWrapper av A} {env} (adt: A) tenv,
  forall fpointer,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfConstructor adt)) env ->
    forall vret ext,
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      {{ tenv }}
        (Call vret fpointer nil)
      {{ [[ vret <-- adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end.

  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfDestructor:
  forall `{FacadeWrapper av A} {env} fpointer vtmp (adt: A) (tenv: Telescope av),
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfDestructor (A := A))) env ->
    forall vadt ext,
      vtmp <> vadt ->
      vtmp ∉ ext ->
      NotInTelescope vtmp tenv ->
      vadt ∉ ext ->
      NotInTelescope vadt tenv ->
      {{ [[ vadt <-- adt as _]] :: tenv }}
        (Call vtmp fpointer (vadt :: nil))
      {{ tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfDestructor':
  forall `{FacadeWrapper av A} {env} fpointer vtmp (adt: Comp A) (tenv: A -> Telescope av),
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfDestructor (A := A))) env ->
    forall vadt ext,
      vtmp <> vadt ->
      vtmp ∉ ext ->
      (forall aadt, adt ↝ aadt -> NotInTelescope vtmp (tenv aadt)) ->
      vadt ∉ ext ->
      (forall aadt, adt ↝ aadt -> NotInTelescope vadt (tenv aadt)) ->
      {{ [[`vadt <~~ adt as aadt]] :: tenv aadt}}
        (Call vtmp fpointer (vadt :: nil))
      {{ [[adt as aadt]] :: tenv aadt }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply miniChomp'.
  intros.
  rewrite Propagate_ret.
  eauto using CompileCallFacadeImplementationOfDestructor.
Qed.
