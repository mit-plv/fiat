Require Import
        Coq.Lists.List
        CertifiedExtraction.Extraction.External.Core.

Unset Implicit Arguments.

Definition FacadeImplementationOfMutation_SCA {av} A `{FacadeWrapper av A} (fAA: W -> A -> A) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists (w: W) (x: A), args = (wrap x) :: (wrap w) :: nil;
      PostCond := fun args ret => exists (w: W) (x: A), args = (wrap x, Some (wrap (fAA w x))) :: (wrap w, None) :: nil /\ ret = wrap (Word.natToWord 32 0)
    |}; spec_t.
Defined.

(* We need two separate lemma, as a wrapper into (Value av) could send some
   things into ADT, and some things into SCAs, and this would create ill-typed
   Facade specs. *)
Definition FacadeImplementationOfMutation_ADT {av} Targ Tadt `{FacadeWrapper av Tadt} `{FacadeWrapper av Targ}
           (fAA: Targ -> Tadt -> Tadt) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists (arg: Targ) (adt: Tadt), args = (wrap adt) :: (wrap arg) :: nil;
      PostCond := fun args ret => exists (arg: Targ) (adt: Tadt), args = (wrap adt, Some (wrap (fAA arg adt))) :: (wrap arg, None) :: nil /\ ret = wrap (Word.natToWord 32 0)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfConstructor {av} A `{FacadeWrapper av A} (fAA: A) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ ret = (wrap fAA)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfCopy {av} A `{FacadeWrapper av A} : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x: A, args = (wrap x) :: nil;
      PostCond := fun args ret => exists x: A, args = (wrap x, Some (wrap x)) :: nil /\ ret = (wrap x)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfDestructor {av} A `{FacadeWrapper av A} : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x: A, args = (wrap x) :: nil;
      PostCond := fun args ret => exists x: A, args = (wrap x, None) :: nil /\ ret = wrap (Word.natToWord 32 0)
    |}; spec_t.
Defined.

Set Implicit Arguments.

Lemma SameValues_Mutation_helper:
  forall (av : Type) (vsrc vret : StringMap.key)
    (ext : StringMap.t (Value av)) (tenv : Telescope av)
    (initial_state : State av) (x : Value av),
    vret <> vsrc ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    StringMap.MapsTo vsrc x initial_state ->
    initial_state ≲ tenv ∪ ext ->
    [vsrc |> x]::M.remove vret initial_state ≲ tenv ∪ ext.
Proof.
  intros;
  rewrite <- remove_add_comm, <- add_redundant_cancel by congruence;
  facade_eauto.
Qed.

Hint Resolve SameValues_Mutation_helper : call_helpers_db.

Lemma CompileCallFacadeImplementationOfCopy:
  forall `{FacadeWrapper av A} {env},
  forall fpointer vsrc,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfCopy A)) env ->
    forall vret (adt: A) (ext: StringMap.t (Value av)) (tenv: Telescope av),
      vret <> vsrc ->
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      StringMap.MapsTo vsrc (wrap adt) ext ->
      {{ tenv }}
        (Call vret fpointer (vsrc :: nil))
      {{ [[ `vret ->> adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end.
  facade_eauto.
  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_SCA:
  forall `{H : FacadeWrapper av A}
    (env : GLabelMap.t (FuncSpec av)) (fADT : W -> A -> A)
    (fpointer : GLabelMap.key) (varg vtmp : StringMap.key) 
    (arg : W) (target : A) (tenv : Telescope av),
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_SCA _ fADT)) env ->
    forall (vret : StringMap.key) (ext : StringMap.t (Value av)),
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[`vret ->> target as _]]::[[`varg ->> arg as _]]::tenv }}
        Call vtmp fpointer (vret :: varg :: nil)
      {{ [[`vret ->> fADT arg target as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || PreconditionSet_t);
  facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_SCA_Alloc:
  forall `{FacadeWrapper av A} {env} fADT,
  forall fpointer varg vtmp (arg: W) (target: A) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_SCA _ fADT)) env ->
    forall vret ext pSCA pADT,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ tenv }}
        pSCA
      {{ [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `varg ->> arg as _]] :: tenv }}
        pADT
      {{ [[ `varg ->> arg as _]] :: [[ `vret ->> target as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq pSCA (Seq pADT (Call vtmp fpointer (vret :: varg :: nil)))
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  rewrite TelEq_swap.
  eauto using CompileCallFacadeImplementationOfMutation_SCA.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_SCA_Replace:
  forall `{FacadeWrapper av A} {env} fADT,
  forall fpointer varg vtmp (arg: W) (target: A) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_SCA _ fADT)) env ->
    forall vret ext pSCA,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        pSCA
      {{ [[ `vret ->> target as _]] :: [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        Seq pSCA (Call vtmp fpointer (vret :: varg :: nil))
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  eauto using CompileCallFacadeImplementationOfMutation_SCA.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_SCA_Replace_strong:
  forall {av Tadt} `{FacadeWrapper av Tadt} {env} fADT,
  forall fpointer varg vtmp (arg: W) (target: Tadt) tenv tenv',
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_SCA Tadt fADT)) env ->
    forall vret ext pArg pCoda,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        pArg
        {{ [[ `vret ->> target as _]] :: [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }}
        pCoda
        {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        Seq (Seq pArg (Call vtmp fpointer (vret :: varg :: nil))) pCoda
        {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  apply CompileCallFacadeImplementationOfMutation_SCA_Replace; PreconditionSet_t; eauto.
Qed.


Lemma CompileCallFacadeImplementationOfMutation_SCA_Replace_strong':
  forall {av Tadt} `{FacadeWrapper av Tadt} {env} fADT,
  forall fpointer varg vtmp (arg: W) (orig target: Tadt) tenv tenv',
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_SCA Tadt fADT)) env ->
    forall vret ext pTarget pArg pCoda,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret ->> orig as _]] :: tenv }}
        pTarget
      {{ [[ `vret ->> target as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        pArg
      {{ [[ `vret ->> target as _]] :: [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }}
        pCoda
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> orig as _]] :: tenv }}
        Seq (Seq pTarget (Seq pArg (Call vtmp fpointer (vret :: varg :: nil)))) pCoda
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare. hoare.
  apply CompileCallFacadeImplementationOfMutation_SCA_Replace; PreconditionSet_t; eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_ADT:
  forall {av Targ Tadt} `{FacadeWrapper av Tadt} `{FacadeWrapper av Targ}
    (env : GLabelMap.t (FuncSpec av)) (fADT : Targ -> Tadt -> Tadt)
    (fpointer : GLabelMap.key) (varg vtmp : StringMap.key) 
    (arg : Targ) (target : Tadt) (tenv : Telescope av),
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_ADT Targ Tadt fADT)) env ->
    forall (vret : StringMap.key) (ext : StringMap.t (Value av)),
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[`vret ->> target as _]]::[[`varg ->> arg as _]]::tenv }}
        Call vtmp fpointer (vret :: varg :: nil)
      {{ [[`vret ->> fADT arg target as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => PreconditionSet_t
         end.

  facade_eauto.
  facade_eauto.
  rewrite remove_remove_comm by congruence.
  facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_ADT_Alloc:
  forall {av Targ Tadt} `{FacadeWrapper av Tadt} `{FacadeWrapper av Targ} {env} fADT,
  forall fpointer varg vtmp (arg: Targ) (target: Tadt) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_ADT Targ Tadt fADT)) env ->
    forall vret ext pArg pTarget,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ tenv }}
        pArg
      {{ [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `varg ->> arg as _]] :: tenv }}
        pTarget
      {{ [[ `varg ->> arg as _]] :: [[ `vret ->> target as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq pArg (Seq pTarget (Call vtmp fpointer (vret :: varg :: nil)))
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  rewrite TelEq_swap.
  apply CompileCallFacadeImplementationOfMutation_ADT; eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_ADT_Replace:
  forall {av Targ Tadt} `{FacadeWrapper av Tadt} `{FacadeWrapper av Targ} {env} fADT,
  forall fpointer varg vtmp (arg: Targ) (target: Tadt) tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_ADT Targ Tadt fADT)) env ->
    forall vret ext pArg,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        pArg
      {{ [[ `vret ->> target as _]] :: [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        Seq pArg (Call vtmp fpointer (vret :: varg :: nil))
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  apply CompileCallFacadeImplementationOfMutation_ADT; eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_ADT_Replace_strong:
  forall {av Targ Tadt} `{FacadeWrapper av Tadt} `{FacadeWrapper av Targ} {env} fADT,
  forall fpointer varg vtmp (arg: Targ) (target: Tadt) tenv tenv',
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_ADT Targ Tadt fADT)) env ->
    forall vret ext pArg pCoda,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        pArg
        {{ [[ `vret ->> target as _]] :: [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }}
        pCoda
        {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        Seq (Seq pArg (Call vtmp fpointer (vret :: varg :: nil))) pCoda
        {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  apply CompileCallFacadeImplementationOfMutation_ADT_Replace; PreconditionSet_t; eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_ADT_Replace_strong':
  forall {av Targ Tadt} `{FacadeWrapper av Tadt} `{FacadeWrapper av Targ} {env} fADT,
  forall fpointer varg vtmp (arg: Targ) (orig target: Tadt) tenv tenv',
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation_ADT Targ Tadt fADT)) env ->
    forall vret ext pTarget pArg pCoda,
      PreconditionSet tenv ext [[[varg; vtmp; vret]]] ->
      {{ [[ `vret ->> orig as _]] :: tenv }}
        pTarget
      {{ [[ `vret ->> target as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> target as _]] :: tenv }}
        pArg
      {{ [[ `vret ->> target as _]] :: [[ `varg ->> arg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv }}
        pCoda
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ [[ `vret ->> orig as _]] :: tenv }}
        Seq (Seq pTarget (Seq pArg (Call vtmp fpointer (vret :: varg :: nil)))) pCoda
      {{ [[ `vret ->> (fADT arg target) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  hoare. eauto.
  apply CompileCallFacadeImplementationOfMutation_ADT_Replace; PreconditionSet_t; eauto.
Qed.

Lemma CompileCallFacadeImplementationOfConstructor:
  forall `{FacadeWrapper av A} {env} (adt: A) tenv,
  forall fpointer,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfConstructor _ adt)) env ->
    forall vret ext,
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      {{ tenv }}
        (Call vret fpointer nil)
      {{ [[ `vret ->> adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => PreconditionSet_t
         end.

  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfDestructor:
  forall `{FacadeWrapper av A} {env} fpointer vtmp (adt: A) (tenv: Telescope av),
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfDestructor A)) env ->
    forall vadt ext,
      vtmp <> vadt ->
      vtmp ∉ ext ->
      NotInTelescope vtmp tenv ->
      vadt ∉ ext ->
      NotInTelescope vadt tenv ->
      {{ [[ `vadt ->> adt as _]] :: tenv }}
        (Call vtmp fpointer (vadt :: nil))
      {{ tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         | _ => PreconditionSet_t
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfDestructor':
  forall `{FacadeWrapper av A} {env} fpointer vtmp (adt: Comp A) (tenv: A -> Telescope av),
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfDestructor A)) env ->
    forall vadt ext,
      vtmp <> vadt ->
      vtmp ∉ ext ->
      (forall aadt, adt ↝ aadt -> NotInTelescope vtmp (tenv aadt)) ->
      vadt ∉ ext ->
      (forall aadt, adt ↝ aadt -> NotInTelescope vadt (tenv aadt)) ->
      {{ [[`vadt ~~> adt as aadt]] :: tenv aadt}}
        (Call vtmp fpointer (vadt :: nil))
      {{ [[adt as aadt]] :: tenv aadt }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply miniChomp'.
  intros.
  rewrite Propagate_ret.
  eauto using CompileCallFacadeImplementationOfDestructor.
Qed.
