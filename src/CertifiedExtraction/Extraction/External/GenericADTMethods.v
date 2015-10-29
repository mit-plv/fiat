Require Import
        Coq.Lists.List
        CertifiedExtraction.Extraction.External.Core.

(* Weak version: should talk about injecting in and projecting out of the main type *)
Definition FacadeImplementationOfMutation av (fAA: W -> av -> av) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists w x, args = (ADT x) :: (SCA _ w) :: nil;
      PostCond := fun args ret => exists w x, args = (ADT x, Some (fAA w x)) :: (SCA _ w, None) :: nil /\ ret = SCA _ (Word.natToWord 32 0)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfConstructor av (fAA: av) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ ret = (ADT fAA)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfCopy av : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x, args = (ADT x) :: nil;
      PostCond := fun args ret => exists x, args = (ADT x, Some x) :: nil /\ ret = (ADT x)
    |}; spec_t.
Defined.

Definition FacadeImplementationOfDestructor av : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x, args = (ADT x) :: nil;
      PostCond := fun args ret => exists x, args = (ADT x, None) :: nil /\ ret = SCA _ (Word.natToWord 32 0)
    |}; spec_t.
Defined.


Lemma SameValues_Mutation_helper:
  forall (av : Type) (vsrc vret : StringMap.key)
    (ext : StringMap.t (Value av)) (tenv : Telescope av)
    (initial_state : State av) (x : av),
    vret <> vsrc ->
    vret ∉ ext ->
    NotInTelescope vret tenv ->
    StringMap.MapsTo vsrc (ADT x) initial_state ->
    initial_state ≲ tenv ∪ ext ->
    [vsrc <-- ADT x]::M.remove vret initial_state ≲ tenv ∪ ext.
Proof.
  intros.
  repeat match goal with
         | _ => rewrite <- remove_add_comm by congruence
         | [ H: StringMap.MapsTo ?k ?v ?st |- context[StringMap.add ?k ?v ?st] ] => rewrite <- (add_redundant_cancel H)
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Hint Resolve SameValues_Mutation_helper : call_helpers_db.

Lemma CompileCallFacadeImplementationOfCopy:
  forall {av} {env},
  forall fpointer vsrc,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfCopy av)) env ->
    forall vret adt ext tenv,
      vret <> vsrc ->
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      StringMap.MapsTo vsrc (ADT adt) ext ->
      {{ tenv }}
        (Call vret fpointer (vsrc :: nil))
      {{ [[ vret <-- ADT adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfMutation_Alloc:
  forall {av} {env} fADT,
  forall fpointer varg vtmp (SCAarg: W) ADTarg tenv,
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
      {{ [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ varg <-- SCA _ SCAarg as _]] :: tenv }}
        pADT
      {{ [[ varg <-- SCA _ SCAarg as _]] :: [[ vret <-- ADT ADTarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq pSCA (Seq pADT (Call vtmp fpointer (vret :: varg :: nil)))
      {{ [[ vret <-- ADT (fADT SCAarg ADTarg) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

(* Lemma CompileCallFacadeImplementationOfMutationB: *)
(*   forall {av} {env} fADT, *)
(*   forall fpointer varg vtmp (SCAarg: W) (ADTarg: av) tenv, *)
(*     GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfMutation fADT)) env -> *)
(*     forall vret ext pSCA, *)
(*       vret <> varg -> *)
(*       vtmp <> varg -> *)
(*       vtmp <> vret -> *)
(*       vret ∉ ext -> *)
(*       vtmp ∉ ext -> *)
(*       varg ∉ ext -> *)
(*       NotInTelescope vret tenv -> *)
(*       NotInTelescope vtmp tenv -> *)
(*       NotInTelescope varg tenv -> *)
(*       {{ [[ vret <-- ADT ADTarg as _]] :: tenv }} *)
(*         pSCA *)
(*       {{ [[ vret <-- ADT ADTarg as _]] :: [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env -> *)
(*       {{ [[ vret <-- ADT ADTarg as _]] :: tenv }} *)
(*         Seq pSCA (Call vtmp fpointer (vret :: varg :: nil)) *)
(*       {{ [[ vret <-- ADT (fADT SCAarg ADTarg) as _]] :: [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   repeat match goal with *)
(*          | _ => SameValues_Facade_t_step *)
(*          | _ => facade_cleanup_call *)
(*          end. *)
(* Qed. *)

Lemma CompileCallFacadeImplementationOfMutation_Replace:
  forall {av} {env} fADT,
  forall fpointer varg vtmp (SCAarg: W) (ADTarg: av) tenv,
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
      {{ [[ vret <-- ADT ADTarg as _]] :: tenv }}
        pSCA
      {{ [[ vret <-- ADT ADTarg as _]] :: [[ varg <-- SCA _ SCAarg as _]] :: tenv }} ∪ {{ ext }} // env ->
      {{ [[ vret <-- ADT ADTarg as _]] :: tenv }}
        Seq pSCA (Call vtmp fpointer (vret :: varg :: nil))
      {{ [[ vret <-- ADT (fADT SCAarg ADTarg) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfConstructor:
  forall {av} {env} adt tenv,
  forall fpointer,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfConstructor adt)) env ->
    forall vret ext,
      vret ∉ ext ->
      NotInTelescope vret tenv ->
      {{ tenv }}
        (Call vret fpointer nil)
      {{ [[ vret <-- @ADT av adt as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Lemma CompileCallFacadeImplementationOfDestructor:
  forall {av} {env} fpointer vtmp adt tenv,
    GLabelMap.MapsTo fpointer (Axiomatic (FacadeImplementationOfDestructor av)) env ->
    forall vadt ext,
      vtmp <> vadt ->
      vtmp ∉ ext ->
      NotInTelescope vtmp tenv ->
      vadt ∉ ext ->
      NotInTelescope vadt tenv ->
      {{ [[ vadt <-- @ADT av adt as _]] :: tenv }}
        (Call vtmp fpointer (vadt :: nil))
      {{ tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.
