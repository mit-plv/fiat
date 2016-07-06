Require Export
        Fiat.CertifiedExtraction.Extraction.Extraction.

Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties.

Require Import
        Coq.Program.Program
        Coq.Lists.List.

Unset Implicit Arguments.

(* Lemma CompileCallAllocOffset: *)
(*   forall (vtmp voffset: string) (tenv tenv' : Telescope ADTValue) *)
(*     ext env pNext fAllocCache, *)
(*     {{ [[ ` voffset ->> 0%N as _]]::tenv }} *)
(*       pNext *)
(*     {{ [[ ` voffset ->> 0%N as _]]::tenv' }} ∪ {{ ext }} // env -> *)
(*     {{ tenv }} *)
(*       Seq (Call vtmp fAllocCache [voffset]) pNext *)
(*     {{ [[ ` voffset ->> 0%N as _]]::tenv' }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   hoare; hoare. *)
(* Admitted. *)

(* (* FIXME there should be a generic wrapper for list of SCA-injected things *) *)
(* Lemma CompileCallListSCALength {A} {W: FacadeWrapper (Value ADTValue) (list A)}: *)
(*   forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue)) *)
(*     env (lst : FixList.FixList 8 A) *)
(*     fLength tenv', *)
(*     GLabelMap.MapsTo fLength (Axiomatic WordListADTSpec.Length) env -> *)
(*     TelEq ext tenv ([[`vlst ->> `lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *) *)
(*     {{ tenv }} *)
(*       Call varg fLength [vlst] *)
(*     {{ [[ ` varg ->> FixList.FixList_getlength lst as _]]::tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(* Admitted. *)

Ltac _encode_FixInt :=
  match_ProgOk                  (* FIXME check when this is needed *)
    ltac:(fun prog pre post ext env =>
            match post with
            | [[ret (FixInt.FixInt_encode _ _) as _]] :: _ =>
              rewrite FixInt_encode_is_copy; (* FIXME make this an autorewrite *)
              setoid_rewrite Propagate_anonymous_ret; simpl;
              apply ProgOk_Transitivity_First
            end).
(* Ltac _compile_CallAllocOffset := *)
(*   may_alloc_head; *)
(*   let vtmp := gensym "tmp" in *)
(*   eapply (CompileCallAllocOffset vtmp). *)

(* Require Import Bedrock.Word. *)

Lemma not_adt_is_sca :
  forall {A} `{FacadeWrapper (Value av) A},
    (forall (a: A), is_adt (wrap a) = false) ->
    exists w, (forall a, wrap a = SCA _ (w a)).
Proof.
  intros.
  exists (fun a => match wrap a with SCA x => x | _ => Word.wzero 32 end).
  intros; specialize (H0 a);
    destruct (wrap a); unfold is_adt in *; congruence.
Qed.

(* FIXME Replace this formulation with is_adt (wrap a) = false by one based on WrapSCA *)
Lemma CompileRead':
  forall {A} `{FacadeWrapper (Value av) A}
    (vfrom vto : string) (a: A)
    (tenv tenv0: Telescope av) ext env,
    (* vfrom ∉ ext -> *)
    vto ∉ ext ->
    vfrom <> vto ->
    NotInTelescope vto tenv0 ->
    (forall a, is_adt (wrap a) = false) ->
    TelEq ext tenv ([[` vfrom ->> a as _]] :: tenv0) ->
    {{ tenv }}
      Assign vto (Var vfrom)
    {{ [[ ` vto ->> a as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? ? ? H; setoid_rewrite H.
  destruct (not_adt_is_sca H4).
  SameValues_Facade_t.
  f_equal; auto.
  match goal with
  | [ H: wrap _ = wrap _ |- _ ] => rewrite H
  end; SameValues_Facade_t.
Qed.

Ltac _compile_Read :=
  may_alloc_head;
  match_ProgOk
    ltac:(fun _ pre post _ _ =>
            lazymatch post with
            | [[ _ ->> ?bs as _]] :: _ =>
              let k := find_name_in_precondition bs in
              eapply (CompileRead' k)
            end).

(* Lemma CompileConstantN : *)
(*   forall {av} {W: FacadeWrapper (Value av) N} *)
(*     N (vto : string) *)
(*     (tenv tenv': Telescope av) pNext ext env, *)
(*     {{ [[ ` vto ->> N as _]]::tenv }} *)
(*       pNext *)
(*     {{ [[ ` vto ->> N as _]]::tenv' }} ∪ {{ ext }} // env -> *)
(*     {{ tenv }} *)
(*       Seq (Assign vto (Const (@Word.NToWord _ N))) pNext *)
(*     {{ [[ ` vto ->> N as _]]::tenv' }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   hoare. *)
(*   hoare. *)
(* Admitted. *)

(* Ltac _compile_ReadConstantN := *)
(*   may_alloc_head; *)
(*   eapply CompileConstantN. *)
