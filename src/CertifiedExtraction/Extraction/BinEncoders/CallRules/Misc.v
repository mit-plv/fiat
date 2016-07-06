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
Lemma CompileRead':             (* FIXME move *)
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


Lemma CompileConstant_SCA:
  forall {A} {Wr: FacadeWrapper W A}
    name env (w: A) ext (tenv: Telescope _),
    name ∉ ext ->
    NotInTelescope name tenv ->
    {{ tenv }}
      (Assign name (Const (wrap w)))
    {{ [[`name ->> w as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  rewrite (TelEq_same_wrap w (wrap (FacadeWrapper := Wr) w)) by reflexivity.
  auto using CompileConstant.
Qed.

(* Lemma CompileConstant_SCA:      (* FIXME would it be better to assume that A wraps into W? *) *)
(*   forall {av A} {Wr: FacadeWrapper (Value av) A} *)
(*     name env (w: A) ext (tenv: Telescope av), *)
(*     name ∉ ext -> *)
(*     NotInTelescope name tenv -> *)
(*     (forall a : A, is_adt (wrap a) = false) -> *)
(*     {{ tenv }} *)
(*       (Assign name (Const (match wrap w with SCA w => w | _ => Word.wzero _ end))) *)
(*     {{ [[`name ->> w as _]]::tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   intros * ? ? not_adt; *)
(*     destruct (not_adt_is_sca not_adt) as (skol & Heq). *)
(*   rewrite (Heq w) in *. *)
(*   rewrite (TelEq_same_wrap _ (skol w)) by eauto. *)
(*   apply CompileConstant; assumption. *)
(* Qed. *)
