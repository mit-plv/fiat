Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Extraction.

Definition extract_facade := proj1_sig.

Opaque Word.natToWord.

Definition EmptyEnv : Env unit := (GLabelMap.GLabelMap.empty (FuncSpec unit)).

Example simple :
  Facade program implementing ( x <- ret (SCA unit (Word.natToWord 32 1));
                                y <- ret (SCA unit (Word.natToWord 32 5));
                                ret (SCA _ (Word.wplus (Word.natToWord 32 1) (Word.natToWord 32 5)))) with EmptyEnv.
Proof.
  compile_step.
  compile_step.
  compile_step.

  Lemma CompileConstant :
    forall av env ext prog tenv tenv' name w,
      name ∉ ext ->
      PropertiesOfTelescopes.NotInTelescope name tenv ->
      {{ [[name <-- SCA av w as _]] :: tenv }} prog {{ [[name <-- SCA av w as _]] :: tenv' }} ∪ {{ ext }} // env ->
      {{ tenv }} (Seq (Assign name (Const w)) prog) {{ [[name <-- SCA av w as _]] :: tenv' }} ∪ {{ ext }} // env.
  Proof.
    eauto using Basics.CompileSeq, Basics.CompileConstant.
  Qed.

  apply CompileConstant; try Core.compile_do_side_conditions.

  compile_step.
  compile_step.
  compile_step.
  compile_step.

  apply CompileConstant; try Core.compile_do_side_conditions.

  repeat compile_step.
  repeat compile_step.
  repeat compile_step.
Defined.

Eval simpl in (extract_facade simple).

(******************************************************************************)
(*+ First example: sum two constants! *)

Example simple_binop :
  Facade program implementing ( x <- ret (Word.natToWord 32 1);
                                y <- ret (Word.natToWord 32 5);
                                ret (SCA _ (Word.wplus x y))) with EmptyEnv.
Proof.
  repeat compile_step.
Defined.

Eval simpl in (extract_facade simple_binop).

(******************************************************************************)
(*+ More constants! *)

Example harder_binop :
  Facade program implementing
         ( x <- ret (Word.natToWord 32 1);
           y <- ret (Word.natToWord 32 5);
           z <- ret (Word.natToWord 32 8);
           t <- ret (Word.natToWord 32 12);
           ret (SCA _ (Word.wplus x (Word.wplus z (Word.wminus y t)))))
with EmptyEnv.
Proof.
  repeat compile_step.
Defined.

Eval simpl in (extract_facade harder_binop).

(******************************************************************************)
(*+ We can extend the engine to call
    external functions *)

Require Import
        CertifiedExtraction.CompUtils
        CertifiedExtraction.PropertiesOfTelescopes
        CertifiedExtraction.Extraction.External.Core.

Definition Random := { x: W | True }%comp.

Definition FRandom {av} : AxiomaticSpec av.
Proof. refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ exists w, ret = SCA av w
    |}; spec_t. Defined.

Lemma Random_characterization {av}:
  forall x : W, WrapComp_W Random ↝ SCA av x.
Proof. constructor. Qed.

Hint Immediate Random_characterization : call_helpers_db.

Lemma CompileCallRandom:
  forall {av} (env : GLabelMap.t (FuncSpec av)),
  forall fpointer tenv,
    GLabelMap.MapsTo fpointer (Axiomatic FRandom) env ->
    forall var ext,
      var ∉ ext ->
      NotInTelescope var tenv ->
      {{ tenv }}
        (DFacade.Call var fpointer nil)
      {{ [[ ` var <~~ WrapComp_W Random as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_cleanup_call
         end; facade_eauto.
Qed.

Ltac compile_random :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?tenv, Cons ?s (@WrapComp_W ?av Random) (fun _ => ?tenv)) =>
              let fpointer := find_function_in_env
                               (Axiomatic (@FRandom av)) env in
              apply (CompileCallRandom (fpointer := fpointer))
            end).

(*! We then tell compiler that the definition is available: *)

Definition BasicEnv :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    (GLabelMap.empty (FuncSpec unit)).

(*! And we can now compile programs using that function! *)

Example random_sample :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                ret (SCA _ (Word.wminus (Word.wplus x x)
                                                        (Word.wplus y y))))
with BasicEnv.
Proof.
  repeat (compile_step || compile_random).
Defined.

Eval simpl in (extract_facade random_sample).

(******************************************************************************)
(*+ We also have support for conditionals,
    and external scalar functions *)

Definition Square x :=
  @Word.wmult 32 x x.

Require Import
        CertifiedExtraction.Extraction.External.External
        CertifiedExtraction.Extraction.External.GenericMethods.

Definition EnvWithSquare {av} :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("mylib", "square") (Axiomatic (FacadeImplementationWW av Square)))
       (GLabelMap.empty (FuncSpec av))).

Example random_test :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                z <- Random;
                                ret (SCA unit (if IL.weqb x y then
                                                 (Word.wplus z z)
                                               else
                                                 if IL.wltb x y then
                                                   z
                                                 else
                                                   (Square z)))) with EnvWithSquare.
Proof.
  repeat (compile_step || compile_random).
Defined.

Eval simpl in (extract_facade random_test).

(******************************************************************************)
(*+ And we can easily add more functions *)

Definition Cube (x: W) := (Word.wmult x (Word.wmult x x)).

Definition EnvWithCubeAsWell {av} :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("mylib", "square") (Axiomatic (FacadeImplementationWW av Square)))
       ((GLabelMap.add ("mylib", "cube") (Axiomatic (FacadeImplementationWW av Cube)))
          (GLabelMap.empty (FuncSpec av)))).

Example random_test_with_cube :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                z <- Random;
                                ret (SCA unit (if IL.weqb x y then
                                                 (Word.wplus z z)
                                               else
                                                 if IL.wltb x y then
                                                   z
                                                 else
                                                   (Cube z)))) with EnvWithCubeAsWell.
Proof.
  repeat (compile_step || compile_random).
Defined.

Eval simpl in (extract_facade random_test_with_cube).

(******************************************************************************)
(*+ To conclude, a bit of ADT stuff: *)

Definition MyEnvW :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("std", "nil") (Axiomatic (FacadeImplementationOfConstructor nil)))
       ((GLabelMap.add ("std", "push") (Axiomatic (FacadeImplementationOfMutation cons)))
          (GLabelMap.empty _))).

(******************************************************************************)
(*+ This example returns a list containing
    a semi-random number > 0 *)

Example random_test_with_adt :
  Facade program implementing ( x <- Random;
                                ret (ADT (if IL.weqb x 0 then
                                            (Word.natToWord 32 1 : W) :: nil
                                          else
                                            x :: nil))) with MyEnvW.
Proof.
  repeat (compile_step || compile_random || compile_constructor || compile_mutation_alloc).
Defined.

Eval simpl in (extract_facade random_test_with_adt).

(******************************************************************************)

Example test_with_adt :
    sigT (fun prog => forall tail, {{ [[`"ret"  <~~  ret (ADT tail) as _ ]] :: Nil }}
                             prog
                           {{ [[`"ret"  <~~  ( x <- Random;
                                             ret (ADT (x :: tail))) as _]] :: Nil }} ∪ {{ ∅ }}
                           // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_random || compile_mutation_replace || compile_step).
Defined.

Eval simpl in (extract_facade test_with_adt).

(******************************************************************************)
(*+ Most exciting example yet:
    - Sample two numbers,
    - take the smallest one,
    - push it into a list *)

Example other_test_with_adt :
    sigT (fun prog => forall seq, {{ [[`"ret" <~~ ret (ADT seq) as _ ]] :: Nil }}
                            prog
                          {{ [[`"ret" <~~ ( x <- Random;
                                          y <- Random;
                                          ret (ADT ((if IL.wltb x y then x else y) :: seq))) as _]] :: Nil }} ∪ {{ ∅ }} // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_step || compile_random || compile_mutation_replace).
Defined.

Eval simpl in (extract_facade other_test_with_adt).

(******************************************************************************)
Example other_test_with_adt' :
    sigT (fun prog => forall seq, {{ [[`"ret" <~~ ret (ADT seq) as _ ]] :: Nil }}
                            prog
                          {{ [[`"ret" <~~ ( x <- Random;
                                          y <- Random;
                                          ret (ADT (if IL.wltb x y then x :: seq else y :: seq))) as _]] :: Nil }} ∪ {{ ∅ }} // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_step || compile_random || compile_mutation_replace).
Defined.

Eval simpl in (extract_facade other_test_with_adt').
