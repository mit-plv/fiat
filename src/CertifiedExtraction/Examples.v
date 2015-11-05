Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Extraction.

Definition extract_facade := proj1_sig.

Opaque Word.natToWord.

Definition EmptyEnv : Env unit := (GLabelMap.GLabelMap.empty (FuncSpec unit)).

Example simple :
  Facade program implementing ( x <- ret (Word.natToWord 32 1);
                                y <- ret (Word.natToWord 32 5);
                                ret (Word.wplus (Word.natToWord 32 1) (Word.natToWord 32 5))) with EmptyEnv.
Proof.
  repeat compile_step.
Defined.

Eval simpl in (extract_facade simple).

(******************************************************************************)
(*+ First example: sum two constants! *)

Example simple_binop :
  Facade program implementing ( x <- ret (Word.natToWord 32 1);
                                y <- ret (Word.natToWord 32 5);
                                ret (Word.wplus x y)) with EmptyEnv.
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
           ret (Word.wplus x (Word.wplus z (Word.wminus y t))))
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

Lemma Random_characterization:
  forall x : W, Random ↝ x.
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
      {{ [[ ` var <~~ Random as _]] :: tenv }} ∪ {{ ext }} // env.
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
            | (?tenv, Cons (av := ?av) ?s Random ?tenv') =>
              let fpointer := find_function_in_env (Axiomatic (@FRandom av)) env in
               call_tactic_after_moving_head_binding_to_separate_goal
                ltac:(apply (CompileCallRandom (fpointer := fpointer)))
            end).

(*! We then tell compiler that the definition is available: *)

Definition BasicEnv :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    (GLabelMap.empty (FuncSpec unit)).

(*! And we can now compile programs using that function! *)

Example random_sample :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                ret (Word.wminus (Word.wplus x x)
                                                 (Word.wplus y y)))
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

Definition EnvWithSquare :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("mylib", "square") (Axiomatic (FacadeImplementationWW unit Square)))
       (GLabelMap.empty (FuncSpec unit))).

Example random_test :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                z <- Random;
                                ret (if IL.weqb x y then
                                       (Word.wplus z z)
                                     else
                                       if IL.wltb x y then
                                         z
                                       else
                                         (Square z))) with EnvWithSquare.
Proof.
  repeat (compile_step || compile_random).
Defined.

Eval simpl in (extract_facade random_test).

(******************************************************************************)
(*+ And we can easily add more functions *)

Definition Cube (x: W) := (Word.wmult x (Word.wmult x x)).

Definition EnvWithCubeAsWell :=
  (GLabelMap.add ("std", "rand") (Axiomatic FRandom))
    ((GLabelMap.add ("mylib", "square") (Axiomatic (FacadeImplementationWW unit Square)))
       ((GLabelMap.add ("mylib", "cube") (Axiomatic (FacadeImplementationWW unit Cube)))
          (GLabelMap.empty (FuncSpec unit)))).

Example random_test_with_cube :
  Facade program implementing ( x <- Random;
                                y <- Random;
                                z <- Random;
                                ret (if IL.weqb x y then
                                       (Word.wplus z z)
                                     else
                                       if IL.wltb x y then
                                         z
                                       else
                                         (Cube z))) with EnvWithCubeAsWell.
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
          (GLabelMap.empty (FuncSpec (list W))))).

(******************************************************************************)
(*+ This example returns a list containing
    a semi-random number > 0 *)

Example random_test_with_adt :
  Facade program implementing ( x <- Random;
                                ret (if IL.weqb x 0 then
                                       (Word.natToWord 32 1 : W) :: nil
                                     else
                                       x :: nil)) with MyEnvW.
Proof.
  repeat (compile_step || compile_random || compile_constructor || compile_mutation_alloc).
Defined.

Ltac pose_ProgOk _prog _pre _post _ext _env := (* FIXME move *)
  let pre := fresh "pre" in pose _pre as pre;
    let post := fresh "post" in pose _post as post;
      let ext := fresh "ext" in pose _ext as ext;
        let env := fresh "env" in pose _env as env;
          let prog := fresh "prog" in pose _prog as prog.

Eval simpl in (extract_facade random_test_with_adt).

(******************************************************************************)

Example test_with_adt :
    sigT (fun prog => forall tail, {{ [[`"ret"  <~~  ret tail as _ ]] :: Nil }}
                             prog
                           {{ [[`"ret"  <~~  ( x <- Random;
                                             ret (x :: tail)) as _]] :: Nil }} ∪ {{ ∅ }}
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
    sigT (fun prog => forall seq, {{ [[`"ret" <~~ ret seq as _ ]] :: Nil }}
                            prog
                          {{ [[`"ret" <~~ ( x <- Random;
                                          y <- Random;
                                          ret ((if IL.wltb x y then x else y) :: seq)) as _]] :: Nil }} ∪ {{ ∅ }} // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_step || compile_random || compile_mutation_replace).
Defined.

Eval simpl in (extract_facade other_test_with_adt).

(******************************************************************************)
Example other_test_with_adt' :
    sigT (fun prog => forall seq, {{ [[`"ret" <~~ ret seq as _ ]] :: Nil }}
                            prog
                          {{ [[`"ret" <~~ ( x <- Random;
                                          y <- Random;
                                          ret (if IL.wltb x y then x :: seq else y :: seq)) as _]] :: Nil }} ∪ {{ ∅ }} // MyEnvW).
Proof.
  econstructor; intros.
  repeat (compile_step || compile_random || compile_mutation_replace).
Defined.

Eval simpl in (extract_facade other_test_with_adt').
