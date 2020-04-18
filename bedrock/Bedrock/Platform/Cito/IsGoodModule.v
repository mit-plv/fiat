Set Implicit Arguments.

Require Import Coq.Program.Basics.

Local Infix "*" := compose.

Require Import Bedrock.Platform.Cito.SyntaxModule.
Require Import Bedrock.Platform.Cito.GoodModule.
Require Import Bedrock.Platform.Cito.GoodFunc.
Require Import Bedrock.Platform.Cito.GoodFunction.
Require Import Bedrock.Platform.Cito.NameDecoration.

Notation MName := SyntaxModule.Name.
Notation FName := SyntaxFunc.Name.
Notation Funcs := SyntaxModule.Functions.
Notation GName := GoodModule.Name.

Definition IsGoodModule (m : Module) :=
  IsGoodModuleName (MName m) /\
  List.Forall (GoodFunc * Core) (Funcs m) /\
  List.NoDup (List.map FName (Funcs m)).

Definition to_good_functions : forall (ls : list Func), List.Forall (GoodFunc * Core) ls -> list GoodFunction.
  refine (fix F (ls : list Func) : List.Forall (GoodFunc * Core) ls -> list GoodFunction :=
    match ls with
      | nil => fun _ => nil
      | a :: ls => fun H => {| Fun := a |} :: F ls _
    end); clear F; abstract (inversion_clear H; auto).
Defined.

Lemma to_good_functions_name : forall ls (h : List.Forall (GoodFunc * Core) ls), map (fun f : GoodFunction => FName f) (to_good_functions h) = map FName ls.
  induction ls; simpl; intros.
  eauto.
  f_equal; eauto.
Qed.

Require Import Bedrock.Platform.Cito.GeneralTactics.

Definition to_good_functions' (m : Module) : IsGoodModule m -> list GoodFunction.
  intros.
  refine
    (@to_good_functions (Funcs m) _).
  abstract (unfold IsGoodModule in *; openhyp;
    eauto).
Defined.

Definition to_good_module (m : Module) : IsGoodModule m -> GoodModule.
  intros.
  refine
    ({|
        GoodModule.Name := MName m;
        GoodModuleName := _;
        Functions := to_good_functions' H;
        NoDupFuncNames := _
      |}).
  abstract (unfold IsGoodModule in *; openhyp;
    eauto).
  abstract (unfold IsGoodModule in *; openhyp;
    unfold to_good_functions';
      rewrite to_good_functions_name; eauto).
Defined.

Definition to_module (m : GoodModule) : Module :=
  {|
    SyntaxModule.Name := GoodModule.Name m;
    SyntaxModule.Functions := map GoodFunction.Fun (GoodModule.Functions m)
  |}.

Coercion to_module : GoodModule >-> Module.
