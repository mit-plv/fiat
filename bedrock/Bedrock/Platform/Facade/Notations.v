Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.DFacade.
Require Import Bedrock.Platform.Cito.NotationsExpr.
Export NotationsExpr.

Require Import Bedrock.Memory Bedrock.IL.

Coercion natToW : nat >-> W.

Require Import Bedrock.Platform.Facade.Listy.
Import Listy.Notations.
Export Listy.Notations.
Import BeginEndNotation.
Import Instances.
Export Instances.
Local Open Scope listy_scope.

Instance seq_Listy : Listy Stmt Stmt := {
  Nil := DFacade.Skip;
  Cons := DFacade.Seq
}.

(* for some reason typeclass inference needs to redeclare this instance *)
Existing Instance list_Listy.

(* for free-standing stmt seq *)
Infix ";;" := DFacade.Seq (right associativity, at level 95) : dfacade_scope.

Delimit Scope dfacade_scope with dfacade.
Local Open Scope dfacade_scope.

Notation skip := DFacade.Skip.

Notation if_ := DFacade.If.

Notation while_ := DFacade.While.

Notation "x <- e" := (DFacade.Assign x e) (no associativity, at level 90) : dfacade_scope.

Notation "'call_' f ()" := (DFacade.Call "_tmp" f nil)
  (no associativity, at level 95, f at level 0) : dfacade_scope.

Notation "'call_' f ( x1 , .. , xN )" := (DFacade.Call "_tmp" f (cons x1 (.. (cons xN nil) ..))) (no associativity, at level 95, f at level 0) : dfacade_scope.

Notation "x <-- 'call_' f ()" := (DFacade.Call x f nil)
  (no associativity, at level 95, f at level 0) : dfacade_scope.

Notation "x <-- 'call_' f ( x1 , .. , xN )" := (DFacade.Call x f (cons x1 (.. (cons xN nil) ..))) (no associativity, at level 95, f at level 0) : dfacade_scope.

Notation "a ! b" := (a, b) (at level 0, only parsing) : dfacade_scope.

Local Open Scope expr_scope.
Local Open Scope string_scope.

(* can mix { a ; b } and ( a ;; b ) *)
Definition test_stmt :=
  "x" <- 1;;
  "y" <- 2;;
  if_ ("x" < "y") {
    "x" <- "y";
    "y" <- "y" * 2
  }{
    skip
  };;
  while_ ("x" <> 0) (
    "y" <- "y" + 1 ;;
    "x" <- "x" - 1
  );;
  "ret" <-- call_ "m"!"f" ("x", "y").

Definition test_ls := {1;2;3}.
Definition test_ls2 := {"1";"2";"3"}.
Definition test_ls3 := { ("a", {"x" <- 1; "y" <- 2}); ("b", {"x" <- 1; "y" <- 2}); ("c", {"x" <- 1; "y" <- 2}) }.

Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list_scope.
Require Import Bedrock.Platform.Cito.ListNotationsFix.
Export ListNotationsFix.
Require Import Bedrock.Platform.Facade.DFModule.

Local Open Scope dfacade_scope.

Notation "'func' () b" :=
  (Build_DFFun (Build_OperationalSpec nil "ret" b eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) eq_refl) (no associativity, at level 95, only parsing) : dfacade_scope.

Notation "'func' ( x , .. , y ) b" :=
  (Build_DFFun (Build_OperationalSpec (cons x (.. (cons y nil) ..)) "ret" b eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) eq_refl) (no associativity, at level 95, only parsing) : dfacade_scope.

Definition test_f :=
  func(){
    "ret" <- 0
  }.

Definition test_2 :=
  func() begin
    "ret" <- 0
  end.

(* notations for pairs *)
Notation "'def' name = v" := (pair name v) (no associativity, at level 95, name at level 0, only parsing) : dfacade_scope.
Infix "==>" := pair (no associativity, at level 95, only parsing) : dfacade_scope.
Infix "::=" := pair (no associativity, at level 95, only parsing) : dfacade_scope.

(* notations for lists *)
Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : dfacade_scope.

Definition test_name_f :=
  def "test" = func(){
    "ret" <- 0
  }.

Require Import Bedrock.Platform.Cito.StringMapFacts.
Require Import Bedrock.Platform.Cito.GLabelMapFacts.

Notation "'module' 'import' imps 'define' fs" :=
  (Build_DFModule (GLabelMapFacts.of_list imps) (StringMapFacts.of_list fs)) (no associativity, at level 95, only parsing) : dfacade_scope.

Section Test.

  Variable ADTValue : Type.
  Variables ArraySeq_newSpec ArraySeq_writeSpec ArraySeq_readSpec ArraySeq_deleteSpec ListSet_newSpec ListSet_addSpec ListSet_sizeSpec ListSet_deleteSpec : AxiomaticSpec ADTValue.

  Definition test_m :=
    module
    import {
      "ADT"!"ArraySeq_new" ==> ArraySeq_newSpec;
      "ADT"!"ListSet_delete" ==> ListSet_deleteSpec
    }
    define {
      def "f1" = func() begin
        "ret" <- 0
      end;
      def "f2" = func("a", "b"){
        "x" <- 2;
        "y" <- "b";
        if_ ("x" < "y") {
          "x" <- "y";
          "y" <- "y" * 2
        }{
          skip
        };
        while_ ("x" <> 0) {
          "y" <- "y" + 1 ;;
          "x" <- "x" - 1
        };
        "ret" <-- call_ "m"!"f" ("x", "y")
      };
      def "f3" = test_f;
      test_name_f;
      "f5" ::= func(){
        test_stmt
      }
    }.

  Definition test_m2 :=
    module
    import {
      "ADT"!"ArraySeq_new" ==> ArraySeq_newSpec;
      "ADT"!"ArraySeq_write" ==> ArraySeq_writeSpec;
      "ADT"!"ArraySeq_read" ==> ArraySeq_readSpec;
      "ADT"!"ArraySeq_delete" ==> ArraySeq_deleteSpec;
      "ADT"!"ListSet_new" ==> ListSet_newSpec;
      "ADT"!"ListSet_add" ==> ListSet_addSpec;
      "ADT"!"ListSet_size" ==> ListSet_sizeSpec;
      "ADT"!"ListSet_delete" ==> ListSet_deleteSpec
    }
    define {
      def "count" = func("arr", "len"){
        "set" <-- call_ "ADT"!"ListSet_new"();
        "i" <- 0;
        while_ ("i" < "len") {
          "e" <-- call_ "ADT"!"ArraySeq_read" ("arr", "i");
          call_ "ADT"!"ListSet_add"("set", "e");
          "i" <- "i" + 1
        };
        "ret" <-- call_ "ADT"!"ListSet_size"("set");
        call_ "ADT"!"ListSet_delete"("set")
      };
      def "main" = func(){
(*
        "arr" <-- call_ "ADT"!"ArraySeq_new"(3);;
        call_ "ADT"!"ArraySeq_write"("arr", 0, 10);;
        call_ "ADT"!"ArraySeq_write"("arr", 1, 20);;
        call_ "ADT"!"ArraySeq_write"("arr", 2, 10);;
        "ret" <-- call_ "count"!"count" ("arr", 3);;
        call_ "ADT"!"ArraySeq_delete"("arr")
*)
        "ret" <- 0
      }
    }.

  Definition test_ms := {
    def "m1" = test_m;
    def "m2" = test_m2
  }.

End Test.

Module OpenScopes.
  Open Scope listy_scope.
  Open Scope dfacade_scope.
  Open Scope expr_scope.
  Open Scope string_scope.
End OpenScopes.
