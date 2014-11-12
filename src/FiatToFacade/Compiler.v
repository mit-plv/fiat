Require Export
        FiatToFacade.Compiler.Prerequisites
        FiatToFacade.Compiler.Utilities
        FiatToFacade.Compiler.Basics
        FiatToFacade.Compiler.Constants
        FiatToFacade.Compiler.NoOp
        FiatToFacade.Compiler.Copy
        FiatToFacade.Compiler.Binops
        FiatToFacade.Compiler.Pairs
        FiatToFacade.Compiler.Cleanup
        FiatToFacade.Compiler.Conditionals
        FiatToFacade.Compiler.ADTs.Folds
        FiatToFacade.Compiler.ADTs.Lists
        FiatToFacade.Compiler.ADTs.ListsInversion
        FiatToFacade.Compiler.ADTs.FiniteSets.

Require Export Common.
Require Export Cito.StringMap.
Require Export Cito.GLabelMap.
Require Export Facade.Facade.
Require Export Facade.DFacade.
Require Export Facade.examples.FiatADTs.

Unset Implicit Arguments.

Definition MakePair {elt} (k: GLabel.glabel) (v: elt) :=
  (k, v).

Definition AddPair {elt} pair m :=
  @GLabelMap.add elt (fst pair) (snd pair) m.

Notation "[[[ p1 ; .. ; pn ]]]" :=
  (AddPair p1 .. (AddPair pn (GLabelMap.empty _)) ..).

Notation "k ⇥ v" :=
  (MakePair k v) (at level 55, no associativity).

Notation "k ↦ v" :=
  (MakePair k (Axiomatic v)) (at level 55, no associativity).

Definition empty_env {av} := GLabelMap.empty (FuncSpec av).

Definition basic_imports := [[[ ("ADT", "empty") ⇥ List_empty;
                                ("ADT", "pop") ⇥ List_pop;
                                ("ADT", "new") ⇥ List_new;
                                ("ADT", "push") ⇥ List_push;
                                ("ADT", "copy") ⇥ List_copy;
                                ("ADT", "delete") ⇥ List_delete;
                                ("ADT", "rev") ⇥ List_rev;
                                ("ADT", "sEmpty") ⇥ FEnsemble_sEmpty;
                                ("ADT", "sAdd") ⇥ FEnsemble_sAdd;
                                ("ADT", "sRemove") ⇥ FEnsemble_sRemove;
                                ("ADT", "sDelete") ⇥ FEnsemble_sDelete;
                                ("ADT", "sIn") ⇥ FEnsemble_sIn;
                                ("ADT", "sSize") ⇥ FEnsemble_sSize
                              ]]].

Definition basic_imports_wrapped := (GLabelMap.map (@Axiomatic _) basic_imports).

Definition basic_env := [[[ ("ADT", "empty") ↦ List_empty;
                            ("ADT", "pop") ↦ List_pop;
                            ("ADT", "new") ↦ List_new;
                            ("ADT", "push") ↦ List_push;
                            ("ADT", "copy") ↦ List_copy;
                            ("ADT", "delete") ↦ List_delete;
                            ("ADT", "rev") ↦ List_rev;
                            ("ADT", "sEmpty") ↦ FEnsemble_sEmpty;
                            ("ADT", "sAdd") ↦ FEnsemble_sAdd;
                            ("ADT", "sRemove") ↦ FEnsemble_sRemove;
                            ("ADT", "sDelete") ↦ FEnsemble_sDelete;
                            ("ADT", "sIn") ↦ FEnsemble_sIn;
                            ("ADT", "sSize") ↦ FEnsemble_sSize
                          ]]].

Require Import Cito.GLabelMapFacts.

Lemma basic_imports_yield_basic_env :
  GLabelMap.Equal basic_imports_wrapped basic_env.
Proof.
  unfold basic_imports_wrapped, basic_imports, basic_env.

  repeat (etransitivity; [ apply GLabelMapFacts.map_add | ];
          apply GLabelMapFacts.F.add_m; try reflexivity).
  apply map_empty.
Qed.

Definition start_adt state vret {ret_type v} wrapper wrapper_inj adts :=
  (@start_compiling_adt_with_precondition _ basic_env state ∅ adts vret ret_type v wrapper wrapper_inj).

Definition start_sca state vret adts :=
  (@start_compiling_sca_with_precondition _ basic_env state ∅ adts vret).
