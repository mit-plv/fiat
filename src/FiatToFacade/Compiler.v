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
Require Export Facade.Facade.
Require Export Facade.DFacade.
Require Export Facade.examples.FiatADTs.
Require Export Cito.StringMap.
Require Export Cito.GLabelMap.

Definition AddPair {av} pair m :=
  @GLabelMap.add (FuncSpec av) (fst pair) (snd pair) m.

Definition MakePair {av} (k: GLabel.glabel) (v: AxiomaticSpec av) :=
  (k, Axiomatic v).

Notation "[[[ p1 ; .. ; pn ]]]" :=
  (AddPair p1 .. (AddPair pn (GLabelMap.empty _)) ..).

Notation "k ↦ v" :=
  (MakePair k v) (at level 55, no associativity).

Definition empty_env {av} := GLabelMap.empty (FuncSpec av).

Definition basic_env := [[[ ("List", "Empty") ↦ List_empty;
                            ("List", "Pop") ↦ List_pop;
                            ("List", "New") ↦ List_new;
                            ("List", "Push") ↦ List_push;
                            ("List", "Copy") ↦ List_copy;
                            ("List", "Delete") ↦ List_delete;
                            ("FSet", "Empty") ↦ FEnsemble_sEmpty;
                            ("FSet", "Add") ↦ FEnsemble_sAdd;
                            ("FSet", "Remove") ↦ FEnsemble_sRemove;
                            ("FSet", "Delete") ↦ FEnsemble_sDelete;
                            ("FSet", "In") ↦ FEnsemble_sIn;
                            ("FSet", "Size") ↦ FEnsemble_sSize
                          ]]].

Unset Implicit Arguments.

Definition start_adt state vret {ret_type v} wrapper wrapper_inj adts :=
  (@start_compiling_adt_with_precondition _ basic_env state ∅ adts vret ret_type v wrapper wrapper_inj).

Definition start_sca state vret adts :=
  (@start_compiling_sca_with_precondition _ basic_env state ∅ adts vret).

Notation refine' := refine.