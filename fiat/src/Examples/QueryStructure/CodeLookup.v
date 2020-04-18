Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition CLASSES := "Classes".
Definition METHODS := "Methods".
Definition CLASSES_METHODS := "Classes_Methods".

Definition CLASS_NAME := "ClassName".
Definition METHOD_NAME := "MethodName".
Definition PACKAGE_NAME := "PackageName".
Definition RETURN_TYPE := "ReturnType".

Definition CodeLookupSchema :=
  Query Structure Schema
        [ relation CLASSES has
                   schema <CLASS_NAME :: string,
                           PACKAGE_NAME :: string>;
          relation METHODS has
                   schema <METHOD_NAME :: string,
                           RETURN_TYPE :: string>;
          relation CLASSES_METHODS has
                   schema <CLASS_NAME :: string,
                           METHOD_NAME :: string> ]
  enforcing [ attribute CLASS_NAME for CLASSES_METHODS references CLASSES;
              attribute METHOD_NAME for CLASSES_METHODS references METHODS ].

Definition CodeLookupSig : ADTSig :=
  ADTsignature {
      Constructor "Init"
             : unit -> rep,
      Method "AddClass"
             : rep x (CodeLookupSchema#CLASSES) -> rep x bool,
      Method "AddMethod"
             : rep x (CodeLookupSchema#METHODS) -> rep x bool,
      Method "AddRelation"
             : rep x (CodeLookupSchema#CLASSES_METHODS) -> rep x bool(*,
      (* Suggest methods from a package with a specific return type  *)
      Method "SuggestMethods"
             : rep x (string * string) -> rep x list name,
      (* Suggest methods using prefix match *)
      Method "AutocompleteMethods"
             : rep x string -> rep x list string*)
  }.

Definition CodeLookupSpec : ADT CodeLookupSig :=
  QueryADTRep CodeLookupSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddClass" (r : rep, class : CodeLookupSchema#CLASSES) : bool :=
      Insert class into r!CLASSES,

    update "AddMethod" (r : rep, method : CodeLookupSchema#METHODS) : bool :=
      Insert method into r!METHODS,

    update "AddRelation" (r : rep, rel : CodeLookupSchema#CLASSES_METHODS) : bool :=
      Insert rel into r!CLASSES_METHODS(*,

    query "SuggestMethods" (r : rep, package_rtype : string * string) : list name :=
      For (c in r!CLASSES)
          (rel in r!CLASSES_METHODS)
          (m in r!METHODS)
          Where (c!PACKAGE_NAME = fst package_rtype)
          Where (rel!CLASS_NAME = c!CLASS_NAME)
          Where (m!METHOD_NAME = rel!METHOD_NAME)
          Where (m!RETURN_TYPE = snd package_rtype)
          Return (c!CLASS_NAME ++ ["."]%char ++ m!METHOD_NAME)%list, 

    query "AutocompleteMethods" (r : rep, prefix : string) : list string :=
      For (m in r!METHODS)
          Return m!METHOD_NAME*)
   }.

Definition SharpenedCodeLookup :
  FullySharpened CodeLookupSpec.
Proof.
  master_plan EqIndexTactics.
Time Defined.

Time Definition CodeLookupImpl : ComputationalADT.cADT CodeLookupSig :=
  Eval simpl in projT1 SharpenedCodeLookup.

Print CodeLookupImpl.