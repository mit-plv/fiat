Require Export Fiat.ADTRefinement.GeneralBuildADTRefinements.
(* TODO: Clean out these imports. *)
Require Import Coq.Lists.List Coq.Arith.Arith
        Fiat.Common Fiat.Computation Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADT.ComputationalADT
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.TransparentAbstract
        Fiat.ADTNotation.BuildADTSig
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildComputationalADT
        Fiat.ADTNotation.BuildADTReplaceMethods
        Fiat.ADTRefinement.Core
        Fiat.ADTRefinement.GeneralRefinements
        Fiat.ADTRefinement.SetoidMorphisms
        Fiat.ADTRefinement.BuildADTSetoidMorphisms.

(* Declare definitions for all the elements in an indexed list, *)
(* used to declare an ADT definition. *)
Ltac cache_ilist_elements id il k :=
  let id' := fresh id in
  lazymatch il with
  | ilist.icons ?b ?il' =>
    cache_term b as id run (fun b' => cache_ilist_elements id il' ltac:(fun il'' => k (ilist.icons b' il'')))
  | inil (B := ?B) => k (inil (B := B))
  end.

(* [abstractADT] makes a [FullySharpened] ADT much nicer for the continuation tactic [k] *)
(* to work with by declaring transparent definitions for the representation type, *)
(* constructors, and methods. *)

Ltac abstractADTImpl adt k :=
  let impl := (eval simpl in (projT1 adt)) in
  let impl_sig :=
      (lazymatch type of impl with
       | DecoratedcADT ?Sig => Sig
       | sigT (ComputationalADT.pcADT ?Sig) => Sig
       end) in
  let impl_rep := (eval simpl in (projT1 impl)) in

  let impl_methods := (eval simpl in (ComputationalADT.pcMethods (projT2 impl))) in
  let impl_methods' :=
      (lazymatch impl_methods with
       | fun idx => cMethBody (ith ?methods' idx) => methods'
       end) in

  let ADTImplSig := fresh "ADTImplSig" in
  let ADTImplRep := fresh "ADTImplRep" in
  let ADTImplMethods := fresh "ADTImplMethods" in
  let ADTImplMethod := fresh "ADTImplMethod" in
  let ADTImplConstructors := fresh "ADTImplMethod" in
  cache_ilist_elements ADTImplMethod impl_methods'
                       ltac:(fun impl_method_defs =>
                               cache_term impl_sig as ADTImplSig
                                                                                     run (fun impl_sig_def =>
                                                                                            cache_term impl_rep as ADTImplRep
                                                                                                                     run (fun impl_rep_def =>
                                                                                                                            cache_term (@ComputationalADT.Build_pcADT impl_sig_def impl_rep_def
                                                                                                                                                                      
                                                                                                                                                                      (fun idx => cMethBody (ith impl_method_defs idx)))
                                                                                                                            as ADTImplMethods
                                                                                                                                 run (fun impl_methods_def =>
                                                                                                                                        let impl' := constr:(
                                                                                                                                                       (existT (ComputationalADT.pcADT impl_sig_def) impl_rep_def impl_methods_def : ComputationalADT.cADT impl_sig_def)) in
                                                                                                                                        k impl')))).

(* [AbstractADT] uses [abstractADTImpl] to build a [Definition] of a [FullySharpenedADT] *)
(* with an abstracted [refineADT] proof term. This should prevent client code from *)
(* blowing up when calling an ADT method. *)

Ltac AbstractADT adt :=
  abstractADTImpl adt ltac:(fun impl' =>
                          refine (existT _ impl' _);
                        abstract (exact (projT2 adt))).
