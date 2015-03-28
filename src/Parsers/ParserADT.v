(* Reference implementation of a splitter and parser based on that splitter *)
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common.List.Operations.
Require Import ADTRefinement.GeneralRefinements.
Require Import Parsers.ParserInterface.
Require Import ADTSynthesis.ADTRefinement.Core.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.
Section ReferenceImpl.
  Context {CharType} {String : string_like CharType} (G : grammar CharType).

  (** Representation of a [String] that can be split *)
  Definition string_rep : ADTSig :=
    ADTsignature {
      Constructor "new" : String -> rep,
      (** Initialize, with a given [String] to be parsed or split. *)

      Method "take" : rep x nat -> rep x unit,
      (** Return the first [n] characters, for the given [n : nat]. *)

      Method "drop" : rep x nat -> rep x unit,
      (** Return everything but the first [n] characters, for the given [n : nat]. *)

      Method "splits" : rep x item CharType * production CharType -> rep x list nat
    }.

  (** Reference implementation of a [String] that can be split *)
  Definition string_spec : ADT string_rep := ADTRep String {
    Def Constructor "new"(s : String) : rep :=
      ret s,

    Def Method "take"(s : rep, n : nat) : unit :=
      ret (fst (SplitAt n s), tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret (snd (SplitAt n s), tt),

    Def Method "splits"(s : rep, p : item CharType * production CharType) : list nat :=
      ls <- { ls : list nat | split_list_is_complete String G s (fst p) (snd p) ls };
      ret (s, ls)
  }.

  Section parser.

    Context (splitter_impl : cADT string_rep)
            (splitter_OK   : refineADT string_spec (LiftcADT splitter_impl)).
    Local Obligation Tactic := idtac.
    (* Don't want it inferring silly method implementations. *)

    Program Definition adt_based_splitter : Splitter String G
      := {| split_rep := cRep splitter_impl (* rep of splitter *);
            split_take n st := _ (* call "take"(st, n) on splitter *);
            split_drop n st := _ (* call "drop"(st, n) on splitter *);
            splits_for st it its := _ (* call "splits"(st, (it, its)) on splitter *);
            split_invariant str st := AbsR (splitter_OK) str st (* rep inv between String and split_rep *);
            take_respectful str st n H := _ (* proof that "take" preserves the rep inv w.r.t. its spec *);
            drop_respectful str st n H := _ (* proof that "drop" preserves the rep inv w.r.t. its spec *);
            splits_for_complete str st it its H := _ (* proof that "splits" obeys its spec, given that the rep inv holds on the input, by H *) |}.
    Next Obligation.
      let impl := eval simpl in
      (fun n st => fst (cMethods splitter_impl {| StringBound.bindex := "take" |} st n)) in
          exact impl.
    Defined.
    Next Obligation.
      let impl := eval simpl in
      (fun n st => fst (cMethods splitter_impl {| StringBound.bindex := "drop" |} st n)) in
          exact impl.
    Defined.
    Next Obligation.
      let impl := eval simpl in
      (fun st it its => snd (cMethods splitter_impl {| StringBound.bindex := "splits" |} st (it, its))) in
          exact impl.
    Defined.
    Next Obligation.
      intros.
      pose proof (ADTRefinementPreservesMethods splitter_OK {|StringBound.bindex := "take" |} _ _ n H ((cMethods splitter_impl {| StringBound.bindex := "take" |} st n)) (ReturnComputes _)).
      computes_to_inv; injections; simpl in *; subst.
      computes_to_inv; subst; simpl in *.
      unfold adt_based_splitter_obligation_1; rewrite <- H0''; eauto.
    Qed.
    Next Obligation.
      intros.
      pose proof (ADTRefinementPreservesMethods splitter_OK {|StringBound.bindex := "drop" |} _ _ n H ((cMethods splitter_impl {| StringBound.bindex := "drop" |} st n)) (ReturnComputes _)).
      computes_to_inv; injections; simpl in *; subst.
      computes_to_inv; subst; simpl in *.
      unfold adt_based_splitter_obligation_2; rewrite <- H0''; eauto.
    Qed.
    Next Obligation.
      intros.
      pose proof (ADTRefinementPreservesMethods splitter_OK {|StringBound.bindex := "splits" |} _ _ (it, its) H ((cMethods splitter_impl {| StringBound.bindex := "splits" |} st (it, its))) (ReturnComputes _)).
      computes_to_inv; injections; simpl in *; subst.
      computes_to_inv; subst; simpl in *.
      unfold adt_based_splitter_obligation_3; rewrite <- H0''; eauto.
    Qed.
  End parser.
End ReferenceImpl.
