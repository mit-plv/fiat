(* Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common.List.Operations.
Require Import ADTRefinement.GeneralRefinements.
Require Import Parsers.ParserInterface.
Require Import ADTSynthesis.ADTRefinement.Core.
Require Import ADTSynthesis.Common.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.
Section ReferenceImpl.
  Section GenericSig.
    Context (Char : Type).

    (** Representation of a [String] that can be split *)
    Definition string_rep : ADTSig :=
      ADTsignature {
        Constructor "new" : String.string -> rep,
        (** Initialize, with a given [string] to be parsed or split. *)

        Method "to_string" : rep x unit -> rep x String.string,
        (** Return the underlying string; hack to get around not having [eq : rep x rep -> bool] *)

        Method "is_char" : rep x Char -> rep x bool,
        (* Return [true] if this string represents a singleton character equal to the given one; otherwise return [false]. *)

        Method "length" : rep x unit -> rep x nat,
        (** Return the length of this string. *)

        Method "take" : rep x nat -> rep x unit,
        (** Return the first [n] characters, for the given [n : nat]. *)

        Method "drop" : rep x nat -> rep x unit,
        (** Return everything but the first [n] characters, for the given [n : nat]. *)

        Method "splits" : rep x item Char * production Char -> rep x list nat
        (** Return a list of locations to split this string at for this production rule. *)
      }.
  End GenericSig.

  Context (G : grammar Ascii.ascii).

  (** Reference implementation of a [String] that can be split *)
  Definition string_spec : ADT (string_rep Ascii.ascii) := ADTRep String.string {
    Def Constructor "new"(s : String) : rep :=
      ret s,

    Def Method "to_string"(s : rep, x : unit) : String.string :=
      ret (s, s),

    Def Method "is_char"(s : rep, x : Ascii.ascii) : bool  :=
      ret (s, string_dec s (String.String x "") : bool),

    Def Method "length"(s : rep, x : unit) : nat :=
      ret (s, String.length s),

    Def Method "take"(s : rep, n : nat) : unit :=
      ret (take n s, tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret (drop n s, tt),

    Def Method "splits"(s : rep, p : item Ascii.ascii * production Ascii.ascii) : list nat :=
      ls <- { ls : list nat | split_list_is_complete G s (fst p) (snd p) ls };
      ret (s, ls)
  }.

  Section parser.

    Context (splitter_impl : cADT (string_rep Ascii.ascii))
            (splitter_OK   : refineADT string_spec (LiftcADT splitter_impl)).

    Local Notation mcall0 proj s := (fun n st => (proj (cMethods splitter_impl {| StringBound.bindex := s |} st n))) (only parsing).
    Local Notation mcall1 s := (mcall0 fst s) (only parsing).
    Local Notation mcall2 s := (mcall0 snd s) (only parsing).


    Let mto_string := Eval simpl in mcall2 "to_string".
    Let mis_char := Eval simpl in mcall2 "is_char".
    Let mlength := Eval simpl in mcall2 "length".
    Let mtake := Eval simpl in mcall1 "take".
    Let mdrop := Eval simpl in mcall1 "drop".
    Let msplits := Eval simpl in mcall2 "splits".

    Local Obligation Tactic :=
      program_simpl; subst_body; simpl in *;
      (lazymatch goal with
      | [ Ok : refineADT ?spec (LiftcADT ?impl),
               H : ?x ≃ ?str |- exists orig, orig ≃ fst (cMethods ?impl ?method ?str ?arg) ]
        => abstract (
               unique pose proof (ADTRefinementPreservesMethods Ok method _ _ arg H (cMethods impl method str arg) (ReturnComputes _));
               computes_to_inv;
               match goal with
                 | [ H : (_, _) = _ |- _ ] => pose proof (f_equal (@fst _ _) H);
                 pose proof (f_equal (@snd _ _) H);
                 clear H
               end;
               simpl in *; subst;
               eexists; eassumption
             )
      | _ => idtac
       end);
      unfold beq in *; simpl in *(*;
      repeat match goal with
               | [ Ok : refineADT ?spec (LiftcADT ?impl),
                        H' : ?x ≃ ?str,
                             H : context[cMethods ?impl ?method ?str ?arg] |- _ ]
                 => unique pose proof (ADTRefinementPreservesMethods Ok method x _ arg H' (cMethods impl method str arg) (ReturnComputes _))
               | [ Ok : refineADT ?spec (LiftcADT ?impl),
                        H' : ?x ≃ ?str
                   |- context[cMethods ?impl ?method ?str ?arg] ]
                 => unique pose proof (ADTRefinementPreservesMethods Ok method x _ arg H' (cMethods impl method str arg) (ReturnComputes _))
             end*).

    Local Arguments string_dec : simpl never.

    Time Program Definition adt_based_splitter : Splitter G
      := {| string_type
            := {| String := { r : cRep splitter_impl | exists orig, AbsR splitter_OK orig r };
                  take n str := mtake n str;
                  drop n str := mdrop n str;
                  length str := mlength tt str;
                  is_char str ch := mis_char ch str;
                  bool_eq s1 s2 := string_dec (mto_string tt s1) (mto_string tt s2)  |};
            string_type_properties := {| singleton_unique := _ |};
            splits_for str it its := msplits (it, its) str |}.
    Local Ltac t' :=
      idtac;
      match goal with
        | _ => reflexivity
        | _ => progress unfold is_true in *
        | _ => progress subst
        | _ => progress simpl in *
        | _ => progress computes_to_inv
        | [ H : (_, _) = _ |- _ ]
          => pose proof (f_equal (@fst _ _) H);
            pose proof (f_equal (@snd _ _) H);
            clear H
        | [ H : ?x = ?x |- _ ] => clear H
        | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
        | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
        | [ H : String.String _ _ = String.String _ _ |- _ ]
          => inversion H; clear H
        | [ H : ?x = true, H' : context[?x] |- _ ]
          => rewrite H in H'
        | [ H : ?x = String.String _ _, H' : context[?x] |- _ ]
          => rewrite H in H'
        | [ H : ?x = String.String _ _ |- context[?x] ]
          => rewrite H
        | [ H : 1 = ?x |- context[?x] ] => rewrite <- H
        | [ H : ?x = 1 |- context[?x] ] => rewrite H
        | [ H : 0 = ?x |- context[?x] ] => rewrite <- H
        | [ H : ?x = 0 |- context[?x] ] => rewrite H
        | [ H : true = ?x |- context[?x] ] => rewrite <- H
        | [ H : ?x = true |- context[?x] ] => rewrite H
        | [ H : false = ?x |- context[?x] ] => rewrite <- H
        | [ H : ?x = false |- context[?x] ] => rewrite H
        | [ H : context[string_dec ?x ?y] |- _ ]
          => destruct (string_dec x y)
        | _ => progress unfold beq in *
        | [ |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
      end.
    Local Ltac t := repeat t'.
    Next Obligation.
    Proof.
      unfold is_true in *.
      repeat match goal with
               | [ Ok : refineADT ?spec (LiftcADT ?impl),
                        H' : ?x ≃ ?str,
                             H : context[cMethods ?impl ?method ?str ?arg] |- _ ]
                 => unique pose proof (ADTRefinementPreservesMethods Ok method x _ arg H' (cMethods impl method str arg) (ReturnComputes _))
               | [ Ok : refineADT ?spec (LiftcADT ?impl),
                        H' : ?x ≃ ?str
                   |- context[cMethods ?impl ?method ?str ?arg] ]
                 => unique pose proof (ADTRefinementPreservesMethods Ok method x _ arg H' (cMethods impl method str arg) (ReturnComputes _))
             end.
      repeat match goal with

        | _ => reflexivity
        | _ => progress unfold is_true in *
        | _ => progress subst
        | _ => progress simpl in *
        | _ => progress computes_to_inv
        | [ H : (_, _) = _ |- _ ]
          => pose proof (f_equal (@fst _ _) H);
            pose proof (f_equal (@snd _ _) H);
            clear H
end.
      clear H4 H
t. Qed.
    Next Obligation.
    Proof. t. Qed.
    Next Obligation.
    Proof. t. Qed.
    Next Obligation.
    Proof. Timeout 10 t.
           repeat intro.
           t.
           destruct_head sig.
           destruct_head ex.
 Qed.
    Next Obligation.
    Proof. Timeout 10 t. Qed.
    Next Obligation.
    Proof. Timeout 10 t. Qed.
    Next Obligation.
    Proof. Timeout 10 t. Qed.
    Next Obligation.
    Proof. Timeout 10 t. Qed.
           rewrite <- H4.
 Qed.

injections.
               end;
               simpl in *; subst;

at (simpl in * || computes_to_inv || subst).
      unfold is_true in *.
      repeat computes_to_inv.
      simpl in *.
      computes_to_inv.


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
