(* Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common.List.Operations.
Require Import ADTRefinement.GeneralRefinements.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.StringLike.String.
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

    Lemma snd_cMethods_comp {method st arg v retv}
          (H0 : Methods string_spec method v arg = ret retv)
          (H1 : AbsR splitter_OK v st)
    : snd (cMethods splitter_impl method st arg) = snd retv.
    Proof.
      pose proof (ADTRefinementPreservesMethods splitter_OK method _ _ arg H1 (cMethods splitter_impl method st arg) (ReturnComputes _)) as H''.
      rewrite H0 in H''; clear H0.
      computes_to_inv.
      match goal with
        | [ H : (_, _) = _ |- _ ]
          => pose proof (f_equal (@fst _ _) H);
            pose proof (f_equal (@snd _ _) H);
            clear H
      end.
      subst.
      destruct_head' prod.
      simpl @fst in *.
      simpl @snd in *.
      subst.
      reflexivity.
    Qed.

    Local Ltac snd_cMethods_comp' :=
      idtac;
      match goal with
        | [ |- appcontext G[snd (cMethods splitter_impl ?meth ?st ?arg)] ]
          => let G' := context G[snd (cMethods splitter_impl meth st arg)] in
             progress change G'
        | [ H : appcontext G[snd (cMethods splitter_impl ?meth ?st ?arg)] |- _ ]
          => let G' := context G[snd (cMethods splitter_impl meth st arg)] in
             progress change G' in H
        | [ H : appcontext G[snd (cMethods splitter_impl ?meth ?st ?arg)] |- _ ]
          => erewrite (@snd_cMethods_comp meth st arg) in H by (eassumption || reflexivity);
            simpl @snd in H
        | [ |- appcontext G[snd (cMethods splitter_impl ?meth ?st ?arg)] ]
          => erewrite (@snd_cMethods_comp meth st arg) by (eassumption || reflexivity);
            simpl @snd
      end.
    Local Ltac snd_cMethods_comp := repeat snd_cMethods_comp'.

    Local Notation mcall0 proj s := (fun n st => (proj (cMethods splitter_impl {| StringBound.bindex := s |} st n))) (only parsing).
    Local Notation mcall1 s := (mcall0 fst s) (only parsing).
    Local Notation mcall2 s := (mcall0 snd s) (only parsing).

    Let mto_string := Eval simpl in mcall2 "to_string".
    Let mis_char := Eval simpl in mcall2 "is_char".
    Let mlength := Eval simpl in mcall2 "length".
    Let mtake := Eval simpl in mcall1 "take".
    Let mdrop := Eval simpl in mcall1 "drop".
    Let msplits := Eval simpl in mcall2 "splits".

    Local Hint Unfold mto_string mis_char mlength mtake mdrop msplits : parser_adt_subst_db.

    Local Obligation Tactic :=
      autounfold with parser_adt_subst_db in *;
      repeat intro;
      destruct_head_hnf sig; destruct_head_hnf ex;
      simpl in *;
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
      unfold beq in *; simpl in *;
      snd_cMethods_comp.


    Local Arguments string_dec : simpl never.
Start Profiling.
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
Show Profile.
    Local Ltac t meth :=
      let H := fresh in
      pose proof (meth Ascii.ascii string_stringlike string_stringlike_properties) as H;
        simpl in H; unfold beq in H; simpl in H;
        eapply H; clear H; simpl; try eassumption.
    Next Obligation. t @singleton_unique. Qed.
    Next Obligation. t @length_singleton. Qed.
    Next Obligation. t @bool_eq_char. Qed.
    Next Obligation. t @is_char_Proper. Qed.
    Next Obligation. t @length_Proper. Qed.
    Next Obligation. t @take_Proper. Qed.
    Next Obligation. t @drop_Proper. Qed.

      repeat match goal with
               | [ |- appcontext G[snd (cMethods splitter_impl ?meth ?st ?arg)] ]
                 => let G' := context G[snd (cMethods splitter_impl meth st arg)] in
                    progress change G'
             end.
      lazymatch goal with
        | [ H : appcontext G[snd (cMethods splitter_impl ?meth ?st ?arg)] |- _ ]
          => let G' := context G[snd (cMethods splitter_impl meth st arg)] in
             change G' in H;
               erewrite (@snd_cMethods_comp meth st arg) in H by (eassumption || reflexivity);
               simpl @snd in H
        | [ |- appcontext G[snd (cMethods splitter_impl ?meth ?st ?arg)] ]
          => let G' := context G[snd (cMethods splitter_impl meth st arg)] in
             change G';
               pattern (snd (cMethods splitter_impl meth st arg))
      end.
               erewrite (@snd_cMethods_comp meth st arg) by (eassumption || reflexivity);
               simpl @snd
      end.
      snd_cMethods_comp.
      lazy
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
      computes_to_inv.
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
