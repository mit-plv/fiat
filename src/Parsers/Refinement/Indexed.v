(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.ParserADTSpecification.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Equality.
Require Import ADTSynthesis.ADTRefinement.
Require Import ADTSynthesis.Common.StringBound ADTSynthesis.Common.ilist.
Require Import ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import ADTSynthesis.Common.IterateBoundedIndex.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section IndexedImpl.
  Context (G : grammar Ascii.ascii).

  Local Notation T := (String.string * (nat * nat))%type (only parsing).

  (** Reference implementation of a [String] that can be split; has a [string], and a start index, and a length *)
  Definition indexed_spec : ADT (string_rep Ascii.ascii) := ADTRep T {
    Def Constructor "new"(s : String.string) : rep :=
      ret (s, (0, String.length s)),

    Def Method "to_string"(s : rep, x : unit) : String.string :=
      ret (s, substring (fst (snd s)) (snd (snd s)) (fst s)),

    Def Method "is_char"(s : rep, ch : Ascii.ascii) : bool  :=
      ret (s, ((Nat.eq_dec (min (String.length (fst s) - fst (snd s)) (snd (snd s))) 1)
                 && (string_dec (substring (fst (snd s)) (snd (snd s)) (fst s)) (String.String ch "")))%bool),

    Def Method "length"(s : rep, x : unit) : nat :=
      ret (s, min (String.length (fst s) - fst (snd s)) (snd (snd s))),

    Def Method "take"(s : rep, n : nat) : unit :=
      ret ((fst s, (fst (snd s), min (snd (snd s)) n)), tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret ((fst s, (fst (snd s) + n, snd (snd s) - n)), tt),

    Def Method "splits"(s : rep, p : item Ascii.ascii * production Ascii.ascii) : list nat :=
      ls <- { ls : list nat | split_list_is_complete G (substring (fst (snd s)) (snd (snd s)) (fst s)) (fst p) (snd p) ls };
      ret (s, ls)
  }.

  (** XXX TODO: Move this to a better place *)
  Local Arguments Ensemble_BoundedIndex_app_comm_cons / .

  Lemma FirstStep
  : refineADT (string_spec G) indexed_spec.
  Proof.
    econstructor 1 with (AbsR := (fun r_o r_n =>
                                    substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o));
    abstract (
        eapply Iterate_Ensemble_BoundedIndex_equiv;
        simpl; intuition; intros; try simplify with monad laws;
        repeat intro; computes_to_inv; subst; simpl;
        try solve [ repeat
                      repeat
                      match goal with
                        | _ => progress intros
                        | [ |- computes_to (Bind _ (fun _ => Return _)) _ ]
                          => eapply BindComputes; [ | eapply ReturnComputes ]
                        | [ |- computes_to (Bind _ _) _ ]
                          => eapply BindComputes
                        | [ |- computes_to (Return ?x) ?y ]
                          => cut (x = y);
                            [ let H := fresh in intro H; try rewrite H; eapply ReturnComputes | ]
                        | [ |- computes_to (Pick _) _ ]
                          => eapply PickComputes
                        | _ => reflexivity
                        | _ => assumption
                        | _ => progress simpl in *
                        | _ => progress subst
                        | [ |- appcontext[fst ?e] ]
                          => is_evar e; pattern e;
                             let P := match goal with |- ?P _ => constr:P end in
                             refine (_ : P (_, _))
                        | [ |- (_, _) = (_, _) ] => apply f_equal2
                        | _ => rewrite substring_correct3'
                        | _ => rewrite substring_correct0
                        | _ => rewrite substring_length
                        | _ => rewrite Nat.add_sub
                        | _ => rewrite Nat.sub_0_r
                        | _ => rewrite substring_substring
                        | _ => rewrite <- Nat.sub_min_distr_r
                        | [ |- context[min (min _ ?x) (?x - ?y)] ]
                          => rewrite <- (Min.min_assoc _ x (x - y)), (Min.min_r x (x - y)) by omega
                        | [ |- substring (?x + ?y) _ _ = substring (?y + ?x) _ _ ]
                          => rewrite (Plus.plus_comm x y)
                        | [ |- context[min ?x ?y] ]
                          => match goal with
                               | [ |- context[min y x] ]
                                 => rewrite (Min.min_comm x y)
                             end
                        | [ H : _ |- _ ] => rewrite substring_correct0 in H
                        | [ H : _ |- _ ] => rewrite substring_length, <- Nat.sub_min_distr_r in H
                        | [ H : _ |- _ ] => rewrite <- plus_n_O in H
                        | [ H : context[?x + S ?y - ?y] |- _ ]
                          => replace (x + S y - y) with (S x) in H by omega
                        | [ H : context[match ?x with 0 => _ | _ => _ end] |- _ ] => is_var x; destruct x
                        | [ |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
                        | [ |- context[option_dec ?H ?x ?y] ] => destruct (option_dec H x y)
                        | [ |- context[Nat.eq_dec ?x ?y] ] => destruct (Nat.eq_dec x y)
                        | [ |- true = false ] => exfalso
                        | [ |- false = true ] => exfalso
                        | [ H : context[min _ 0] |- _ ] => rewrite Min.min_0_r in H
                        | [ H : context[min 0 _] |- _ ] => rewrite Min.min_0_l in H
                        | [ H : min _ ?x <> 1 |- _ ] => is_var x; destruct x
                        | _ => congruence
                        | [ |- substring ?x ?y ?z = substring ?x (min ?w ?y) ?z ]
                          => apply (@Min.min_case_strong w y)
                        | [ H : substring _ _ _ = String.String _ _ |- _ ]
                          => apply (f_equal String.length) in H
                        | _ => apply substring_correct4; omega
                      end ]
      ).
  Defined.

  (*Lemma AllTheSteps
  : Sharpened (string_spec G).
    eapply SharpenStep.
    apply FirstStep.

    (*hone representation using
         (fun r_o r_n =>
                    substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o).
    hone constructor "new".
    {
      simplify with monad laws.
      refine pick val (d, (0, String.length d)).
      subst H; higher_order_reflexivity.
      simpl.
      finish honing. *)

  Admitted.



  (** now I want to show that indexed_spec refines string_spec *)*)

End IndexedImpl.
