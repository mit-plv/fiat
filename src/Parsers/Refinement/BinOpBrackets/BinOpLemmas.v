Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Common.

(*
Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.SetoidInstances.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.
Require Import Fiat.Common.SetoidInstances.


Require Import Fiat.

Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.ContextFreeGrammarEquality.
Require Import Coq.Program.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.Wf.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.Splitters.BruteForce.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerFull.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.FoldGrammar.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.ContextFreeGrammarValid.
Require Import Fiat.Parsers.ContextFreeGrammarValidProperties.
Require Import Fiat.Parsers.ContextFreeGrammarValidReflective.
Require Fiat.Parsers.Reachable.All.MinimalReachable.
Require Fiat.Parsers.Reachable.All.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.All.ReachableParse.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.ReachableParse.
Require Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Fiat.Parsers.Reachable.MaybeEmpty.MinimalOfCore.
Require Fiat.Parsers.Reachable.MaybeEmpty.OfParse.
*)
Set Implicit Arguments.

Section helpers.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  Local Ltac induction_str_len str :=
    let len := fresh "len" in
    set (len := length str);
      generalize (eq_refl : length str = len);
      clearbody len; revert str;
      induction len; intros str ?.

  Local Ltac t :=
    repeat match goal with
             | [ |- ?x = ?x ] => reflexivity
             | [ H : is_true false |- _ ] => solve [ inversion H ]
             | [ H : false = true |- _ ] => solve [ inversion H ]
             | _ => progress rewrite ?take_length, ?drop_length
             | [ H : _ |- _ ] => progress rewrite ?take_length, ?drop_length, ?drop_take, ?drop_0, ?NPeano.Nat.sub_0_r, ?NPeano.Nat.sub_1_r in H
             | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : length ?str = 0, H' : is_true (take _ (drop _ ?str) ~= [ _ ])%string_like |- _ ]
               => apply length_singleton in H'
             | [ H : get 0 _ = None |- _ ] => apply no_first_char_empty in H
             | _ => progress simpl in *
             | _ => progress subst
             | _ => setoid_rewrite Bool.andb_true_iff
             | [ H : (_ && _ = true)%bool |- _ ] => apply Bool.andb_true_iff in H
             | _ => progress specialize_by omega
             | _ => progress specialize_by assumption
             | _ => progress split_and
             | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
             | [ H : context[if ?e then _ else _] |- _ ] => destruct e eqn:?
             | _ => solve [ eauto with nocore ]
             | [ H : context[drop _ (drop _ _)] |- _ ] => setoid_rewrite drop_drop in H
             | [ |- appcontext[match get 0 (take _ _) with _ => _ end] ] => rewrite !get_take_lt by omega
             | [ H : context[_ + 1] |- _ ] => setoid_rewrite NPeano.Nat.add_1_r in H
             | [ |- context[get 0 ?str] ] => erewrite (proj1 (get_0 str _)) by eassumption
             | [ |- context[get 0 (take 0 ?str)] ] => rewrite (has_first_char_nonempty (take 0 str))
                                                     by (rewrite take_length; reflexivity)
             | [ H : context[Compare_dec.zerop ?x] |- _ ] => destruct (Compare_dec.zerop x)
             | _ => progress intros
             | _ => omega
             | [ H : context[match get 0 ?str with _ => _ end] |- _ ] => destruct (get 0 str) eqn:?
             | _ => progress unfold is_true in *
           end.

  Lemma paren_balanced_hiding'_prefix (str : String) (n n' level : nat)
        (H_hiding : paren_balanced_hiding' (take n str) level)
        (H_hiding_prefix : paren_balanced' (take n' str) level)
        {ch}
        (Hlt : n' < n)
        (H_ch : (take 1 (drop n' str) ~= [ ch ])%string_like)
        (H_bin_op : is_bin_op ch)
  : False.
  Proof.
    generalize dependent level.
    generalize dependent n'.
    generalize dependent n.
    induction_str_len str.
    { t. }
    { specialize (IHlen (drop 1 str)).
      specialize_by ltac:(rewrite drop_length; omega).
      intros ?????.
      rewrite paren_balanced_hiding'_recr, paren_balanced'_recr.
      unfold paren_balanced_hiding'_step, paren_balanced'_step.
      destruct n' as [|n'].
      { t. }
      { specialize (IHlen (pred n) n').
        t. } }
  Qed.
End helpers.
