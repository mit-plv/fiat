Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.MakeBinOpTable.
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
  Context (is_bin_op : Char -> bool)
          (is_open : Char -> bool) (is_close : Char -> bool).

  Lemma paren_balanced_hiding'_prefix (str : String) (n n' level : nat)
        (H_hiding : paren_balanced_hiding' is_bin_op is_open is_close (take n str) level)
        (H_hiding_prefix : paren_balanced' is_bin_op is_open is_close (take n' str) level)
        {ch}
        (Hlt : n' < n)
        (H_ch : (take 1 (drop n' str) ~= [ ch ])%string_like)
        (H_bin_op : is_bin_op ch)
  : False.
  Proof.
    admit.
  Qed.
End helpers.
