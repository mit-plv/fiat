Require Import Fiat.Common.Tactics.DestructHyps.
Ltac destruct_sig_matcher HT :=
  match eval hnf in HT with
  | ex _ => idtac
  | ex2 _ _ => idtac
  | sig _ => idtac
  | sig2 _ _ => idtac
  | sigT _ => idtac
  | sigT2 _ _ => idtac
  | and _ _ => idtac
  | prod _ _ => idtac
  end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.
