(* Require Import Fiat.BinEncoders.Env.Common.Sig
               Fiat.BinEncoders.Env.Common.Compose.


Require Import Fiat.BinEncoders.Env.BinLib.Core
               Fiat.BinEncoders.Env.BinLib.FixInt
               Fiat.BinEncoders.Env.BinLib.Char
               Fiat.BinEncoders.Env.BinLib.Bool
               Fiat.BinEncoders.Env.BinLib.Enum
               Fiat.BinEncoders.Env.Lib.FixList
               Fiat.BinEncoders.Env.Lib.IList
               Fiat.BinEncoders.Env.Lib.SteppingCacheList.

Ltac enum_part eq_dec :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func in
    let h := fresh in
      evar (h:func_t);
      unify (fun n => if eq_dec _ n arg then res else h n) func;
      reflexivity
  end.

Ltac enum_finish :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func
    in  unify ((fun _  => res) : func_t) func;
        reflexivity
  end.

Ltac idtac' :=
  match goal with
    | |- _ => idtac (* I actually need this idtac for some unknown reason *)
  end.

Definition FixInt_eq_dec (size : nat) (n m : {n | (n < exp2 size)%N }) : {n = m} + {n <> m}.
  refine (if N.eq_dec (proj1_sig n) (proj1_sig m) then left _ else right _);
    abstract (destruct n; destruct m; try congruence; simpl in *; rewrite <- sig_equivalence; eauto).
Defined.

Ltac solve_enum :=
  let h := fresh in
  intros h; destruct h;
  [ idtac'; enum_part FixInt_eq_dec ..
  | idtac'; enum_finish ].

Ltac solve_done :=
  let hdata := fresh in
  eexists;
  intros ? ? ? ? hdata ? ? ? ? ? ? ?; destruct hdata; simpl in *;
  instantiate (1:=fun b e => (_, b, e));
  cbv beta; intros; repeat match goal with
                           | [ H : (_, _) = (_, _) |- _ ] => inversion H; subst; clear H
                           end; intuition; subst; eauto.

Ltac solve_predicate :=
  unfold SteppingList_predicate, IList_predicate, FixList_predicate;
  intuition eauto; instantiate (1:=fun _ => True); solve_predicate.

Ltac eauto_typeclass :=
  match goal with
  | |- context [ Bool_encode ] => eapply Bool_decoder
  | |- context [ Char_encode ] => eapply Char_decoder
  | |- context [ FixInt_encode ] => eapply FixInt_decoder
  | |- context [ FixList_encode _  ] => eapply FixList_decoder
  | |- context [ IList_encode _ ] => eapply IList_decoder
  | |- context [ SteppingList_encode _ ] => eapply SteppingListCache_decoder
  end; eauto.

Ltac solve_decoder :=
  match goal with
  | |- _ => solve [ solve_done ]
  | |- _ => solve [ eauto_typeclass; solve_decoder ]
  | |- _ => solve [ eapply Enum_decoder; solve_enum ]
  | |- _ => eapply compose_decoder; [ solve_decoder | solve_predicate | intro; solve_decoder ]
  end. *)