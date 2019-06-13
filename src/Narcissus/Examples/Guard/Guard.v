Require Export Fiat.ADT Fiat.ADTNotation Fiat.ADTRefinement Fiat.ADTRefinement.BuildADTRefinements.

Require Export Fiat.Narcissus.Examples.Guard.Core.
Require Export Fiat.Narcissus.Examples.Guard.IPTablesGuard.

Definition GuardSig : ADTSig := ADTsignature {
  Constructor "Init" : rep,
  Method "ProcessPacket" : rep * bytes -> rep * result
}.

Definition GuardSpec : ADT GuardSig := IPGuard {{
    iptables -P FORWARD DROP;
    iptables -A FORWARD --protocol "UDP" --source-port bootps --not --source 192*168*0*1 -j DROP;
    iptables -A FORWARD --protocol "UDP" --source-port bootpc --not --destination 255*255*255*255 -j DROP
}}.

Arguments andb : simpl nomatch.
Arguments Word.NToWord : simpl never.
Arguments Word.wones : simpl never.
Arguments Word.wzero : simpl never.
Arguments Word.zext : simpl never.
Hint Rewrite Bool.andb_true_l : iptables.

Ltac t_ :=
  match goal with
  | _ => progress (subst || cbn)
  | _ => progress (autounfold with iptables || autorewrite with iptables)
  | _ => simplify with monad laws
  | _ => refine pick eq
  end.

Ltac t := repeat t_.

Ltac guardc :=
  start sharpening ADT;
  hone representation using eq; t;
    [ finish honing.. | finish_SharpeningADT_WithoutDelegation ].

Theorem SharpenedGuard :
  FullySharpened GuardSpec.
Proof. guardc. Defined.

Definition GuardImpl :=
  Eval cbn in projT1 SharpenedGuard.
