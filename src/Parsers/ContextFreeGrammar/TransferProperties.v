(** * Properties about Context Free Grammars *)
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.StringLike.Core Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Coq.Classes.RelationClasses.
Require Import Fiat.Common Fiat.Common.UIP.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties Fiat.Parsers.ContextFreeGrammar.Transfer.

Set Implicit Arguments.

Local Open Scope list_scope.

Section cfg.
  Context {Char} {HSL1 HSL2 : StringLike Char}
          {G : grammar Char}
          {R : @String Char HSL1 -> @String Char HSL2 -> Prop}
          {TR : transfer_respectful R}.
  Context {P : String.string -> Type}.

  Definition transfer_forall_parse_of_item'
        (transfer_forall_parse_of
         : forall str1 str2 it (HR : R str1 str2) p,
             @Forall_parse_of Char _ G (fun _ => P) str1 it p
             -> @Forall_parse_of Char _ G (fun _ => P) str2 it (transfer_parse_of HR p))
        {str1 str2 it}
        (HR : R str1 str2)
        {p}
  : @Forall_parse_of_item' Char HSL1 G (fun _ => P) (@Forall_parse_of _ _ _ (fun _ => P)) str1 it p
    -> @Forall_parse_of_item' Char HSL2 G (fun _ => P) (@Forall_parse_of _ _ _ (fun _ => P)) str2 it (transfer_parse_of_item HR p)
    := match
        p in (parse_of_item _ _ it)
        return
        (@Forall_parse_of_item' Char HSL1 G (fun _ => P) (@Forall_parse_of _ _ _ (fun _ => P)) str1 it p
         -> @Forall_parse_of_item' Char HSL2 G (fun _ => P) (@Forall_parse_of _ _ _ (fun _ => P)) str2 it (transfer_parse_of_item HR p))
      with
        | ParseTerminal _ _ => fun x => x
        | ParseNonTerminal _ H' p' => fun xy => (fst xy, transfer_forall_parse_of _ _ _ _ p' (snd xy))
      end.

  Fixpoint transfer_forall_parse_of
           str1 str2 pats
           (HR : R str1 str2)
           {p}
           {struct p}
  : @Forall_parse_of Char HSL1 G (fun _ => P) str1 pats p
    -> @Forall_parse_of Char HSL2 G (fun _ => P) str2 pats (transfer_parse_of HR p)
    := match
        p in (parse_of _ _ pats)
        return
        (@Forall_parse_of Char HSL1 G (fun _ => P) str1 pats p
         -> @Forall_parse_of Char HSL2 G (fun _ => P) str2 pats (transfer_parse_of HR p))
      with
        | ParseHead _ _ p' => @transfer_forall_parse_of_production _ _ _ _ p'
        | ParseTail _ _ p' => @transfer_forall_parse_of _ _ _ _ p'
      end
  with transfer_forall_parse_of_production
         str1 str2 pat
         (HR : R str1 str2)
         {p}
         {struct p}
       : @Forall_parse_of_production Char HSL1 G (fun _ => P) str1 pat p
         -> @Forall_parse_of_production Char HSL2 G (fun _ => P) str2 pat (transfer_parse_of_production HR p)
       := match
           p in (parse_of_production _ _ pat)
           return
           (@Forall_parse_of_production Char HSL1 G (fun _ => P) str1 pat p
            -> @Forall_parse_of_production Char HSL2 G (fun _ => P) str2 pat (transfer_parse_of_production HR p))
         with
           | ParseProductionNil _ => fun x => x
           | ParseProductionCons _ _ _ p0 p1
             => fun xy
                => (@transfer_forall_parse_of_item' (@transfer_forall_parse_of) _ _ _ _ p0 (fst xy),
                    @transfer_forall_parse_of_production _ _ _ _ p1 (snd xy))
         end.

  Global Arguments transfer_forall_parse_of {_ _ _} HR {_} _.
  Global Arguments transfer_forall_parse_of_production {_ _ _} HR {_} _.

  Definition transfer_forall_parse_of_item
             {str1 str2 it}
             (HR : R str1 str2)
             {p}
  : @Forall_parse_of_item Char HSL1 G (fun _ => P) str1 it p
    -> @Forall_parse_of_item Char HSL2 G (fun _ => P) str2 it (transfer_parse_of_item HR p)
    := @transfer_forall_parse_of_item' (@transfer_forall_parse_of) str1 str2 it HR p.
End cfg.
