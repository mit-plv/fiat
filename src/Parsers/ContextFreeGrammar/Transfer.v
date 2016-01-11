(** * Properties about Context Free Grammars *)
Require Import Fiat.Parsers.StringLike.Core Fiat.Parsers.ContextFreeGrammar.Core.

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.

Section cfg.
  Context {Char} {HSLM1 HSLM2 : StringLikeMin Char}
          {HSL1 : @StringLike _ HSLM1}
          {HSL2 : @StringLike _ HSLM2}
          (G : @grammar Char).
  Context (R : @String _ HSLM1 -> @String _ HSLM2 -> Prop).
  Class transfer_respectful :=
    { is_char_respectful : forall str1 str2 ch,
                             R str1 str2 -> is_char str1 ch -> is_char str2 ch;
      is_empty_respectful : forall str1 str2,
                              R str1 str2 -> length str1 = 0 -> length str2 = 0;
      take_respectful : forall str1 str2 n,
                          R str1 str2 -> R (take n str1) (take n str2);
      drop_respectful : forall str1 str2 n,
                          R str1 str2 -> R (drop n str1) (drop n str2) }.
  Context {is_respectful : transfer_respectful}.

  Fixpoint transfer_parse_of {str1 str2 pats} (H : R str1 str2) (p : parse_of G str1 pats)
  : parse_of G str2 pats
    := match p in (parse_of _ _ pats) return parse_of _ _ pats with
         | ParseHead _ _ p' => ParseHead _ (@transfer_parse_of_production _ _ _ H p')
         | ParseTail _ _ p' => ParseTail _ (@transfer_parse_of _ _ _ H p')
       end
  with transfer_parse_of_production {str1 str2 pat} (H : R str1 str2) (p : parse_of_production G str1 pat)
  : parse_of_production G str2 pat
       := match p in (parse_of_production _ _ pat) return parse_of_production _ _ pat with
            | ParseProductionNil pf => ParseProductionNil _ _ (@is_empty_respectful _ _ _ H pf)
            | ParseProductionCons _ _ _ p0 p1
              => ParseProductionCons
                   _ _
                   (@transfer_parse_of_item _ _ _ (@take_respectful _ _ _ _ H) p0)
                   (@transfer_parse_of_production _ _ _ (@drop_respectful _ _ _ _ H) p1)
          end
  with transfer_parse_of_item {str1 str2 it} (H : R str1 str2) (p : parse_of_item G str1 it)
  : parse_of_item G str2 it
       := match p in (parse_of_item _ _ it) return parse_of_item _ _ it with
            | ParseTerminal _ _ pf1 pf2 => ParseTerminal _ _ _ _ pf1 (@is_char_respectful _ _ _ _ H pf2)
            | ParseNonTerminal _ H' p' => ParseNonTerminal _ H' (@transfer_parse_of _ _ _ H p')
          end.
End cfg.
