(** * Definition of ε, the CFG accepting only "" *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Section generic.
  Variable CharType : Type.
  Variable String : string_like CharType.

  Definition trivial_grammar : grammar CharType :=
    {| Start_symbol := "";
       Lookup := fun _ => nil::nil;
       Valid_nonterminals := ""%string::nil |}.

  Definition trivial_grammar_parses_empty_string : parse_of_grammar _ (Empty String) trivial_grammar.
  Proof.
    hnf; simpl.
    apply ParseHead.
    constructor.
  Defined.

  Lemma trivial_grammar_parses_only_empty_string s : parse_of_grammar _ s trivial_grammar -> s = Empty String.
  Proof.
    intro H; hnf in H; simpl in H.
    repeat match goal with
             | _ => reflexivity
             | [ H : parse_of _ _ _ _ |- _ ] => inversion_clear H
             | [ H : parse_of_production _ _ _ _ |- _ ] => inversion_clear H
           end.
  Qed.
End generic.
