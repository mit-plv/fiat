Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.ContextFreeGrammar.Notations.
Require Import Fiat.Common.StringOperations Fiat.Common.StringFacts.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.String.

Require Import Fiat.Parsers.Grammars.JSON.

Local Arguments Equality.ascii_beq !_ !_.
Local Arguments Equality.string_beq !_ !_.
Local Arguments list_to_productions / .
Local Arguments ascii_of_nat !_ / .
Local Arguments ascii_of_pos !_ / .

Local Notation LF := (ascii_of_nat 10).
Local Notation CR := (ascii_of_nat 13).
Local Notation TAB := (ascii_of_nat 9).
Local Notation SPACE := " "%char.

Local Coercion test_string_of_ascii (ch : ascii) := String.String ch EmptyString.
Global Arguments test_string_of_ascii / .

Local Notation newline := (String.String LF EmptyString).

Local Ltac unfolder :=
  unfold Lookup;
  repeat match goal with
         | [ |- context[Operations.List.first_index_error ?f ?ls] ]
           => let c := constr:(Operations.List.first_index_error f ls) in
              let c' := (eval cbv in c) in
              change c with c'
         | _ => progress unfold option_rect
         | _ => progress unfold nth
         end.

Local Ltac safe_step :=
  idtac;
  (match goal with
   | _ => reflexivity
   | [ |- context[Valid_nonterminals ?G] ]
     => let c := constr:(Valid_nonterminals G) in
        let c' := (eval cbv in c) in
        change c with c'
   | [ |- context G[Lookup ?x ?y] ]
     => is_var x;
        let x' := (eval unfold x in x) in
        let G' := context G[Lookup x' y] in
        change G';
        unfolder
   | [ |- parse_of_production _ ?s (Terminal _ :: _) ]
     => apply ParseProductionCons with (n := 1)
   | [ |- parse_of_production _ ?s (_ :: nil) ]
     => apply ParseProductionCons with (n := String.length s)
   | [ |- parse_of_production _ ?s (_ :: nil) ]
     => apply ParseProductionCons with (n := String.length s)
   | [ |- parse_of_production _ ?s (_ :: Terminal _ :: nil) ]
     => apply ParseProductionCons with (n := String.length s - 1)
   | [ |- parse_of_production _ ?s (_ :: Terminal _ :: Terminal _ :: nil) ]
     => apply ParseProductionCons with (n := String.length s - 2)
   | [ |- parse_of_production _ _ nil ]
     => apply ParseProductionNil
   | [ |- parse_of_item _ (String.String ?ch EmptyString) (Terminal _) ]
     => refine (ParseTerminal _ _ ch _ _ _); simpl; reflexivity
   | [ |- parse_of_item _ _ (Terminal _) ]
     => (refine (ParseTerminal _ _ _ _ _ _);
          simpl;
          erewrite ?Equality.ascii_lb by reflexivity;
          reflexivity)
   | [ |- parse_of_item _ _ (NonTerminal _) ]
     => apply ParseNonTerminal
   | [ |- parse_of _ _ (_::nil) ] => apply ParseHead
   | [ |- parse_of _ ?s (nil::_) ]
     => first [ unify s ""%string; apply ParseHead
              | apply ParseTail ]
    | [ |- parse_of _ (String.String ?ch _) (((Terminal (Equality.ascii_beq ?ch')):: _)::_) ]
      => first [ unify ch ch'; fail 1
               | apply ParseTail ]
   | [ |- is_true (is_char (take 1 _) _) ] => apply get_0
   | _ => progress simpl
   | _ => tauto
   end).

Section json.
  Example json_parses_singleline : parse_of_grammar ("[ " ++ CR ++ LF ++ TAB ++ """xy ]z\"""" ]")%string json_grammar.
  Proof.
    hnf.
    Opaque json_grammar.
    simpl.
    Transparent json_grammar.
    set (x := json_grammar).
    set (y := Start_productions x).
    unfold json_grammar in x; simpl in x.
    unfold list_to_grammar in x.
    simpl @map in x.
    unfold list_to_productions in x.
    repeat
    match eval unfold x in x with
    | context[Operations.List.uniquize ?beq ?ls]
      => let c := constr:(Operations.List.uniquize beq ls) in
         change c with ls in (value of x)
    end.
    simpl @map in x.
    simpl @hd in x.
    unfold Start_productions in y.
    Set Printing Coercions.
    unfold Start_symbol in y.
    unfold x at 2 in (value of y).
    unfold Lookup in y.
    unfold x in y.
    Time match eval unfold y in y with
    | context[Operations.List.first_index_error ?f ?ls]
      => let c := constr:(Operations.List.first_index_error f ls) in
         let c' := (eval cbv in c) in
         change c with c' in (value of y)
         end.
    unfold option_rect in y.
    unfold nth in y.
    subst y.
    apply ParseTail; repeat safe_step.
    apply ParseHead; repeat safe_step.
    apply ParseProductionCons with (n := 4); repeat safe_step.
    apply ParseProductionCons with (n := 9); simpl; repeat safe_step.
    { apply ParseHead; repeat safe_step.
      apply ParseProductionCons with (n := 1); repeat safe_step.
      apply ParseProductionCons with (n := 1); repeat safe_step.
      apply ParseProductionCons with (n := 1); repeat safe_step.
      apply ParseProductionCons with (n := 1); repeat safe_step.
      apply ParseProductionCons with (n := 1); repeat safe_step.
      apply ParseHead; repeat safe_step.
      apply ParseProductionCons with (n := 1); repeat safe_step. }
    { apply ParseProductionCons with (n := 1); simpl; repeat safe_step. }
  Qed.
End json.
