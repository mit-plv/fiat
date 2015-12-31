Require Import Coq.Strings.Ascii.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.Enumerable.BoolProp.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.FlattenList.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.StringOperations.
Require Import Fiat.Common.StringFacts.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.

Local Open Scope type_scope.

Definition default_nonterminal_carrierT : Type := nat.
(** (nonterminal, production_index, drop_count) *)
Definition default_production_carrierT : Type
  := default_nonterminal_carrierT * (nat * nat).

Global Instance dnc_BoolDecR : BoolDecR default_nonterminal_carrierT := _.
Global Instance dnc_BoolDec_bl : BoolDec_bl (@eq default_nonterminal_carrierT)
  := _.
Global Instance dnc_BoolDec_lb : BoolDec_lb (@eq default_nonterminal_carrierT)
  := _.

Local Ltac eassumption' :=
  idtac;
  match goal with
    | [ H : _ |- _ ] => solve [ refine H ]
  end.

Definition default_production_carrierT_beq : default_production_carrierT -> default_production_carrierT -> bool
  := Equality.beq.
Definition default_production_carrierT_bl
: forall {x y}, default_production_carrierT_beq x y = true -> x = y
  := Equality.bl.
Definition default_production_carrierT_lb
: forall {x y}, x = y -> default_production_carrierT_beq x y = true
  := Equality.lb.

Section grammar.
  Context {Char} {G : grammar Char}.

  Local Notation unique_valid_nonterminals := (uniquize string_beq (Valid_nonterminals G)).

  Definition some_invalid_nonterminal
    := string_copy (S (List.fold_right max 0 (List.map String.length unique_valid_nonterminals))) "a"%char.

  Lemma some_invalid_nonterminal_invalid_helper
  : forall x, List.In x unique_valid_nonterminals -> String.length x < String.length some_invalid_nonterminal.
  Proof.
    unfold some_invalid_nonterminal in *.
    induction unique_valid_nonterminals as [|x xs IHxs].
    { intros ? []. }
    { intros nt H.
      destruct H as [H|H]; subst.
      { clear IHxs; simpl.
        rewrite string_copy_length; simpl.
        apply Max.max_case_strong; simpl; intros; omega. }
      { specialize (IHxs _ H).
        rewrite string_copy_length in IHxs |- *; simpl in *.
        apply Max.max_case_strong; omega. } }
  Qed.
  Lemma some_invalid_nonterminal_invalid'
  : ~List.In some_invalid_nonterminal unique_valid_nonterminals.
  Proof.
    intro H; apply some_invalid_nonterminal_invalid_helper in H.
    omega.
  Qed.
  Lemma some_invalid_nonterminal_invalid
  : ~List.In some_invalid_nonterminal (Valid_nonterminals G).
  Proof.
    intro H; apply some_invalid_nonterminal_invalid'.
    apply uniquize_In_refl.
    { apply string_lb; reflexivity. }
    { apply @string_bl. }
    { assumption. }
  Qed.

  Definition default_to_nonterminal
  : default_nonterminal_carrierT -> String.string
    := fun nt => List.nth nt unique_valid_nonterminals some_invalid_nonterminal.

  Section index.
    Context (idx : default_production_carrierT).

    Let nt_idx := fst idx.
    Let nts := (Lookup G (default_to_nonterminal nt_idx)).
    Let ps_idx := List.length nts - S (fst (snd idx)).
    Let drop_count := snd (snd idx).
    Let ps := (List.nth ps_idx nts nil).

    Definition default_to_production : production Char
    := List.drop drop_count ps.

    Definition default_production_tl : default_production_carrierT
      := (nt_idx,
          (fst (snd idx),
           if Compare_dec.leb (S drop_count) (List.length ps)
           then S drop_count
           else drop_count)).

    Definition default_production_carrier_valid : bool
      := ((Compare_dec.leb (S nt_idx) (List.length unique_valid_nonterminals))
            && ((Compare_dec.leb (S (fst (snd idx))) (List.length nts))
                  && (Compare_dec.leb drop_count (List.length ps))))%bool.
  End index.

  Global Instance default_production_carrier_valid_enumerable
  : Enumerable { idx : default_production_carrierT | is_true (default_production_carrier_valid idx) }.
  Proof.
    exact _.
  Defined.
End grammar.
