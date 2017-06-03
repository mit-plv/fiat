(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.ContextFreeGrammar.Properties Fiat.Parsers.WellFoundedParse.
Require Import Fiat.Parsers.CorrectnessBaseTypes Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Export Fiat.Parsers.MinimalParse.
Require Export Fiat.Parsers.WellFoundedParseProperties.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Notation "f ∘ g" := (fun x => f (g x)).

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}.
  Context (nonterminals_listT_R_respectful : forall x y,
                                        sub_nonterminals_listT x y
                                        -> x <> y
                                        -> nonterminals_listT_R x y).

  Lemma strle_from_min_parse_of_production {len0 valid strs pats}
        (p1 : minimal_parse_of_production (G := G) len0 valid strs pats)
  : length strs <= len0.
  Proof.
    destruct p1; omega.
  Qed.

  Definition parse_of_item_nonterminal__of__minimal_parse_of_nonterminal'
             (parse_of__of__minimal_parse_of
              : forall len0 valid str prods,
                  minimal_parse_of (G := G) len0 valid str prods
                  -> parse_of G str prods)
             {len0 valid str nonterminal} (p : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal)
  : parse_of_item G str (NonTerminal nonterminal)
    := let p'
           := (@parse_of__of__minimal_parse_of
                 _ _ _ _
                 (match p as p in (@MinimalParse.minimal_parse_of_nonterminal _ _ _ _ _ len0 valid str nonterminal)
                        return minimal_parse_of (match p with
                                                   | MinParseNonTerminalStrLt _ _ _ _ _ _ _ => _
                                                   | MinParseNonTerminalStrEq _ _ _ _ _ _ _ _ => _
                                                 end)
                                                (match p with
                                                   | MinParseNonTerminalStrLt _ _ _ _ _ _ _ => _
                                                   | MinParseNonTerminalStrEq _ _ _ _ _ _ _ _ => _
                                                 end)
                                                str (Lookup G nonterminal) with
                    | MinParseNonTerminalStrLt len0 valid nonterminal str pf pf' p' => p'
                    | MinParseNonTerminalStrEq len0 str valid nonterminal pf H H' p' => p'
                  end)) in
       let pf := (match p in (@MinimalParse.minimal_parse_of_nonterminal _ _ _ _ _ len0 valid str nonterminal)
                        return (is_valid_nonterminal initial_nonterminals_data (of_nonterminal nonterminal))
                  with
                    | MinParseNonTerminalStrLt _ _ _ _ _ pf _ => pf
                    | MinParseNonTerminalStrEq _ _ _ _ _ pf _ _ => pf
                  end) in
       (ParseNonTerminal
          nonterminal
          (proj1 (initial_nonterminals_correct _) pf)
          p').

  Definition parse_of_item__of__minimal_parse_of_item'
             (parse_of__of__minimal_parse_of
              : forall len0 valid str prods,
                  minimal_parse_of (G := G) len0 valid str prods
                  -> parse_of G str prods)
             {len0 valid str it} (p : minimal_parse_of_item (G := G) len0 valid str it)
  : parse_of_item G str it
    := match p in (MinimalParse.minimal_parse_of_item len0 valid str it)
             return parse_of_item G str it
       with
         | MinParseTerminal len0 valid str ch P pf1 pf2
           => ParseTerminal G str ch P pf1 pf2
         | MinParseNonTerminal len0 valid _ _ p'
           => @parse_of_item_nonterminal__of__minimal_parse_of_nonterminal' (@parse_of__of__minimal_parse_of) _ _ _ _ p'
       end.

  Fixpoint parse_of__of__minimal_parse_of {len0 valid str pats} (p : minimal_parse_of (G := G) len0 valid str pats)
  : parse_of G str pats
    := match p with
         | MinParseHead len0 valid str pat pats p'
           => let p'' := (parse_of_production__of__minimal_parse_of_production p') in
              ParseHead pats p''
         | MinParseTail len0 valid str pat pats p'
           => let p'' := (parse_of__of__minimal_parse_of p') in
              ParseTail pat p''
       end
  with parse_of_production__of__minimal_parse_of_production {len0 valid str pat} (p : minimal_parse_of_production (G := G) len0 valid str pat)
       : parse_of_production G str pat
       := match p with
            | MinParseProductionNil len0 valid str pf
              => ParseProductionNil _ _ pf
            | MinParseProductionCons len0 valid str strs pat pats pf p' p''
              => let p0 := (parse_of_item__of__minimal_parse_of_item' (@parse_of__of__minimal_parse_of) p') in
                 let p1 := (parse_of_production__of__minimal_parse_of_production p'') in
                 ParseProductionCons _ _ p0 p1
          end.

  Definition parse_of_item_nonterminal__of__minimal_parse_of_nonterminal
  : forall {len0 valid str nonterminal} (p : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal),
      parse_of_item G str (NonTerminal nonterminal)
    := @parse_of_item_nonterminal__of__minimal_parse_of_nonterminal' (@parse_of__of__minimal_parse_of).

  Definition parse_of_item__of__minimal_parse_of_item
  : forall {len0 valid str it},
      minimal_parse_of_item (G := G) len0 valid str it
      -> parse_of_item G str it
    := @parse_of_item__of__minimal_parse_of_item' (@parse_of__of__minimal_parse_of).

  (** Re-add this so rewrite works *)
  Global Add Parametric Morphism : remove_nonterminal
  with signature sub_nonterminals_listT ==> eq ==> sub_nonterminals_listT
    as remove_nonterminal_mor.
  Proof.
    intros; apply (@remove_nonterminal_mor _ G); try assumption; reflexivity.
  Qed.

  Local Ltac clear_not_beq
    := repeat match goal with
                | [ H : ?T |- _ ]
                  => match T with
                       | beq _ _ => fail 1
                       | _ < _ => fail 1
                       | _ ≤s _ => fail 1
                       | _ = _ => fail 1
                       | _ <= _ => fail 1
                       | _ ~= [ _ ] => fail 1
                       | StringLikeProperties _ => fail 1
                       | _ => clear H
                     end
              end.

  Local Ltac solve_by_subst tac :=
    repeat subst;
    match goal with
      | [ |- beq _ _ ] => idtac
      | [ |- beq _ _ \/ _ ] => idtac
      | [ |- _ \/ beq _ _ ] => idtac
      | [ |- _ = _ \/ _ ] => idtac
      | [ |- _ \/ _ = _ ] => idtac
      | [ |- _ < _ ] => idtac
      | [ |- _ <= _ ] => idtac
      | [ |- _ = _ ] => idtac
      | [ |- _ ≤s _ ] => idtac
      | [ |- False ] => idtac
    end;
    clear_not_beq;
    repeat match goal with
             | [ H : @beq ?string ?SLM ?SL _ _ |- _ ] => setoid_subst_rel (@beq string SLM SL)
           end;
    solve [ assumption | reflexivity | left; reflexivity | right; reflexivity | tac ].

  Section expand.
    Local Notation Hlen0T len0 len0' str str'
      := (len0 <= len0'
          \/ (length str < len0 /\ length str' < len0')
          \/ (length str = len0%nat /\ length str' = len0'%nat)) (only parsing).

    Definition expand_minimal_parse_of_nonterminal'
               (expand_minimal_parse_of
                : forall {len0 len0' valid valid' str str' prods}
                         (Hlen0 : Hlen0T len0 len0' str str')
                         (H : sub_nonterminals_listT valid valid')
                         (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
                         (Hstr : str =s str')
                         (p : minimal_parse_of (G := G) len0 valid str prods),
                    minimal_parse_of (G := G) len0' valid' str' prods)
               {len0 len0' valid valid' str str' nonterminal}
               (Hlen0 : Hlen0T len0 len0' str str')
               (H : sub_nonterminals_listT valid valid')
               (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
               (Hstr : str =s str')
               (p : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal)
    : minimal_parse_of_nonterminal (G := G) len0' valid' str' nonterminal.
    Proof.
      destruct p;
      first [ apply MinParseNonTerminalStrLt;
              destruct_head or;
              destruct_head and; repeat subst;
              solve [ rewrite <- Hstr; omega
                    | assumption
                    | eapply expand_minimal_parse_of; [ .. | eassumption ];
                      solve [ reflexivity
                            | left; rewrite Hstr; reflexivity
                            | rewrite Hstr; reflexivity ] ]
            | idtac ];
      [].
      { destruct (lt_eq_lt_dec len0 len0') as [[Hlen0'|Hlen0']|Hlen0'];
        [ apply MinParseNonTerminalStrLt
        | apply MinParseNonTerminalStrEq
        | destruct (lt_eq_lt_dec (length str') len0') as [[Hlen0''|Hlen0'']|Hlen0''];
          [ apply MinParseNonTerminalStrLt
          | apply MinParseNonTerminalStrEq
          | exfalso ] ];
        solve [ assumption
              | apply H; assumption
              | solve_by_subst idtac
              | eapply expand_minimal_parse_of; [ .. | eassumption ];
                solve [ reflexivity
                      | rewrite !H;
                        eauto using sub_nonterminals_listT_remove;
                        reflexivity
                      | solve_by_subst idtac
                      | destruct Hinit as [Hinit|Hinit];
                        [ exfalso; clear_not_beq; setoid_subst_rel beq; omega
                        | ];
                        rewrite ?H, !Hinit;
                        eauto using sub_nonterminals_listT_remove;
                        reflexivity
                      | destruct_head or; destruct_head and; repeat subst; omega ]
              | destruct_head or; destruct_head and; repeat subst; omega
              | setoid_subst_rel beq; subst; assumption ]. }
    Defined.

    Definition expand_minimal_parse_of_item'
               (expand_minimal_parse_of
                : forall {len0 len0' valid valid' str str' prods}
                         (Hlen0 : Hlen0T len0 len0' str str')
                         (H : sub_nonterminals_listT valid valid')
                         (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
                         (Hstr : str =s str')
                         (p : minimal_parse_of (G := G) len0 valid str prods),
                    minimal_parse_of (G := G) len0' valid' str' prods)
               {len0 len0' valid valid' str str' it}
               (Hlen0 : Hlen0T len0 len0' str str')
               (H : sub_nonterminals_listT valid valid')
               (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
               (Hstr : str =s str')
               (p : minimal_parse_of_item (G := G) len0 valid str it)
    : minimal_parse_of_item (G := G) len0' valid' str' it.
    Proof.
      destruct p.
      { eapply MinParseTerminal; setoid_subst_rel beq; trivial; eassumption. }
      { apply MinParseNonTerminal; [].
        eapply expand_minimal_parse_of_nonterminal'; [..| eassumption ];
        try assumption. }
    Defined.

    Lemma expand_helper_1 {len0 len0' str str'}
          (pf : length str <= len0)
          (Hlen0 : Hlen0T len0 len0' str str')
          (Hstr : str =s str')
    : length str' <= len0'.
    Proof.
      setoid_subst_rel beq.
      destruct_head or; omega.
    Qed.

    Lemma Hlen0_take {len0 len0' str str' n}
          (Hlen0 : Hlen0T len0 len0' str str')
          (Hstr : str =s str')
    : Hlen0T len0 len0' (take n str) (take n str').
    Proof.
      setoid_subst str'.
      rewrite take_length.
      apply Min.min_case_strong; omega.
    Qed.

    Lemma Hlen0_drop {len0 len0' str str' n}
          (Hlen0 : Hlen0T len0 len0' str str')
          (Hstr : str =s str')
    : Hlen0T len0 len0' (drop n str) (drop n str').
    Proof.
      setoid_subst str'.
      rewrite drop_length.
      omega.
    Qed.

    Fixpoint expand_minimal_parse_of
             {len0 len0' valid valid' str str' pats}
             (Hlen0 : Hlen0T len0 len0' str str')
             (H : sub_nonterminals_listT valid valid')
             (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
             (Hstr : str =s str')
             (p : minimal_parse_of (G := G) len0 valid str pats)
    : minimal_parse_of (G := G) len0' valid' str' pats
      := match p in (MinimalParse.minimal_parse_of len0 valid str pats)
               return ((Hlen0T len0 len0' str str')
                       -> sub_nonterminals_listT valid valid'
                       -> len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data
                       -> str =s str'
                       -> minimal_parse_of (G := G) len0' valid' str' pats)
         with
           | MinParseHead len0 valid str pat pats p'
             => fun Hlen0 H Hinit Hstr => MinParseHead pats (@expand_minimal_parse_of_production _ _ _ _ _ _ _ Hlen0 H Hinit Hstr p')
           | MinParseTail len0 valid str pat pats p'
             => fun Hlen0 H Hinit Hstr => MinParseTail pat (@expand_minimal_parse_of _ _ _ _ _ _ _ Hlen0 H Hinit Hstr p')
         end Hlen0 H Hinit Hstr
    with expand_minimal_parse_of_production
           {len0 len0' valid valid' str str' pat}
           (Hlen0 : Hlen0T len0 len0' str str')
           (H : sub_nonterminals_listT valid valid')
           (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
           (Hstr : str =s str')
           (p : minimal_parse_of_production (G := G) len0 valid str pat)
         : minimal_parse_of_production (G := G) len0' valid' str' pat
         := match p in (MinimalParse.minimal_parse_of_production len0 valid str pats)
                  return (Hlen0T len0 len0' str str'
                          -> sub_nonterminals_listT valid valid'
                          -> len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data
                          -> str =s str'
                          -> minimal_parse_of_production len0' valid' str' pats)
            with
              | MinParseProductionNil len0 valid str pf
                => fun _ _ _ Hstr => MinimalParse.MinParseProductionNil _ _ str' (transitivity (symmetry ((_ : Proper (beq ==> eq) length) _ _ Hstr))  pf)
              | MinParseProductionCons len0 valid str n pat pats pf p' p''
                => fun Hlen0 H Hinit Hstr
                   => MinParseProductionCons
                        _
                        n
                        (expand_helper_1 pf Hlen0 Hstr)
                        (expand_minimal_parse_of_item' (@expand_minimal_parse_of) (Hlen0_take Hlen0 Hstr) H Hinit ((_ : Proper (eq ==> beq ==> beq) take) _ _ eq_refl _ _ Hstr) p')
                        (@expand_minimal_parse_of_production _ _ _ _ _ _ _ (Hlen0_drop Hlen0 Hstr) H Hinit ((_ : Proper (eq ==> beq ==> beq) drop) _ _ eq_refl _ _ Hstr) p'')
            end Hlen0 H Hinit Hstr.

    Definition expand_minimal_parse_of_nonterminal
    : forall {len0 len0' valid valid' str str' nonterminal}
             (Hlen0 : Hlen0T len0 len0' str str')
             (H : sub_nonterminals_listT valid valid')
             (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
             (Hstr : str =s str')
             (p : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal),
        minimal_parse_of_nonterminal (G := G) len0' valid' str' nonterminal
      := @expand_minimal_parse_of_nonterminal' (@expand_minimal_parse_of).

    Definition expand_minimal_parse_of_item
    : forall {len0 len0' valid valid' str str' it}
             (Hlen0 : Hlen0T len0 len0' str str')
             (H : sub_nonterminals_listT valid valid')
             (Hinit : len0 = len0' \/ sub_nonterminals_listT valid' initial_nonterminals_data)
             (Hstr : str =s str')
             (p : minimal_parse_of_item (G := G) len0 valid str it),
        minimal_parse_of_item (G := G) len0' valid' str' it
      := @expand_minimal_parse_of_item' (@expand_minimal_parse_of).
  End expand.

  Section expand_beq.
    Definition expand_minimal_parse_of_beq
             {len0 valid str str' pats}
             (Hstr : str =s str')
             (p : minimal_parse_of (G := G) len0 valid str pats)
    : minimal_parse_of (G := G) len0 valid str' pats.
    Proof.
      eapply expand_minimal_parse_of; try (eassumption || reflexivity || left; reflexivity).
    Defined.

    Definition expand_minimal_parse_of_production_beq
               {len0 valid str str' pat}
               (Hstr : str =s str')
               (p : minimal_parse_of_production (G := G) len0 valid str pat)
    : minimal_parse_of_production (G := G) len0 valid str' pat.
    Proof.
      eapply expand_minimal_parse_of_production; try (eassumption || reflexivity || left; reflexivity).
    Defined.

    Definition expand_minimal_parse_of_nonterminal_beq
               {len0 valid str str' nonterminal}
               (Hstr : str =s str')
               (p : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal)
    : minimal_parse_of_nonterminal (G := G) len0 valid str' nonterminal.
    Proof.
      eapply expand_minimal_parse_of_nonterminal; try (eassumption || reflexivity || left; reflexivity).
    Defined.

    Definition expand_minimal_parse_of_item_beq
               {len0 valid str str' it}
               (Hstr : str =s str')
               (p : minimal_parse_of_item (G := G) len0 valid str it)
    : minimal_parse_of_item (G := G) len0 valid str' it.
    Proof.
      eapply expand_minimal_parse_of_item; try (eassumption || reflexivity || left; reflexivity).
    Defined.
  End expand_beq.


  Section contract.
    Local Hint Constructors MinimalParse.minimal_parse_of_nonterminal.

    Definition contract_minimal_parse_of_nonterminal_lt
               {len0 str valid valid' nonterminal}
               (Hlt : length str < len0)
               (p : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal)
    : minimal_parse_of_nonterminal (G := G) len0 valid' str nonterminal.
    Proof.
      destruct p.
      { constructor; assumption. }
      { exfalso; clear_not_beq; setoid_subst_rel beq; omega. }
    Defined.

    Definition contract_minimal_parse_of_item_lt
               {len0 str valid valid' it}
               (Hlt : length str < len0)
               (p : minimal_parse_of_item (G := G) len0 valid str it)
    : minimal_parse_of_item (G := G) len0 valid' str it.
    Proof.
      destruct p as [p|p].
      { econstructor; trivial; eassumption. }
      { constructor; eapply contract_minimal_parse_of_nonterminal_lt; eassumption. }
    Defined.

    Definition contract_minimal_parse_of_production_lt
               {len0 str valid valid' pat}
               (Hlt : length str < len0)
               (p : minimal_parse_of_production (G := G) len0 valid str pat)
    : minimal_parse_of_production (G := G) len0 valid' str pat.
    Proof.
      induction p.
      { constructor; trivial. }
      { apply (MinParseProductionCons _ n); trivial;
        try first [ eapply contract_minimal_parse_of_item_lt; try eassumption
                  | eapply IHp; try eassumption
                  | assumption ];
        clear -Hlt HSLP;
        abstract (rewrite ?str_le_take, ?str_le_drop; assumption). }
    Defined.

    Definition contract_minimal_parse_of_lt
               {len0 str valid valid' pats}
               (Hlt : length str < len0)
               (p : minimal_parse_of (G := G) len0 valid str pats)
    : minimal_parse_of (G := G) len0 valid' str pats.
    Proof.
      induction p.
      { constructor; eapply contract_minimal_parse_of_production_lt; eassumption. }
      { constructor; eapply IHp; assumption. }
    Defined.

    Section contract_eq.
      Lemma parse_of_contract_minimal_parse_of_item_lt
            {len0} {str : String} {valid valid' : nonterminals_listT}
            {Hlt : length str < len0}
            {it}
            (p : minimal_parse_of_item (G := G) len0 valid str it)
      : parse_of_item__of__minimal_parse_of_item
          (contract_minimal_parse_of_item_lt (valid' := valid') Hlt p)
        = parse_of_item__of__minimal_parse_of_item p.
      Proof.
        destruct_head @MinimalParse.minimal_parse_of_item; simpl; try reflexivity.
        destruct_head @MinimalParse.minimal_parse_of_nonterminal; try reflexivity.
        unfold False_rect.
        match goal with
          | [ |- context[match ?e with end] ] => destruct e
        end.
      Qed.

      Lemma parse_of_contract_minimal_parse_of_production_lt
            {len0} {str : String} {valid valid' : nonterminals_listT}
            {Hlt : length str < len0}
            {pat}
            (p : minimal_parse_of_production (G := G) len0 valid str pat)
      : parse_of_production__of__minimal_parse_of_production
          (contract_minimal_parse_of_production_lt (valid' := valid') Hlt p)
        = parse_of_production__of__minimal_parse_of_production p.
      Proof.
        induction p; simpl; try reflexivity.
        fold @parse_of_item__of__minimal_parse_of_item in *.
        rewrite IHp, parse_of_contract_minimal_parse_of_item_lt.
        reflexivity.
      Qed.

      Lemma parse_of_contract_minimal_parse_of_lt
            {len0} {str : String} {valid valid' : nonterminals_listT}
            {Hlt : length str < len0}
            {pats}
            (p : minimal_parse_of (G := G) len0 valid str pats)
      : parse_of__of__minimal_parse_of
          (contract_minimal_parse_of_lt (valid' := valid') Hlt p)
        = parse_of__of__minimal_parse_of p.
      Proof.
        induction p; simpl;
        progress rewrite ?IHp, ?parse_of_contract_minimal_parse_of_production_lt;
        reflexivity.
      Qed.
    End contract_eq.
  End contract.

  Section minimize.
    Let alt_option h valid str
      := { nonterminal : _ & (is_valid_nonterminal valid (of_nonterminal nonterminal) = false /\ is_valid_nonterminal initial_nonterminals_data (of_nonterminal nonterminal))
                      * { p : parse_of G str (Lookup G nonterminal)
                        | size_of_parse p < h } }%type.

    Lemma not_alt_all {h str} (ps : alt_option h initial_nonterminals_data str)
    : False.
    Proof.
      destruct ps as [ ? [ H' _ ] ].
      revert H'; clear; intros [? ?].
      congruence.
    Qed.

    Definition alt_all_elim {h str T} (ps : T + alt_option h initial_nonterminals_data str)
    : T.
    Proof.
      destruct ps as [|ps]; [ assumption | exfalso ].
      eapply not_alt_all; eassumption.
    Defined.

    Definition expand_alt_option' {h h' str str' valid valid'}
               (H : h <= h') (H' : sub_nonterminals_listT valid' valid) (H'' : str =s str')
    : alt_option h valid str -> alt_option h' valid' str'.
    Proof.
      hnf in H'; unfold alt_option.
      repeat match goal with
               | [ |- sigT _ -> _ ] => intros_destruct
               | [ |- sig _ -> _ ] => intros_destruct
               | [ |- prod _ _ -> _ ] => intros_destruct
               | [ |- and _ _ -> _ ] => intros_destruct
               | _ => intro
               | _ => progress subst
               | _ => rewrite <- size_of_parse_respectful
               | [ H : beq ?str ?str', p : parse_of ?G ?str ?n
                   |- { p' : parse_of ?G ?str' ?n | _ } ]
                 => exists (parse_of_respectful H (reflexivity _) p)
               | [ |- sigT _ ] => esplit
               | [ |- prod _ _ ] => split
               | [ |- and _ _ ] => split
               | [ H : _ = false |- _ = false ]
                 => apply Bool.not_true_iff_false in H;
                   apply Bool.not_true_iff_false;
                   intro; apply H
               | _ => eapply H'; eassumption
               | _ => assumption
               | [ |- _ < _ ] => eapply Lt.lt_trans; eassumption
               | [ |- _ < _ ] => eapply Lt.lt_le_trans; eassumption
             end.
    Defined.

    Definition expand_alt_option {h h' str str' valid valid'}
               (H : h < h') (H' : sub_nonterminals_listT valid' valid) (H'' : str =s str')
    : alt_option h valid str -> alt_option h' valid' str'.
    Proof.
      apply expand_alt_option'; try assumption.
      apply Lt.lt_le_weak; assumption.
    Defined.

    Section wf_parts.
      Let of_parse_item_T' h
          {len0} {str : String} (pf : length str <= len0)
          (valid : nonterminals_listT) {it : item Char}
          (p : parse_of_item G str it)
        := forall (p_small : size_of_parse_item p < h),
             sub_nonterminals_listT valid initial_nonterminals_data
             -> ({ p' : minimal_parse_of_item (G := G) len0 valid str it
                 | size_of_parse_item (parse_of_item__of__minimal_parse_of_item p') <= size_of_parse_item p })%type
                + alt_option (size_of_parse_item p) valid str.

      Let of_parse_item_T len0 h
        := forall str pf valid it p, @of_parse_item_T' h len0 str pf valid it p.

      Let of_parse_production_T' h
          {len0} {str : String} (pf : length str <= len0)
          (valid : nonterminals_listT) {pat : production Char}
          (p : parse_of_production G str pat)
        := forall (p_small : size_of_parse_production p < h),
             sub_nonterminals_listT valid initial_nonterminals_data
             -> ({ p' : minimal_parse_of_production (G := G) len0 valid str pat
                 | size_of_parse_production (parse_of_production__of__minimal_parse_of_production p') <= size_of_parse_production p })%type
                + alt_option (size_of_parse_production p) valid str.

      Let of_parse_production_T len0 h
        := forall str pf valid pat p, @of_parse_production_T' h len0 str pf valid pat p.

      Let of_parse_T' h
          {len0} {str : String} (pf : length str <= len0)
          (valid : nonterminals_listT) {pats : productions Char}
          (p : parse_of G str pats)
        := forall (p_small : size_of_parse p < h),
             sub_nonterminals_listT valid initial_nonterminals_data
             -> ({ p' : minimal_parse_of (G := G) len0 valid str pats
                 | (size_of_parse (parse_of__of__minimal_parse_of p') <= size_of_parse p) })%type
                + alt_option (size_of_parse p) valid str.

      Let of_parse_T len0 h
        := forall str pf valid pats p, @of_parse_T' h len0 str pf valid pats p.

      Let of_parse_nonterminal_T {len0 str valid nonterminal} (p : parse_of G str (Lookup G nonterminal)) h
        := forall Hvalid : List.In nonterminal (Valid_nonterminals G),
             size_of_parse_item (ParseNonTerminal _ Hvalid p) < h
             -> length str <= len0
             -> sub_nonterminals_listT valid initial_nonterminals_data
             -> ({ p' : minimal_parse_of_nonterminal (G := G) len0 valid str nonterminal
                 | size_of_parse_item (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) <= size_of_parse_item (ParseNonTerminal _ Hvalid p) })%type
                + alt_option (size_of_parse_item (ParseNonTerminal _ Hvalid p)) valid str.

      Section item.
        Context {len0 : nat} {str : String} {valid : nonterminals_listT}.

        Definition minimal_parse_of_item__of__parse_of_item'
                   h
                   (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                    : forall h' (pf : h' < S (S h)) {len0 str valid nonterminal}
                             (p : parse_of G str (Lookup G nonterminal)),
                        @of_parse_nonterminal_T len0 str valid nonterminal p h')
        : of_parse_item_T len0 h.
        Proof.
          intros str' pf valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [ ch P pf0 pf0' |nonterminal' ? p'].
          { left.
            eexists (MinimalParse.MinParseTerminal _ _ _ _ _ pf0 pf0');
              simpl; constructor. }
          { edestruct (fun pf => @minimal_parse_of_nonterminal__of__parse_of_nonterminal (S h') pf len0 _ valid' _ p') as [ [p'' H''] | p'' ];
            try solve [ repeat (apply Lt.lt_n_Sn || apply Lt.lt_S)
                      | exact Hinit'
                      | exact H_h
                      | exact H_forall
                      | exact pf ];
            [|];
            [ left | right ].
            { exists (MinParseNonTerminal p'').
              simpl in *.
              exact H''. }
            { exact p''. } }
        Defined.
      End item.

      Section production.
        Context {len0 : nat} {str : String} {valid : nonterminals_listT}.

        Local Ltac min_parse_prod_t' :=
          idtac;
          match goal with
            | _ => assumption
            | [ |- ?R ?x ?x ]
              => reflexivity
            | _ => progress destruct_head prod
            | [ H : False |- _ ]
              => solve [ destruct H ]
            | _ => progress simpl
            | _ => progress subst
            | _ => progress fold @parse_of_item__of__minimal_parse_of_item in *
            | _ => progress rewrite ?parse_of_contract_minimal_parse_of_item_lt, ?parse_of_contract_minimal_parse_of_production_lt, ?parse_of_contract_minimal_parse_of_lt
            | [ |- context G[size_of_parse_production (ParseProductionCons ?s ?n ?a ?b)] ]
              => let G' := context G[S (size_of_parse_item a + size_of_parse_production b)] in
                 change G'
            | [ H : alt_option _ initial_nonterminals_data _ |- _ ]
              => apply not_alt_all in H
            | [ p0 : minimal_parse_of_item ?ns' ?v (take ?n ?s) ?pat,
                     p1 : minimal_parse_of_production ?ns' ?v (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns'
                |- ({ p' : minimal_parse_of_production ?ns' ?v ?s (?pat :: ?pats) | _ } + _)%type ]
              => left; exists (MinParseProductionCons _ n H p0 p1)
            | [ p0 : minimal_parse_of_item ?ns' _ (take ?n ?s) ?pat,
                     p1 : minimal_parse_of_production ?ns' ?v (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns'
                |- ({ p' : minimal_parse_of_production ?ns' ?v ?s (?pat :: ?pats) | _ } + _)%type ]
              => let H' := fresh in
                 assert (H' : length (take n s) < ns')
                   by (rewrite <- H, ?take_short_length by omega; omega);
                   left; exists (MinParseProductionCons
                                   _
                                   n
                                   H
                                   (contract_minimal_parse_of_item_lt (valid' := v) H' p0)
                                   p1)
            | [ p0 : minimal_parse_of_item ?ns' ?v (take ?n ?s) ?pat,
                     p1 : minimal_parse_of_production ?ns' _ (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns'
                |- ({ p' : minimal_parse_of_production ?ns' ?v ?s (?pat :: ?pats) | _ } + _)%type ]
              => let H' := fresh in
                 assert (H' : length (drop n s) < ns')
                   by (rewrite <- H, drop_length; omega);
                   left; exists (MinParseProductionCons
                                   _
                                   n
                                   H
                                   p0
                                   (contract_minimal_parse_of_production_lt (valid' := v) H' p1))
            | [ p0 : minimal_parse_of_item ?ns' _ (take ?n ?s) ?pat,
                     p1 : minimal_parse_of_production ?ns' _ (drop ?n ?s) ?pats,
                          H : length ?s <= ?ns',
                              H' : ?n < length ?s,
                                   H'' : 0 < ?n
                |- ({ p' : minimal_parse_of_production ?ns' ?v ?s (?pat :: ?pats) | _ } + _)%type ]
              => let H0' := fresh in
                 let H1' := fresh in
                 assert (H1' : length (drop n s) < ns')
                   by (rewrite <- H, drop_length; omega);
                   assert (H0' : length (take n s) < ns')
                   by (rewrite <- H, ?take_short_length by omega; omega);
                   left; eexists (MinParseProductionCons
                                    _
                                    n
                                    H
                                    (contract_minimal_parse_of_item_lt (valid' := v) H0' p0)
                                    (contract_minimal_parse_of_production_lt (valid' := v) H1' p1))
            | [ |- (_ * _)%type ]
              => split
            | [ H : _ <= _ |- _ <= _ ] => apply H
            | _ => apply Le.le_n_S
            | _ => apply Plus.plus_le_compat
            | [ H0 : Forall_parse_of_item _ _,
                     H1 : Forall_parse_of_production _ _
                |- Forall_parse_of_production _ _ ]
              => exact (H0, H1)
            | [ H : alt_option _ ?v (drop 0 ?x)
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : alt_option _ ?v (drop ?n ?x), H' : length ?x <= ?n
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : alt_option _ ?v (take ?n ?x), H' : length ?x = ?n
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : alt_option _ ?v (take ?n ?x), H' : length ?x <= ?n
                |- (_ + alt_option _ ?v ?x)%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : length ?s = 0 |- beq _ ?s ] => apply bool_eq_empty
            | [ H : length ?s = 0 |- beq ?s _ ] => apply bool_eq_empty
            | _ => rewrite take_short_length by assumption
            | _ => rewrite take_long by assumption
            | [ H : context[min _ _] |- _ ] => rewrite min_l in H by assumption
            | [ H : context[min _ _] |- _ ] => rewrite min_r in H by assumption
            | [ H : context[min _ _] |- _ ] => rewrite min_l in H by omega
            | [ H : context[min _ _] |- _ ] => rewrite min_r in H by omega
            | _ => rewrite drop_length
            | _
              => solve [ eauto using le_S, Le.le_trans, Plus.le_plus_l, Plus.le_plus_r, drop_0, take_long, NPeano.Nat.eq_le_incl, bool_eq_empty, drop_length, (fun x y => proj2 (NPeano.Nat.sub_0_le x y)) with nocore ]
          end.
        Local Ltac min_parse_prod_t := repeat min_parse_prod_t'.

        (** This is the proof where we pay the proof for conceptual
            mismatch.  We are, conceptually, simultaneously
            "minimizing parse trees" and "producing parse traces".  It
            is marginally nicer(!!) to contain the ugliness in this
            single proof, rather than have it infect everything.  So
            we must conceptually minimize the passed parse tree while
            in fact building a trace of the parse algorithm.  To do
            this, in the cons case, we need to figure out how we're
            decreasing.  According with conceptual minimization, when
            we have parsed [s0 ++ s1] as a cons of [p0] and [p1],
            having a smaller parse tree for, say [s0], with any other
            pattern, does us no good, unless [s1] is empty (and [s0 =
            s0 ++ s1]), when we can simply pass that smaller parse up
            the function call tree.  So we must eliminate the
            "alternate" option, by expanding the valid list to the
            initial data.  Luckily(?!), in the case where [s1] is
            non-empty, [s0] is strictly smaller than [s0 ++ s1], and
            thus we can rebuild the minimal parse tree to contract it.
            This, finally, allows us to either build a minimal parse
            tree for the thing we are asked about (or to contract the
            "alternate option" parse tree, passing it back up?). *)

        Fixpoint minimal_parse_of_production__of__parse_of_production'
                 h
                 (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                  : forall h' (pf : h' < S (S h)) {len0 str valid nonterminal}
                           (p : parse_of G str (Lookup G nonterminal)),
                      @of_parse_nonterminal_T len0 str valid nonterminal p h')
                 {struct h}
        : of_parse_production_T len0 h.
        Proof.
          intros str' pf valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [ pf0' | n pat' pats' p0' p1' ].
          { clear minimal_parse_of_production__of__parse_of_production'.
            left.
            eexists (@MinimalParse.MinParseProductionNil _ _ _ _ _ _ _ _ pf0');
              repeat (reflexivity || esplit). }
          { specialize (fun h' pf
                        => @minimal_parse_of_nonterminal__of__parse_of_nonterminal
                             h' (transitivity pf (Lt.lt_n_Sn _))).
            change (S ((size_of_parse_item p0')
                       + (size_of_parse_production p1'))
                    < S h') in H_h.
            apply Lt.lt_S_n in H_h.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_l _ _) H_h) as H_h0.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_r _ _) H_h) as H_h1.
            clear H_h.
            assert (pf0' : length (take n str') <= length str')
              by (rewrite take_length; apply Min.min_case_strong; omega).
            assert (pf1' : length (drop n str') <= length str')
              by (rewrite drop_length; omega).
            pose proof (fun valid Hinit => @minimal_parse_of_item__of__parse_of_item' _ h'  minimal_parse_of_nonterminal__of__parse_of_nonterminal _ (transitivity pf0' pf) valid _ p0' H_h0 Hinit) as p_it.
            pose proof (fun valid Hinit => @minimal_parse_of_production__of__parse_of_production' h' minimal_parse_of_nonterminal__of__parse_of_nonterminal _ (transitivity pf1' pf) valid _ p1' H_h1 Hinit) as p_prod.
            clear pf0' pf1'.
            destruct (le_lt_dec (length str') n) as [ Hle | Hle ], (zerop (min n (length str'))) as [Hstr' | Hstr' ].
            { (* empty, empty *)
              rewrite Min.min_r in Hstr' by assumption.
              specialize (p_it valid' Hinit'); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* nonempty, empty *)
              specialize (p_it valid' Hinit'); specialize (p_prod initial_nonterminals_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* empty, nonempty *)
              specialize (p_it initial_nonterminals_data (reflexivity _)); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* nonempty, nonempty *)
              specialize (p_it initial_nonterminals_data (reflexivity _)); specialize (p_prod initial_nonterminals_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. } }
        Defined.
      End production.

      Section productions.
        Context {len0 : nat} {str : String} {valid : nonterminals_listT}.

        Fixpoint minimal_parse_of_productions__of__parse_of_productions'
                 h
                 (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                  : forall h' (pf : h' < S h) {len0 str valid nonterminal}
                           (p : parse_of G str (Lookup G nonterminal)),
                      @of_parse_nonterminal_T len0 str valid nonterminal p h')
                 {struct h}
        : of_parse_T len0 h.
        Proof.
          intros str' pf valid' pats p H_h Hinit'.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [pat pats p' | pat pats p'].
          { clear minimal_parse_of_productions__of__parse_of_productions'.
            edestruct (@minimal_parse_of_production__of__parse_of_production' _ h' minimal_parse_of_nonterminal__of__parse_of_nonterminal _ pf valid' _ p') as [ [p'' p''H] | [nonterminal' H'] ];
            try solve [ exact (Lt.lt_S_n _ _ H_h)
                      | exact H_forall
                      | exact Hinit' ];
            [|].
            { left.
              exists (MinParseHead pats p'').
              simpl.
              exact (Le.le_n_S _ _ p''H). }
            { right.
              exists nonterminal'.
              split;
                try solve [ exact (fst H') ];
                [].
              exists (proj1_sig (snd H')).
              exact (Lt.lt_S _ _ (proj2_sig (snd H'))). } }
          { specialize (fun h' pf
                        => @minimal_parse_of_nonterminal__of__parse_of_nonterminal
                             h' (transitivity pf (Lt.lt_n_Sn _))).
            edestruct (minimal_parse_of_productions__of__parse_of_productions' h'  minimal_parse_of_nonterminal__of__parse_of_nonterminal _ pf valid' _ p') as [ [p'' p''H] | [nonterminal' H'] ];
            try solve [ exact (Lt.lt_S_n _ _ H_h)
                      | exact Hinit'
                      | exact H_forall ];
            [|].
            { left.
              exists (MinParseTail pat p'').
              simpl.
              exact (Le.le_n_S _ _ p''H). }
            { right.
              exists nonterminal'.
              split;
                try solve [ exact (fst H') ];
                [].
              exists (proj1_sig (snd H')).
              exact (Lt.lt_S _ _ (proj2_sig (snd H'))). } }
        Defined.
      End productions.

      Section nonterminal.
        Section step.
          Definition minimal_parse_of_nonterminal__of__parse_of_nonterminal_step
                     h
                     (minimal_parse_of_nonterminal__of__parse_of_nonterminal
                      : forall h' (pf : h' < h) {len0 str valid nonterminal}
                               (p : parse_of G str (Lookup G nonterminal)),
                          @of_parse_nonterminal_T len0 str valid nonterminal p h')
                     {len0 str valid nonterminal}
                     (p : parse_of G str (Lookup G nonterminal))
          : @of_parse_nonterminal_T len0 str valid nonterminal p h.
          Proof.
            destruct h as [|h]; [ clear; repeat intro; exfalso; omega | ].
            intros Hvalid' pf Hstr Hinit'.
            let H := match goal with H : length str <= len0 |- _ => constr:(H) end in

            destruct (le_lt_eq_dec _ _ H) as [pf_lt|pf_eq].
            { (** [str] got smaller, so we reset the valid nonterminals list *)
              destruct (@minimal_parse_of_productions__of__parse_of_productions' (length str) h minimal_parse_of_nonterminal__of__parse_of_nonterminal str (reflexivity _) initial_nonterminals_data (Lookup G nonterminal) p (Lt.lt_S_n _ _ pf) (reflexivity _)) as [p'|p'].
              { left.
                exists (MinParseNonTerminalStrLt valid _ pf_lt (proj2 (initial_nonterminals_correct _) Hvalid') (proj1_sig p'));
                  simpl.
                simpl in *.
                exact (Le.le_n_S _ _ (proj2_sig p')). }
              { simpl.
                right; eapply expand_alt_option; [..| exact p' ];
                solve [ apply Lt.lt_n_Sn
                      | assumption
                      | reflexivity ]. } }
            { (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
              destruct (Sumbool.sumbool_of_bool (is_valid_nonterminal valid (of_nonterminal nonterminal))) as [ Hvalid | Hinvalid ].
              { destruct (@minimal_parse_of_productions__of__parse_of_productions' len0 h minimal_parse_of_nonterminal__of__parse_of_nonterminal str Hstr (remove_nonterminal valid (of_nonterminal nonterminal)) (Lookup G nonterminal) p (Lt.lt_S_n _ _ pf) (transitivity (R := sub_nonterminals_listT) (@sub_nonterminals_listT_remove _ _ _ _ _ _) Hinit')) as [p'|p'].
                { left.
                  exists (@MinimalParse.MinParseNonTerminalStrEq _ _ _ _ _ _ _ _ _ pf_eq (proj2 (initial_nonterminals_correct _) Hvalid') Hvalid (proj1_sig p')).
                  simpl in *.
                  exact (Le.le_n_S _ _ (proj2_sig p')). }
                { destruct p' as [nonterminal' p'].
                  destruct (string_dec nonterminal nonterminal') as [|n].
                  { subst nonterminal; simpl in *.
                    edestruct (@minimal_parse_of_nonterminal__of__parse_of_nonterminal (S (size_of_parse p)) pf len0 _ valid nonterminal' (proj1_sig (snd p'))) as [p''|p''];
                    try solve [ apply Lt.lt_n_S, (proj2_sig (snd p'))
                              | subst; reflexivity
                              | assumption
                              | split; [ exact (proj2 (fst p'))
                                       | exact (snd (proj2_sig (snd p'))) ] ];
                    [|].
                    { left.
                      exists (proj1_sig p'').
                      etransitivity;
                        [ exact (proj2_sig p'')
                        | exact (Lt.lt_le_weak _ _ (Lt.lt_n_S _ _ (proj2_sig (snd p')))) ]. }
                    { right.
                      exists (projT1 p'').
                      split;
                        [ exact (fst (projT2 p''))
                        | ].
                      exists (proj1_sig (snd (projT2 p''))).
                      etransitivity;
                        [ exact (proj2_sig (snd (projT2 p'')))
                        | exact (Lt.lt_n_S _ _ (proj2_sig (snd p'))) ]. } }
                  { right.
                    exists nonterminal'.
                    destruct p' as [p'H p'p].
                    split.
                    { rewrite remove_nonterminal_5
                        in p'H
                        by repeat match goal with
                                    | _ => assumption
                                    | _ => progress subst
                                    | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
                                    | _ => progress destruct_head' and
                                    | _ => intro
                                    | [ H : of_nonterminal _ = of_nonterminal _ |- _ ]
                                      => let H' := fresh in
                                         pose proof (f_equal to_nonterminal H) as H';
                                           progress
                                             (rewrite !to_of_nonterminal
                                               in H'
                                               by (apply initial_nonterminals_correct;
                                                   first [ assumption
                                                         | rewrite <- H; assumption
                                                         | rewrite -> H; assumption ]));
                                           clear H
                                  end.
                      exact p'H. }
                    { exists (proj1_sig p'p).
                      exact (Lt.lt_S _ _ (proj2_sig p'p)). } } } }
              { (** oops, we already saw this nonterminal in the past.  ABORT! *)
                right.
                exists nonterminal.
                pose proof (proj2 (initial_nonterminals_correct _) Hvalid').
                split; [ split; assumption
                       | ].
                exists p.
                apply Lt.lt_n_Sn. } }
          Defined.
        End step.

        Section wf.
          Definition minimal_parse_of_nonterminal__of__parse_of_nonterminal'
          : forall h
                   {len0 str valid nonterminal}
                   (p : parse_of G str (Lookup G nonterminal)),
              @of_parse_nonterminal_T len0 str valid nonterminal p h
            := @Fix
                 _ lt lt_wf
                 (fun h => forall {len0 str valid nonterminal}
                                  (p : parse_of G str (Lookup G nonterminal)),
                             @of_parse_nonterminal_T len0 str valid nonterminal p h)
                 (@minimal_parse_of_nonterminal__of__parse_of_nonterminal_step).
        End wf.
      End nonterminal.
    End wf_parts.

    Definition minimal_parse_of_item__of__parse_of_item
               {str : String}
               {it : item Char}
               (p : parse_of_item G str it)
    : { p' : minimal_parse_of_item (G := G) (length str) initial_nonterminals_data str it
      | (size_of_parse_item (parse_of_item__of__minimal_parse_of_item p') <= size_of_parse_item p) }%type.
    Proof.
      eapply alt_all_elim, minimal_parse_of_item__of__parse_of_item';
      hnf; intros; try (assumption || reflexivity); [].
      eapply minimal_parse_of_nonterminal__of__parse_of_nonterminal'; try assumption.
      hnf; reflexivity.
    Defined.

    Definition minimal_parse_of_production__of__parse_of_production
               {str : String}
               {its : production Char}
               (p : parse_of_production G str its)
    : { p' : minimal_parse_of_production (G := G) (length str) initial_nonterminals_data str its
      | size_of_parse_production (parse_of_production__of__minimal_parse_of_production p') <= size_of_parse_production p }%type.
    Proof.
      eapply alt_all_elim, minimal_parse_of_production__of__parse_of_production';
      hnf; intros; try (assumption || reflexivity); [].
      eapply minimal_parse_of_nonterminal__of__parse_of_nonterminal'; try assumption.
      hnf; reflexivity.
    Defined.

    Definition minimal_parse_of_productions__of__parse_of_productions
               {str : String}
               {ps : productions Char}
               (p : parse_of G str ps)
    : { p' : minimal_parse_of (G := G) (length str) initial_nonterminals_data str ps
      | size_of_parse (parse_of__of__minimal_parse_of p') <= size_of_parse p }%type.
    Proof.
      eapply alt_all_elim, minimal_parse_of_productions__of__parse_of_productions';
      hnf; intros; try (assumption || reflexivity); [].
      eapply minimal_parse_of_nonterminal__of__parse_of_nonterminal'; try assumption.
      hnf; reflexivity.
    Defined.

    Definition minimal_parse_of_nonterminal__of__parse_of_nonterminal
               {str : String}
               {nonterminal : String.string}
               (Hvalid : In nonterminal (Valid_nonterminals G))
               (p : parse_of G str (Lookup G nonterminal))
    : { p' : minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data str nonterminal
      | size_of_parse_item (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) <= size_of_parse_item (ParseNonTerminal nonterminal Hvalid p) }%type.
    Proof.
      eapply alt_all_elim, minimal_parse_of_nonterminal__of__parse_of_nonterminal';
      hnf; intros; try (assumption || reflexivity).
    Defined.

    Definition minimal_parse_of_nonterminal__of__parse_of_item_nonterminal_helper
               {str : String}
               {nonterminal : String.string}
               its
               (Hits : NonTerminal nonterminal = its)
               (p : parse_of_item G str its)
    : { p' : minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data str nonterminal
      | size_of_parse_item (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) <= size_of_parse_item p }%type.
    Proof.
      destruct p.
      { exfalso; clear -Hits.
        abstract inversion Hits. }
      { inversion Hits; subst.
        apply minimal_parse_of_nonterminal__of__parse_of_nonterminal; assumption. }
    Defined.

    Definition minimal_parse_of_nonterminal__of__parse_of_item_nonterminal
               {str : String}
               {nonterminal : String.string}
               (p : parse_of_item G str (NonTerminal nonterminal))
    : { p' : minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data str nonterminal
      | size_of_parse_item (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) <= size_of_parse_item p }%type.
    Proof.
      apply minimal_parse_of_nonterminal__of__parse_of_item_nonterminal_helper.
      { reflexivity. }
    Defined.
  End minimize.
End cfg.
