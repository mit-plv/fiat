(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Setoids.Setoid Coq.Arith.Compare_dec.
Require Import Coq.Program.Wf Coq.Arith.Wf_nat.
Require Import Parsers.ContextFreeGrammar Parsers.ContextFreeGrammarProperties Parsers.WellFoundedParse.
Require Export Parsers.MinimalParse.
Require Import Common Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Notation "f ∘ g" := (fun x => f (g x)).

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (names_listT : Type)
          (initial_names_data : names_listT)
          (is_valid_name : names_listT -> string -> bool)
          (remove_name : names_listT -> string -> names_listT)
          (names_listT_R : names_listT -> names_listT -> Prop)
          (remove_name_dec : forall ls name,
                               is_valid_name ls name = true
                               -> names_listT_R (remove_name ls name) ls)
          (remove_name_1
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = true
               -> is_valid_name ls ps' = true)
          (remove_name_2
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = false
               <-> is_valid_name ls ps' = false \/ ps = ps')
          (ntl_wf : well_founded names_listT_R).

  Context (names_listT_R_respectful : forall x y,
                                        sub_names_listT is_valid_name x y
                                        -> x <> y
                                        -> names_listT_R x y).

  Local Notation minimal_parse_of_production := (@minimal_parse_of_production CharType String G names_listT initial_names_data is_valid_name remove_name).
  Local Notation minimal_parse_of := (@minimal_parse_of CharType String G names_listT initial_names_data is_valid_name remove_name).
  Local Notation minimal_parse_of_name := (@minimal_parse_of_name CharType String G names_listT initial_names_data is_valid_name remove_name).
  Local Notation minimal_parse_of_item := (@minimal_parse_of_item CharType String G names_listT initial_names_data is_valid_name remove_name).

  Lemma strle_from_min_parse_of_production {str0 valid strs pats}
        (p1 : minimal_parse_of_production str0 valid strs pats)
  : strs ≤s str0.
  Proof.
    destruct p1; trivial; [].
    destruct (stringlike_dec str0 (Empty _)) as [|n];
      subst; [ reflexivity | left ].
    rewrite Length_Empty.
    case_eq (Length str0); intro H; [ exfalso | ];
    eauto using Empty_Length with arith.
  Qed.

  Definition parse_of_item_name__of__minimal_parse_of_name'
             (parse_of__of__minimal_parse_of
              : forall str0 valid str prods,
                  @minimal_parse_of str0 valid str prods -> parse_of String G str prods)
             {str0 valid str name} (p : @minimal_parse_of_name str0 valid str name)
  : parse_of_item String G str (NonTerminal _ name)
    := ParseNonTerminal
         name
         (@parse_of__of__minimal_parse_of
            _ _ _ _
            (match p as p in (@MinimalParse.minimal_parse_of_name _ _ _ _ _ _ _ str0 valid str name)
                   return minimal_parse_of (match p with
                                              | MinParseNonTerminalStrLt _ _ _ _ _ _ _ => _
                                              | MinParseNonTerminalStrEq _ _ _ _ _ _ => _
                                            end)
                                           (match p with
                                              | MinParseNonTerminalStrLt _ _ _ _ _ _ _ => _
                                              | MinParseNonTerminalStrEq _ _ _ _ _ _ => _
                                            end)
                                           str (Lookup G name) with
               | MinParseNonTerminalStrLt str0 valid name str pf pf' p' => p'
               | MinParseNonTerminalStrEq str valid name H H' p' => p'
             end)).

  Definition parse_of_item__of__minimal_parse_of_item'
             (parse_of__of__minimal_parse_of
              : forall str0 valid str prods,
                  @minimal_parse_of str0 valid str prods -> parse_of String G str prods)
             {str0 valid str it} (p : @minimal_parse_of_item str0 valid str it)
  : parse_of_item String G str it
    := match p in (@MinimalParse.minimal_parse_of_item _ _ _ _ _ _ _ str0 valid str it) return parse_of_item String G str it with
         | MinParseTerminal str0 valid x
           => ParseTerminal String G x
         | MinParseNonTerminal str0 valid _ _ p'
           => @parse_of_item_name__of__minimal_parse_of_name' (@parse_of__of__minimal_parse_of) _ _ _ _ p'
       end.

  Fixpoint parse_of__of__minimal_parse_of {str0 valid str pats} (p : @minimal_parse_of str0 valid str pats)
  : parse_of String G str pats
    := match p with
         | MinParseHead str0 valid str pat pats p'
           => ParseHead pats (parse_of_production__of__minimal_parse_of_production p')
         | MinParseTail str0 valid str pat pats p'
           => ParseTail pat (parse_of__of__minimal_parse_of p')
       end
  with parse_of_production__of__minimal_parse_of_production {str0 valid str pat} (p : @minimal_parse_of_production str0 valid str pat)
       : parse_of_production String G str pat
       := match p with
            | MinParseProductionNil str0 valid
              => ParseProductionNil _ _
            | MinParseProductionCons str0 valid str strs pat pats pf p' p''
              => ParseProductionCons
                   (parse_of_item__of__minimal_parse_of_item' (@parse_of__of__minimal_parse_of) p')
                   (parse_of_production__of__minimal_parse_of_production p'')
          end.

  Definition parse_of_item_name__of__minimal_parse_of_name
  : forall {str0 valid str name} (p : @minimal_parse_of_name str0 valid str name),
      parse_of_item String G str (NonTerminal _ name)
    := @parse_of_item_name__of__minimal_parse_of_name' (@parse_of__of__minimal_parse_of).

  Definition parse_of_item__of__minimal_parse_of_item
  : forall {str0 valid str it},
      @minimal_parse_of_item str0 valid str it
      -> parse_of_item String G str it
    := @parse_of_item__of__minimal_parse_of_item' (@parse_of__of__minimal_parse_of).

  Section contract.
    Local Hint Constructors MinimalParse.minimal_parse_of_name.

    Definition contract_minimal_parse_of_name_lt
               {str0 str valid valid' name}
               (Hlt : Length str < Length str0)
               (p : @minimal_parse_of_name str0 valid str name)
    : @minimal_parse_of_name str0 valid' str name.
    Proof.
      destruct p.
      { constructor (assumption). }
      { exfalso; clear -Hlt; omega. }
    Defined.

    Definition contract_minimal_parse_of_item_lt
               {str0 str valid valid' it}
               (Hlt : Length str < Length str0)
               (p : @minimal_parse_of_item str0 valid str it)
    : @minimal_parse_of_item str0 valid' str it.
    Proof.
      destruct p as [p|p].
      { constructor. }
      { constructor (eapply contract_minimal_parse_of_name_lt; eassumption). }
    Defined.

    Definition contract_minimal_parse_of_production_lt
               {str0 str valid valid' pat}
               (Hlt : Length str < Length str0)
               (p : @minimal_parse_of_production str0 valid str pat)
    : @minimal_parse_of_production str0 valid' str pat.
    Proof.
      induction p.
      { constructor. }
      { constructor;
        try first [ eapply contract_minimal_parse_of_item_lt; try eassumption
                  | eapply IHp; try eassumption
                  | assumption ];
        clear -Hlt;
        abstract (
            rewrite <- Length_correct in Hlt;
            eauto using le_S, Lt.le_lt_trans, Plus.le_plus_l, Plus.le_plus_r with nocore
          ). }
    Defined.

    Definition contract_minimal_parse_of_lt
               {str0 str valid valid' pats}
               (Hlt : Length str < Length str0)
               (p : @minimal_parse_of str0 valid str pats)
    : @minimal_parse_of str0 valid' str pats.
    Proof.
      induction p.
      { constructor (eapply contract_minimal_parse_of_production_lt; eassumption). }
      { constructor (eapply IHp; assumption). }
    Defined.

    Section contract_eq.
      Lemma parse_of_contract_minimal_parse_of_item_lt
            {str0 str : String} {valid valid' : names_listT}
            {Hlt : Length str < Length str0}
            {it}
            (p : @minimal_parse_of_item str0 valid str it)
      : parse_of_item__of__minimal_parse_of_item
          (contract_minimal_parse_of_item_lt (valid' := valid') Hlt p)
        = parse_of_item__of__minimal_parse_of_item p.
      Proof.
        destruct_head MinimalParse.minimal_parse_of_item; simpl; try reflexivity.
        destruct_head MinimalParse.minimal_parse_of_name; try reflexivity.
        unfold False_rect.
        match goal with
          | [ |- appcontext[match ?e with end] ] => destruct e
        end.
      Qed.

      Lemma parse_of_contract_minimal_parse_of_production_lt
            {str0 str : String} {valid valid' : names_listT}
            {Hlt : Length str < Length str0}
            {pat}
            (p : @minimal_parse_of_production str0 valid str pat)
      : parse_of_production__of__minimal_parse_of_production
          (contract_minimal_parse_of_production_lt (valid' := valid') Hlt p)
        = parse_of_production__of__minimal_parse_of_production p.
      Proof.
        induction p; simpl; try reflexivity.
        rewrite IHp, parse_of_contract_minimal_parse_of_item_lt.
        reflexivity.
      Qed.

      Lemma parse_of_contract_minimal_parse_of_lt
            {str0 str : String} {valid valid' : names_listT}
            {Hlt : Length str < Length str0}
            {pats}
            (p : @minimal_parse_of str0 valid str pats)
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

  (** Re-add this so rewrite works *)
  Global Add Parametric Morphism : remove_name
  with signature (sub_names_listT is_valid_name) ==> eq ==> (sub_names_listT is_valid_name)
    as remove_name_mor.
  Proof.
    intros; apply (@remove_name_mor); try assumption; reflexivity.
  Qed.

  Definition expand_minimal_parse_of_name'
             (expand_minimal_parse_of
              : forall {str0 str0' valid valid' str prods}
                       (Hstr : str0 ≤s str0')
                       (H : sub_names_listT is_valid_name valid valid')
                       (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
                       (p : @minimal_parse_of str0 valid str prods),
                  @minimal_parse_of str0' valid' str prods)
             {str0 str0' valid valid' str name}
             (Hstr : str0 ≤s str0')
             (H : sub_names_listT is_valid_name valid valid')
             (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
             (p : @minimal_parse_of_name str0 valid str name)
  : @minimal_parse_of_name str0' valid' str name.
  Proof.
    destruct p;
    first [ apply MinParseNonTerminalStrLt;
            solve [ eapply length_le_trans; eassumption
                  | assumption ]
          | idtac ]; [].
    { destruct (strle_to_sumbool _ Hstr); subst;
      [ apply MinParseNonTerminalStrLt
      | apply MinParseNonTerminalStrEq ];
      solve [ assumption
            | apply H; assumption
            | eapply expand_minimal_parse_of; [ .. | eassumption ];
              solve [ reflexivity
                    | rewrite ?H, ?Hinit;
                      eauto using sub_names_listT_remove;
                      reflexivity ] ]. }
  Defined.

  Definition expand_minimal_parse_of_item'
             (expand_minimal_parse_of
              : forall {str0 str0' valid valid' str prods}
                       (Hstr : str0 ≤s str0')
                       (H : sub_names_listT is_valid_name valid valid')
                       (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
                       (p : @minimal_parse_of str0 valid str prods),
                  @minimal_parse_of str0' valid' str prods)
             {str0 str0' valid valid' str it}
             (Hstr : str0 ≤s str0')
             (H : sub_names_listT is_valid_name valid valid')
             (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
             (p : @minimal_parse_of_item str0 valid str it)
  : @minimal_parse_of_item str0' valid' str it.
  Proof.
    destruct p.
    { apply MinParseTerminal. }
    { apply MinParseNonTerminal; [].
      eapply expand_minimal_parse_of_name'; [..| eassumption ];
      try assumption. }
  Defined.

  Fixpoint expand_minimal_parse_of
           {str0 str0' valid valid' str pats}
           (Hstr : str0 ≤s str0')
           (H : sub_names_listT is_valid_name valid valid')
           (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
           (p : @minimal_parse_of str0 valid str pats)
  : @minimal_parse_of str0' valid' str pats
    := match p in (@MinimalParse.minimal_parse_of _ _ _ _ _ _ _ str0 valid str pats)
             return (str0 ≤s str0'
                     -> sub_names_listT is_valid_name valid valid'
                     -> @minimal_parse_of str0' valid' str pats)
       with
         | MinParseHead str0 valid str pat pats p'
           => fun Hstr H => MinParseHead pats (expand_minimal_parse_of_production Hstr H Hinit p')
         | MinParseTail str0 valid str pat pats p'
           => fun Hstr H => MinParseTail pat (expand_minimal_parse_of Hstr H Hinit p')
       end Hstr H
  with expand_minimal_parse_of_production
         {str0 str0' valid valid' str pat}
         (Hstr : str0 ≤s str0')
         (H : sub_names_listT is_valid_name valid valid')
         (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
         (p : @minimal_parse_of_production str0 valid str pat)
       : @minimal_parse_of_production str0' valid' str pat
       := match p in (@MinimalParse.minimal_parse_of_production _ _ _ _ _ _ _ str0 valid str pats)
                return (str0 ≤s str0' -> sub_names_listT is_valid_name valid valid' -> minimal_parse_of_production str0' valid' str pats)
          with
            | MinParseProductionNil str0 valid
              => fun _ _ => MinimalParse.MinParseProductionNil _ _ _ _ _ _ _
            | MinParseProductionCons str0 valid str strs pat pats pf p' p''
              => fun Hstr H => MinParseProductionCons
                                 (transitivity pf Hstr)
                                 (expand_minimal_parse_of_item' (@expand_minimal_parse_of) Hstr H Hinit p')
                                 (expand_minimal_parse_of_production Hstr H Hinit p'')
          end Hstr H.

  Definition expand_minimal_parse_of_name
  : forall {str0 str0' valid valid' str name}
           (Hstr : str0 ≤s str0')
           (H : sub_names_listT is_valid_name valid valid')
           (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
           (p : @minimal_parse_of_name str0 valid str name),
      @minimal_parse_of_name str0' valid' str name
    := @expand_minimal_parse_of_name' (@expand_minimal_parse_of).

  Definition expand_minimal_parse_of_item
  : forall {str0 str0' valid valid' str it}
           (Hstr : str0 ≤s str0')
           (H : sub_names_listT is_valid_name valid valid')
           (Hinit : sub_names_listT is_valid_name valid' initial_names_data)
           (p : @minimal_parse_of_item str0 valid str it),
      @minimal_parse_of_item str0' valid' str it
    := @expand_minimal_parse_of_item' (@expand_minimal_parse_of).

  Section minimize.
    Let P : String -> string -> Prop
      := fun _ p => is_valid_name initial_names_data p = true.

    Let alt_option h valid str
      := { name : _ & (is_valid_name valid name = false /\ P str name)
                      * { p : parse_of String G str (Lookup G name)
                              & (size_of_parse p < h)
                                * Forall_parse_of P p } }%type.

    Lemma not_alt_all {h str} (ps : alt_option h initial_names_data str)
    : False.
    Proof.
      subst P; simpl in *.
      destruct ps as [ ? [ H' _ ] ].
      revert H'; clear; intros [? ?].
      congruence.
    Qed.

    Definition alt_all_elim {h str T} (ps : T + alt_option h initial_names_data str)
    : T.
    Proof.
      destruct ps as [|ps]; [ assumption | exfalso ].
      eapply not_alt_all; eassumption.
    Defined.

    Definition expand_alt_option' {h h' str str' valid valid'}
               (H : h <= h') (H' : sub_names_listT is_valid_name valid' valid) (H'' : str = str')
    : alt_option h valid str -> alt_option h' valid' str'.
    Proof.
      hnf in H'; unfold alt_option.
      repeat match goal with
               | [ |- sigT _ -> _ ] => intros []
               | [ |- sig _ -> _ ] => intros []
               | [ |- prod _ _ -> _ ] => intros []
               | [ |- and _ _ -> _ ] => intros []
               | _ => intro
               | _ => progress subst
               | [ |- sigT _ ] => esplit
               | [ |- sig _ ] => esplit
               | [ |- prod _ _ ] => esplit
               | [ |- and _ _ ] => esplit
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
               (H : h < h') (H' : sub_names_listT is_valid_name valid' valid) (H'' : str = str')
    : alt_option h valid str -> alt_option h' valid' str'.
    Proof.
      apply expand_alt_option'; try assumption.
      apply Lt.lt_le_weak; assumption.
    Defined.

    Section wf_parts.
      Let of_parse_item_T' h
          {str0 str : String} (pf : str ≤s str0)
          (valid : names_listT) {it : item CharType}
          (p : parse_of_item String G str it)
        := forall (p_small : size_of_parse_item p < h),
             sub_names_listT is_valid_name valid initial_names_data
             -> Forall_parse_of_item P p
             -> ({ p' : @minimal_parse_of_item str0 valid str it
                        & (size_of_parse_item (parse_of_item__of__minimal_parse_of_item p') <= size_of_parse_item p)
                          * Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item p') })%type
                + alt_option (size_of_parse_item p) valid str.

      Let of_parse_item_T str0 h
        := forall str pf valid it p, @of_parse_item_T' h str0 str pf valid it p.

      Let of_parse_production_T' h
          {str0 str : String} (pf : str ≤s str0)
          (valid : names_listT) {pat : production CharType}
          (p : parse_of_production String G str pat)
        := forall (p_small : size_of_parse_production p < h),
             sub_names_listT is_valid_name valid initial_names_data
             -> Forall_parse_of_production P p
             -> ({ p' : @minimal_parse_of_production str0 valid str pat
                        & (size_of_parse_production (parse_of_production__of__minimal_parse_of_production p') <= size_of_parse_production p)
                          * Forall_parse_of_production P (parse_of_production__of__minimal_parse_of_production p') })%type
                + alt_option (size_of_parse_production p) valid str.

      Let of_parse_production_T str0 h
        := forall str pf valid pat p, @of_parse_production_T' h str0 str pf valid pat p.

      Let of_parse_T' h
          {str0 str : String} (pf : str ≤s str0)
          (valid : names_listT) {pats : productions CharType}
          (p : parse_of String G str pats)
        := forall (p_small : size_of_parse p < h),
             sub_names_listT is_valid_name valid initial_names_data
             -> Forall_parse_of P p
             -> ({ p' : @minimal_parse_of str0 valid str pats
                        & (size_of_parse (parse_of__of__minimal_parse_of p') <= size_of_parse p)
                          * Forall_parse_of P (parse_of__of__minimal_parse_of p') })%type
                + alt_option (size_of_parse p) valid str.

      Let of_parse_T str0 h
        := forall str pf valid pats p, @of_parse_T' h str0 str pf valid pats p.

      Let of_parse_name_T {str0 str valid name} (p : parse_of String G str (Lookup G name)) h
        := size_of_parse_item (ParseNonTerminal name p) < h
           -> str ≤s str0
           -> sub_names_listT is_valid_name valid initial_names_data
           -> Forall_parse_of_item P (ParseNonTerminal name p)
           -> ({ p' : @minimal_parse_of_name str0 valid str name
                      & (size_of_parse_item (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) <= size_of_parse_item (ParseNonTerminal name p))
                        * Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item (MinParseNonTerminal p')) })%type
              + alt_option (size_of_parse_item (ParseNonTerminal name p)) valid str.

      Section item.
        Context {str0 str : String} {valid : names_listT}.

        Definition minimal_parse_of_item__of__parse_of_item
                   h
                   (minimal_parse_of_name__of__parse_of_name
                    : forall h' (pf : h' < S (S h)) {str0 str valid name}
                             (p : parse_of String G str (Lookup G name)),
                        @of_parse_name_T str0 str valid name p h')
        : of_parse_item_T str h.
        Proof.
          intros str' pf valid' pats p H_h Hinit' H_forall.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [|name' str'' p'].
          { left.
            eexists (@MinimalParse.MinParseTerminal _ _ _ _ _ _ _ _ _ _);
              split; simpl; constructor. }
          { edestruct (fun pf => @minimal_parse_of_name__of__parse_of_name (S h') pf str _ valid' _ p') as [ [p'' H''] | p'' ];
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
        Context {str0 str : String} {valid : names_listT}.

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
            | _ => progress rewrite ?parse_of_contract_minimal_parse_of_item_lt, ?parse_of_contract_minimal_parse_of_production_lt, ?parse_of_contract_minimal_parse_of_lt
            | [ |- context G[size_of_parse_production (ParseProductionCons ?a ?b)] ]
              => let G' := context G[S (size_of_parse_item a + size_of_parse_production b)] in
                 change G'
            | [ H : alt_option _ initial_names_data _ |- _ ]
              => apply not_alt_all in H
            | [ p0 : minimal_parse_of_item _ _ ?s0 ?pat,
                     p1 : minimal_parse_of_production _ _ ?s1 ?pats,
                          H : ?s0 ++ ?s1 ≤s ?s'
                |- ({ p' : minimal_parse_of_production ?s' _ (?s0 ++ ?s1) (?pat :: ?pats) & _ } + _)%type ]
              => left; exists (MinParseProductionCons H p0 p1)
            | [ p0 : minimal_parse_of_item ?s' _ ?s0 ?pat,
                     p1 : minimal_parse_of_production ?s' _ ?s1 ?pats,
                          H : ?s0 ++ ?s1 ≤s ?s',
                              H' : Length ?s0 < Length ?s'
                |- ({ p' : minimal_parse_of_production ?s' ?v (?s0 ++ ?s1) (?pat :: ?pats) & _ } + _)%type ]
              => left; exists (MinParseProductionCons
                                 H
                                 (contract_minimal_parse_of_item_lt (valid' := v) H' p0)
                                 p1)
            | [ p0 : minimal_parse_of_item ?s' _ ?s0 ?pat,
                     p1 : minimal_parse_of_production ?s' _ ?s1 ?pats,
                          H : ?s0 ++ ?s1 ≤s ?s',
                              H' : Length ?s1 < Length ?s'
                |- ({ p' : minimal_parse_of_production ?s' ?v (?s0 ++ ?s1) (?pat :: ?pats) & _ } + _)%type ]
              => left; exists (MinParseProductionCons
                                 H
                                 p0
                                 (contract_minimal_parse_of_production_lt (valid' := v) H' p1))
            | [ p0 : minimal_parse_of_item ?s' _ ?s0 ?pat,
                     p1 : minimal_parse_of_production ?s' _ ?s1 ?pats,
                          H : ?s0 ++ ?s1 ≤s ?s',
                              H' : Length ?s0 < Length ?s',
                                   H'' : Length ?s1 < Length ?s'
                |- ({ p' : minimal_parse_of_production ?s' ?v (?s0 ++ ?s1) (?pat :: ?pats) & _ } + _)%type ]
              => left; exists (MinParseProductionCons
                                 H
                                 (contract_minimal_parse_of_item_lt (valid' := v) H' p0)
                                 (contract_minimal_parse_of_production_lt (valid' := v) H'' p1))
            | [ |- (_ * _)%type ]
              => split
            | [ H : _ <= _ |- _ <= _ ] => apply H
            | _ => apply Le.le_n_S
            | _ => apply Plus.plus_le_compat
            | [ H0 : Forall_parse_of_item _ _,
                     H1 : Forall_parse_of_production _ _
                |- Forall_parse_of_production _ _ ]
              => exact (H0, H1)
            | [ H : alt_option _ ?v ?x
                |- (_ + alt_option _ ?v (?x ++ Empty _))%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ H : alt_option _ ?v ?x
                |- (_ + alt_option _ ?v (Empty _ ++ ?x))%type ]
              => right; eapply expand_alt_option'; [ .. | exact H ]
            | [ |- _ = _ ]
              => progress rewrite ?LeftId, ?RightId
            | _
              => solve [ eauto using le_S, Le.le_trans, Plus.le_plus_l, Plus.le_plus_r with nocore ]
          end.
        Local Ltac min_parse_prod_pose_t' :=
          idtac;
          match goal with
            | [ H : ?a <> Empty _,
                    H' : ?a ++ _ ≤s _ |- _ ]
              => unique pose proof (strle_to_lt_nonempty_r H H')
            | [ H : ?a <> Empty _,
                    H' : _ ++ ?a ≤s _ |- _ ]
              => unique pose proof (strle_to_lt_nonempty_l H H')
          end.
        Local Ltac min_parse_prod_pose_t := repeat min_parse_prod_pose_t'.
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

        Fixpoint minimal_parse_of_production__of__parse_of_production
                 h
                 (minimal_parse_of_name__of__parse_of_name
                  : forall h' (pf : h' < S (S h)) {str0 str valid name}
                           (p : parse_of String G str (Lookup G name)),
                      @of_parse_name_T str0 str valid name p h')
                 {struct h}
        : of_parse_production_T str h.
        Proof.
          intros str' pf valid' pats p H_h Hinit' H_forall.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [| str' strs' str'' pat' p0' p1' ].
          { clear minimal_parse_of_production__of__parse_of_production.
            left.
            eexists (@MinimalParse.MinParseProductionNil _ _ _ _ _ _ _ _ _);
              repeat (reflexivity || esplit). }
          { specialize (fun h' pf
                        => @minimal_parse_of_name__of__parse_of_name
                             h' (transitivity pf (Lt.lt_n_Sn _))).
            change (S ((size_of_parse_item p0')
                       + (size_of_parse_production p1'))
                    < S h') in H_h.
            apply Lt.lt_S_n in H_h.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_l _ _) H_h) as H_h0.
            pose proof (Lt.le_lt_trans _ _ _ (Plus.le_plus_r _ _) H_h) as H_h1.
            clear H_h.
            pose proof (fun valid Hinit => @minimal_parse_of_item__of__parse_of_item _ h'  minimal_parse_of_name__of__parse_of_name _ (transitivity (str_le1_append _ _ _) pf) valid _ p0' H_h0 Hinit (fst H_forall)) as p_it.
            pose proof (fun valid Hinit => @minimal_parse_of_production__of__parse_of_production h' minimal_parse_of_name__of__parse_of_name _ (transitivity (str_le2_append _ _ _) pf) valid _ p1' H_h1 Hinit (snd H_forall)) as p_prod.
            destruct (stringlike_dec str' (Empty _)), (stringlike_dec str'' (Empty _));
              subst.
            { (* empty, empty *)
              specialize (p_it valid' Hinit'); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t. }
            { (* empty, nonempty *)
              specialize (p_it initial_names_data (reflexivity _)); specialize (p_prod valid' Hinit').
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t;
                min_parse_prod_pose_t;
                min_parse_prod_t. }
            { (* nonempty, empty *)
              specialize (p_it valid' Hinit'); specialize (p_prod initial_names_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t;
                min_parse_prod_pose_t;
                min_parse_prod_t. }
            { (* nonempty, nonempty *)
              specialize (p_it initial_names_data (reflexivity _)); specialize (p_prod initial_names_data (reflexivity _)).
              destruct p_it as [ [ p0'' H0''] |], p_prod as [ [ p1'' H1'' ] |];
                [ | | | ];
                min_parse_prod_t;
                min_parse_prod_pose_t;
                min_parse_prod_t. } }
        Defined.
      End production.

      Section productions.
        Context {str0 str : String} {valid : names_listT}.

        Fixpoint minimal_parse_of_productions__of__parse_of_productions
                 h
                 (minimal_parse_of_name__of__parse_of_name
                  : forall h' (pf : h' < S h) {str0 str valid name}
                           (p : parse_of String G str (Lookup G name)),
                      @of_parse_name_T str0 str valid name p h')
                 {struct h}
        : of_parse_T str h.
        Proof.
          intros str' pf valid' pats p H_h Hinit' H_forall.
          destruct h as [|h']; [ exfalso; omega | ].
          destruct p as [str' pat pats p' | str' pat pats p'].
          { clear minimal_parse_of_productions__of__parse_of_productions.
            edestruct (@minimal_parse_of_production__of__parse_of_production _ h' minimal_parse_of_name__of__parse_of_name _ pf valid' _ p') as [ [p'' p''H] | [name' H'] ];
            try solve [ exact (Lt.lt_S_n _ _ H_h)
                      | exact H_forall
                      | exact Hinit' ];
            [|].
            { left.
              exists (MinParseHead pats p'').
              simpl.
              split;
                solve [ exact (Le.le_n_S _ _ (fst p''H))
                      | exact (snd p''H) ]. }
            { right.
              exists name'.
              split;
                try solve [ exact (fst H') ];
                [].
              exists (projT1 (snd H'));
                split;
                try solve [ exact (snd (projT2 (snd H')))
                          | exact (Lt.lt_S _ _ (fst (projT2 (snd H')))) ]. } }
          { specialize (fun h' pf
                        => @minimal_parse_of_name__of__parse_of_name
                             h' (transitivity pf (Lt.lt_n_Sn _))).
            edestruct (minimal_parse_of_productions__of__parse_of_productions h'  minimal_parse_of_name__of__parse_of_name _ pf valid' _ p') as [ [p'' p''H] | [name' H'] ];
            try solve [ exact (Lt.lt_S_n _ _ H_h)
                      | exact Hinit'
                      | exact H_forall ];
            [|].
            { left.
              exists (MinParseTail pat p'').
              simpl.
              split;
                solve [ exact (Le.le_n_S _ _ (fst p''H))
                      | exact (snd p''H) ]. }
            { right.
              exists name'.
              split;
                try solve [ exact (fst H') ];
                [].
              exists (projT1 (snd H'));
                split;
                try solve [ exact (snd (projT2 (snd H')))
                          | exact (Lt.lt_S _ _ (fst (projT2 (snd H')))) ]. } }
        Defined.
      End productions.

      Section name.
        Section step.
          Definition minimal_parse_of_name__of__parse_of_name_step
                     h
                     (minimal_parse_of_name__of__parse_of_name
                      : forall h' (pf : h' < h) {str0 str valid name}
                               (p : parse_of String G str (Lookup G name)),
                          @of_parse_name_T str0 str valid name p h')
                     {str0 str valid name}
                     (p : parse_of String G str (Lookup G name))
          : @of_parse_name_T str0 str valid name p h.
          Proof.
            destruct h as [|h]; [ clear; repeat intro; exfalso; omega | ].
            intros pf Hstr Hinit' H_forall.
            let H := match goal with H : str ≤s str0 |- _ => constr:H end in
            destruct (strle_to_sumbool _ H) as [pf_lt|pf_eq].
            { (** [str] got smaller, so we reset the valid names list *)
              destruct (@minimal_parse_of_productions__of__parse_of_productions str h minimal_parse_of_name__of__parse_of_name str (reflexivity _) initial_names_data (Lookup G name) p (Lt.lt_S_n _ _ pf) (reflexivity _) (snd H_forall)) as [p'|p'].
              { left.
                exists (MinParseNonTerminalStrLt _ valid _ pf_lt (fst H_forall) (projT1 p'));
                  simpl.
                simpl in *.
                split;
                  [ exact (Le.le_n_S _ _ (fst (projT2 p')))
                  | split;
                    [ exact (fst H_forall)
                    | exact (snd (projT2 p')) ] ]. }
              { simpl.
                right; eapply expand_alt_option; [..| exact p' ];
                solve [ apply Lt.lt_n_Sn
                      | assumption
                      | reflexivity ]. } }
            { (** [str] didn't get smaller, so we cache the fact that we've hit this name already *)
              destruct (Sumbool.sumbool_of_bool (is_valid_name valid name)) as [ Hvalid | Hinvalid ].
              { destruct (@minimal_parse_of_productions__of__parse_of_productions str h minimal_parse_of_name__of__parse_of_name str (reflexivity _) (remove_name valid name) (Lookup G name) p (Lt.lt_S_n _ _ pf) (transitivity (R := sub_names_listT is_valid_name) (@sub_names_listT_remove _ is_valid_name _ remove_name_1 _ _) Hinit') (snd H_forall)) as [p'|p'].
                { left.
                  subst str.
                  eexists (@MinimalParse.MinParseNonTerminalStrEq _ _ _ _ _ _ _ _ _ _ (fst H_forall) Hvalid (projT1 p')).
                  simpl in *.
                  split;
                    [ exact (Le.le_n_S _ _ (fst (projT2 p')))
                    | split;
                      [ exact (fst H_forall)
                      | exact (snd (projT2 p')) ] ]. }
                { destruct p' as [name' p'].
                  destruct (string_dec name name') as [|n].
                  { subst name; simpl in *.
                    edestruct (@minimal_parse_of_name__of__parse_of_name (S (size_of_parse p)) pf str0 _ valid name' (projT1 (snd p'))) as [p''|p''];
                    try solve [ apply Lt.lt_n_S, (fst (projT2 (snd p')))
                              | subst; reflexivity
                              | assumption
                              | split; [ exact (proj2 (fst p'))
                                       | exact (snd (projT2 (snd p'))) ] ];
                    [|].
                    { left.
                      exists (projT1 p'').
                      split.
                      { etransitivity;
                        [ exact (fst (projT2 p''))
                        | exact (Lt.lt_le_weak _ _ (Lt.lt_n_S _ _ (fst (projT2 (snd p'))))) ]. }
                      { exact (snd (projT2 p'')). } }
                    { right.
                      exists (projT1 p'').
                      split;
                        [ exact (fst (projT2 p''))
                        | ].
                      exists (projT1 (snd (projT2 p''))).
                      split;
                        [ etransitivity;
                          [ exact (fst (projT2 (snd (projT2 p''))))
                          | exact (Lt.lt_n_S _ _ (fst (projT2 (snd p')))) ]
                        | exact (snd (projT2 (snd (projT2 p'')))) ]. } }
                  { right.
                    exists name'.
                    destruct p' as [p'H p'p].
                    split.
                    { rewrite remove_name_5 in p'H by assumption.
                      exact p'H. }
                    { exists (projT1 p'p).
                      split; [ exact (Lt.lt_S _ _ (fst (projT2 p'p)))
                             | exact (snd (projT2 p'p)) ]. } } } }
              { (** oops, we already saw this name in the past.  ABORT! *)
                right.
                exists name.
                destruct H_forall.
                split; [ split; assumption
                       | ].
                exists p.
                split; solve [ assumption
                             | apply Lt.lt_n_Sn ]. } }
          Defined.
        End step.

        Section wf.
          Definition minimal_parse_of_name__of__parse_of_name
          : forall h
                   {str0 str valid name}
                   (p : parse_of String G str (Lookup G name)),
              @of_parse_name_T str0 str valid name p h
            := @Fix
                 _ lt lt_wf
                 (fun h => forall {str0 str valid name}
                                  (p : parse_of String G str (Lookup G name)),
                             @of_parse_name_T str0 str valid name p h)
                 (@minimal_parse_of_name__of__parse_of_name_step).
        End wf.
      End name.
    End wf_parts.
  End minimize.
End cfg.
