(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Parsers.ContextFreeGrammar Parsers.ContextFreeGrammarProperties Parsers.WellFoundedParse.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Notation "f ∘ g" := (fun x => f (g x)).

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (names_listT : Type)
          (initial_names_data : names_listT)
          (is_valid_name : names_listT -> string -> bool)
          (remove_name : names_listT -> string -> names_listT)
          (remove_name_1
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = true
               -> is_valid_name ls ps' = true)
          (remove_name_2
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = false
               <-> is_valid_name ls ps' = false \/ ps = ps').

  Lemma remove_name_3
        ls ps ps' (H : is_valid_name ls ps = false)
  : is_valid_name (remove_name ls ps) ps' = is_valid_name ls ps'.
  Proof.
    case_eq (is_valid_name (remove_name ls ps) ps');
    case_eq (is_valid_name ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_name_1 in H''
          | apply remove_name_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Lemma remove_name_4
        ls ps ps' (H : is_valid_name (remove_name ls ps) ps' = true)
  : ps <> ps'.
  Proof.
    intro H'.
    pose proof (proj2 (remove_name_2 ls _ _) (or_intror H')).
    congruence.
  Qed.

  Lemma remove_name_5
        ls ps ps' (H : ps <> ps')
  : is_valid_name (remove_name ls ps) ps' = is_valid_name ls ps'.
  Proof.
    case_eq (is_valid_name (remove_name ls ps) ps');
    case_eq (is_valid_name ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_name_1 in H''
          | apply remove_name_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Lemma remove_name_6
        ls ps
  : is_valid_name (remove_name ls ps) ps = false.
  Proof.
    apply remove_name_2; right; reflexivity.
  Qed.

  (** The [names_listT] is the current list of valid names to compare
      against; the extra [String] argument to some of these is the
      [String] we're using to do well-founded recursion, which the
      current [String] must be no longer than. *)
  Inductive minimal_parse_of
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      productions CharType -> Type :=
  | MinParseHead : forall str0 valid str pat pats,
                     @minimal_parse_of_production str0 valid str pat
                     -> @minimal_parse_of str0 valid str (pat::pats)
  | MinParseTail : forall str0 valid str pat pats,
                     @minimal_parse_of str0 valid str pats
                     -> @minimal_parse_of str0 valid str (pat::pats)
  with minimal_parse_of_production
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      production CharType -> Type :=
  | MinParseProductionNil : forall str0 valid,
                              @minimal_parse_of_production str0 valid (Empty _) nil
  | MinParseProductionCons : forall str0 valid str strs pat pats,
                               @minimal_parse_of_item str0 valid str pat
                               -> @minimal_parse_of_production str0 valid strs pats
                               -> @minimal_parse_of_production str0 valid (str ++ strs) (pat::pats)
  with minimal_parse_of_item
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      item CharType -> Type :=
  | MinParseTerminal : forall str0 valid x,
                         @minimal_parse_of_item str0 valid [[ x ]]%string_like (Terminal x)
  | MinParseNonTerminal
    : forall str0 valid str name,
        @minimal_parse_of_name str0 valid str name
        -> @minimal_parse_of_item str0 valid str (NonTerminal CharType name)
  with minimal_parse_of_name
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      string -> Type :=
  | MinParseNonTerminalStrLt
    : forall str0 valid name str,
        Length str < Length str0
        -> @minimal_parse_of str initial_names_data str (Lookup G name)
        -> @minimal_parse_of_name str0 valid str name
  | MinParseNonTerminalStrEq
    : forall str valid name,
        is_valid_name valid name = true
        -> @minimal_parse_of str (remove_name valid name) str (Lookup G name)
        -> @minimal_parse_of_name str valid str name.

  Definition parse_of_item_name__of__minimal_parse_of_name'
             (parse_of__of__minimal_parse_of
              : forall str0 valid str prods,
                  @minimal_parse_of str0 valid str prods -> parse_of String G str prods)
             {str0 valid str name} (p : @minimal_parse_of_name str0 valid str name)
  : parse_of_item String G str (NonTerminal _ name)
    := match p in (@minimal_parse_of_name str0 valid str name) return parse_of_item String G str (NonTerminal _ name) with
         | MinParseNonTerminalStrLt str0 valid name str pf p'
           => ParseNonTerminal name (@parse_of__of__minimal_parse_of _ _ _ _ p')
         | MinParseNonTerminalStrEq str valid name H p'
           => ParseNonTerminal name (@parse_of__of__minimal_parse_of _ _ _ _ p')
       end.

  Definition parse_of_item__of__minimal_parse_of_item'
             (parse_of__of__minimal_parse_of
              : forall str0 valid str prods,
                  @minimal_parse_of str0 valid str prods -> parse_of String G str prods)
             {str0 valid str it} (p : @minimal_parse_of_item str0 valid str it)
  : parse_of_item String G str it
    := match p in (@minimal_parse_of_item str0 valid str it) return parse_of_item String G str it with
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
            | MinParseProductionCons str0 valid str strs pat pats p' p''
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

  Definition sub_names_listT (x y : names_listT) : Prop
    := forall p, is_valid_name x p = true -> is_valid_name y p = true.

  Global Instance sub_names_listT_Reflexive : Reflexive sub_names_listT
    := fun x y f => f.

  Global Instance sub_names_listT_Transitive : Transitive sub_names_listT.
  Proof.
    lazy; auto.
  Defined.

  Add Parametric Morphism : remove_name
  with signature sub_names_listT ==> eq ==> sub_names_listT
    as remove_name_mor.
  Proof.
    intros x y H z w H'.
    hnf in H.
    pose proof (remove_name_4 H').
    apply remove_name_1 in H'.
    rewrite remove_name_5 by assumption.
    auto.
  Qed.

  Lemma sub_names_listT_remove ls ps
  : sub_names_listT (remove_name ls ps) ls.
  Proof.
    intros p.
    apply remove_name_1.
  Qed.

  Lemma sub_names_listT_remove_2 ls ls' ps (H : sub_names_listT ls ls')
  : sub_names_listT (remove_name ls ps) ls'.
  Proof.
    etransitivity; eauto using sub_names_listT_remove.
  Qed.

  Lemma sub_names_listT_remove_3 ls ls' p
        (H0 : is_valid_name ls p = false)
        (H1 : sub_names_listT ls ls')
  : sub_names_listT ls (remove_name ls' p).
  Proof.
    intros p' H'.
    rewrite remove_name_5; intuition (subst; eauto; congruence).
  Qed.


  Definition expand_minimal_parse_of_name'
             (expand_minimal_parse_of
              : forall {str0 str0' valid valid' str prods}
                       (Hstr : str0 ≤s str0')
                       (H : sub_names_listT valid valid')
                       (Hinit : sub_names_listT valid' initial_names_data)
                       (p : @minimal_parse_of str0 valid str prods),
                  @minimal_parse_of str0' valid' str prods)
             {str0 str0' valid valid' str name}
             (Hstr : str0 ≤s str0')
             (H : sub_names_listT valid valid')
             (Hinit : sub_names_listT valid' initial_names_data)
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
                       (H : sub_names_listT valid valid')
                       (Hinit : sub_names_listT valid' initial_names_data)
                       (p : @minimal_parse_of str0 valid str prods),
                  @minimal_parse_of str0' valid' str prods)
             {str0 str0' valid valid' str it}
             (Hstr : str0 ≤s str0')
             (H : sub_names_listT valid valid')
             (Hinit : sub_names_listT valid' initial_names_data)
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
           (H : sub_names_listT valid valid')
           (Hinit : sub_names_listT valid' initial_names_data)
           (p : @minimal_parse_of str0 valid str pats)
  : @minimal_parse_of str0' valid' str pats
    := match p in (@minimal_parse_of str0 valid str pats)
             return (str0 ≤s str0'
                     -> sub_names_listT valid valid'
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
         (H : sub_names_listT valid valid')
         (Hinit : sub_names_listT valid' initial_names_data)
         (p : @minimal_parse_of_production str0 valid str pat)
       : @minimal_parse_of_production str0' valid' str pat
       := match p in (minimal_parse_of_production str0 valid str pats)
                return (str0 ≤s str0' -> sub_names_listT valid valid' -> minimal_parse_of_production str0' valid' str pats)
          with
            | MinParseProductionNil str0 valid
              => fun _ _ => MinParseProductionNil str0' valid'
            | MinParseProductionCons str0 valid str strs pat pats p' p''
              => fun Hstr H => MinParseProductionCons
                                 (expand_minimal_parse_of_item' (@expand_minimal_parse_of) Hstr H Hinit p')
                                 (expand_minimal_parse_of_production Hstr H Hinit p'')
          end Hstr H.

  Definition expand_minimal_parse_of_name
  : forall {str0 str0' valid valid' str name}
           (Hstr : str0 ≤s str0')
           (H : sub_names_listT valid valid')
           (Hinit : sub_names_listT valid' initial_names_data)
           (p : @minimal_parse_of_name str0 valid str name),
      @minimal_parse_of_name str0' valid' str name
    := @expand_minimal_parse_of_name' (@expand_minimal_parse_of).

  Definition expand_minimal_parse_of_item
  : forall {str0 str0' valid valid' str it}
           (Hstr : str0 ≤s str0')
           (H : sub_names_listT valid valid')
           (Hinit : sub_names_listT valid' initial_names_data)
           (p : @minimal_parse_of_item str0 valid str it),
      @minimal_parse_of_item str0' valid' str it
    := @expand_minimal_parse_of_item' (@expand_minimal_parse_of).

  Section minimize.
    Let P : string -> Prop
      := fun p => is_valid_name initial_names_data p = true.

    Let alt_option h valid str
      := { name : _ & (is_valid_name valid name = false /\ P name)
                      * { p : parse_of String G str (Lookup G name)
                              & (height_of_parse p < h)
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

    Definition expand_alt_option {h h' str str' valid valid'}
               (H : h < h') (H' : sub_names_listT valid' valid) (H'' : str = str')
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
             end.
    Defined.

    Section wf_parts.
      Let of_parse_T' h
          {str0 str : String} (pf : str ≤s str0)
          (valid : names_listT) {pats : productions CharType}
          (p : parse_of String G str pats)
        := forall (p_small : height_of_parse p < h),
             Forall_parse_of P p
             -> ({ p' : @minimal_parse_of str0 valid str pats
                        & (height_of_parse (parse_of__of__minimal_parse_of p') <= height_of_parse p)
                          * Forall_parse_of P (parse_of__of__minimal_parse_of p') })%type
                + alt_option (height_of_parse p) valid str.

      Let of_parse_T str0 h
        := forall str pf valid pats p, @of_parse_T' h str0 str pf valid pats p.

      Definition of_parse_T_resp {str0 str0'} {h h'} (Hstr : str0' ≤s str0) (H : h' < h)
                 (parse : of_parse_T str0 h)
      : of_parse_T str0' h'.
      Proof.
        intros str' pf' valid' pats' p' p_small' H'.
        pose (@parse str' (transitivity pf' Hstr) valid' pats' p' (Lt.lt_trans _ _ _ p_small' H) H') as p''.
        Set Printing Implicit.

      Let of_parse_item_T {str0 str pf valid it} (p : parse_of_item String G str it) h
        := height_of_parse_item p < h
           -> Forall_parse_of_item P p
           -> ({ p' : @minimal_parse_of_item str0 valid str it
                      & (height_of_parse_item (parse_of_item__of__minimal_parse_of_item p') <= height_of_parse_item p)
                        * Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item p') })%type
              + alt_option (height_of_parse_item p) valid str.

      Section item.
        Context {str0 str : String} (pf : str ≤s str0) (valid : names_listT) {it : item CharType}.

        Let rec_T str0 str pf it h
          := forall h', h' < h -> of_parse_T h' -> forall p, @of_parse_item_T str0 str pf valid it p h'.

        Section helper.
          Context (h : nat)
                  (minimal_parse_of_item__of__parse_of_item_rec : rec_T pf it h)
                  (minimal_parse_of__of__parse_of : of_parse_T h).

          Definition minimal_parse_of_item__of__parse_of_item'_helper
                     (p : parse_of_item String G str it)
          : @of_parse_item_T str0 str pf valid it p h.
            refine
              (match h as h, p as p in (parse_of_item _ _ str it)
                     return (forall pf : str ≤s str0,
                               @rec_T str0 str pf it h
                               -> @of_parse_T h
                               -> @of_parse_item_T str0 str pf valid it p h)
               with
                 | _, ParseTerminal x
                   => fun pf _ _ H' _ => inl (existT _ (@MinParseTerminal str0 valid x pf) (le_n _, tt))
                 | 0, ParseNonTerminal _ _ _
                   => fun _ _ _ H' _ => match Lt.lt_n_0 _ H' : False with end
                 | S h', ParseNonTerminal name str' p'
                   => fun pf
                          minimal_parse_of_item__of__parse_of_item_rec
                          minimal_parse_of__of__parse_of
                          p_small forall_parse
                      => _
               end
                 pf
                 (@minimal_parse_of_item__of__parse_of_item_rec)
                 (@minimal_parse_of__of__parse_of)).
            exists ).
inl (existT _ (MinParseTerminal _ x) )
                 | S h',
                   => fun minimal_parse_of_item__of__parse_of_item_rec
                          minimal_parse_of__of__parse_of
                          p_small forall_parse
                      => match @minimal_parse_of__of__parse_of
                                 _ (remove_name valid name) _
                                 p'
                                 (NPeano.Nat.lt_succ_l _ _ p_small)
                                 (snd forall_parse)
                         with
                           | inl (existT mp (H0, H0_forall))
                             => match Sumbool.sumbool_of_bool (is_valid_name valid name) with
                                  | left H'
                                    => inl (existT _ (MinParseNonTerminal H' mp) (Le.le_n_S _ _ H0, (fst forall_parse, H0_forall)))
                                  | right H'
                                    => inr (existT
                                              _ name
                                              (conj H' (fst forall_parse),
                                               existT
                                                 _ (parse_of__of__minimal_parse_of mp)
                                                 (Lt.le_lt_n_Sm _ _ H0, H0_forall)))
                                end
                           | inr (existT name' other)
                             => match string_dec name name' with
                                  | right pf
                                    => inr (existT
                                              _ name'
                                              (conj
                                                 (eq_trans (eq_sym (remove_name_5 valid pf)) (proj1 (fst other)))
                                                 (proj2 (fst other)),
                                               (existT
                                                  _ (projT1 (snd other))
                                                  (Lt.lt_S _ _ (fst (projT2 (snd other))), snd (projT2 (snd other))))))
                                  | left pf
                                    => match Sumbool.sumbool_of_bool (is_valid_name valid name) with
                                         | left H'
                                           => let other' :=
                                                  (match eq_sym pf in (_ = y)
                                                         return (is_valid_name (remove_name valid name) y =
                                                                 false /\ P y) *
                                                                { p0 : parse_of String G _ (Lookup G y)
                                                                       & ((height_of_parse p0 < height_of_parse _) * Forall_parse_of P p0)%type }
                                                   with
                                                     | eq_refl => other
                                                   end) in
                                              let p'' := (@minimal_parse_of_item__of__parse_of_item_rec
                                                            _ p_small
                                                            (of_parse_T_resp p_small minimal_parse_of__of__parse_of)
                                                            (ParseNonTerminal name (projT1 (snd other')))
                                                            (Lt.lt_n_S _ _ (fst (projT2 (snd other'))))
                                                            (proj2 (fst other'), snd (projT2 (snd other')))) in

                                              match p'' with
                                                | inl (existT p''' (H'', H''_forall))
                                                  => inl (existT
                                                            _ p'''
                                                            (Le.le_trans _ _ _ H'' (Lt.lt_le_weak _ _ (Lt.lt_n_S _ _ (fst (projT2 (snd other'))))), H''_forall))
                                                | inr p'''
                                                  => inr (expand_alt_option
                                                            (Lt.lt_n_S _ _ (fst (projT2 (snd other'))))
                                                            (reflexivity _)
                                                            (reflexivity _)
                                                            p''')
                                              end
                                         | right H'
                                           => inr (existT
                                                     _ name'
                                                     (conj
                                                        (match pf in (_ = y)
                                                               return is_valid_name valid y = false
                                                         with
                                                           | eq_refl => H'
                                                         end)
                                                        (proj2 (fst other)),
                                                      (existT
                                                         _ (projT1 (snd other))
                                                         (Lt.lt_S _ _ (fst (projT2 (snd other))), snd (projT2 (snd other))))))
                                       end
                                end
                         end
               end
                 (@minimal_parse_of_item__of__parse_of_item_rec)
                 (@minimal_parse_of__of__parse_of)).
        End helper.

        Definition minimal_parse_of_item__of__parse_of_item'
        : forall (h : nat)
                 (minimal_parse_of__of__parse_of : of_parse_T h)
                 (p : parse_of_item String G str it),
            of_parse_item_T p h
          := Fix Wf_nat.lt_wf _ minimal_parse_of_item__of__parse_of_item'_helper.
      End item.

      Section production.
        Let of_parse_production_T {str valid pat} (p : parse_of_production String G str pat) h
          := height_of_parse_production p < h
             -> Forall_parse_of_production P p
             -> ({ p' : minimal_parse_of_production valid str pat
                        & (height_of_parse_production (parse_of_production__of__minimal_parse_of_production p') <= height_of_parse_production p)
                          * Forall_parse_of_production P (parse_of_production__of__minimal_parse_of_production p') })%type
                + alt_option (height_of_parse_production p) valid str.

        Let rec_T h
          := forall h', h' < h -> of_parse_T h' -> forall str valid pat p, @of_parse_production_T str valid pat p h'.

        Section helper.
          Context (h : nat)
                  (minimal_parse_of_production__of__parse_of_production_rec : rec_T h)
                  (minimal_parse_of__of__parse_of : of_parse_T h).

          Let minimal_parse_of_production__of__parse_of_production h' H
          : forall {str} valid {pat} (p : parse_of_production String G str pat),
              of_parse_production_T p h'
            := @minimal_parse_of_production__of__parse_of_production_rec
                 h' H (of_parse_T_resp H (@minimal_parse_of__of__parse_of)).

          Let minimal_parse_of_item__of__parse_of_item {str} valid {it}
            := @minimal_parse_of_item__of__parse_of_item' str valid it h minimal_parse_of__of__parse_of.

          Context {str : String} (valid : names_listT) {pat : production CharType}.

          Definition minimal_parse_of_production__of__parse_of_production'_helper
                     (p : parse_of_production String G str pat)
          : @of_parse_production_T str valid pat p h.
          Proof.
            refine (
                match h as h, p as p in (parse_of_production _ _ str pat)
                      return ((forall h' (H : h' < h) str valid pat (p : parse_of_production String G str pat),
                                 of_parse_production_T p h')
                              -> (forall str valid it p', @of_parse_item_T str valid it p' h) -> of_parse_production_T p h)
                with
                  | 0, _ => fun _ _ H' _ => match Lt.lt_n_0 _ H' : False with end
                  | S h', ParseProductionNil
                    => fun _ _ p_small forall_parse
                       => inl (existT
                                 _ (MinParseProductionNil _)
                                 (reflexivity _, forall_parse))
                  | S h', ParseProductionCons str0 pat' str1 pats' p0' p1'
                    => fun minimal_parse_of_production__of__parse_of_production
                           minimal_parse_of_item__of__parse_of_item
                           p_small forall_parse
                       => let mp0 := @minimal_parse_of_item__of__parse_of_item _ valid _ p0' (NPeano.Nat.lt_succ_l _ _ (proj1 (proj1 (NPeano.Nat.max_lub_lt_iff _ _ _) p_small))) (fst forall_parse) in
                          let mp0' := alt_all_elim (@minimal_parse_of_item__of__parse_of_item _ initial_names_data _ p0' (NPeano.Nat.lt_succ_l _ _ (proj1 (proj1 (NPeano.Nat.max_lub_lt_iff _ _ _) p_small))) (fst forall_parse)) in
                          let mp1 := (@minimal_parse_of_production__of__parse_of_production _ p_small _ valid _ p1' (Max.le_max_r _ _) (snd forall_parse)) in
                          let mp1' := alt_all_elim (@minimal_parse_of_production__of__parse_of_production _ p_small _ initial_names_data _ p1' (Max.le_max_r _ _) (snd forall_parse)) in
                          match stringlike_dec str0 (Empty _), stringlike_dec str1 (Empty _) with
                            | right pf0, right pf1
                              => inl (existT
                                        _ (MinParseProductionConsDec valid pf0 pf1 (projT1 mp0') (projT1 mp1'))
                                        (NPeano.Nat.max_le_compat _ _ _ _ (Le.le_n_S _ _ (fst (projT2 mp0'))) (Le.le_n_S _ _ (fst (projT2 mp1'))),
                                         (snd (projT2 mp0'), snd (projT2 mp1'))))
                            | left pf0, left pf1
                              => let eq_pf0 := (_ : str0 = str0 ++ str1) in
                                 let eq_pf1 := (_ : str1 = str0 ++ str1) in
                                 match mp0, mp1 with
                                   | inl mp0'', inl mp1''
                                     => inl (existT
                                               _ (MinParseProductionConsEmpty01 pf0 pf1 (projT1 mp0'') (projT1 mp1''))
                                               (NPeano.Nat.max_le_compat _ _ _ _ (Le.le_n_S _ _ (fst (projT2 mp0''))) (Le.le_n_S _ _ (fst (projT2 mp1''))),
                                                (snd (projT2 mp0''), snd (projT2 mp1''))))
                                   | inr other, _
                                     => inr (expand_alt_option
                                               (Max.le_max_l _ _)
                                               (reflexivity _)
                                               eq_pf0
                                               other)
                                   | _, inr other
                                     => inr (expand_alt_option
                                               (Max.le_max_r _ _)
                                               (reflexivity _)
                                               eq_pf1
                                               other)
                                 end
                            | left pf0, right pf1
                              => let eq_pf := (_ : str1 = str0 ++ str1) in
                                 match mp1 with
                                   | inl mp1''
                                     => inl (existT
                                               _ (MinParseProductionConsEmpty0 pf0 pf1 (projT1 mp0') (projT1 mp1''))
                                               (NPeano.Nat.max_le_compat _ _ _ _ (Le.le_n_S _ _ (fst (projT2 mp0'))) (Le.le_n_S _ _ (fst (projT2 mp1''))),
                                                (snd (projT2 mp0'), snd (projT2 mp1''))))
                                   | inr other
                                     => inr (expand_alt_option
                                               (Max.le_max_r _ _)
                                               (reflexivity _)
                                               eq_pf
                                               other)
                                 end
                            | right pf0, left pf1
                              => let eq_pf := (_ : str0 = str0 ++ str1) in
                                 match mp0 with
                                   | inl mp0''
                                     => inl (existT
                                               _ (MinParseProductionConsEmpty1 pf0 pf1 (projT1 mp0'') (projT1 mp1'))
                                               (NPeano.Nat.max_le_compat _ _ _ _ (Le.le_n_S _ _ (fst (projT2 mp0''))) (Le.le_n_S _ _ (fst (projT2 mp1'))),
                                                (snd (projT2 mp0''), snd (projT2 mp1'))))
                                   | inr other
                                     => inr (expand_alt_option
                                               (Max.le_max_l _ _)
                                               (reflexivity _)
                                               eq_pf
                                               other)
                                 end
                          end
                end
                  (@minimal_parse_of_production__of__parse_of_production)
                  (@minimal_parse_of_item__of__parse_of_item));
            simpl in *;
            try solve [ subst; rewrite ?LeftId, ?RightId; trivial ].
          Defined.
        End helper.

        Definition minimal_parse_of_production__of__parse_of_production'
        : forall (h : nat)
                 (minimal_parse_of__of__parse_of : of_parse_T h)
                 {str} valid {pat}
                 (p : parse_of_production String G str pat),
            @of_parse_production_T str valid pat p h
          := Fix Wf_nat.lt_wf _ minimal_parse_of_production__of__parse_of_production'_helper.
      End production.

      Section parse_of.
        Let rec_T h
          := forall h', h' < h -> of_parse_T h'.

        Section helper.
          Context (h : nat)
                  (minimal_parse_of__of__parse_of_rec : rec_T h).

          Let minimal_parse_of__of__parse_of h' H
          : of_parse_T h'
            := @minimal_parse_of__of__parse_of_rec h' H.

          Context {str : String} (valid : names_listT) {pats : productions CharType}.

          Definition minimal_parse_of__of__parse_of'_helper
                     (p : parse_of String G str pats)
          : @of_parse_T' h str valid pats p
            := match h as h, p as p in (parse_of _ _ str pats)
                     return ((forall h' (H : h' < h), of_parse_T h')
                             -> @of_parse_T' h str valid pats p)
               with
                 | 0, _ => fun _ H' => match Lt.lt_n_0 _ H' : False with end
                 | S h', ParseHead _ pat' pats' p'
                   => fun minimal_parse_of__of__parse_of
                          p_small
                          forall_parse
                      => let minimal_parse_of_production__of__parse_of_production
                               {str} valid {pat}
                             := @minimal_parse_of_production__of__parse_of_production' h' (@minimal_parse_of__of__parse_of _ (Lt.lt_n_Sn _)) str valid pat in
                         match minimal_parse_of_production__of__parse_of_production valid p' (Lt.lt_S_n _ _ p_small) forall_parse with
                           | inl mp
                             => inl (existT
                                       _ (MinParseHead pats' (projT1 mp))
                                       (Le.le_n_S _ _ (fst (projT2 mp)),
                                        snd (projT2 mp)))
                           | inr other
                             => inr (expand_alt_option
                                       (Lt.lt_n_Sn _)
                                       (reflexivity _)
                                       (reflexivity _)
                                       other)
                         end
                 | S h', ParseTail _ pat' pats' p'
                   => fun minimal_parse_of__of__parse_of
                          p_small
                          forall_parse
                      => match minimal_parse_of__of__parse_of _ (Lt.lt_n_Sn _) _ valid _ p' (Lt.lt_S_n _ _ p_small) forall_parse with
                           | inl mp
                             => inl (existT
                                       _ (MinParseTail pat' (projT1 mp))
                                       (Le.le_n_S _ _ (fst (projT2 mp)),
                                        snd (projT2 mp)))
                           | inr other
                             => inr (expand_alt_option
                                       (Lt.lt_n_Sn _)
                                       (reflexivity _)
                                       (reflexivity _)
                                       other)
                         end
               end
                 (@minimal_parse_of__of__parse_of).
        End helper.

        Definition minimal_parse_of__of__parse_of'
        : forall (h : nat)
                 {str} valid {pats}
                 (p : parse_of String G str pats),
            @of_parse_T' h str valid pats p
          := Fix Wf_nat.lt_wf _ minimal_parse_of__of__parse_of'_helper.
      End parse_of.
    End wf_parts.

    Definition minimal_parse_of__of__parse_of
               {str : String} {pats : productions CharType}
               (p : parse_of String G str pats)
               (H : Forall_parse_of P p)
    : minimal_parse_of initial_names_data str pats
      := match @minimal_parse_of__of__parse_of'
                 _ str initial_names_data pats p
                 (Lt.lt_n_Sn _)
                 H with
           | inl p' => projT1 p'
           | inr other => let H' := fst (projT2 other) in
                          match Bool.eq_true_false_abs _ (proj2 H') (proj1 H') : False with end
         end.

    Definition minimal_parse_of_production__of__parse_of_production
               {str : String} {pat : production CharType}
               (p : parse_of_production String G str pat)
               (H : Forall_parse_of_production P p)
    : minimal_parse_of_production initial_names_data str pat
      := match @minimal_parse_of_production__of__parse_of_production'
                 _ (@minimal_parse_of__of__parse_of' _) str initial_names_data pat p
                 (Lt.lt_n_Sn _)
                 H with
           | inl p' => projT1 p'
           | inr other => let H' := fst (projT2 other) in
                          match Bool.eq_true_false_abs _ (proj2 H') (proj1 H') : False with end
         end.

    Definition minimal_parse_of_item__of__parse_of_item
               {str : String} {it : item CharType}
               (p : parse_of_item String G str it)
               (H : Forall_parse_of_item P p)
    : minimal_parse_of_item initial_names_data str it
      := match @minimal_parse_of_item__of__parse_of_item'
                 str initial_names_data it
                 _ (@minimal_parse_of__of__parse_of' _) p
                 (Lt.lt_n_Sn _)
                 H with
           | inl p' => projT1 p'
           | inr other => let H' := fst (projT2 other) in
                          match Bool.eq_true_false_abs _ (proj2 H') (proj1 H') : False with end
         end.
  End minimize.
End cfg.
