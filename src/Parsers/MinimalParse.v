(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Parsers.ContextFreeGrammar Parsers.ContextFreeGrammarProperties Parsers.WellFoundedParse.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Notation "f ∘ g" := (fun x => f (g x)).

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType)
          (chartype_dec : forall x y : CharType, {x = y} + {x <> y}).
  Context (productions_listT : Type)
          (initial_productions_data : productions_listT)
          (is_valid_productions : productions_listT -> productions CharType -> bool)
          (remove_productions : productions_listT -> productions CharType -> productions_listT)
          (remove_productions_1
           : forall ls ps ps',
               is_valid_productions (remove_productions ls ps) ps' = true
               -> is_valid_productions ls ps' = true)
          (remove_productions_2
           : forall ls ps ps',
               is_valid_productions (remove_productions ls ps) ps' = false
               <-> is_valid_productions ls ps' = false \/ ps = ps').

  Lemma remove_productions_3
        ls ps ps' (H : is_valid_productions ls ps = false)
  : is_valid_productions (remove_productions ls ps) ps' = is_valid_productions ls ps'.
  Proof.
    case_eq (is_valid_productions (remove_productions ls ps) ps');
    case_eq (is_valid_productions ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_productions_1 in H''
          | apply remove_productions_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Lemma remove_productions_4
        ls ps ps' (H : is_valid_productions (remove_productions ls ps) ps' = true)
  : ps <> ps'.
  Proof.
    intro H'.
    pose proof (proj2 (remove_productions_2 ls _ _) (or_intror H')).
    congruence.
  Qed.

  Lemma remove_productions_5
        ls ps ps' (H : ps <> ps')
  : is_valid_productions (remove_productions ls ps) ps' = is_valid_productions ls ps'.
  Proof.
    case_eq (is_valid_productions (remove_productions ls ps) ps');
    case_eq (is_valid_productions ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_productions_1 in H''
          | apply remove_productions_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Inductive minimal_parse_of
  : productions_listT -> String -> productions CharType -> Type :=
  | MinParseHead : forall valid str pat pats,
                     minimal_parse_of_production valid str pat
                     -> minimal_parse_of valid str (pat::pats)
  | MinParseTail : forall valid str pat pats,
                     minimal_parse_of valid str pats
                     -> minimal_parse_of valid str (pat::pats)
  with minimal_parse_of_production
  : productions_listT -> String -> production CharType -> Type :=
  | MinParseProductionNil : forall valid,
                              minimal_parse_of_production valid (Empty _) nil
  | MinParseProductionConsDec : forall valid str pat strs pats,
                                  str <> Empty _
                                  -> strs <> Empty _
                                  -> minimal_parse_of_item initial_productions_data str pat
                                  -> minimal_parse_of_production initial_productions_data strs pats
                                  -> minimal_parse_of_production valid (str ++ strs) (pat::pats)
  | MinParseProductionConsEmpty0 : forall valid str pat strs pats,
                                     str = Empty _
                                     -> strs <> Empty _
                                     -> minimal_parse_of_item initial_productions_data str pat
                                     -> minimal_parse_of_production valid strs pats
                                     -> minimal_parse_of_production valid (str ++ strs) (pat::pats)
  | MinParseProductionConsEmpty1 : forall valid str pat strs pats,
                                     str <> Empty _
                                     -> strs = Empty _
                                     -> minimal_parse_of_item valid str pat
                                     -> minimal_parse_of_production initial_productions_data strs pats
                                     -> minimal_parse_of_production valid (str ++ strs) (pat::pats)
  | MinParseProductionConsEmpty01 : forall valid str pat strs pats,
                                     str = Empty _
                                     -> strs = Empty _
                                     -> minimal_parse_of_item valid str pat
                                     -> minimal_parse_of_production valid strs pats
                                     -> minimal_parse_of_production valid (str ++ strs) (pat::pats)
  with minimal_parse_of_item
  : productions_listT -> String -> item CharType -> Type :=
  | MinParseTerminal : forall valid x,
                         minimal_parse_of_item valid [[ x ]]%string_like (Terminal x)
  | MinParseNonTerminal
    : forall valid name str,
        is_valid_productions valid (Lookup G name) = true
        -> minimal_parse_of (remove_productions valid (Lookup G name)) str (Lookup G name)
        -> minimal_parse_of_item valid str (NonTerminal CharType name).

  Fixpoint parse_of__of__minimal_parse_of {valid str pats} (p : minimal_parse_of valid str pats)
  : parse_of String G str pats
    := match p with
         | MinParseHead valid str pat pats p'
           => ParseHead pats (parse_of_production__of__minimal_parse_of_production p')
         | MinParseTail valid str pat pats p'
           => ParseTail pat (parse_of__of__minimal_parse_of p')
       end
  with parse_of_production__of__minimal_parse_of_production {valid str pat} (p : minimal_parse_of_production valid str pat)
       : parse_of_production String G str pat
       := (let parse_of_item__of__minimal_parse_of_item {valid str it} (p : minimal_parse_of_item valid str it)
               := match p in (minimal_parse_of_item valid str it) return parse_of_item String G str it with
                    | MinParseTerminal valid x
                      => ParseTerminal String G x
                    | MinParseNonTerminal valid name str H p'
                      => ParseNonTerminal name (parse_of__of__minimal_parse_of p')
                  end in
                   match p with
                     | MinParseProductionNil valid
                       => ParseProductionNil _ _
                     | MinParseProductionConsDec valid str pat strs pats _ _ p' p''
                       => ParseProductionCons
                            (parse_of_item__of__minimal_parse_of_item p')
                            (parse_of_production__of__minimal_parse_of_production p'')
                     | MinParseProductionConsEmpty0 valid str pat strs pats _ _ p' p''
                       => ParseProductionCons
                            (parse_of_item__of__minimal_parse_of_item p')
                            (parse_of_production__of__minimal_parse_of_production p'')
                     | MinParseProductionConsEmpty1 valid str pat strs pats _ _ p' p''
                       => ParseProductionCons
                            (parse_of_item__of__minimal_parse_of_item p')
                            (parse_of_production__of__minimal_parse_of_production p'')
                     | MinParseProductionConsEmpty01 valid str pat strs pats _ _ p' p''
                       => ParseProductionCons
                            (parse_of_item__of__minimal_parse_of_item p')
                            (parse_of_production__of__minimal_parse_of_production p'')
                   end).

  Definition parse_of_item__of__minimal_parse_of_item {valid str it} (p : minimal_parse_of_item valid str it)
    := match p in (minimal_parse_of_item valid str it) return parse_of_item String G str it with
         | MinParseTerminal valid x
           => ParseTerminal String G x
         | MinParseNonTerminal valid name str H p'
           => ParseNonTerminal name (parse_of__of__minimal_parse_of p')
       end.

  Definition sub_productions_listT (x y : productions_listT) : Prop
    := forall p, is_valid_productions x p = true -> is_valid_productions y p = true.

  Global Instance sub_productions_listT_Reflexive : Reflexive sub_productions_listT
    := fun x y f => f.

  Global Instance sub_productions_listT_Transitive : Transitive sub_productions_listT.
  Proof.
    lazy; auto.
  Defined.

  Add Parametric Morphism : remove_productions
  with signature sub_productions_listT ==> eq ==> sub_productions_listT
    as remove_productions_mor.
  Proof.
    intros x y H z w H'.
    hnf in H.
    pose proof (remove_productions_4 H').
    apply remove_productions_1 in H'.
    rewrite remove_productions_5 by assumption.
    auto.
  Qed.

  Lemma sub_productions_listT_remove ls ps
  : sub_productions_listT (remove_productions ls ps) ls.
  Proof.
    intros p.
    apply remove_productions_1.
  Qed.

  Lemma sub_productions_listT_remove_2 ls ls' ps (H : sub_productions_listT ls ls')
  : sub_productions_listT (remove_productions ls ps) ls'.
  Proof.
    etransitivity; eauto using sub_productions_listT_remove.
  Qed.

  Fixpoint expand_minimal_parse_of {valid valid' str pats} (H : sub_productions_listT valid valid') (p : minimal_parse_of valid str pats)
  : minimal_parse_of valid' str pats
    := match p in (minimal_parse_of valid str pats) return (sub_productions_listT valid valid' -> _) with
         | MinParseHead valid str pat pats p'
           => fun H => MinParseHead pats (expand_minimal_parse_of_production H p')
         | MinParseTail valid str pat pats p'
           => fun H => MinParseTail pat (expand_minimal_parse_of H p')
       end H
  with expand_minimal_parse_of_production {valid valid' str pat} (H : sub_productions_listT valid valid') (p : minimal_parse_of_production valid str pat)
       : minimal_parse_of_production valid' str pat
       := (let expand_minimal_parse_of_item {valid valid' str it} (H : sub_productions_listT valid valid') (p : minimal_parse_of_item valid str it)
               := match p in (minimal_parse_of_item valid str it) return (sub_productions_listT valid valid' -> minimal_parse_of_item valid' str it) with
                    | MinParseTerminal valid x
                      => fun _ => MinParseTerminal valid' x
                    | MinParseNonTerminal valid name str H p'
                      => fun H' => MinParseNonTerminal name (H' _ H) (expand_minimal_parse_of (remove_productions_mor H' eq_refl) p')
                  end H in
                   match p in (minimal_parse_of_production valid str pats) return (sub_productions_listT valid valid' -> minimal_parse_of_production valid' str pats) with
                     | MinParseProductionNil valid
                       => fun _ => MinParseProductionNil valid'
                     | MinParseProductionConsDec valid str pat strs pats pf pf' p' p''
                       => fun H => MinParseProductionConsDec
                                     valid'
                                     pf pf'
                                     (expand_minimal_parse_of_item (reflexivity _) p')
                                     (expand_minimal_parse_of_production (reflexivity _) p'')
                     | MinParseProductionConsEmpty0 valid str pat strs pats pf pf' p' p''
                       => fun H => MinParseProductionConsEmpty0
                                     (valid := valid')
                                     pf pf'
                                     (expand_minimal_parse_of_item (reflexivity _) p')
                                     (expand_minimal_parse_of_production (fun p H0 => H _ H0) p'')
                     | MinParseProductionConsEmpty1 valid str pat strs pats pf pf' p' p''
                       => fun H => MinParseProductionConsEmpty1
                                     (valid := valid')
                                     pf pf'
                                     (expand_minimal_parse_of_item (fun p H0 => H _ H0) p')
                                     (expand_minimal_parse_of_production (reflexivity _) p'')
                     | MinParseProductionConsEmpty01 valid str pat strs pats pf pf' p' p''
                       => fun H => MinParseProductionConsEmpty01
                                     (valid := valid')
                                     pf pf'
                                     (expand_minimal_parse_of_item (fun p H0 => H _ H0) p')
                                     (expand_minimal_parse_of_production (fun p H0 => H _ H0) p'')
                   end H).

  Definition expand_minimal_parse_of_item {valid valid' str it} (H : sub_productions_listT valid valid') (p : minimal_parse_of_item valid str it)
    := match p in (minimal_parse_of_item valid str it) return (sub_productions_listT valid valid' -> minimal_parse_of_item valid' str it) with
         | MinParseTerminal valid x
           => fun _ => MinParseTerminal valid' x
         | MinParseNonTerminal valid name str H p'
           => fun H' => MinParseNonTerminal name (H' _ H) (expand_minimal_parse_of (remove_productions_mor H' eq_refl) p')
       end H.

  Section minimize.
    Let P : productions CharType -> Prop
      := fun p => is_valid_productions initial_productions_data p = true.

    Let alt_option h valid str
      := { name : _ & (is_valid_productions valid (Lookup G name) = false /\ P (Lookup G name))
                      * { p : parse_of String G str (Lookup G name)
                              & (height_of_parse p < h)
                                * Forall_parse_of P p } }%type.

    Lemma not_alt_all {h str} (ps : alt_option h initial_productions_data str)
    : False.
    Proof.
      subst P; simpl in *.
      destruct ps as [ ? [ H' _ ] ].
      revert H'; clear; intros [? ?].
      congruence.
    Qed.

    Definition alt_all_elim {h str T} (ps : T + alt_option h initial_productions_data str)
    : T.
    Proof.
      destruct ps as [|ps]; [ assumption | exfalso ].
      eapply not_alt_all; eassumption.
    Defined.

    Definition expand_alt_option {h h' str str' valid valid'}
               (H : h < h') (H' : sub_productions_listT valid' valid) (H'' : str = str')
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
          {str : String} (valid : productions_listT) {pats : productions CharType}
          (p : parse_of String G str pats)

        := forall (p_small : height_of_parse p < h),
             Forall_parse_of P p
             -> ({ p' : minimal_parse_of valid str pats
                        & (height_of_parse (parse_of__of__minimal_parse_of p') <= height_of_parse p)
                          * Forall_parse_of P (parse_of__of__minimal_parse_of p') })%type
                + alt_option (height_of_parse p) valid str.

      Let of_parse_T h
        := forall str valid pats p, @of_parse_T' h str valid pats p.

      Definition of_parse_T_resp {h h'} (H : h' < h) (parse : of_parse_T h)
      : of_parse_T h'
        := fun str' valid' pats' p' p_small'
           => @parse str' valid' pats' p' (Lt.lt_trans _ _ _ p_small' H).

      Let of_parse_item_T {str valid it} (p : parse_of_item String G str it) h
        := height_of_parse_item p < h
           -> Forall_parse_of_item P p
           -> ({ p' : minimal_parse_of_item valid str it
                      & (height_of_parse_item (parse_of_item__of__minimal_parse_of_item p') <= height_of_parse_item p)
                        * Forall_parse_of_item P (parse_of_item__of__minimal_parse_of_item p') })%type
              + alt_option (height_of_parse_item p) valid str.

      Section item.
        Context {str : String} (valid : productions_listT) {it : item CharType}.

        Let rec_T str it h
          := forall h', h' < h -> of_parse_T h' -> forall p, @of_parse_item_T str valid it p h'.

        Section helper.
          Context (h : nat)
                  (minimal_parse_of_item__of__parse_of_item_rec : rec_T str it h)
                  (minimal_parse_of__of__parse_of : of_parse_T h).

          Definition minimal_parse_of_item__of__parse_of_item'_helper
                     (p : parse_of_item String G str it)
          : of_parse_item_T p h
            := match h as h, p as p in (parse_of_item _ _ str it)
                     return (rec_T str it h -> of_parse_T h -> of_parse_item_T p h)
               with
                 | _, ParseTerminal x
                   => fun _ _ H' _ => inl (existT _ (MinParseTerminal _ x) (le_n _, tt))
                 | 0, ParseNonTerminal _ _ _
                   => fun _ _ H' _ => match Lt.lt_n_0 _ H' : False with end
                 | S h', ParseNonTerminal name str' p'
                   => fun minimal_parse_of_item__of__parse_of_item_rec
                          minimal_parse_of__of__parse_of
                          p_small forall_parse
                      => match @minimal_parse_of__of__parse_of
                                 _ (remove_productions valid (G name)) _
                                 p'
                                 (NPeano.Nat.lt_succ_l _ _ p_small)
                                 (snd forall_parse)
                         with
                           | inl (existT mp (H0, H0_forall))
                             => match Sumbool.sumbool_of_bool (is_valid_productions valid (G name)) with
                                  | left H'
                                    => inl (existT _ (MinParseNonTerminal name H' mp) (Le.le_n_S _ _ H0, (fst forall_parse, H0_forall)))
                                  | right H'
                                    => inr (existT
                                              _ name
                                              (conj H' (fst forall_parse),
                                               existT
                                                 _ (parse_of__of__minimal_parse_of mp)
                                                 (Lt.le_lt_n_Sm _ _ H0, H0_forall)))
                                end
                           | inr (existT name' other)
                             => match productions_dec chartype_dec (G name) (G name') with
                                  | right pf
                                    => inr (existT
                                              _ name'
                                              (conj
                                                 (eq_trans (eq_sym (remove_productions_5 valid pf)) (proj1 (fst other)))
                                                 (proj2 (fst other)),
                                               (existT
                                                  _ (projT1 (snd other))
                                                  (Lt.lt_S _ _ (fst (projT2 (snd other))), snd (projT2 (snd other))))))
                                  | left pf
                                    => match Sumbool.sumbool_of_bool (is_valid_productions valid (G name)) with
                                         | left H'
                                           => let other' :=
                                                  (match eq_sym pf in (_ = y)
                                                         return (is_valid_productions (remove_productions valid (G name)) y =
                                                                 false /\ P y) *
                                                                { p0 : parse_of String G _ y
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
                                                               return is_valid_productions valid y = false
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
                 (@minimal_parse_of__of__parse_of).
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

          Context {str : String} (valid : productions_listT) {pat : production CharType}.

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
                          let mp0' := alt_all_elim (@minimal_parse_of_item__of__parse_of_item _ initial_productions_data _ p0' (NPeano.Nat.lt_succ_l _ _ (proj1 (proj1 (NPeano.Nat.max_lub_lt_iff _ _ _) p_small))) (fst forall_parse)) in
                          let mp1 := (@minimal_parse_of_production__of__parse_of_production _ p_small _ valid _ p1' (Max.le_max_r _ _) (snd forall_parse)) in
                          let mp1' := alt_all_elim (@minimal_parse_of_production__of__parse_of_production _ p_small _ initial_productions_data _ p1' (Max.le_max_r _ _) (snd forall_parse)) in
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

          Context {str : String} (valid : productions_listT) {pats : productions CharType}.

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
    : minimal_parse_of initial_productions_data str pats
      := match @minimal_parse_of__of__parse_of'
                 _ str initial_productions_data pats p
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
    : minimal_parse_of_production initial_productions_data str pat
      := match @minimal_parse_of_production__of__parse_of_production'
                 _ (@minimal_parse_of__of__parse_of' _) str initial_productions_data pat p
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
    : minimal_parse_of_item initial_productions_data str it
      := match @minimal_parse_of_item__of__parse_of_item'
                 str initial_productions_data it
                 _ (@minimal_parse_of__of__parse_of' _) p
                 (Lt.lt_n_Sn _)
                 H with
           | inl p' => projT1 p'
           | inr other => let H' := fst (projT2 other) in
                          match Bool.eq_true_false_abs _ (proj2 H') (proj1 H') : False with end
         end.
  End minimize.
End cfg.
