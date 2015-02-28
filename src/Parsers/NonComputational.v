(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar.
Require Import Common Common.ilist.

Set Implicit Arguments.
(*(** We implement a generic recursive descent parser.  We parameterize
    over a number of parameters:

    - [T : Type] - the type of results of successful parsing.
      Parameterizing over this allows, e.g., higher-order parsing.

      TODO?: generalize this to use continuations instead, so we can
      do monadic side-effects when parsing.

    - [aggregate : String → T → String → T → T] - takes the results of
      two successful adjacent parses and combines them.

    - [pick_parses : String → nonterminal → list (list String)] - A
      non-terminal is a list of patterns.  This function will break up
      a string into a list of possible splits; a split is an
      assignment of a part of the string to each pattern.


    The basic idea is that

FIXME *)*)
(** TODO: rename pattern to production *)

Section wf.
  Section wf_prod.
    Context A B (RA : relation A) (RB : relation B).

    Definition prod_relation : relation (A * B)
      := fun ab a'b' =>
           RA (fst ab) (fst a'b') \/ (fst a'b' = fst ab /\ RB (snd ab) (snd a'b')).

    Fixpoint well_founded_prod_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : well_founded RB) {struct wf_A}
    : Acc prod_relation (a, b)
      := match wf_A with
           | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc RB b') : Acc prod_relation (a, b')
                              := Acc_intro
                                   _
                                   (fun ab =>
                                      match ab as ab return prod_relation ab (a, b') -> Acc prod_relation ab with
                                        | (a'', b'') =>
                                          fun pf =>
                                            match pf with
                                              | or_introl pf'
                                                => @well_founded_prod_relation_helper
                                                     _ _
                                                     (fa _ pf')
                                                     wf_B
                                              | or_intror (conj pfa pfb)
                                                => match wf_B' with
                                                     | Acc_intro fb
                                                       => eq_rect
                                                            _
                                                            (fun a'' => Acc prod_relation (a'', b''))
                                                            (wf_B_rec _ (fb _ pfb))
                                                            _
                                                            pfa
                                                   end
                                            end
                                      end)
                             ) b (wf_B b)
         end.

    Definition well_founded_prod_relation : well_founded RA -> well_founded RB -> well_founded prod_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_prod_relation_helper; auto.
    Defined.
  End wf_prod.

  Section wf_sig.
    Context A B (RA : relation A) (RB : forall a : A, relation (B a)).

    Definition sigT_relation : relation (sigT B)
      := fun ab a'b' =>
           RA (projT1 ab) (projT1 a'b') \/ (exists pf : projT1 a'b' = projT1 ab, RB (projT2 ab)
                                                                                    (eq_rect _ B (projT2 a'b') _ pf)).

    Fixpoint well_founded_sigT_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : forall a, well_founded (@RB a)) {struct wf_A}
    : Acc sigT_relation (existT _ a b).
    Proof.
      refine match wf_A with
               | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc (@RB a) b') : Acc sigT_relation (existT _ a b')
                                  := Acc_intro
                                       _
                                       (fun ab =>
                                          match ab as ab return sigT_relation ab (existT _ a b') -> Acc sigT_relation ab with
                                            | existT a'' b'' =>
                                              fun pf =>
                                                match pf with
                                                  | or_introl pf'
                                                    => @well_founded_sigT_relation_helper
                                                         _ _
                                                         (fa _ pf')
                                                         wf_B
                                                  | or_intror (ex_intro pfa pfb)
                                                    => match wf_B' with
                                                         | Acc_intro fb
                                                           => _(*eq_rect
                                                            _
                                                            (fun a'' => Acc sigT_relation (existT B a'' _(*b''*)))
                                                            (wf_B_rec _ (fb _ _(*pfb*)))
                                                            _
                                                            pfa*)
                                                       end
                                                end
                                          end)
                                 ) b (wf_B a b)
             end;
      simpl in *.
      destruct pfa; simpl in *.
      exact (wf_B_rec _ (fb _ pfb)).
    Defined.

    Definition well_founded_sigT_relation : well_founded RA
                                            -> (forall a, well_founded (@RB a))
                                            -> well_founded sigT_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_sigT_relation_helper; auto.
    Defined.
  End wf_sig.
End wf.

Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  (** FIXME: The type of the list of nonterminals should be able to
  depend on the string we're parsing, so we can store proofs in it to
  pass down the parse tree to handle impossible cases.  This will
  require a [Total] lexicographic ordering on strings. *)
  Context (nonterminal_listT : String -> Type)
          (initial_nonterminal_data : forall str, nonterminal_listT str)
          (is_valid_nonterminal : forall str, nonterminal_listT str -> nonterminal CharType -> bool)
          (remove_nonterminal : forall str, nonterminal_listT str -> nonterminal CharType -> nonterminal_listT str)
          (nonterminal_listT_R : forall str, nonterminal_listT str -> nonterminal_listT str -> Prop)
          (remove_nonterminal_dec : forall str ls nt, is_valid_nonterminal str ls nt = true
                                                  -> nonterminal_listT_R str (remove_nonterminal str ls nt) ls)
          (ntl_wf : forall str, well_founded (nonterminal_listT_R str)).
  Section generic.
    Context (T : String -> nonterminal CharType -> Type)
            (T_reverse_lookup : forall str name, T str (Lookup G name) -> T str [ [ NonTerminal _ name ] ]).
    Context (parse_pattern_by_picking
             : forall str0
                      (parse_pattern_from_split_list'
                       : forall (strs : list { str : String | Length _ str < Length _ str0 \/ str = str0 })
                                (pat : pattern CharType),
                           ilist (fun sp => T (proj1_sig (fst sp)) [ [ snd sp ] ]) (combine strs pat))
                      (str : String)
                      (pf : Length _ str < Length _ str0 \/ str = str0)
                      (pat : pattern CharType),
                 T str [ pat ]).
    Context (decide_leaf : forall str ch, T str [ [ Terminal ch ] ]).
    Context (fold_patterns : forall str (pats : list (pattern CharType)),
                               ilist (fun pat => T str [ pat ]) pats
                               -> T str pats).
    Context (make_abort : forall str nt valid_list, @is_valid_nonterminal str valid_list nt = false -> T str nt).


    Section parts.
      Section item.
        Context (str : String)
                (parse_nonterminal : forall nt, T str nt).

        Definition parse_item it : T str [ [ it ] ]
          := match it with
               | Terminal ch => decide_leaf str ch
               | NonTerminal name => T_reverse_lookup _ (parse_nonterminal (Lookup G name))
             end.
      End item.

      Section pattern.
        Variable str0 : String.
        Variable parse_nonterminal : forall (str : String)
                                            (pf : Length _ str < Length _ str0 \/ str = str0)
                                            nt, T str nt.

        Definition parse_pattern_from_split_list
                   (strs : list { str : String | Length _ str < Length _ str0 \/ str = str0 })
                   (pat : pattern CharType)
        : ilist (fun sp => T (proj1_sig (fst sp)) [ [ snd sp ] ]) (combine strs pat)
          := imap_list (fun sp => T (proj1_sig (fst sp)) [ [ snd sp ] ])
                       (fun sp => parse_item (@parse_nonterminal _ (proj2_sig (fst sp))) (snd sp))
                       (combine strs pat).

        Definition parse_pattern (str : String) (pf : Length _ str < Length _ str0 \/ str = str0) (pat : pattern CharType)
        : T str [ pat ]
          := parse_pattern_by_picking parse_pattern_from_split_list pf pat.
      End pattern.

      Section nonterminal.
        Section step.
          Variable str0 : String.
          Variable parse_nonterminal : forall (str : String)
                                              (pf : Length _ str < Length _ str0 \/ str = str0)
                                              nt, T str nt.

          Definition parse_nonterminal_step (str : String) (pf : Length _ str < Length _ str0 \/ str = str0) (nt : nonterminal CharType)
          : T str nt
            := fold_patterns (imap_list (fun pat => T str [ pat ])
                                        (parse_pattern parse_nonterminal pf)
                                        nt).
        End step.

        Section wf.
          Definition parse_nonterminal_or_abort str0 str (valid_list : forall str, nonterminal_listT str)
                     (pf : Length _ str < Length _ str0 \/ str = str0)
                     (nt : nonterminal CharType)
          : T str nt.
          Proof.
            revert str pf nt.
            change str0 with (projT1 (existT nonterminal_listT str0 (valid_list str0))).
            generalize (existT nonterminal_listT str0 (valid_list str0)); clear str0 valid_list.
            refine (@Fix (sigT nonterminal_listT) _ (@well_founded_sigT_relation
                                                       String
                                                       nonterminal_listT
                                                       _
                                                       _
                                                       (well_founded_ltof _ (Length String))
                                                       ntl_wf)
                         _ _).
            intros [str0 valid_list] parse_nonterminal str pf nt; simpl in *.
            destruct (lt_dec (Length _ str) (Length _ str0)) as [pf'|pf'];
              [ | assert (str = str0) by intuition; subst ].
            { (** [str] got smaller, so we reset the valid nonterminals *)
              specialize (parse_nonterminal
                            (existT _ str (initial_nonterminal_data str))
                            (or_introl pf')); simpl in *.
              exact (parse_nonterminal_step parse_nonterminal (or_intror eq_refl) nt). }
            { (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
              case_eq (is_valid_nonterminal valid_list nt).
              { (** It was valid, so we can remove it *)
                intro H.
                specialize (fun pf' => parse_nonterminal
                              (existT _ str0 (remove_nonterminal valid_list nt))
                              (or_intror (ex_intro _ eq_refl pf'))); simpl in *.
                specialize (parse_nonterminal (remove_nonterminal_dec H)).
                exact (parse_nonterminal_step parse_nonterminal (or_intror eq_refl) nt). }
              { (** oops, we already saw this nonterminal in the past.  ABORT! *)
                apply make_abort. } }
          Defined.

          Definition parse_nonterminal str nt : T str nt
            := @parse_nonterminal_or_abort str str initial_nonterminal_data
                                           (or_intror eq_refl) nt.
        End wf.
      End nonterminal.
    End parts.
  End generic.

  Section parse_tree_no_split.
    Local Hint Constructors parse_of parse_of_pattern parse_of_item : parse_tree.
    Local Hint Resolve ParseHead ParsePatternSingleton : parse_tree.
    Local Hint Extern 1 => apply ParseHead : parse_tree.
    Local Hint Extern 0 (option (parse_of _ _ _ [])) => exact None : parse_tree.

    Definition parse_tree_no_split_for : forall str nt, option (parse_of String G str nt).
    Proof with auto with parse_tree nocore.
      apply (@parse_nonterminal (fun str nt => option (parse_of _ G str nt))).
      { intros str name [p|]; [ apply Some | exact None ]... }
      { intros.
        specialize (parse_pattern_from_split_list' ((exist _ str pf)::nil) pat); simpl in *.
        destruct pat as [|pat0 [|pat1 pats] ]; simpl in *.
        { case_eq (str =s Empty _); intro H; [ apply Some | exact None ]...
          apply bool_eq_correct in H; subst... }
        { destruct (ilist_hd parse_pattern_from_split_list') as [tree|]; simpl in *; [ apply Some | exact None ]... }
        { (** we don't handle the case where we need to split the string *)
          exact None. } }
      { (** decide_leaf *)
        intros str ch.
        case_eq (str =s [[ch]]); intro H; [ apply bool_eq_correct in H; apply Some | exact None ].
        subst... }
      { (** fold_patterns *)
        intros str pats parses; induction parses; simpl in *...
        repeat match goal with H : option _ |- _ => destruct H end;
          try solve [ apply Some; auto with parse_tree nocore
                    | apply Some;
                      repeat match goal with
                               | _ => progress auto with parse_tree nocore
                               | [ H : parse_of _ _ _ _ |- _ ] => inversion H; clear H; subst
                             end
                    | match goal with
                        | [ H : parse_of _ _ _ _ |- _ ] => fail 1
                        | _ => idtac
                      end;
                      exact None ]. }
      { (** make_abort *)
        intros; exact None. }
    Defined.
  End parse_tree_no_split.
End recursive_descent_parser.

Section recursive_descent_parser_list.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Variable (CharType_eq_dec : forall x y : CharType, {x = y} + {x <> y}).
  Definition rdp_list_nonterminal_listT : String -> Type := fun _ => list (nonterminal CharType).
  Definition rdp_list_is_valid_nonterminal : forall str, rdp_list_nonterminal_listT str -> nonterminal CharType -> bool
    := fun str ls nt => if in_dec (nonterminal_dec CharType_eq_dec) nt ls then true else false.
  Definition rdp_list_remove_nonterminal : forall str, rdp_list_nonterminal_listT str -> nonterminal CharType -> rdp_list_nonterminal_listT str
    := fun str ls nt =>
         filter (fun x => if nonterminal_dec CharType_eq_dec nt x then false else true) ls.
  Definition rdp_list_nonterminal_listT_R : forall str, rdp_list_nonterminal_listT str -> rdp_list_nonterminal_listT str -> Prop
    := fun _ => ltof _ (@List.length _).
  Lemma filter_list_dec {T} f (ls : list T) : List.length (filter f ls) <= List.length ls.
  Proof.
    induction ls; trivial; simpl in *.
    repeat match goal with
             | [ |- context[if ?a then _ else _] ] => destruct a; simpl in *
             | [ |- S _ <= S _ ] => solve [ apply Le.le_n_S; auto ]
             | [ |- _ <= S _ ] => solve [ apply le_S; auto ]
           end.
  Defined.
  Lemma rdp_list_remove_nonterminal_dec : forall str ls nt, @rdp_list_is_valid_nonterminal str ls nt = true
                                                            -> @rdp_list_nonterminal_listT_R str (@rdp_list_remove_nonterminal str ls nt) ls.
  Proof.
    intros.
    unfold rdp_list_is_valid_nonterminal, rdp_list_nonterminal_listT_R, rdp_list_remove_nonterminal, ltof in *.
    destruct (in_dec (nonterminal_dec CharType_eq_dec) nt ls); [ | discriminate ].
    match goal with
      | [ H : In ?nt ?ls |- context[filter ?f ?ls] ]
        => assert (~In nt (filter f ls))
    end.
    { intro H'.
      apply filter_In in H'.
      destruct H' as [? H'].
      destruct (nonterminal_dec CharType_eq_dec nt nt); congruence. }
    { match goal with
        | [ |- context[filter ?f ?ls] ] => generalize dependent f; intros
      end.
      induction ls; simpl in *; try congruence.
      repeat match goal with
               | [ |- context[if ?x then _ else _] ] => destruct x; simpl in *
               | [ H : _ \/ _ |- _ ] => destruct H
               | _ => progress subst
               | [ H : ~(_ \/ _) |- _ ] => apply Decidable.not_or in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : ?x <> ?x |- _ ] => exfalso; apply (H eq_refl)
               | _ => apply Lt.lt_n_S
               | _ => apply Le.le_n_S
               | _ => apply filter_list_dec
               | [ H : _ -> _ -> ?G |- ?G ] => apply H; auto
             end. }
  Defined.
  Lemma rdp_list_ntl_wf : forall str, well_founded (@rdp_list_nonterminal_listT_R str).
  Proof.
    unfold rdp_list_nonterminal_listT_R.
    intro.
    apply well_founded_ltof.
  Defined.
End recursive_descent_parser_list.

(*

  Section parse_tree.
    Context (make_splits : forall (str : String) (pat : pattern CharType),
                             list
                               {str' : String |
                                Length String str' <= Length _ str}).
    Local Hint Constructors parse_of parse_of_pattern parse_of_item : parse_tree.
    Local Hint Resolve ParseHead ParsePatternSingleton : parse_tree.
    Local Hint Extern 1 => apply ParseHead : parse_tree.
    Local Hint Extern 0 (option (parse_of _ _ _ [])) => exact None : parse_tree.

    Definition parse_tree_for : forall str nt, option (parse_of String G str nt).
    Proof with auto with parse_tree nocore.
      apply (@parse_nonterminal (fun str nt => option (parse_of _ G str nt))).
      { intros str name [p|]; [ apply Some | exact None ]... }
      { intros.
        specialize (make_splits str).
        pose proof (fun pat => map (fun spf => exist (fun s => Length _ s <= max_len)
                                                     (proj1_sig spf)
                                                     (transitivity (R := le) (proj2_sig spf) pf))
                                   (make_splits pat)) as make_splits'.
        specialize (fun pat => parse_pattern_from_split_list' (make_splits' pat) pat).
Goal (fun x : nat => x) = (fun x : nat => x).
  match goal with
    | |- context[fun x => x] => pose (fun y : Set => y)
  end. (* success *)
  match goal with
    | |- context[fun y => y] => pose (fun y : Set => y)
  end. (* Toplevel input, characters 0-78:
Error: Ltac variable y is not bound to an identifier.
It cannot be used in a binder. *)
        Variable pick_splits : forall (str : String) (pat : pattern CharType),
                                 { strs : list { str' : String | Length _ str' <= Length _ str }
                                 | fold_left (fun sp acc => proj1_sig (fst sp) ++ acc) (Empty _) (combine strs pat) = str
                                   /\
        admit. }
      { (** decide_leaf *)
        intros str ch.
        case_eq (str =s [[ch]]); intro H; [ apply bool_eq_correct in H; apply Some | exact None ].
        subst... }
      { (** fold_patterns *)
        intros str pats parses; induction parses; simpl in *...
        repeat match goal with H : option _ |- _ => destruct H end;
          try solve [ apply Some; auto with parse_tree nocore
                    | apply Some;
                      repeat match goal with
                               | _ => progress auto with parse_tree nocore
                               | [ H : parse_of _ _ _ _ |- _ ] => inversion H; clear H; subst
                             end
                    | match goal with
                        | [ H : parse_of _ _ _ _ |- _ ] => fail 1
                        | _ => idtac
                      end;
                      exact None ]. }
      { (** make_abort *)
        intros; exact None. }
    Defined.
        {
        apply Some.
        apply ParseHead.
        inversion p; subst.
        try solve [ apply Some.. ].

        auto with parse_tree nocore.
        .

        exact (fun str ch =>
                 if str =s [ [ ch ] ] as b return (

Print Universes.
        apply ParsePatternSingleton.
        constructor.
        assumption.
        eapply ParsePatternCons.
        Print parse_of_pattern.
      Print parse_of.

End recursive_descent_parser.

Section
*)


Module example_parse_empty_grammar.
  Definition make_parse_of : forall str nt, option (parse_of string_stringlike (trivial_grammar _) str nt).
  Proof.
    eapply parse_tree_no_split_for
    with (nonterminal_listT := rdp_list_nonterminal_listT)
           (is_valid_nonterminal := rdp_list_is_valid_nonterminal Ascii.ascii_dec)
           (remove_nonterminal := rdp_list_remove_nonterminal Ascii.ascii_dec)
           (nonterminal_listT_R := rdp_list_nonterminal_listT_R).
    { intros; exact [Lookup (trivial_grammar _) ""%string]. }
    { apply rdp_list_remove_nonterminal_dec. }
    { apply rdp_list_ntl_wf. }
  Defined.

  Definition parse : forall str : string,
                       option (parse_of string_stringlike (trivial_grammar _) str (trivial_grammar _))
    := fun str => make_parse_of str _.

  Eval hnf in if (parse "") then true else false.
  Eval hnf in if (parse "a") then true else false.

  Goal True.
    pose (parse "") as X.
    hnf in X; simpl in X.
    pose (parse "a") as Y.
    hnf in Y; simpl in Y.
  Abort.
End example_parse_empty_grammar.
