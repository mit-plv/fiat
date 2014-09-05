(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Common ADTNotation.ilist.

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
End wf.

Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (T : String -> nonterminal CharType -> Type)
          (T_reverse_lookup : forall str name, T str (Lookup G name) -> T str [ [ NonTerminal _ name ] ]).
  Context (parse_pattern_by_picking
           : forall (parse_pattern_from_split_list
                     : forall (strs : list String)
                              (pat : pattern CharType),
                         ilist (fun sp => T (fst sp) [ [ snd sp ] ]) (combine strs pat))
                    (str : String)
                    (pat : pattern CharType),
               T str [ pat ]).
  Context (decide_leaf : forall str ch, T str [ [ Terminal ch ] ]).
  Context (fold_patterns : forall str (pats : list (pattern CharType)),
                             ilist (fun pat => T str [ pat ]) pats
                             -> T str pats).
  (** FIXME: The type of the list of nonterminals should be able to
  depend on the string we're parsing, so we can store proofs in it to
  pass down the parse tree to handle impossible cases.  This will
  require a [Total] lexicographic ordering on strings. *)
  Context nonterminal_listT
          (initial_nonterminal_data : nonterminal_listT)
          (is_valid_nonterminal : nonterminal_listT -> nonterminal CharType -> bool)
          (remove_nonterminal : nonterminal_listT -> nonterminal CharType -> nonterminal_listT)
          (nonterminal_listT_R : nonterminal_listT -> nonterminal_listT -> Prop)
          (remove_nonterminal_dec : forall ls nt, is_valid_nonterminal ls nt = true
                                                  -> nonterminal_listT_R (remove_nonterminal ls nt) ls)
          (ntl_wf : well_founded nonterminal_listT_R).
  Context (make_abort : forall str nt valid_list, is_valid_nonterminal valid_list nt = false -> T str nt).


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
      Variable parse_nonterminal : forall str nt, T str nt.

      Definition parse_pattern_from_split_list
                 (strs : list String)
                 (pat : pattern CharType)
      : ilist (fun sp => T (fst sp) [ [ snd sp ] ]) (combine strs pat)
        := imap_list (fun sp => T (fst sp) [ [ snd sp ] ])
                     (fun sp => parse_item (parse_nonterminal (fst sp)) (snd sp))
                     (combine strs pat).

      Definition parse_pattern (str : String) (pat : pattern CharType) : T str [ pat ]
        := parse_pattern_by_picking parse_pattern_from_split_list str pat.
    End pattern.

    Section nonterminal.
      Section step.
        Variable parse_nonterminal : forall str nt, T str nt.

        Definition parse_nonterminal_step (str : String) (nt : nonterminal CharType) : T str nt
          := fold_patterns (imap_list (fun pat => T str [ pat ])
                                      (parse_pattern parse_nonterminal str)
                                      nt).
      End step.

      Section wf.
        Definition parse_nonterminal_or_abort (valid_list : nonterminal_listT) (max_len : nat)
                   (str : String)
                   (pf : Length _ str <= max_len)
                   (nt : nonterminal CharType)
        : T str nt.
        Proof.
          revert str pf nt.
          change max_len with (fst (max_len, valid_list)).
          generalize (max_len, valid_list); clear max_len valid_list.
          refine (@Fix (nat * nonterminal_listT) _ (well_founded_prod_relation
                                                      lt_wf
                                                      ntl_wf)
                       _ _).
          intros [max_len valid_list] parse_nonterminal str pf nt.
          apply le_lt_eq_dec in pf; simpl in *.
          destruct pf as [pf|pf].
          { (** [str] got smaller, so we reset the valid nonterminals *)
            destruct max_len as [|max_len]; [ solve [ destruct (Lt.lt_n_0 _ pf) ] | ].
            exact (parse_nonterminal
                     (max_len, initial_nonterminal_data)
                     (or_introl (Lt.lt_n_Sn _))
                     str
                     (le_S_n _ _ pf)
                     nt). }
          { (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
            case_eq (is_valid_nonterminal valid_list nt).
            { (** It was valid, so we can remove it *)
              intro H.
              exact (parse_nonterminal
                       (Length _ str, remove_nonterminal valid_list nt)
                       (or_intror (conj (eq_sym pf) (remove_nonterminal_dec H)))
                       str
                       (reflexivity _)
                       nt). }
            { (** oops, we already saw this nonterminal in the past.  ABORT! *)
              apply make_abort. } }
        Defined.
