(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf.
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
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (T : String -> nonterminal CharType -> Type)
          (aggregate : forall s1 pat, T s1 [ [ pat ] ] -> forall s2 pats, T s2 [pats] -> T (s1 ++ s2)%string_like [pat::pats]%list)
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
  Context (make_empty : T (Empty _) [ [ ] ]).
  Context (fold_patterns : forall str (pats : list (pattern CharType)),
                             ilist (fun pat => T str [ pat ]) pats
                             -> T str pats).

  Section parts.
    Local Ltac t' :=
      idtac;
      match goal with
        | _ => progress subst
        | _ => exact id
        | _ => assumption
        | [ H : ?x <> ?x |- _ ] => solve [ destruct (H eq_refl) ]
        | [ H : parse_of_item _ _ _ _ |- _ ] => inversion H; clear H
        | [ H : parse_of_pattern _ _ _ _ |- _ ] => inversion H; clear H
        | [ H : _ -> False |- False ] => apply H; clear H; solve [ repeat t' ]
      end.

    Class by_t' T := make_by_t' : T.
    Hint Extern 0 (by_t' _) => unfold by_t'; solve [ repeat t' ] : typeclass_instances.

    Local Ltac t :=
      repeat match goal with
               | [ |- False ] => clear abstract by_t' || fail 1
               | _ => progress t'
             end.


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
        Check Fix.
        SearchAbout well_founded.
    End nonterminal
                                        Proof.
        refine (match nt with
                  | nil => make_false str
                  | pat::pats => _
                end).
      Definition parse_nonterminal str nt : T str nt
        := reverse_nonterminal_permutation (parse_nonterminal_helper str (choose_nonterminal_order str nt)).
    End nonterminal.
