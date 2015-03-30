(** * Properties about Context Free Grammars *)
Require Import ADTSynthesis.Parsers.StringLike ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import Coq.Classes.RelationClasses.
Require Import ADTSynthesis.Common.

Set Implicit Arguments.

Local Open Scope list_scope.

Section cfg.
  Context {string} `{HSL : StringLike string} `{HSLP : @StringLikeProperties string HSL} (G : grammar string).

  Fixpoint parse_of_respectful (str1 str2 : String) (H : str1 =s str2) (pats : productions string) (p : parse_of G str1 pats) : parse_of G str2 pats
    := match p in (parse_of _ _ pats) return parse_of G str2 pats with
         | ParseHead pat pats p' => ParseHead pats (parse_of_production_respectful H p')
         | ParseTail pat pats p' => ParseTail pat (parse_of_respectful H p')
       end
  with parse_of_production_respectful (str1 str2 : String) (H : str1 =s str2) (pat : production string) (p : parse_of_production G str1 pat) : parse_of_production G str2 pat
       := match p in (parse_of_production _ _ pat) return parse_of_production G str2 pat with
            | ParseProductionNil pf => ParseProductionNil G str2 (transitivity (eq_sym (length_Proper H)) pf)
            | ParseProductionCons n pat pats p0 p1 => ParseProductionCons _ n (parse_of_item_respectful (take_Proper eq_refl H) p0) (parse_of_production_respectful (drop_Proper eq_refl H) p1)
          end
  with parse_of_item_respectful (str1 str2 : String) (H : str1 =s str2) (it : item string) (p : parse_of_item G str1 it) : parse_of_item G str2 it
       := match p in (parse_of_item _ _ it) return parse_of_item G str2 it with
            | ParseTerminal ch pf => ParseTerminal G str2 ch (transitivity (eq_sym (is_char_Proper H eq_refl)) pf)
            | ParseNonTerminal nt p' => ParseNonTerminal _ (parse_of_respectful H p')
          end.

  (*Global Instance parse_of_Proper : Proper (beq ==> eq ==> iff) (parse_of G).
  Proof.
    split; subst; apply parse_of_respectful; [ assumption | symmetry; assumption ].
  Qed.

  Global Instance parse_of_production_Proper : Proper (beq ==> eq ==> iff) (parse_of_production G).
  Proof.
    split; subst; apply parse_of_production_respectful; [ assumption | symmetry; assumption ].
  Qed.

  Global Instance parse_of_item_Proper : Proper (beq ==> eq ==> iff) (parse_of_item G).
  Proof.
    split; subst; apply parse_of_item_respectful; [ assumption | symmetry; assumption ].
  Qed.*)

  Definition ParseProductionSingleton str it (p : parse_of_item G str it) : parse_of_production G str [ it ].
  Proof.
    econstructor.
    { eapply parse_of_item_respectful; [ | eassumption ].
      rewrite take_long; reflexivity. }
    { constructor.
      rewrite drop_length; auto with arith. }
  Defined.

  (*Definition ParseProductionApp str1 str2 p1 p2 (pop1 : parse_of_production str1 p1) (pop2 : parse_of_production str2 p2)
  : parse_of_production (str1 ++ str2) (p1 ++ p2)%list.
  Proof.
    induction pop1; simpl.
    { rewrite LeftId; assumption. }
    { rewrite Associativity.
      constructor; assumption. }
  Defined.

    Definition ParseApp str1 str2 p1 p2 (po1 : parse_of str1 [ p1 ]) (po2 : parse_of str2 [ p2 ])
    : parse_of (str1 ++ str2) [ (p1 ++ p2)%list ].
    Proof.
      inversion_clear po1; inversion_clear po2;
      try match goal with
            | [ H : parse_of _ [] |- _ ] => exfalso; revert H; clear; intro H; abstract inversion H
          end.
      { constructor. apply ParseProductionApp; assumption. }
    Defined.*)

  Section definitions.
    Context (P : String -> String.string -> Type).

    Definition Forall_parse_of_item'
               (Forall_parse_of : forall {str pats} (p : parse_of G str pats), Type)
               {str it} (p : parse_of_item G str it)
      := match p return Type with
           | ParseTerminal ch pf => unit
           | ParseNonTerminal nt p'
             => (P str nt * Forall_parse_of p')%type
         end.

    Fixpoint Forall_parse_of {str pats} (p : parse_of G str pats)
      := match p with
           | ParseHead pat pats p'
             => Forall_parse_of_production p'
           | ParseTail _ _ p'
             => Forall_parse_of p'
         end
    with Forall_parse_of_production {str pat} (p : parse_of_production G str pat)
         := match p return Type with
              | ParseProductionNil pf => unit
              | ParseProductionCons pat strs pats p' p''
                => (Forall_parse_of_item' (@Forall_parse_of) p' * Forall_parse_of_production p'')%type
            end.

    Definition Forall_parse_of_item {str it} (p : parse_of_item G str it)
      := @Forall_parse_of_item' (@Forall_parse_of) str it p.
  End definitions.

  Section expand.
    Context {P P' : String -> String.string -> Type}.

    Definition expand_forall_parse_of_item'
               {str}
               {Forall_parse_of : forall P {str pats} (p : parse_of G str pats), Type}
               (expand : forall {pats p}, @Forall_parse_of P str pats p -> @Forall_parse_of P' str pats p)
               (f : forall n, P str n -> P' str n)
               {it p}
    : @Forall_parse_of_item' P (@Forall_parse_of P) str it p
      -> @Forall_parse_of_item' P' (@Forall_parse_of P') str it p.
    Proof.
      destruct p; simpl.
      { exact (fun x => x). }
      { intro ab.
        exact (f _ (fst ab), expand _ _ (snd ab)). }
    Defined.

    Global Arguments expand_forall_parse_of_item' : simpl never.

    Fixpoint expand_forall_parse_of
             str
             (f : forall str', str' ≤s str -> forall n, P str' n -> P' str' n)
             pats (p : parse_of G str pats)
             {struct p}
    : Forall_parse_of P p -> Forall_parse_of P' p
    with expand_forall_parse_of_production
           str
           (f : forall str', str' ≤s str -> forall n, P str' n -> P' str' n)
           pat (p : parse_of_production G str pat)
           {struct p}
         : Forall_parse_of_production P p -> Forall_parse_of_production P' p.
    Proof.
      { exact (match p in parse_of _ _ pats'
                     return (forall str'', str'' ≤s str -> forall n, P str'' n -> P' str'' n)
                            -> Forall_parse_of P p -> Forall_parse_of P' p
               with
                 | ParseHead _ _ p'
                   => fun f' => @expand_forall_parse_of_production _ f' _ p'
                 | ParseTail _ _ p'
                   => fun f' => @expand_forall_parse_of _ f' _ p'
               end f). }
      { refine (match p in parse_of_production _ _ pats'
                      return (forall str'', str'' ≤s str -> forall n, P str'' n -> P' str'' n)
                             -> Forall_parse_of_production P p -> Forall_parse_of_production P' p
                with
                  | ParseProductionNil pf => fun _ x => x
                  | ParseProductionCons pat strs' pats p' p''
                    => fun f' ab
                       => (_ : Forall_parse_of_item' _ (@Forall_parse_of _) _,
                           expand_forall_parse_of_production
                             _
                             (fun str'' pf'' => f' str'' (transitivity pf'' str_le_drop))
                             _ _
                             (snd ab))
                end f).
        destruct p'; simpl.
        { exact tt. }
        { refine (f' _ str_le_take _ (fst (fst ab)),
                  expand_forall_parse_of _ _ _ _ (snd (fst ab))).
          intros ??; apply f'.
          etransitivity; [ eassumption | exact str_le_take ]. } }
    Defined.

    Global Arguments expand_forall_parse_of : simpl never.
    Global Arguments expand_forall_parse_of_production : simpl never.

    Definition expand_forall_parse_of_item {str} f {it} {p : parse_of_item G str it}
      := @expand_forall_parse_of_item' str _ (@expand_forall_parse_of str f) (f _ (reflexivity _)) it p.

    Global Arguments expand_forall_parse_of_item : simpl never.
  End expand.
End cfg.
