(** * Properties about Context Free Grammars *)
Require Import Parsers.StringLike Parsers.ContextFreeGrammar.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.

Delimit Scope string_like_scope with string_like.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType).

  Section definitions.
    Context (P : String -> String.string -> Type).

    Definition Forall_parse_of_item'
               (Forall_parse_of : forall {str pats} (p : parse_of String G str pats), Type)
               {str it} (p : parse_of_item String G str it)
      := match p return Type with
           | ParseTerminal x => unit
           | ParseNonTerminal name str p'
             => (P str name * Forall_parse_of p')%type
         end.

    Fixpoint Forall_parse_of {str pats} (p : parse_of String G str pats)
      := match p with
           | ParseHead str pat pats p'
             => Forall_parse_of_production p'
           | ParseTail _ _ _ p'
             => Forall_parse_of p'
         end
    with Forall_parse_of_production {str pat} (p : parse_of_production String G str pat)
         := match p return Type with
              | ParseProductionNil => unit
              | ParseProductionCons str pat strs pats p' p''
                => (Forall_parse_of_item' (@Forall_parse_of) p' * Forall_parse_of_production p'')%type
            end.

    Definition Forall_parse_of_item {str it} (p : parse_of_item String G str it)
      := @Forall_parse_of_item' (@Forall_parse_of) str it p.
  End definitions.

  Section expand.
    Context {P P' : String -> String.string -> Type}.

    Definition expand_forall_parse_of_item'
               {str}
               {Forall_parse_of : forall P {str pats} (p : parse_of String G str pats), Type}
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
             pats (p : parse_of String G str pats)
             {struct p}
    : Forall_parse_of P p -> Forall_parse_of P' p
    with expand_forall_parse_of_production
           str
           (f : forall str', str' ≤s str -> forall n, P str' n -> P' str' n)
           pat (p : parse_of_production String G str pat)
           {struct p}
         : Forall_parse_of_production P p -> Forall_parse_of_production P' p.
    Proof.
      { exact (match p in parse_of _ _ str' pats'
                     return (forall str'', str'' ≤s str' -> forall n, P str'' n -> P' str'' n)
                            -> Forall_parse_of P p -> Forall_parse_of P' p
               with
                 | ParseHead _ _ _ p'
                   => fun f' => @expand_forall_parse_of_production _ f' _ p'
                 | ParseTail _ _ _ p'
                   => fun f' => @expand_forall_parse_of _ f' _ p'
               end f). }
      { refine (match p in parse_of_production _ _ str' pats'
                      return (forall str'', str'' ≤s str' -> forall n, P str'' n -> P' str'' n)
                             -> Forall_parse_of_production P p -> Forall_parse_of_production P' p
                with
                  | ParseProductionNil => fun _ x => x
                  | ParseProductionCons str' pat strs' pats p' p''
                    => fun f' ab
                       => (_ : Forall_parse_of_item' _ (@Forall_parse_of _) _,
                           expand_forall_parse_of_production
                             _
                             (fun str'' pf'' => f' str'' (transitivity pf'' (str_le2_append _ _ _)))
                             _ _
                             (snd ab))
                end f).
        destruct p'; simpl.
        { exact tt. }
        { refine (f' _ (str_le1_append _ _ _) _ (fst (fst ab)),
                  expand_forall_parse_of _ _ _ _ (snd (fst ab))).
          intros ??; apply f'.
          etransitivity; [ eassumption | exact (str_le1_append _ _ _) ]. } }
    Defined.

    Global Arguments expand_forall_parse_of : simpl never.
    Global Arguments expand_forall_parse_of_production : simpl never.

    Definition expand_forall_parse_of_item {str} f {it} {p : parse_of_item String G str it}
      := @expand_forall_parse_of_item' str _ (@expand_forall_parse_of str f) (f _ (reflexivity _)) it p.

    Global Arguments expand_forall_parse_of_item : simpl never.
  End expand.
End cfg.
