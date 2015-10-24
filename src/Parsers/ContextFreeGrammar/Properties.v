(** * Properties about Context Free Grammars *)
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.StringLike.Core Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Coq.Classes.RelationClasses.
Require Import Fiat.Common Fiat.Common.UIP.

Set Implicit Arguments.

Local Open Scope list_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {HSLP : @StringLikeProperties Char HSL} (G : grammar Char).

  Definition parse_of_item_respectful'
             (parse_of_respectful : forall {str1 str2} (H : str1 =s str2) {pats} (p : parse_of G str1 pats), parse_of G str2 pats)
             {str1 str2} (H : str1 =s str2) {it} (p : parse_of_item G str1 it)
  : parse_of_item G str2 it
    := match p in (parse_of_item _ _ it) return parse_of_item G str2 it with
         | ParseTerminal ch pf => ParseTerminal G str2 ch (transitivity (eq_sym (is_char_Proper H eq_refl)) pf)
         | ParseNonTerminal nt p' => ParseNonTerminal _ (parse_of_respectful H p')
          end.

  Fixpoint parse_of_respectful {str1 str2} (H : str1 =s str2) {pats} (p : parse_of G str1 pats) : parse_of G str2 pats
    := match p in (parse_of _ _ pats) return parse_of G str2 pats with
         | ParseHead pat pats p' => ParseHead pats (parse_of_production_respectful H p')
         | ParseTail pat pats p' => ParseTail pat (parse_of_respectful H p')
       end
  with parse_of_production_respectful {str1 str2} (H : str1 =s str2) {pat} (p : parse_of_production G str1 pat) : parse_of_production G str2 pat
       := match p in (parse_of_production _ _ pat) return parse_of_production G str2 pat with
            | ParseProductionNil pf => ParseProductionNil G str2 (transitivity (eq_sym (length_Proper H)) pf)
            | ParseProductionCons n pat pats p0 p1 => ParseProductionCons _ n (parse_of_item_respectful' (@parse_of_respectful) (take_Proper eq_refl H) p0) (parse_of_production_respectful (drop_Proper eq_refl H) p1)
          end.

  Definition parse_of_item_respectful : forall {str1 str2} H {it} p, _
    := @parse_of_item_respectful' (@parse_of_respectful).

  Fixpoint parse_of_respectful_refl {str pf pats} (p : parse_of G str pats) : parse_of_respectful pf p = p
    := match p return parse_of_respectful pf p = p with
         | ParseHead pat pats p' => f_equal (ParseHead _) (parse_of_production_respectful_refl p')
         | ParseTail pat pats p' => f_equal (@ParseTail _ _ _ _ _ _) (parse_of_respectful_refl p')
       end
  with parse_of_production_respectful_refl {str pf pat} (p : parse_of_production G str pat) : parse_of_production_respectful pf p = p
       := match p return parse_of_production_respectful pf p = p with
            | ParseProductionNil pf => f_equal (ParseProductionNil _ _) (dec_eq_uip (Nat.eq_dec _) _ _)
            | ParseProductionCons n pat pats p0 p1
              => f_equal2 (@ParseProductionCons _ _ _ _ _ _ _)
                          (parse_of_item_respectful_refl p0)
                          (parse_of_production_respectful_refl p1)
          end
  with parse_of_item_respectful_refl {str pf it} (p : parse_of_item G str it) : parse_of_item_respectful pf p = p
       := match p return parse_of_item_respectful pf p = p with
            | ParseTerminal ch pf => f_equal (ParseTerminal _ _ _) (dec_eq_uip (Bool.bool_dec _) _ _)
            | ParseNonTerminal nt p' => f_equal (ParseNonTerminal _) (parse_of_respectful_refl p')
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
               {str str' str''}
               {Forall_parse_of : forall P {str pats} (p : parse_of G str pats), Type}
               (expand : forall {pats} (H : str =s str') (H' : str =s str'') {p}, @Forall_parse_of P str' pats (parse_of_respectful H p) -> @Forall_parse_of P' str'' pats (parse_of_respectful H' p))
               (f : forall n, P str' n -> P' str'' n)
               {it p} (H : str =s str') (H' : str =s str'')
    : @Forall_parse_of_item' P (@Forall_parse_of P) str' it (parse_of_item_respectful H p)
      -> @Forall_parse_of_item' P' (@Forall_parse_of P') str'' it (parse_of_item_respectful H' p).
    Proof.
      destruct p; simpl.
      { exact (fun x => x). }
      { intro ab.
        exact (f _ (fst ab), expand _ H H' _ (snd ab)). }
    Defined.

    Global Arguments expand_forall_parse_of_item' : simpl never.

    Fixpoint expand_forall_parse_of
             str str' str''
             (f : forall str0' str1', str0' ≤s str -> str0' =s str1' -> forall n, P str0' n -> P' str1' n)
             pats (H : str =s str') (H' : str =s str'') (p : parse_of G str pats)
             {struct p}
    : Forall_parse_of P (parse_of_respectful H p) -> Forall_parse_of P' (parse_of_respectful H' p)
    with expand_forall_parse_of_production
           str str' str''
           (f : forall str0' str1', str0' ≤s str -> str0' =s str1' -> forall n, P str0' n -> P' str1' n)
           pat (H : str =s str') (H' : str =s str'') (p : parse_of_production G str pat)
           {struct p}
         : Forall_parse_of_production P (parse_of_production_respectful H p) -> Forall_parse_of_production P' (parse_of_production_respectful H' p).
    Proof.
      { destruct p.
        simpl.
        { apply expand_forall_parse_of_production; exact f. }
        { refine (expand_forall_parse_of _ _ _ _ _ _ _ p); exact f. } }
      { destruct p as [ | n pat pats pit pits ]; simpl.
        { exact (fun x => x). }
        { pose proof (fun f' f'' => @expand_forall_parse_of_item' _ (take n str') (take n str'') (@Forall_parse_of) (@expand_forall_parse_of _ _ _ f') f'' _ pit) as expand_forall_parse_of_item.
          specialize (fun f' H H' => expand_forall_parse_of_production _ (drop n str') (drop n str'') f' _ H H' pits).
          clear expand_forall_parse_of.
          change (Forall_parse_of_item P (parse_of_item_respectful (take_Proper eq_refl H) pit) * Forall_parse_of_production P (parse_of_production_respectful (drop_Proper eq_refl H) pits)
                  -> Forall_parse_of_item P' (parse_of_item_respectful (take_Proper eq_refl H') pit) * Forall_parse_of_production P' (parse_of_production_respectful (drop_Proper eq_refl H') pits))%type.
          intro xy.
          split.
          { eapply expand_forall_parse_of_item; [ .. | exact (fst xy) ].
            { intros ? ? H''; apply f.
              rewrite str_le_take in H''; assumption. }
            { intro; apply f.
              { clear -H HSLP.
                rewrite str_le_take, H; reflexivity. }
              { rewrite <- H, <- H'; reflexivity. } } }
          { eapply expand_forall_parse_of_production; [ .. | exact (snd xy) ].
            intros ? ? H''; apply f.
            etransitivity; [ eassumption | apply str_le_drop ]. } } }
    Defined.

    Global Arguments expand_forall_parse_of : simpl never.
    Global Arguments expand_forall_parse_of_production : simpl never.

    Definition expand_forall_parse_of_item {str str' str''} f {it} {p : parse_of_item G str it} (H : str =s str') (H' : str =s str'')
      := @expand_forall_parse_of_item' str str' str'' _ (@expand_forall_parse_of str str' str'' f) (f _ _ ((_ : Proper (beq ==> beq ==> impl) str_le) _ _ H _ _ (reflexivity _) (reflexivity _)) (transitivity (symmetry H) H')) it p.

    Global Arguments expand_forall_parse_of_item : simpl never.
  End expand.
End cfg.
