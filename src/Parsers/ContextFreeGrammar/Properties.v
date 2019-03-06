(** * Properties about Context Free Grammars *)
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Common Fiat.Common.UIP.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.

Set Implicit Arguments.

Local Open Scope list_scope.

Global Instance item_rect_Proper {Char T}
: Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq ==> eq)
         (@item_rect Char (fun _ => T)).
Proof.
  lazy.
  intros ?? H ?? H' ? [?|?] ?; subst; eauto with nocore.
Qed.
Global Instance item_rect_Proper_forall {Char T}
: Proper (forall_relation (fun _ => eq) ==> forall_relation (fun _ => eq) ==> forall_relation (fun _ => eq))
         (@item_rect Char T).
Proof.
  lazy.
  intros ?? H ?? H' [?|?]; subst; eauto with nocore.
Qed.

Global Instance item_rect_Proper_forall_R {C A} {R : relation A}
  : Proper
      ((pointwise_relation _ R)
         ==> (pointwise_relation _ R)
         ==> forall_relation (fun _ : item C => R))
      (item_rect (fun _ : item C => A)).
Proof.
  lazy; intros ?????? [?|?]; trivial.
Qed.

Hint Extern 1 (Proper _ (@item_rect _ _)) => exact item_rect_Proper : typeclass_instances.
Hint Extern 0 (Proper _ (@item_rect _ _)) => exact item_rect_Proper_forall : typeclass_instances.
Hint Extern 0 (Proper (pointwise_relation _ _ ==> pointwise_relation _ _ ==> forall_relation _) (item_rect _))
=> refine item_rect_Proper_forall_R : typeclass_instances.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} (G : grammar Char).

  Definition parse_of_item_respectful'
             (parse_of_respectful : forall {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats), parse_of G str2 pats')
             {str1 str2} (H : str1 =s str2) {it it'} (Hit : item_code it it') (p : parse_of_item G str1 it)
  : parse_of_item G str2 it'
    := match p in (parse_of_item _ _ it), it' return item_code it it' -> parse_of_item G str2 it' with
         | ParseTerminal ch P pf0 pf1, Terminal P' => fun Hit => ParseTerminal G str2 ch P' (transitivity (symmetry (Hit _)) pf0) (transitivity (eq_sym (is_char_Proper H eq_refl)) pf1)
         | ParseTerminal _ _ _ _, NonTerminal _ => fun Hit => match Hit with end
         | ParseNonTerminal nt H' p', NonTerminal nt'
           => fun Hit
              => ParseNonTerminal
                   _
                   (match Hit in (_ = nt') return List.In nt' _ with
                      | eq_refl => H'
                    end)
                   (@parse_of_respectful
                      _ _ H (Lookup G nt) (Lookup G nt')
                      (match Hit in (_ = nt') return productions_code (G nt) (G nt') with
                         | eq_refl => reflexivity _
                       end)
                      p')
         | ParseNonTerminal _ _ _, Terminal _ => fun Hit => match Hit with end
       end Hit.

  Global Arguments parse_of_item_respectful' _ _ _ _ _ !_ _ !_ / .

  Section bodies.
    Context (parse_of_respectful : forall {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats), parse_of G str2 pats')
            (parse_of_production_respectful : forall {str1 str2} (H : str1 =s str2) {pat pat'} (Hpat : production_code pat pat') (p : parse_of_production G str1 pat), parse_of_production G str2 pat').

    Definition parse_of_respectful_step {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats) : parse_of G str2 pats'.
    Proof.
      refine (match p in (parse_of _ _ pats), pats' return productions_code pats pats' -> parse_of G str2 pats' with
                | ParseHead pat pats p', pat'::pats' => fun Hpats' => ParseHead pats' (@parse_of_production_respectful _ _ H _ _ _ p')
                | ParseTail pat pats p', pat'::pats' => fun Hpats' => ParseTail pat' (@parse_of_respectful _ _ H _ _ _ p')
                | ParseHead _ _ _, nil => fun Hpats' => match _ : False with end
                | ParseTail _ _ _, nil => fun Hpats' => match _ : False with end
              end Hpats);
      try solve [ clear -Hpats'; abstract inversion Hpats'
                | clear -Hpats'; inversion Hpats'; subst; assumption ].
    Defined.

    Definition parse_of_production_respectful_step {str1 str2} (H : str1 =s str2) {pat pat'} (Hpat : production_code pat pat') (p : parse_of_production G str1 pat) : parse_of_production G str2 pat'.
    Proof.
      refine (match p in (parse_of_production _ _ pat), pat' return production_code pat pat' -> parse_of_production G str2 pat' with
                | ParseProductionNil pf, nil => fun Hpat' => ParseProductionNil G str2 (transitivity (eq_sym (length_Proper H)) pf)
                | ParseProductionCons n pat pats p0 p1, pat'::pats' => fun Hpat' => ParseProductionCons _ n (parse_of_item_respectful' (@parse_of_respectful) (take_Proper eq_refl H) _ p0) (@parse_of_production_respectful _ _ (drop_Proper eq_refl H) _ _ _ p1)
                | ParseProductionNil _, _::_ => fun Hpat' => match _ : False with end
                | ParseProductionCons _ _ _ _ _, nil => fun Hpat' => match _ : False with end
              end Hpat);
      try solve [ clear -Hpat'; abstract inversion Hpat'
                | clear -Hpat'; inversion Hpat'; subst; assumption ].
    Defined.

    Global Arguments parse_of_respectful_step _ _ _ _ _ _ !_ / .
    Global Arguments parse_of_production_respectful_step _ _ _ _ _ _ !_ / .
  End bodies.

  Fixpoint parse_of_respectful {str1 str2} (H : str1 =s str2) {pats pats'} (Hpats : productions_code pats pats') (p : parse_of G str1 pats) : parse_of G str2 pats'
    := @parse_of_respectful_step (@parse_of_respectful) (@parse_of_production_respectful) _ _ H _ _ Hpats p
  with parse_of_production_respectful {str1 str2} (H : str1 =s str2) {pat pat'} (Hpat : production_code pat pat') (p : parse_of_production G str1 pat) : parse_of_production G str2 pat'
    := @parse_of_production_respectful_step (@parse_of_respectful) (@parse_of_production_respectful) _ _ H _ _ Hpat p.

  Definition parse_of_item_respectful : forall {str1 str2} H {it it'} Hit p, _
    := @parse_of_item_respectful' (@parse_of_respectful).

  Global Arguments parse_of_item_respectful _ _ _ _ !_ _ !_ / .

  Fixpoint parse_of_respectful_refl {str pf pats Hpats} (p : parse_of G str pats) : parse_of_respectful pf Hpats p = p
    := match p return forall Hpats, parse_of_respectful pf Hpats p = p with
         | ParseHead pat pats p' => fun Hpats => f_equal (ParseHead _) (parse_of_production_respectful_refl p')
         | ParseTail pat pats p' => fun Hpats => f_equal (@ParseTail _ _ _ _ _ _ _) (parse_of_respectful_refl p')
       end Hpats
  with parse_of_production_respectful_refl {str pf pat Hpat} (p : parse_of_production G str pat) : parse_of_production_respectful pf Hpat p = p
       := match p return forall Hpat, parse_of_production_respectful pf Hpat p = p with
            | ParseProductionNil pf => fun Hpat => f_equal (ParseProductionNil _ _) (dec_eq_uip (Nat.eq_dec _) _ _)
            | ParseProductionCons n pat pats p0 p1
              => fun Hpat => f_equal2 (@ParseProductionCons _ _ _ _ _ _ _ _)
                                      (parse_of_item_respectful_refl p0)
                                      (parse_of_production_respectful_refl p1)
          end Hpat
  with parse_of_item_respectful_refl {str pf it Hit} (p : parse_of_item G str it) : parse_of_item_respectful pf Hit p = p
       := match p return forall Hit, parse_of_item_respectful pf Hit p = p with
            | ParseTerminal ch P pf1 pf2 => fun Hit => f_equal2 (ParseTerminal _ _ _ _) (dec_eq_uip (Bool.bool_dec _) _ _) (dec_eq_uip (Bool.bool_dec _) _ _)
            | ParseNonTerminal nt H' p'
              => fun Hit'
                 => f_equal2 (ParseNonTerminal nt)
                             match dec_eq_uip (@Equality.string_eq_dec nt) eq_refl Hit' in (_ = Hit') return match Hit' in (_ = nt') return List.In nt' _ with eq_refl => H' end = H' with
                               | eq_refl => eq_refl
                             end
                             (@parse_of_respectful_refl _ _ _ _ p')
          end Hit.

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
    { eapply parse_of_item_respectful; [ | reflexivity | eassumption ].
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
           | ParseTerminal ch P pf1 pf2 => unit
           | ParseNonTerminal nt H' p'
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

  (*Section expand.
    Context {P P' : String -> String.string -> Type}.

    Definition expand_forall_parse_of_item'
               {str str' str''}
               {Forall_parse_of : forall P {str pats} (p : parse_of G str pats), Type}
               (expand : forall {pats pats' pats''} (Hpats : productions_code pats pats') (Hpats' : productions_code pats' pats'') (H : str =s str') (H' : str =s str'') {p}, @Forall_parse_of P str' pats' (parse_of_respectful H Hpats p) -> @Forall_parse_of P' str'' pats'' (parse_of_respectful H' Hpats' p))
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
  End expand.*)
End cfg.

Ltac simpl_parse_of_respectful :=
  repeat match goal with
           | [ |- context[@parse_of_respectful ?Char ?HSLM ?HSL ?HSLP ?G ?str1 ?str2 ?H ?pat ?pat' ?Hpat ?p] ]
             => change (@parse_of_respectful Char HSLM HSL HSLP G str1 str2 H pat pat' Hpat p)
                with (@parse_of_respectful_step Char HSLM HSL G (@parse_of_respectful Char HSLM HSL HSLP G) (@parse_of_production_respectful Char HSLM HSL HSLP G) str1 str2 H pat pat' Hpat p);
               simpl @parse_of_respectful_step
           | [ |- context[@parse_of_production_respectful ?Char ?HSLM ?HSL ?HSLP ?G ?str1 ?str2 ?H ?pat ?pat' ?Hpat ?p] ]
             => change (@parse_of_production_respectful Char HSLM HSL HSLP G str1 str2 H pat pat' Hpat p)
                with (@parse_of_production_respectful_step Char HSLM HSL G (@parse_of_respectful Char HSLM HSL HSLP G) (@parse_of_production_respectful Char HSLM HSL HSLP G) str1 str2 H pat pat' Hpat p);
               simpl @parse_of_production_respectful_step
           | _ => progress simpl @parse_of_item_respectful
           | _ => progress simpl @parse_of_item_respectful'
         end.

Section parse_of_proper.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char} {str : String}.

  Local Ltac t_parse_of_impl lem :=
    repeat intro;
    match goal with
      | [ H : Proper _ _, H' : _ -> _ |- _ ] => eapply H; [ eassumption.. | apply H'; try clear H H' ]
    end;
    eapply lem; [ .. | eassumption ];
    try first [ assumption
              | reflexivity
              | symmetry; assumption ].

  Section fun0.
    Context {P : _ -> _ -> Prop}
            {H : Proper (@item_code Char ==> @production_code Char ==> impl) P}.

    Global Instance parse_of_item_fun0_Proper
    : Proper (item_code ==> production_code ==> impl) (fun it (its : production Char) => parse_of_item G str it -> P it its).
    Proof. t_parse_of_impl (@parse_of_item_respectful). Qed.
    Global Instance parse_of_production_fun0_Proper
    : Proper (item_code ==> production_code ==> impl) (fun (it : item Char) (its : production Char) => parse_of_production G str its -> P it its).
    Proof. t_parse_of_impl (@parse_of_production_respectful). Qed.
  End fun0.
  Section fun0_flip.
    Context {P : _ -> _ -> Prop}
            {H : Proper (@item_code Char ==> @production_code Char ==> flip impl) P}.

    Global Instance parse_of_item_fun0_Proper_flip
    : Proper (item_code ==> production_code ==> flip impl) (fun it (its : production Char) => parse_of_item G str it -> P it its).
    Proof. t_parse_of_impl (@parse_of_item_respectful). Qed.
    Global Instance parse_of_production_fun0_Proper_flip
    : Proper (item_code ==> production_code ==> flip impl) (fun (it : item Char) (its : production Char) => parse_of_production G str its -> P it its).
    Proof. t_parse_of_impl (@parse_of_production_respectful). Qed.
  End fun0_flip.

  Section fun1.
    Context {A} {RA : relation A}
            {P : _ -> _ -> _ -> Prop}
            {H : Proper (@item_code Char ==> @production_code Char ==> RA ==> impl) P}.

    Global Instance parse_of_item_fun1_Proper
    : Proper (item_code ==> production_code ==> RA ==> impl) (fun it (its : production Char) x => parse_of_item G str it -> P it its x).
    Proof. t_parse_of_impl (@parse_of_item_respectful). Qed.
    Global Instance parse_of_production_fun1_Proper
    : Proper (item_code ==> production_code ==> RA ==> impl) (fun (it : item Char) (its : production Char) x => parse_of_production G str its -> P it its x).
    Proof. t_parse_of_impl (@parse_of_production_respectful). Qed.
  End fun1.
  Section fun1_flip.
    Context {A} {RA : relation A}
            {P : _ -> _ -> _ -> Prop}
            {H : Proper (@item_code Char ==> @production_code Char ==> RA ==> flip impl) P}.

    Global Instance parse_of_item_fun1_Proper_flip
    : Proper (item_code ==> production_code ==> RA ==> flip impl) (fun it (its : production Char) x => parse_of_item G str it -> P it its x).
    Proof. t_parse_of_impl (@parse_of_item_respectful). Qed.
    Global Instance parse_of_production_fun1_Proper_flip
    : Proper (item_code ==> production_code ==> RA ==> flip impl) (fun (it : item Char) (its : production Char) x => parse_of_production G str its -> P it its x).
    Proof. t_parse_of_impl (@parse_of_production_respectful). Qed.
  End fun1_flip.
End parse_of_proper.
