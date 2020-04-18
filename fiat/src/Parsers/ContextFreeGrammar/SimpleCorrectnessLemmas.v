(** * Lemmas about what it means for a simple_parse_of to be correct *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.

Section correctness.
  Context {Char} {HSLM} {HSL : @StringLike Char HSLM}.
  Context (G : grammar Char).

  Fixpoint simple_parse_of_correct_correct_1 {str pats}
           (p : parse_of G str pats)
    : exists p, simple_parse_of_correct G str pats p
  with simple_parse_of_production_correct_correct_1 {str pat}
           (p : parse_of_production G str pat)
    : exists p, simple_parse_of_production_correct G str pat p
  with simple_parse_of_item_correct_correct_1 {str it}
           (p : parse_of_item G str it)
    : exists p, simple_parse_of_item_correct G str it p.
  Proof.
    { refine match p with
             | ParseHead _ _ p' => _
             | ParseTail _ _ p' => _
             end;
      [ apply simple_parse_of_production_correct_correct_1 in p'
      | apply simple_parse_of_correct_correct_1 in p' ];
      destruct p' as [p' H];
      [ (exists (SimpleParseHead p'))
      | (exists (SimpleParseTail p')) ];
      simpl_simple_parse_of_correct;
      exact H. }
    { refine match p with
             | ParseProductionNil _ => _
             | ParseProductionCons n _ _ p'0 p'1 => _
             end;
      [ (exists SimpleParseProductionNil)
      | apply simple_parse_of_item_correct_correct_1 in p'0;
        apply simple_parse_of_production_correct_correct_1 in p'1;
        destruct p'0 as [p'0 H0], p'1 as [p'1 H1];
        exists (SimpleParseProductionCons p'0 p'1) ];
      simpl_simple_parse_of_correct;
      eauto. }
    { refine match p with
             | ParseTerminal ch _ _ _ => _
             | ParseNonTerminal nt _ p' => _
             end;
      [ (exists (SimpleParseTerminal ch))
      | apply simple_parse_of_correct_correct_1 in p';
        destruct p' as [p' H];
        (exists (SimpleParseNonTerminal nt p')) ];
      simpl_simple_parse_of_correct;
      [ apply Bool.andb_true_iff
      | ];
      auto. }
  Defined.

  Fixpoint simple_parse_of_correct_correct_2
           {str pats}
           p
    : simple_parse_of_correct G str pats p -> inhabited (parse_of G str pats)
  with simple_parse_of_production_correct_correct_2
         {str pat}
         p
       : simple_parse_of_production_correct G str pat p -> inhabited (parse_of_production G str pat)
  with simple_parse_of_item_correct_correct_2
         {str it}
         p
       : simple_parse_of_item_correct G str it p -> inhabited (parse_of_item G str it).
  Proof.
    { refine match p with
             | SimpleParseHead p' => _
             | SimpleParseTail p' => _
             end;
      (destruct pats as [|pat' pats']; [ intros [] | ]);
      simpl_simple_parse_of_correct;
      intro H;
      [ apply simple_parse_of_production_correct_correct_2 in H
      | apply simple_parse_of_correct_correct_2 in H ];
      destruct H as [H]; constructor;
      [ left; exact H
      | right; exact H ]. }
    { refine match p with
             | SimpleParseProductionNil => _
             | SimpleParseProductionCons p'0 p'1 => _
             end;
      simpl_simple_parse_of_correct;
      intro H.
      { destruct H as [H0 H1], pat.
        { do 2 constructor; assumption. }
        { exfalso; simpl in H1; clear -H1; abstract congruence. } }
      { destruct pat.
        { destruct H. }
        { destruct H as [n [H0 H1]].
          apply simple_parse_of_item_correct_correct_2 in H0.
          apply simple_parse_of_production_correct_correct_2 in H1.
          destruct H0 as [H0], H1 as [H1].
          do 2 econstructor; eassumption. } } }
    { refine match p with
             | SimpleParseTerminal ch => _
             | SimpleParseNonTerminal nt p' => _
             end;
      simpl_simple_parse_of_correct;
      destruct it; try solve [ intros [] ].
      { intro H.
        apply Bool.andb_true_iff in H; destruct H.
        do 2 econstructor; eassumption. }
      { intros (H0 & H1 & H2).
        apply simple_parse_of_correct_correct_2 in H2.
        destruct H2 as [H2].
        do 2 econstructor.
        { subst; assumption. }
        { subst; assumption. } } }
  Defined.

  Lemma simple_parse_of_correct_correct (str : String) (pats : productions Char)
    : inhabited (parse_of G str pats) <-> exists p, simple_parse_of_correct G str pats p.
  Proof.
    split.
    { intros [p]; apply simple_parse_of_correct_correct_1; assumption. }
    { intros [p H]; eapply simple_parse_of_correct_correct_2; eassumption. }
  Qed.

  Lemma simple_parse_of_production_correct_correct (str : String) (pat : production Char)
    : inhabited (parse_of_production G str pat) <-> exists p, simple_parse_of_production_correct G str pat p.
  Proof.
    split.
    { intros [p]; apply simple_parse_of_production_correct_correct_1; assumption. }
    { intros [p H]; eapply simple_parse_of_production_correct_correct_2; eassumption. }
  Qed.

  Lemma simple_parse_of_item_correct_correct (str : String) (it : item Char)
    : inhabited (parse_of_item G str it) <-> exists p, simple_parse_of_item_correct G str it p.
  Proof.
    split.
    { intros [p]; apply simple_parse_of_item_correct_correct_1; assumption. }
    { intros [p H]; eapply simple_parse_of_item_correct_correct_2; eassumption. }
  Qed.
End correctness.
