(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarEquality.
Require Import Coq.Program.Equality.
Require Import ADTSynthesis.Common.
Require Import ADTSynthesis.Common.Equality.
Require Import ADTSynthesis.Common.Wf.
Require Import ADTSynthesis.Parsers.Splitters.RDPList.
Require Import ADTSynthesis.Parsers.Splitters.BruteForce.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.BaseTypes.
Require Import ADTSynthesis.Parsers.CorrectnessBaseTypes.
Require Import ADTSynthesis.Parsers.BooleanRecognizerFull.
Require Import ADTSynthesis.Parsers.BooleanRecognizerCorrect.
Require Import ADTSynthesis.Common.List.Operations.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Parsers.MinimalParseOfParse.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarProperties.

Set Implicit Arguments.

Section all_possible.
  Context {Char : Type}.
  Definition possible_terminals := list Char.

  Definition possible_terminals_of_production' (terminals_of_nt : String.string -> possible_terminals)
             (its : production Char)
  : possible_terminals
    := flat_map
         (fun it =>
            match it with
              | Terminal ch => [ch]
              | NonTerminal nt => terminals_of_nt nt
            end)
         its.

  Lemma possible_terminals_of_production'_ext
        f g
        (ext : forall b, f b = g b)
        b
  : @possible_terminals_of_production' f b = possible_terminals_of_production' g b.
  Proof.
    induction b as [ | x ]; try reflexivity; simpl.
    destruct x; rewrite ?IHb, ?ext; reflexivity.
  Qed.

  Definition possible_terminals_of_productions' (possible_terminals_of_nt : String.string -> possible_terminals)
             (prods : productions Char)
  : possible_terminals
    := flat_map
         (possible_terminals_of_production' possible_terminals_of_nt)
         prods.

  Lemma possible_terminals_of_productions'_ext
        f g
        (ext : forall b, f b = g b)
        b
  : @possible_terminals_of_productions' f b = possible_terminals_of_productions' g b.
  Proof.
    unfold possible_terminals_of_productions'.
    induction b as [ | x ]; try reflexivity; simpl.
    rewrite IHb.
    erewrite possible_terminals_of_production'_ext by eassumption.
    reflexivity.
  Qed.

  Definition possible_terminals_of_nt_step (G : grammar Char) (predata := @rdp_list_predata _ G)
             (valid0 : nonterminals_listT)
             (possible_terminals_of_nt : forall valid, nonterminals_listT_R valid valid0
                                                       -> String.string -> possible_terminals)
             (nt : String.string)
  : possible_terminals.
  Proof.
    refine (if Sumbool.sumbool_of_bool (is_valid_nonterminal valid0 nt)
            then possible_terminals_of_productions'
                   (@possible_terminals_of_nt (remove_nonterminal valid0 nt) (remove_nonterminal_dec _ _ _))
                   (Lookup G nt)
            else nil);
    assumption.
  Defined.

  Lemma possible_terminals_of_nt_step_ext {G}
        x0 f g
        (ext : forall y p b, f y p b = g y p b)
        b
  : @possible_terminals_of_nt_step G x0 f b = possible_terminals_of_nt_step g b.
  Proof.
    unfold possible_terminals_of_nt_step.
    edestruct Sumbool.sumbool_of_bool; trivial.
    apply possible_terminals_of_productions'_ext; eauto.
  Qed.

  Definition possible_terminals_of_nt (G : grammar Char) initial : String.string -> possible_terminals
    := let predata := @rdp_list_predata _ G in
       @Fix _ _ ntl_wf _
            (@possible_terminals_of_nt_step G)
            initial.

  Definition possible_terminals_of (G : grammar Char) : String.string -> possible_terminals
    := @possible_terminals_of_nt G initial_nonterminals_data.

  Definition possible_terminals_of_productions G := @possible_terminals_of_productions' (@possible_terminals_of G).
End all_possible.

Section only_first.
  Context (G : grammar Ascii.ascii).

  Record possible_first_terminals :=
    { actual_possible_first_terminals :> list Ascii.ascii;
      might_be_empty : bool }.

  Definition possible_first_terminals_of_production' (possible_first_terminals_of_nt : String.string -> possible_first_terminals)
             (its : production Ascii.ascii)
  : possible_first_terminals
    := {| actual_possible_first_terminals
          := fold_right
               (fun it rest_terminals =>
                  match it with
                    | Terminal ch => [ch]
                    | NonTerminal nt
                      => (possible_first_terminals_of_nt nt)
                           ++ if might_be_empty (possible_first_terminals_of_nt nt)
                              then rest_terminals
                              else []
                  end)
               nil
               its;
          might_be_empty
          := brute_force_parse_production G ""%string its |}.

  Lemma possible_first_terminals_of_production'_ext
        f g
        (ext : forall b, f b = g b)
        b
  : @possible_first_terminals_of_production' f b = possible_first_terminals_of_production' g b.
  Proof.
    unfold possible_first_terminals_of_production'; f_equal.
    induction b as [ | x ]; try reflexivity; simpl.
    destruct x; rewrite ?IHb, ?ext; reflexivity.
  Qed.

  Definition possible_first_terminals_of_productions' (possible_first_terminals_of_nt : String.string -> possible_first_terminals)
             (prods : productions Ascii.ascii)
  : possible_first_terminals
    := {| actual_possible_first_terminals
          := flat_map
               actual_possible_first_terminals
               (map (possible_first_terminals_of_production' possible_first_terminals_of_nt)
                    prods);
          might_be_empty
          := fold_right
               orb
               false
               (map
                  might_be_empty
                  (map
                     (possible_first_terminals_of_production' possible_first_terminals_of_nt)
                     prods)) |}.

  Local Opaque possible_first_terminals_of_production'.

  Lemma possible_first_terminals_of_productions'_ext
        f g
        (ext : forall b, f b = g b)
        b
  : @possible_first_terminals_of_productions' f b = possible_first_terminals_of_productions' g b.
  Proof.
    unfold possible_first_terminals_of_productions'.
    f_equal;
      induction b as [ | x ]; try reflexivity; simpl;
      rewrite IHb; try reflexivity;
      erewrite possible_first_terminals_of_production'_ext by eassumption;
      reflexivity.
  Qed.

  Local Transparent possible_first_terminals_of_production'.

  Definition possible_first_terminals_of_nt_step (predata := @rdp_list_predata _ G)
             (valid0 : nonterminals_listT)
             (possible_first_terminals_of_nt : forall valid, nonterminals_listT_R valid valid0
                                                       -> String.string -> possible_first_terminals)
             (nt : String.string)
  : possible_first_terminals.
  Proof.
    refine (if Sumbool.sumbool_of_bool (is_valid_nonterminal valid0 nt)
            then possible_first_terminals_of_productions'
                   (@possible_first_terminals_of_nt (remove_nonterminal valid0 nt) (remove_nonterminal_dec _ _ _))
                   (Lookup G nt)
            else {| actual_possible_first_terminals := nil;
                    might_be_empty
                    := brute_force_parse_nonterminal G ""%string nt |});
    assumption.
  Defined.

  Lemma possible_first_terminals_of_nt_step_ext
        x0 f g
        (ext : forall y p b, f y p b = g y p b)
        b
  : @possible_first_terminals_of_nt_step x0 f b = possible_first_terminals_of_nt_step g b.
  Proof.
    unfold possible_first_terminals_of_nt_step.
    edestruct Sumbool.sumbool_of_bool; trivial.
    apply possible_first_terminals_of_productions'_ext; eauto.
  Qed.

  Definition possible_first_terminals_of_nt initial : String.string -> possible_first_terminals
    := let predata := @rdp_list_predata _ G in
       @Fix _ _ ntl_wf _
            (@possible_first_terminals_of_nt_step)
            initial.

  Definition possible_first_terminals_of : String.string -> possible_first_terminals
    := @possible_first_terminals_of_nt initial_nonterminals_data.

  Definition possible_first_terminals_of_productions := @possible_first_terminals_of_productions' (@possible_first_terminals_of).

  Definition possible_first_terminals_of_production := @possible_first_terminals_of_production' (@possible_first_terminals_of).
End only_first.

Local Open Scope string_like_scope.

Local Arguments string_beq : simpl never.

Lemma terminals_disjoint_search_for_not {G : grammar Ascii.ascii} (str : @String Ascii.ascii string_stringlike)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
      (Hpit : Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) pit)
      (Hpits : Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) pits)
: (forall n' ch, n' < n
                        -> (take 1 (drop n' str)) ~= [ ch ]
                        -> list_bin ascii_beq ch (possible_terminals_of G nt))
  /\ ((length str <= n /\ might_be_empty (possible_first_terminals_of_production G its))
      \/ (forall ch, (take 1 (drop n str)) ~= [ ch ]
                     -> (negb (list_bin ascii_beq ch (possible_terminals_of G nt))))).
Proof.
  destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
  apply and_comm; split.
  { destruct (Compare_dec.le_dec (length str) n); [ left | right ].
    { split; trivial.
      pose proof (drop_length str n) as H.
      rewrite (proj2 (Nat.sub_0_le (length str) n)) in H by assumption.
      generalize dependent (drop n str); clear -Hpit HinV HinL.
      intros.
      destruct s; simpl in *; try discriminate; [].
      clear H.
      unfold possible_first_terminals_of_production, possible_first_terminals_of_production', brute_force_parse_production; simpl.
      intros.
      eapply parse_production_complete;
        [ ..
        | refine ((fun pf =>
                     projT1 (@alt_all_elim
                               _ _ G (@rdp_list_predata _ G) _ _ _
                               (@minimal_parse_of_production__of__parse_of_production
                                  _ _ _ G (@rdp_list_predata _ G) ""%string (S (WellFoundedParse.size_of_parse_production pits))
                                  (fun _ _ => @minimal_parse_of_nonterminal__of__parse_of_nonterminal _ _ _ _ _ _ _)
                                  ""%string
                                  (@reflexivity _ _ str_le_refl _)
                                  initial_nonterminals_data
                                  _ pits
                                  (Lt.lt_n_Sn _)
                                  (reflexivity _)
                                  pf))) _) ];
        eauto.
      { let p := match goal with p : parse_of_item _ _ _ |- _ => constr:p end in
        let H := fresh in
        rename p into H;
          dependent destruction H; []; simpl in *; destruct_head prod.
        unfold brute_force_parse_nonterminal.
        repeat intro.
        assert (str0 = ""%string)
          by (destruct_head_hnf or; subst; trivial; try omega;
              apply string_bl; assumption); subst.
        let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
        destruct (@parse_of_item_nonterminal__of__minimal_parse_of_nonterminal
                    _ _ G (@rdp_list_predata _ G) _ _ _ _ p)
          as [p' Hp'].
        dependent destruction p'.
        exact (@parse_nonterminal_complete
                 _ _ _ G _ (brute_force_cdata G) rdp_list_rdata'
                 _ _ _ Hp'). }
      { intros.
        refine (I : (fun _ _ _ => True) _ _ _). }
      { intros str0 valid str1 pf.
        eapply list_in_lb in HinV; [ | exact (@string_lb) ].
        pose proof (@split_string_for_production_complete
                      _ _  G _ (brute_force_cdata G)
                      str0 valid str1 pf nt' HinV) as X.
        induction (G nt'); simpl in *; destruct_head False; []; destruct_head prod.
        match goal with
          | [ H : ?a = ?b \/ ?H' |- _ ]
            => let n := fresh in
               destruct (@production_eq_dec' _ (@ascii_eq_dec) a b);
              [ clear H; subst
              | assert H' by intuition; clear H ]
        end.
        { match goal with
            | [ H : Forall_tails ?f (?ls ++ ?x::?xs)
                |- Forall_tails ?f ?xs ]
              => clear -H;
                revert H;
                change (Forall_tails f (ls ++ x::xs) -> Forall_tails f xs);
                generalize f;
                clear;
                intros ? H;
                induction ls; simpl in *; intuition
          end. }
        { intuition. } }
      { erewrite <- parse_of_production_respectful_refl.
        erewrite <- parse_of_production_respectful_refl in Hpits.
        revert Hpits.
        apply (@expand_forall_parse_of_production
                 _ _ _ G); simpl.
        intros ????? H'.
        apply list_in_lb; trivial; apply (@string_lb). } }
    { clear -pits Hpits H_disjoint.
      generalize dependent (drop n str).
      generalize dependent (possible_terminals_of G nt).
      intros terms H_disjoint str' pits Hpits ch H'.
      simpl in *.
      apply string_bl in H'.
      inversion H'; subst; clear -pits H_disjoint H' Hpits.
      apply Bool.negb_true_iff, Bool.not_true_iff_false.
      intro H.
      eapply list_in_bl in H; [ | exact (@ascii_bl) ].
      eapply disjoint_bl in H_disjoint; try eassumption; try exact (@ascii_lb); [].
      clear H_disjoint.
      generalize dependent str'.
      induction its; simpl.
      { intros ? p.
        dependent destruction p.
        destruct str'; simpl in *; congruence. }
      { intros str' pits Hpits H'.
        dependent destruction pits; simpl in *.
        edestruct (_ : item _);
          repeat match goal with
                   | [ H : Forall_parse_of_production ?f (ParseProductionCons _ _ ?p ?ps) |- _ ]
                     => change (Forall_parse_of_item f p * Forall_parse_of_production f ps)%type in H
                   | [ H : prod _ _ |- _ ] => destruct H
                   | [ H : parse_of_item _ _ (Terminal _) |- _ ]
                     => let H' := fresh in
                        rename H into H';
                          dependent destruction H'
                   | [ H : parse_of_item _ _ (NonTerminal _) |- _ ]
                     => let H' := fresh in
                        rename H into H';
                          dependent destruction H'
                   | _ => progress simpl in *
                   | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
                   | [ |- _ \/ False ] => left
                 end.
        { destruct str' as [| ? str' ]; simpl in *; try congruence; [].
          repeat match goal with
                   | [ H : context[match ?e with _ => _ end] |- _ ] => atomic e; destruct e
                   | _ => progress simpl in *
                   | _ => congruence
                   | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
                 end. }
        { apply in_or_app.
          let n := match type of pits with parse_of_production _ (substring ?n _ _) _ => constr:n end in
          destruct n.
          { repeat match goal with H : _ |- _ => generalize dependent H; rewrite substring_correct0; intros end.
            right.
            match goal with
              | [ |- context[might_be_empty ?e] ]
                => destruct (might_be_empty e) eqn:?
            end.
            { eapply IHits; [ eassumption | ].
              rewrite substring_correct3'; trivial. }
            {
              lazymatch goal with
                | [ H : parse_of ?G ""%string (Lookup ?G ?s), H' : might_be_empty (possible_first_terminals_of ?G ?s) = false, H'' : In ?s (Valid_nonterminals ?G) |- _ ]
                  => exfalso; clear -s H H' H''; revert s H H' H''
              end.
              intros s p H H'.
              unfold possible_first_terminals_of in *.
              unfold possible_first_terminals_of_nt in *.
              rewrite Fix1_eq in H by apply possible_first_terminals_of_nt_step_ext.
              simpl in *.
              unfold possible_first_terminals_of_nt_step in *.
              simpl in *.
              edestruct dec;
                [
                | eapply list_in_lb in H'; [ | exact (@string_lb) ];
                  unfold rdp_list_is_valid_nonterminal in *; congruence ].
              simpl in *.
              clear -p H.
              induction (G s) as [ | x xs IHGs ]; simpl in *.
              { dependent destruction p. }
              { apply Bool.orb_false_iff in H.
                destruct H as [H ?].
                dependent destruction p.

              Focus 2.

              SearchAbout (substring 0).
            eauto.

            unfold possible_first_terminals_of at 1; simpl.
            unfold possible_first_terminals_of_nt; simpl.
            unfold possible_first_terminals_of_nt_step; simpl.
            destruct (Valid_nonterminals G); simpl.
          SearchAbout (substring _ 0).
          { right; eauto.
            eapply IHits.
            eassumption.

          edestruct might_be_empty.
          {
SearchAbout (In _ (_ ++ _)).
          simpl in *.


      dependent destruction pits; simpl.
      SearchAbout true false.
      dependent destruction
      rewrite substring_substring in H'; simpl in H'.

induction prefix; simpl in *; destruct_head prod; eauto.
        simpl in *.
        intros str0 valid str1 pf0.
        specialize (pf str0 valid str1 pf0).
        induction (Valid_nonterminals G); simpl in *.
        { exfalso; destruct_head ex; intuition. }
        {

).




          try eassumption; []; simpl.
        apply and_assoc; split; [ | reflexivity ].
        split.
        { let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
          destruct p; assumption. }
        { destruct X.
          destruct m.
        let p :=


        hnf; intros; simpl in *.
                     pose proof (@parse_nonterminal_complete
                                   _ _ _ G _ (brute_force_cdata G) rdp_list_rdata').
        s
 (@rdp_list_predata _ G)).
        apply parse_nonterminal_complete; try eassumption.
        { apply brute_force_cdata. }
        { apply rdp_list_rdata'. }
        { simpl.
          split.
          { let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
            destruct p; assumption. }
          {

rewrite <- (parse_of_respectful_refl (pf := reflexivity _)).
lazymatch goal with
               | [ H : Forall_parse_of _ ?x |- _ ]
                 => atomic x; rewrite <- (parse_of_respectful_refl (pf := reflexivity _)) in H
            end.

let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
            destruct p; assumption. }
 }
        as X; simpl in *.
      pose ().


SearchAbout (?x < S ?x).
      specialize (X (reflexivity _)).
                 (reflexivity );
        simpl in *.
                                                                  (@minimal_parse_of_production__of__parse_of));
      simpl in *.
      SearchAbout (_ - _ = 0).
      Check drop_length.
      SearchAbout length drop.

{ splits : list nat
                                       | forall n,
                                           n <= ilength s
                                           -> parse_of_item G (take n (string_of_indexed s)) (NonTerminal nt)
                                           -> parse_of_production G (drop n (string_of_indexed s)) p'
                                           -> List.In n splits }%comp
Definition possible_terminals_of_production' (terminals_of_nt : String.string -> possible_terminals)
           (its : production Char)
: possible_terminals
  := flat_map
       (fun it =>
          match it with
            | Terminal ch => [ch]
            | NonTerminal nt => terminals_of_nt nt
          end)
       its.




Lemma has_only_terminals_parse_of_production_length (G : grammar Ascii.ascii) {n}
      f pat
      (H_f : forall nt str n', f nt = same_length n' -> parse_of G str (Lookup G nt) -> String.length str = n')
      (H : possible_first_terminals_of_production' f pat = same_length n)
      str
      (p : parse_of_production G str pat)
: String.length str = n.
Proof.
  revert n H; induction p; simpl in *.
  { congruence. }
  { edestruct (_ : item _).
    { match goal with
        | [ H : context[possible_first_terminals_of_production' ?f ?p] |- _ ] => revert H; case_eq (possible_first_terminals_of_production' f p); intros
      end;
      repeat match goal with
               | [ H : ?x = ?x |- _ ] => clear H
               | [ H : ?x = _ :> length_result, H' : context[?x] |- _ ] => rewrite H in H'
               | _ => exfalso; discriminate
               | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
               | _ => progress subst
               | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
               | [ H : is_true (_ ~= [ _ ])%string_like |- _ ] => apply length_singleton in H
               | [ H : _ |- _ ] => progress rewrite ?(@take_length _ string_stringlike _), ?(@drop_length _ string_stringlike _), ?substring_length, ?Plus.plus_0_r, ?NPeano.Nat.sub_0_r, ?NPeano.Nat.add_sub in H
               | [ H : context[min ?x (?y + ?z) - ?z] |- _ ] => rewrite <- (@NPeano.Nat.sub_min_distr_r x (y + z) z) in H
               | [ H : context[min ?x ?y], H' : ?x <= ?y |- _ ] => rewrite (@Min.min_l x y) in H by assumption
               | [ H : context[min ?x ?y], H' : ?y <= ?x |- _ ] => rewrite (@Min.min_r x y) in H by assumption
               | [ H : context[min (?x - ?y) ?x] |- _ ] => rewrite (@Min.min_l (x - y) x) in H by (clear; omega)
               | [ H : forall n, same_length _ = same_length n -> _ |- _ ] => specialize (H _ eq_refl)
               | [ H : context[min _ _] |- _ ] => revert H; apply Min.min_case_strong; intros; omega
             end. }
    { intros.
      match goal with
        | [ H : context[f ?x] |- _ ] => revert H; case_eq (f x); intros
      end;
        match goal with
          | [ H : context[possible_first_terminals_of_production' ?f ?p] |- _ ] => revert H; case_eq (possible_first_terminals_of_production' f p); intros
        end;
        repeat match goal with
                 | [ H : ?x = ?x |- _ ] => clear H
                 | [ H : ?x = _ :> length_result, H' : context[?x] |- _ ] => rewrite H in H'
                 | _ => exfalso; discriminate
                 | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
                 | _ => progress subst
                 | [ H : forall n, same_length _ = same_length n -> _ |- _ ] => specialize (H _ eq_refl)
                 | _ => progress rewrite ?(@take_length _ string_stringlike _), ?(@drop_length _ string_stringlike _), ?substring_length, ?Plus.plus_0_r, ?NPeano.Nat.sub_0_r, ?NPeano.Nat.add_sub
                 | [ |- context[min ?x (?y + ?z) - ?z] ] => rewrite <- (@NPeano.Nat.sub_min_distr_r x (y + z) z)
                 | [ |- context[min (?x - ?y) ?x] ] => rewrite (@Min.min_l (x - y) x) by (clear; omega)
                 | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
                 | [ H : parse_of_item _ _ (NonTerminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
                 | [ H : parse_of _ _ _ |- _ ] => eapply H_f in H; [ | eassumption.. ]
                 | _ => apply Min.min_case_strong; omega
               end. } }
Qed.

Lemma has_only_terminals_parse_of_length (G : grammar Ascii.ascii) {n}
      nt
      (H : possible_first_terminals_of G nt = same_length n)
      str
      (p : parse_of G str (Lookup G nt))
: String.length str = n.
Proof.
  unfold possible_first_terminals_of, possible_first_terminals_of_nt in H.
  revert n nt H str p.
  match goal with
    | [ |- forall a b, Fix ?wf _ _ ?x _ = _ -> _ ]
      => induction (wf x)
  end.
  intros ? ?.
  rewrite Fix1_eq by apply possible_first_terminals_of_nt_step_ext.
  unfold possible_first_terminals_of_nt_step at 1; simpl.
  edestruct dec; simpl;
  [
  | solve [ intros; discriminate ] ].
  generalize dependent (G nt).
  intros.
  unfold possible_first_terminals_of_productions' in *.
  let p := match goal with H : parse_of _ _ _ |- _ => constr:H end in
  let H := fresh in
  rename p into H;
    induction H; simpl in *.
  { match goal with
      | [ H : context[possible_first_terminals_of_production' ?f ?p] |- _ ] => revert H; case_eq (possible_first_terminals_of_production' f p); intros
    end;
    repeat match goal with
             | [ H' : rdp_list_is_valid_nonterminal ?x ?nt = true,
                      H : forall y, rdp_list_nonterminals_listT_R y ?x -> _ |- _ ]
               => specialize (fun nt' str0 n' H0 => H _ (@rdp_list_remove_nonterminal_dec _ nt H') n' nt' H0 str0)
             | [ H : possible_first_terminals_of_production' _ _ = same_length _ |- _ ] => eapply has_only_terminals_parse_of_production_length in H; [ | eassumption.. ]
             | _ => reflexivity
             | _ => discriminate
             | _ => progress subst
             | [ H : possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length in H
             | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ \/ _ |- _ ] => destruct H; [ (discriminate || congruence) | ]
             | [ H : _ \/ _ |- _ ] => destruct H; [ | (discriminate || congruence) ]
             | [ H : ?x = same_length _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : fold_right possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length_fold_right in H
           end. }
  { edestruct (_ : productions _).
    { match goal with
        | [ H : parse_of _ _ [] |- _ ] => inversion H
      end. }
    { repeat match goal with
               | _ => progress simpl in *
               | [ H : possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : fold_right possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length_fold_right in H
               | [ H : fold_right possible_first_terminals_of_productions'_f _ _ = same_length _ -> _ |- _ ]
                 => specialize (fun H' => H (proj2 possible_first_terminals_of_productions'_f_same_length_fold_right H'))
               | _ => progress eauto
             end. } }
Qed.
