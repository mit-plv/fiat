(** * Definition of a parse-tree-returning CFG parser-recognizer *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common Fiat.Common.Wf.
Require Import Fiat.Parsers.MinimalParse.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties Fiat.Parsers.WellFoundedParse.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid Fiat.Parsers.ContextFreeGrammar.ValidProperties.
(*Require Import Coq.Logic.Eqdep_dec.*)
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.BooleanRecognizerExt.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Arguments dec_stabalize : simpl never.

Local Ltac subst_le_proof :=
  idtac;
  match goal with
    | [ H : ?x <= ?y, H' : ?x <= ?y |- _ ]
      => assert (H = H') by apply Le.le_proof_irrelevance; subst
  end.

Local Ltac subst_nat_eq_proof :=
  idtac;
  match goal with
    | [ H : ?x = ?y :> nat, H' : ?x = ?y |- _ ]
      => assert (H = H') by apply UIP_nat; subst
  end.

Local Ltac subst_valid_proof :=
  idtac;
  match goal with
    | [ H : item_valid ?it, H' : item_valid ?it |- _ ]
      => assert (H = H') by apply item_valid_proof_irrelevance; subst
    | [ H : production_valid ?it, H' : production_valid ?it |- _ ]
      => assert (H = H') by apply production_valid_proof_irrelevance; subst
    | [ H : productions_valid ?it, H' : productions_valid ?it |- _ ]
      => assert (H = H') by apply productions_valid_proof_irrelevance; subst
  end.

Local Ltac prove_nonterminals_t' :=
  idtac;
  match goal with
    | _ => assumption
    | [ H : is_true (is_valid_nonterminal initial_nonterminals_data (of_nonterminal _)) |- _ ]
      => apply initial_nonterminals_correct in H
    | [ H : In (to_nonterminal _) (Valid_nonterminals ?G) |- _ ]
      => apply initial_nonterminals_correct' in H
  end.
Local Ltac prove_nonterminals_t := repeat prove_nonterminals_t'.
Local Ltac solve_nonterminals_t' :=
  idtac;
  match goal with
    | _ => prove_nonterminals_t'
    | [ H : context[of_nonterminal (to_nonterminal _)] |- _ ]
      => rewrite of_to_nonterminal in H by prove_nonterminals_t
  end.
Local Ltac solve_nonterminals_t := repeat solve_nonterminals_t'.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} (G : grammar Char).
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ G data}
          {rdata : @parser_removal_dataT' _ G _}
          {gvalid : grammar_valid G}.

  Local Notation dec T := (T + (T -> False))%type (only parsing).

  Local Notation iffT x y := ((x -> y) * (y -> x))%type (only parsing).

  Lemma dec_prod {A B} (HA : dec A) (HB : dec B) : dec (A * B).
  Proof.
    destruct HA; [ destruct HB; [ left; split; assumption | right ] | right ];
    intros [? ?]; eauto with nocore.
  Defined.

  Lemma dec_In {A} {P : A -> Type} (HA : forall a, dec (P a)) ls
  : dec { a : _ & (In a ls * P a) }.
  Proof.
    induction ls as [|x xs IHxs]; simpl.
    { right; intros [? [? ?]]; assumption. }
    { destruct (HA x); [ left; exists x; split; eauto | destruct IHxs; [ left | right ] ];
      intros;
      destruct_head sigT;
      destruct_head prod;
      destruct_head or;
      subst;
      eauto. }
  Defined.

  Lemma parse_complete_stabalize' {len0 valid str it its}
        (n m : nat)
        (Hn : n >= length str)
        (Hm : m >= length str)
  : (minimal_parse_of_item (G := G) len0 valid (take n str) it
     * minimal_parse_of_production (G := G) len0 valid (drop n str) its)
    -> (minimal_parse_of_item (G := G) len0 valid (take m str) it
        * minimal_parse_of_production (G := G) len0 valid (drop m str) its).
  Proof.
    intros [pi pp]; split;
    [ eapply expand_minimal_parse_of_item; [ .. | eassumption ]
    | eapply expand_minimal_parse_of_production; [ .. | eassumption ] ];
    try reflexivity; eauto.
    { clear -Hn Hm HSLP.
      abstract (rewrite !take_long by assumption; reflexivity). }
    { clear -Hn Hm HSLP.
      abstract (apply bool_eq_empty; rewrite drop_length; omega). }
  Defined.

  Definition parse_complete_stabalize'' {len0 valid str it its}
        (n m : nat)
        (Hn : n >= length str)
        (Hm : m >= length str)
    := (@parse_complete_stabalize' len0 valid str it its n m Hn Hm,
        @parse_complete_stabalize' len0 valid str it its m n Hm Hn).

  Definition parse_complete_stabalize {len0 valid str it its}
        (n : nat)
        (Hn : n >= length str)
    := @parse_complete_stabalize'' len0 valid str it its n (S n) Hn (le_S _ _ Hn).

  Global Arguments parse_complete_stabalize : simpl never.

 (* Lemma Lookup_production_S it its nt_index prods_index prod_index
        (H : it::its = Lookup_production (G := G) nt_index prods_index (S prod_index))
  : its = Lookup_production (G := G) nt_index prods_index (min prod_index (pred (Datatypes.length (Lookup_production' (G := G) nt_index prods_index)))).
  Proof.
    unfold Lookup_production, Lookup_production_gen in *.
    change (Lookup_production'_gen (G := G) (map G (Valid_nonterminals G)) nt_index prods_index)
    with (Lookup_production' (G := G) nt_index prods_index) in *.
    apply Min.min_case_strong; intro.
    { rewrite NPeano.Nat.sub_succ_r in *.
      match goal with
        | [ H : context[pred ?x] |- _ ] => destruct x eqn:?
      end.
      { simpl in *; exfalso.
        repeat match goal with
                 | [ H : List.length ?x = 0 |- _ ] => destruct x eqn:?; simpl in *
                 | [ H : _::_ = [] |- _ ] => inversion H
                 | [ H : S _ = 0 |- _ ] => inversion H
               end. }
      { rewrite NPeano.Nat.sub_succ_l in * by omega.
        simpl pred in H.
        rewrite <- drop_dropS, <- H; simpl; reflexivity. } }
    { match goal with
        | [ |- context[pred (List.length ?ls)] ]
          => destruct ls eqn:?; simpl in * |- ; [ congruence | ]
      end.
      match goal with
        | [ H : context[?x - ?y], H' : ?x <= ?y |- _ ] => replace (x - y) with 0 in H by omega; simpl in H
      end.
      simpl Datatypes.length; simpl pred.
      repeat match goal with
               | _ => reflexivity
               | [ |- context[S ?x - ?x] ] => replace (S x - x) with 1 by omega
               | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; clear H
             end. }
  Qed.

  Lemma lookup_first_index_helper nt
  : (Lookup_productions
       (G := G)
       (List.length (map G (Valid_nonterminals G)) - (first_index (Equality.string_beq nt) (Valid_nonterminals G))))
    = if is_valid_nonterminal initial_nonterminals_data nt
      then Lookup G nt
      else nil.
  Proof.
    unfold Lookup_productions, Lookup_productions_gen.
    destruct (Bool.bool_dec (is_valid_nonterminal initial_nonterminals_data nt) true) as [b|b].
    { rewrite b.
      apply all_valid_nt in b.
      clear -b.
      induction (Valid_nonterminals G) as [|x xs IHxs].
      { destruct b. }
      { destruct b; subst; simpl.
        { rewrite Equality.string_lb, minus_diag by reflexivity.
          reflexivity. }
        { case_eq (Equality.string_beq nt x).
          { rewrite minus_diag.
            intro H'.
            apply Equality.string_bl in H'; subst; clear -H'.
            subst; reflexivity. }
          { specialize (IHxs H).
            intro H'.
            rewrite <- IHxs; clear IHxs.
            generalize (map G xs).
            generalize (first_index (Equality.string_beq nt) xs).
            clear; intros n ls.
            rewrite sub_twice.
            apply Min.min_case_strong.
            { rewrite <- NPeano.Nat.sub_0_le;
              intro H; rewrite H; reflexivity. }
            { intro H; apply le_lt_eq_dec in H.
              destruct H as [H|H]; subst.
              { apply NPeano.Nat.sub_gt in H.
                revert H.
                case_eq (Datatypes.length ls - n).
                { intros ? H; destruct (H eq_refl). }
                { intros n0 H _.
                  replace (Datatypes.length ls - n0) with (S n) by omega.
                  reflexivity. } }
              { rewrite minus_diag; reflexivity. } } } } } }
    { rewrite (Bool.not_true_is_false _ b).
      pose proof (fun H => b (proj2 (all_valid_nt nt) H)) as b'.
      clear -b'.
      induction (Valid_nonterminals G) as [|x xs IHxs].
      { reflexivity. }
      { simpl in b'.
        simplify_hyps.
        simpl map.
        simpl Datatypes.length.
        simpl @first_index.
        case_eq (Equality.string_beq nt x).
        { intro H'; exfalso; clear -H' b'.
          apply Equality.string_bl in H'; subst.
          simpl in *; subst.
          tauto. }
        { intros _.
          rewrite NPeano.Nat.sub_succ.
          rewrite <- minus_Sn_m by omega.
          simpl nth.
          apply IHxs. } } }
  Qed.*)

  Section min.
    Section parts.
      Local Ltac expand_onceL :=
        idtac;
        match goal with
          | [ |- bool_of_sum ?x = ?y ]
            => let x' := head x in
               unfold x'
        end.
      Local Ltac expand_onceR :=
        idtac;
        match goal with
          | [ |- bool_of_sum ?x = ?y ]
            => let y' := head y in
               unfold y'
        end.
      Local Ltac expand_once := try expand_onceL; try expand_onceR.
      Local Ltac expand_both_once :=
        idtac;
        match goal with
          | [ |- ?x = ?y ]
            => let x' := head x in
               let y' := head y in
               try unfold x'; try unfold y'
        end.

      Local Ltac eq_t' :=
        first [ progress subst_le_proof
              | progress subst_nat_eq_proof
              | progress subst_valid_proof
              | idtac;
                match goal with
                  | [ |- ?x = ?x ] => reflexivity
                  | [ |- bool_of_sum (match ?x with
                                        | inl H => inl (@?L H)
                                        | inr H => inr (@?R H)
                                      end) = _ ]
                    => transitivity (bool_of_sum x);
                      [ case x; reflexivity | ]
                  | [ |- bool_of_sum (match ?x with
                                        | left H => inl _
                                        | right H => inr _
                                      end) = _ ]
                    => transitivity (match x with
                                       | left _ => true
                                       | right _ => false
                                     end);
                      [ case x; reflexivity | ]
                  | _ => solve [ eauto with nocore ]
                  | [ |- bool_of_sum (sumbool_rect _ _ _ ?sb) = option_rect _ _ _ (sumbool_rect _ _ _ ?sb) ]
                    => destruct sb; simpl
                  | [ |- context[?e] ]
                    => not is_var e;
                      not is_evar e;
                      match type of e with
                        | _ <= _ => idtac
                        | ?x = _ :> nat => not constr_eq e (eq_refl x)
                      end;
                      generalize e; intro
                end
              | rewrite fold_left_orb_true
              | idtac;
                let LHS := match goal with |- ?LHS = ?RHS => LHS end in
                let RHS := match goal with |- ?LHS = ?RHS => RHS end in
                match RHS with
                  | context R[bool_of_sum ?f0]
                    => match f0 with
                         | ?f ?ae ?be ?ce ?de ?ee ?ge
                           => match LHS with
                                | context L[f ?a ?b ?c ?d ?e ?g]
                                  => unify a ae; unify b be; unify c ce; unify d de; unify e ee; unify g ge;
                                     let v := fresh in
                                     set (v := f a b c d e g);
                                       let L' := context L[v] in
                                       let R' := context R[bool_of_sum v] in
                                       change (L' = R');
                                         clearbody v; destruct v
                              end
                       end
                end
              | idtac;
                let LHS := match goal with |- ?LHS = ?RHS => LHS end in
                let RHS := match goal with |- ?LHS = ?RHS => RHS end in
                match RHS with
                  | context R[bool_of_sum ?f0]
                    => match f0 with
                         | ?f ?ae ?be ?ce ?de ?ee
                           => match LHS with
                                | context L[f ?a ?b ?c ?d ?e]
                                  => unify a ae; unify b be; unify c ce; unify d de; unify e ee;
                                     let v := fresh in
                                     set (v := f a b c d e);
                                       let L' := context L[v] in
                                       let R' := context R[bool_of_sum v] in
                                       change (L' = R');
                                         clearbody v; destruct v
                              end
                       end
                end
              | idtac;
                let RHS := match goal with |- _ = ?RHS => constr:RHS end in
                match RHS with
                  | appcontext[match ?it with Terminal _ => _ | _ => _ end]
                    => destruct it eqn:?
                  | _ => progress subst
                  | _ => progress simpl @bool_of_sum
                  | appcontext G[is_char ?x ?y]
                    => let H := fresh in
                       destruct (Utils.dec (is_char x y)) as [H|H];
                         [ let G' := context G[true] in
                           transitivity G'; [ | symmetry; exact H ]
                         | let G' := context G[false] in
                           transitivity G'; [ | symmetry; exact H ] ]
                  | appcontext G[beq_nat ?x ?y]
                    => let H := fresh in
                       destruct (Utils.dec (beq_nat x y)) as [H|H];
                         [ let G' := context G[true] in
                           transitivity G'; [ | symmetry; exact H ]
                         | let G' := context G[false] in
                           transitivity G'; [ | symmetry; exact H ] ]
                end ].

      Local Ltac eq_t := expand_once; repeat eq_t'.

      Local Ltac eq_list_rect
        := (idtac;
            lazymatch goal with
            | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls ?a ?b ?c ?d ?e ?f) = list_rect ?P' ?N' ?C' ?ls ?c ?d ?f ]
              => (let P0 := fresh in
                  let N0 := fresh in
                  let C0 := fresh in
                  let P1 := fresh in
                  let N1 := fresh in
                  let C1 := fresh in
                  set (P0 := P);
                  set (P1 := P');
                  set (N0 := N);
                  set (N1 := N');
                  set (C0 := C);
                  set (C1 := C');
                  refine (list_rect
                            (fun ls' => forall a' b' c' d' e' f' f'' ,
                                          bool_of_sum (list_rect P0 N0 C0 ls' a' b' c' d' e' f')
                                          = list_rect P1 N1 C1 ls' c' d' f'')
                            _
                            _
                            ls a b c d e f f);
                  simpl @list_rect;
                  [ subst N0 N1; simpl; intros
                  | intros; unfold C0 at 1, C1 at 1; simpl ])
            | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls ?a ?b ?c ?d ?e) = list_rect ?P' ?N' ?C' ?ls ?b ?c ?e ]
              => (let P0 := fresh in
                  let N0 := fresh in
                  let C0 := fresh in
                  let P1 := fresh in
                  let N1 := fresh in
                  let C1 := fresh in
                  set (P0 := P);
                  set (P1 := P');
                  set (N0 := N);
                  set (N1 := N');
                  set (C0 := C);
                  set (C1 := C');
                  refine (list_rect
                            (fun ls' => forall a' b' c' d' e' e'',
                                          bool_of_sum (list_rect P0 N0 C0 ls' a' b' c' d' e')
                                          = list_rect P1 N1 C1 ls' b' c' e'')
                            _
                            _
                            ls a b c d e e);
                  simpl @list_rect;
                  [ subst N0 N1; simpl; intros
                  | intros; unfold C0 at 1, C1 at 1; simpl ])
            end).

      Local Ltac eq_list_rect_fold_left_orb :=
        idtac;
        match goal with
          | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls) = fold_left orb (map ?f ?ls) false ]
            => let P' := fresh in
               let N' := fresh in
               let N' := fresh in
               let C' := fresh in
               let f' := fresh in
               set (P' := P);
                 set (N' := N);
                 set (C' := C);
                 set (f' := f);
                 refine (list_rect
                           (fun ls' => bool_of_sum (list_rect P' N' C' ls')
                                       = fold_left orb (map f' ls') false)
                           _
                           _
                           ls);
                 simpl @list_rect; simpl @fold_left; intros;
                 [ subst P' f' N'
                 | unfold C' at 1, f' at 2 ]
        end.

      Local Ltac eq_list_rect_fold_right_orb :=
        (idtac;
         lazymatch goal with
         | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls ?k0 ?k1) = fold_right orb false (map ?f ?ls) ]
           => (let P' := fresh in
               let N' := fresh in
               let C' := fresh in
               let f' := fresh in
               set (P' := P);
               set (N' := N);
               set (C' := C);
               set (f' := f);
               refine (list_rect
                         (fun ls' => forall k0' k1',
                                       bool_of_sum (list_rect P' N' C' ls' k0' k1')
                                       = fold_right orb false (map f' ls'))
                         _
                         _
                         ls k0 k1);
               simpl @list_rect; simpl @fold_right; intros;
               [ subst P' f' N'
               | unfold C' at 1, f' at 1 ];
               cbv beta)
         | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls ?k0) = fold_right orb false (map ?f ?ls) ]
           => (let P' := fresh in
               let N' := fresh in
               let C' := fresh in
               let f' := fresh in
               set (P' := P);
               set (N' := N);
               set (C' := C);
               set (f' := f);
               refine (list_rect
                         (fun ls' => forall k0',
                                       bool_of_sum (list_rect P' N' C' ls' k0')
                                       = fold_right orb false (map f' ls'))
                         _
                         _
                         ls k0);
               simpl @list_rect; simpl @fold_right; intros;
               [ subst P' f' N'
               | unfold C' at 1, f' at 1 ];
               cbv beta)
         end).

      Local Ltac t_item str_matches_nonterminal' :=
        unfold parse_item'; simpl;
        repeat match goal with
                 | _ => assumption
                 | _ => solve [ reflexivity ]
                 | [ H : ?A -> False, H' : ?A |- _ ] => destruct (H H')
                 | [ H := _ |- _ ] => subst H
                 | [ H : ?e = true |- context[?e] ] => rewrite H
                 | [ H : ?e = false |- context[?e] ] => rewrite H
                 | [ H' : _ = false, H : minimal_parse_of_item _ _ _ ?it |- False ]
                   => clear -H H'; abstract (inversion H; subst; congruence)
                 | [ H' : _ -> False, H : minimal_parse_of_item _ _ _ ?it |- False ]
                   => clear -H H'; abstract (inversion H; subst; auto with nocore)
                 | [ H : forall nt, { d : _ | _ = str_matches_nonterminal' _} |- context[_ = str_matches_nonterminal' _] ]
                   => rewrite <- (fun nt => proj2_sig (H nt))
                 | [ |- context[bool_of_sum ?e] ] => destruct e; simpl
                 | [ H : context[to_nonterminal (of_nonterminal _)] |- _ ]
                   => rewrite to_of_nonterminal in H by assumption
                 | [ H : minimal_parse_of_nonterminal _ _ _ (to_nonterminal (of_nonterminal ?nt)) |- _ ]
                   => assert (List.In nt (Valid_nonterminals G));
                     [ inversion H; clear H
                     | rewrite to_of_nonterminal in H by assumption ]
                 | _ => progress subst
                 | [ H : is_true (is_valid_nonterminal _ (of_nonterminal _)) |- _ ]
                   => apply initial_nonterminals_correct in H
                 | [ H : List.In (to_nonterminal _) _ |- _ ]
                   => apply initial_nonterminals_correct' in H
                 | [ H : minimal_parse_of_nonterminal _ _ _ (to_nonterminal (of_nonterminal ?nt)) -> False |- _ ]
                   => assert (List.In nt (Valid_nonterminals G))
                     by (clear H; t_item str_matches_nonterminal');
                     rewrite to_of_nonterminal in H by assumption
                 | [ H : minimal_parse_of_item _ _ _ (NonTerminal ?nt) |- List.In ?nt (Valid_nonterminals G) ]
                   => inversion H; clear H
                 | [ H : minimal_parse_of_nonterminal _ _ _ ?nt |- List.In ?nt (Valid_nonterminals G) ]
                   => inversion H; clear H
               end.

      Section item.
        Context {len0 valid}
                (str : String)
                (str_matches_nonterminal'
                 : nonterminal_carrierT -> bool)
                (str_matches_nonterminal
                 : forall nt : nonterminal_carrierT,
                     dec (minimal_parse_of_nonterminal (G := G) len0 valid str (to_nonterminal nt))).

        Section valid.
          Context (Hmatches
                   : forall nt,
                       is_valid_nonterminal initial_nonterminals_data nt
                       -> str_matches_nonterminal nt = str_matches_nonterminal' nt :> bool)
                  (it : item Char)
                  (Hvalid : item_valid it).

          Definition parse_item'
          : dec (minimal_parse_of_item (G := G) len0 valid str it).
          Proof.
            clear Hvalid.
            refine (match it return dec (minimal_parse_of_item len0 valid str it) with
                      | Terminal ch => if Sumbool.sumbool_of_bool (str ~= [ ch ])
                                       then inl (MinParseTerminal _ _ _ _ _)
                                       else inr (fun _ => !)
                      | NonTerminal nt => if str_matches_nonterminal (of_nonterminal nt)
                                          then inl (MinParseNonTerminal _)
                                          else inr (fun _ => !)
                    end);
              clear str_matches_nonterminal Hmatches;
              t_item str_matches_nonterminal'.
          Defined.

          Definition parse_item'_eq
          : parse_item' = BooleanRecognizer.parse_item' str_matches_nonterminal' str it :> bool.
          Proof. eq_t. Qed.
        End valid.

        Section all.
          Context (Hmatches
                   : forall nt,
                       str_matches_nonterminal nt = str_matches_nonterminal' nt :> bool)
                  (it : item Char).

          Definition parse_item'_eq_all
          : parse_item' it = BooleanRecognizer.parse_item' str_matches_nonterminal' str it :> bool.
          Proof. eq_t. Qed.
        End all.
      End item.

      Definition parse_item'_ext
                 {len0 valid}
                 (str : String)
                 (str_matches_nonterminal str_matches_nonterminal'
                  : forall nt : nonterminal_carrierT,
                      dec (minimal_parse_of_nonterminal (G := G) len0 valid str (to_nonterminal nt)))
                 (ext : forall nt,
                          str_matches_nonterminal nt = str_matches_nonterminal' nt)
                (it : item Char)
      : parse_item' str_matches_nonterminal it
        = parse_item' str_matches_nonterminal' it.
      Proof.
        expand_both_once; destruct it; try reflexivity; [].
        rewrite ext.
        clear ext str_matches_nonterminal.
        reflexivity.
      Qed.

      Section production.
        Context {len0 valid}
                (parse_nonterminal
                 : forall (str : String) (len : nat) (Hlen : length str = len) (pf : len <= len0) (nt : nonterminal_carrierT),
                     dec (minimal_parse_of_nonterminal (G := G) len0 valid str (to_nonterminal nt))).

        Lemma dec_in_helper {ls it its str}
        : iffT {n0 : nat &
                     (In (min (length str) n0) (map (min (length str)) ls) *
                      minimal_parse_of_item (G := G) len0 valid (take n0 str) it *
                      minimal_parse_of_production (G := G) len0 valid (drop n0 str) its)%type}
               {n0 : nat &
                     (In n0 ls *
                      (minimal_parse_of_item (G := G) len0 valid (take n0 str) it *
                       minimal_parse_of_production (G := G) len0 valid (drop n0 str) its))%type}.
        Proof.
          split; first [ intros [n [[H0 H1] H2]]
                       | intros [n [H0 [H1 H2]]] ].
          { destruct (le_lt_dec (length str) n) as [pf|pf].
            { rewrite Min.min_l in H0 by assumption.
              clear -H0 H1 H2 rdata cdata pf HSLP.
              induction ls as [|x xs IHxs]; destruct_head_hnf False.
              destruct (le_lt_dec (length str) x).
              { exists x.
                repeat split.
                { left; reflexivity. }
                { eapply expand_minimal_parse_of_item_beq; [ .. | eassumption ].
                  rewrite !take_long by omega; reflexivity. }
                { eapply expand_minimal_parse_of_production_beq; [ .. | eassumption ].
                  apply bool_eq_empty; rewrite drop_length; omega. } }
              { simpl in *.
                rewrite Min.min_r in H0 by omega.
                destruct IHxs as [n' [IH0 [IH1 IH2]]].
                { destruct H0; try omega; assumption. }
                { exists n'; repeat split; try assumption.
                  right; assumption. } } }
            { exists n; repeat split; try assumption; [].
              apply in_map_iff in H0.
              repeat match goal with
                       | _ => progress destruct_head ex
                       | _ => progress destruct_head and
                       | [ H : context[min ?x ?y] |- _ ]
                         => rewrite (Min.min_r x y) in H by omega
                       | _ => progress subst
                       | [ H : min ?x ?y < ?x |- _ ] => revert H; apply (Min.min_case_strong x y)
                       | _ => intro
                       | _ => omega
                       | _ => assumption
                     end. } }
          { exists n; repeat split; try assumption.
            apply in_map; assumption. }
        Defined.

        Local Opaque dec_in_helper.

        Lemma parse_production'_helper {str it its} (pf : length str <= len0)
        : dec {n0 : nat &
                    (minimal_parse_of_item (G := G) len0 valid (take n0 str) it *
                     minimal_parse_of_production (G := G) len0 valid (drop n0 str) its)%type}
          -> dec (minimal_parse_of_production (G := G) len0 valid str (it :: its)).
        Proof.
          intros [H|H]; [ left; destruct H as [n [??]] | right; intro p; apply H; clear H ].
          { econstructor; eassumption. }
          { clear -p; abstract (inversion p; subst; eexists; split; eassumption). }
        Defined.

        Local Ltac t_parse_production_for :=
          repeat
            match goal with
              | [ H : (beq_nat _ _) = true |- _ ] => apply EqNat.beq_nat_true in H
              | _ => progress subst
              | _ => solve [ constructor; assumption ]
              | [ H : minimal_parse_of_production _ _ _ nil |- _ ] => (inversion H; clear H)
              | [ H : minimal_parse_of_production _ _ _ (_::_) |- _ ] => (inversion H; clear H)
              | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
              | _ => progress simpl in *
              | _ => discriminate
              | [ H : forall x, (_ * _)%type -> _ |- _ ] => specialize (fun x y z => H x (y, z))
              | _ => solve [ eauto with nocore ]
              | _ => solve [ apply Min.min_case_strong; omega ]
              | _ => omega
              | [ H : production_valid (_::_) |- _ ]
                => let H' := fresh in
                   pose proof H as H';
                     apply production_valid_cons in H;
                     apply hd_production_valid in H'
            end.

        Lemma production_is_reachableT_tl {it its}
        : production_is_reachableT G (it :: its) -> production_is_reachableT G its.
        Proof.
          intros [nt [prefix [H0 H1]]].
          exists nt. exists (prefix ++ [it]); split; try assumption.
          rewrite <- app_assoc; assumption.
        Qed.

        Lemma parse_production'_for__helper__split_list_completeT_for
              {splits : item Char -> production Char -> String -> list nat}
              (Hsplits : forall str it its,
                  production_is_reachableT G (it :: its)
                  -> forall pf' : length str <= len0,
                    split_list_completeT_for (G := G) (valid := valid) it its str pf' (splits it its str))
              {it its}
              {str : String}
              (Hreachable : production_is_reachableT G (it :: its))
              (p : {a : nat
                   & (In a (splits it its str) *
                      (minimal_parse_of_item (G := G) len0 valid (take a str) it
                       * minimal_parse_of_production (G := G) len0 valid (drop a str) its))%type} -> False)
              (pf' : length str <= len0)
          : split_list_completeT_for (G := G) (valid := valid) it its str pf' (splits it its str).
        Proof.
          t_parse_production_for.
        Qed.

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Definition parse_production'_for
                 (splits : item Char -> production Char -> String -> list nat)
                 (Hsplits : forall str it its (Hreachable : production_is_reachableT G (it::its)) pf', split_list_completeT_for (len0 := len0) (G := G) (valid := valid) it its str pf' (splits it its str))
                 (str : String)
                 (len : nat)
                 (Hlen : length str = len)
                 (pf : len <= len0)
                 (prod : production Char)
                 (Hreachable : production_is_reachableT G prod)
        : dec (minimal_parse_of_production (G := G) len0 valid str prod).
        Proof.
          revert prod Hreachable str len Hlen pf.
          refine
            (list_rect
               (fun prod =>
                  forall (Hreachable : production_is_reachableT G prod)
                         (str : String)
                         (len : nat)
                         (Hlen : length str = len)
                         (pf : len <= len0),
                    dec (minimal_parse_of_production (G := G) len0 valid str prod))
               ((** 0-length production, only accept empty *)
                 fun Hreachable str len Hlen pf
                 => match Utils.dec (beq_nat len 0) with
                      | left H => inl _
                      | right H => inr (fun p => _)
                    end)
               (fun it its parse_production' Hreachable str len Hlen pf
                => parse_production'_helper
                     _
                     (let parse_item := (fun n pf => parse_item' (parse_nonterminal (take n str) (len := min n len) (eq_trans take_length (f_equal (min _) Hlen)) pf) it) in
                      let parse_item := (fun n => parse_item n (Min.min_case_strong n len (fun k => k <= len0) (fun Hlen => (Nat.le_trans _ _ _ Hlen pf)) (fun Hlen => pf))) in
                      let parse_production := (fun n => parse_production' (production_is_reachableT_tl Hreachable) (drop n str) (len - n) (eq_trans (drop_length _ _) (f_equal (fun x => x - _) Hlen)) (Nat.le_trans _ _ _ (Nat.le_sub_l _ _) pf)) in
                      match dec_In
                              (fun n => dec_prod (parse_item n) (parse_production n))
                              (splits it its str)
                      with
                        | inl p => inl (existT _ (projT1 p) (snd (projT2 p)))
                        | inr p
                          => let pf' := (Nat.le_trans _ _ _ (Nat.eq_le_incl _ _ Hlen) pf) in
                             let H := (parse_production'_for__helper__split_list_completeT_for Hsplits Hreachable p pf' : split_list_completeT_for (G := G) (len0 := len0) (valid := valid) it its str pf' (splits it its str)) in
                             inr (fun p' => p (fst dec_in_helper (H p')))
                      end)
            (*match dec_stabalize
                           _
                           (length str)
                           (parse_complete_stabalize (len0 := len0) (valid := valid) (it := it) (its := its))
                           _ with
                     | inl p => inl (MinParseProductionCons _ _ _ (fst (snd (projT2 p))) (snd (snd (projT2 p))))
                     | inr p => inr (fun p' => _)
                   end*)(*fold_left
                     orb
                     (map (fun n =>
                             (parse_item'
                                (parse_nonterminal (take n str) (len := min n len) _)
                                (take n str)
                                it)
                               && parse_production' (drop n str) (len - n) _)%bool
                          (splits it its str))
                     false)*)));
            [ clear parse_nonterminal Hsplits splits rdata cdata
            | clear parse_nonterminal Hsplits splits rdata cdata
            | .. ];
            abstract t_parse_production_for.
        Defined.

        Definition parse_production'_for_eq
                   (parse_nonterminal'
                    : forall (str : String) (len : nat) (pf : len <= len0) (nt : nonterminal_carrierT),
                        bool)
                   (parse_nonterminal_eq
                    : forall str len Hlen pf nt,
                        is_valid_nonterminal initial_nonterminals_data nt
                        -> @parse_nonterminal str len Hlen pf nt = parse_nonterminal' str len pf nt :> bool)
                   (splits : item Char -> production Char -> String -> list nat)
                   (Hsplits : forall str it its Hreachable pf', split_list_completeT_for (len0 := len0) (G := G) (valid := valid) it its str pf' (splits it its str))
                   (str : String)
                   (len : nat)
                   (Hlen : length str = len)
                   (pf pf' : len <= len0)
                   (prod : production Char)
                   (Hreachable : production_is_reachableT G prod)
                   (Hvalid : production_valid prod)
        : parse_production'_for splits Hsplits str Hlen pf Hreachable = BooleanRecognizer.parse_production'_for parse_nonterminal' splits str pf' prod :> bool.
        Proof.
          eq_t; eq_list_rect; repeat eq_t'; [].
          expand_onceL; repeat eq_t'; [].
          expand_onceL; eq_list_rect_fold_left_orb; repeat eq_t'; [].
          let parse_nt := match goal with
                          | [ |- context[parse_item' ?pnt _] ] => pnt
                          end in
          erewrite <- (parse_item'_eq _ parse_nt);
            [
            | intros; etransitivity;
              [ apply parse_nonterminal_eq; assumption
              | repeat (f_equal; []); apply Le.le_proof_irrelevance ]
            | repeat match goal with
                       | [ H : production_is_reachableT ?G (?a :: ?ls) |- item_valid ?a ]
                         => let H' := fresh in
                            assert (H' : production_is_reachable G (a::ls));
                              [ clear -H;
                                repeat first [ let x := fresh in destruct H as [x H]; exists x
                                             | assumption ];
                                destruct H; split; (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4464 *)
                                repeat first [ assumption
                                             | apply In_InT ]
                              | apply (@reachable_production_valid _ G _ gvalid), hd_production_valid in H'; assumption ]
                       | _ => assumption
                     end ];
            [].
          repeat eq_t'; simpl; repeat eq_t'.
          match goal with H : _ |- _ => erewrite <- H; repeat eq_t' end.
        Qed.

        Lemma split_list_completeT_production_is_reachable
              {it its str pf splits}
              (H : split_list_completeT (G := G) splits)
              (Hreachable : production_is_reachableT G (it::its))
        : split_list_completeT_for (G := G) (len0 := len0) (valid := valid) it its str pf (splits it its str).
        Proof.
          specialize (H len0 valid str pf).
          hnf in Hreachable.
          destruct Hreachable as [nt [prefix [Hr0 Hr1]]].
          specialize (H nt).
          apply initial_nonterminals_correct in Hr0.
          specialize_by assumption.
          generalize dependent (G nt).
          intro p; induction p as [|x xs IHxs]; simpl.
          { intros ? []. }
          { intros H [H'|H']; subst;
            destruct_head prod;
            specialize_by assumption; trivial.
            match goal with
              | [ H : Forall_tails _ (_ ++ _) |- _ ]
                => apply Forall_tails_app, Forall_tails_id in H; assumption
            end. }
        Qed.

        Definition parse_production'
                 (str : String)
                 (len : nat)
                 (Hlen : length str = len)
                 (pf : len <= len0)
                 (prod : production Char)
                 (Hreachable : production_is_reachableT G prod)
        : dec (minimal_parse_of_production (G := G) len0 valid str prod)
          := parse_production'_for split_string_for_production (fun str it its Hreachable pf' => split_list_completeT_production_is_reachable split_string_for_production_complete Hreachable) str Hlen pf Hreachable.

        Definition parse_production'_eq
                   (parse_nonterminal'
                    : forall (str : String) (len : nat) (pf : len <= len0) (nt : nonterminal_carrierT),
                        bool)
                   (parse_nonterminal_eq
                    : forall str len Hlen pf nt,
                        is_valid_nonterminal initial_nonterminals_data nt
                        -> @parse_nonterminal str len Hlen pf nt = parse_nonterminal' str len pf nt :> bool)
                   (str : String)
                   (len : nat)
                   (Hlen : length str = len)
                   (pf pf' : len <= len0)
                   (prod : production Char)
                   (Hreachable : production_is_reachableT G prod)
        : parse_production' str Hlen pf Hreachable = BooleanRecognizer.parse_production' parse_nonterminal' str pf' prod :> bool.
        Proof.
          apply parse_production'_for_eq; try assumption.
          eapply reachable_production_valid; try eassumption.
          destruct_head_hnf sigT; destruct_head Datatypes.prod.
          repeat esplit; try eassumption.
          apply In_InT; eassumption.
        Qed.
      End production.

      Section productions.
        Context {len0 valid}
                (parse_nonterminal'
                 : forall (str : String) (len : nat),
                     len <= len0
                     -> forall nt : nonterminal_carrierT,
                          bool)
                (parse_nonterminal
                 : forall (str : String)
                          (len : nat)
                          (Hlen : length str = len)
                          (pf : len <= len0)
                          (nt : nonterminal_carrierT),
                     dec (minimal_parse_of_nonterminal (G := G) len0 valid str (to_nonterminal nt)))
                (Hmatches
                 : forall (str : String)
                          (len : nat)
                          (Hlen : length str = len)
                          (pf : len <= len0)
                          (nt : nonterminal_carrierT)
                          (Hvalid : is_valid_nonterminal initial_nonterminals_data nt),
                     parse_nonterminal str len Hlen pf nt = parse_nonterminal' str len pf nt :> bool)
                (str : String)
                (len : nat).

        Definition productions_is_reachable (prods : productions Char)
          := { nt : _ & { prefix : _ | In nt (Valid_nonterminals G) /\ prefix ++ prods = Lookup G nt } }.

        Lemma hd_productions_is_reachable (p : production Char) (ps : productions Char) (H : productions_is_reachable (p :: ps))
        : production_is_reachable G p.
        Proof.
          destruct H as [nt H]; exists nt.
          eexists nil; simpl.
          destruct H as [prefix [? H]]; split; try assumption; [].
          rewrite <- H; clear.
          induction prefix as [|x xs IHxs]; simpl.
          { left; reflexivity. }
          { right; assumption. }
        Qed.

        Local Ltac t_prods_fin :=
          try solve
              [ eassumption
              | idtac;
                match goal with
                  | [ p : _ |- _ ] => clear -p; abstract inversion p
                end
              | repeat
                  match goal with
                    | [ Hreachable : productions_is_reachable (?p :: ?ps)
                        |- productions_is_reachable ?ps ]
                      => exists (projT1 Hreachable); destruct Hreachable as [nt Hreachable]; simpl
                    | [ Hreachable : productions_is_reachable (?p :: ?ps)
                        |- production_is_reachableT ?G ?p ]
                      => exists (projT1 Hreachable); destruct Hreachable as [nt Hreachable]; simpl
                    | [ Hreachable : { prefix : _ | ?V /\ prefix ++ ?p::?ps = ?k }
                        |- { prefix : _ | ?V /\ prefix ++ ?ps = ?k } ]
                      => exists (proj1_sig Hreachable ++ [p]); destruct Hreachable as [prefix [? Hreachable]]; split; [ assumption | simpl ]
                    | [ H : ?x ++ ?y::?z = ?k |- (?x ++ [?y]) ++ ?z = ?k ]
                      => clear -H; abstract (rewrite <- app_assoc; assumption)
                    | [ |- { prefix : _ & (_ * _)%type } ]
                      => eexists nil; simpl; split
                    | [ H : { x : _ | ?k /\ _ } |- ?k ] => destruct H as [? [? ?]]; assumption
                    | [ H : { prefix : _ | _ /\ prefix ++ ?p :: ?ps = ?k } |- InT ?p ?k ]
                      => let prefix' := fresh "prefix" in
                         destruct H as [prefix' [? H]]; clear -prefix' H;
                         generalize dependent k; intros; subst;
                         induction prefix'; simpl in *
                    | [ |- ((?x = ?x) + _)%type ] => left; reflexivity
                    | [ |- (_ + ?k)%type ] => right; assumption
                    | [ H0 : minimal_parse_of_production _ _ _ ?p -> False,
                             H1 : minimal_parse_of _ _ _ ?ps -> False,
                                  H2 : minimal_parse_of _ _ _ (?p :: ?ps)
                        |- False ]
                      => clear -H0 H1 H2; abstract (inversion p'; subst; eauto with nocore)
                    | [ H : productions_valid (_::_) |- _ ]
                      => let H' := fresh in
                         pose proof H as H';
                           apply productions_valid_cons in H;
                           apply hd_productions_valid in H'
                    | _ => assumption
                  end ].

        Definition parse_productions'
                   (Hlen : length str = len)
                   (pf : len <= len0)
                   (prods : productions Char)
                   (Hreachable : productions_is_reachable prods)
        : dec (minimal_parse_of (G := G) len0 valid str prods).
        Proof.
          revert prods Hreachable.
          refine (list_rect
                    (fun prods
                     => productions_is_reachable prods
                        -> dec (minimal_parse_of (G := G) len0 valid str prods))
                    (fun _ => inr (fun p => _))
                    (fun p ps IHps Hreachable
                     => match parse_production' parse_nonterminal str Hlen pf _ with
                          | inl H => inl (MinParseHead _ _)
                          | inr H
                            => match IHps _ with
                                 | inl H' => inl (MinParseTail _ _)
                                 | inr H' => inr (fun p' => _)
                               end
                        end));
            t_prods_fin; t_prods_fin.
        Defined.

        Lemma parse_productions'_eq
              (Hlen : length str = len)
              (pf pf' : len <= len0)
              (prods : productions Char)
              (Hreachable : productions_is_reachable prods)
        : (@parse_productions' Hlen pf prods Hreachable)
          = (BooleanRecognizer.parse_productions' parse_nonterminal' str pf' prods)
              :> bool.
        Proof.
          eq_t; eq_list_rect_fold_right_orb; repeat eq_t'.
          erewrite <- parse_production'_eq
            by first [ exact Hmatches
                     | eapply reachable_production_valid, hd_productions_is_reachable; eassumption ];
            repeat eq_t'.
          simpl; reflexivity.
        Qed.
      End productions.

      Section nonterminals.
        Section step.
          Context {len0 valid_len}
                  (parse_nonterminal'
                   : forall (p : nat * nat),
                       prod_relation lt lt p (len0, valid_len)
                       -> forall (valid : nonterminals_listT)
                                 (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                                 (str : String) (len : nat)
                                 (pf : len <= fst p)
                                 (nt : nonterminal_carrierT),
                            bool)
                  (parse_nonterminal
                   : forall (p : nat * nat)
                            (pR : prod_relation lt lt p (len0, valid_len))
                            (valid : nonterminals_listT)
                            (Hvalid_len : nonterminals_length valid <= snd p)
                            (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                            (str : String) (len : nat)
                            (Hlen : length str = len)
                            (pf : len <= fst p)
                            (nt : nonterminal_carrierT),
                       dec (minimal_parse_of_nonterminal (G := G) (fst p) valid str (to_nonterminal nt)))
                  (Hmatches
                   : forall (p : nat * nat)
                            (pR : prod_relation lt lt p (len0, valid_len))
                            (valid : nonterminals_listT)
                            (Hvalid_len : nonterminals_length valid <= snd p)
                            (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                            (str : String) (len : nat)
                            (Hlen : length str = len)
                            (pf : len <= fst p)
                            (nt : nonterminal_carrierT)
                            (Hvalid : is_valid_nonterminal initial_nonterminals_data nt),
                       (@parse_nonterminal p pR valid Hvalid_len str len Hlen pf nt)
                       = (@parse_nonterminal' p pR valid str len pf nt)
                           :> bool).

          Definition parse_nonterminal_step
                     (valid : nonterminals_listT)
                     (Hvalid_len : nonterminals_length valid <= valid_len)
                     (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                     (str : String)
                     (len : nat)
                     (Hlen : length str = len)
                     (pf : len <= len0)
                     (nt : nonterminal_carrierT)
          : dec (minimal_parse_of_nonterminal (G := G) len0 valid str (to_nonterminal nt)).
          Proof.
            destruct (Utils.dec (is_valid_nonterminal initial_nonterminals_data nt)) as [Hvalid|Hvalid];
            [
            | right; clear -rdata Hvalid Hlen; intro p;
              abstract (
                  inversion p; subst; try omega;
                  solve_nonterminals_t;
                  congruence
            ) ].
            refine (sumbool_rect (fun _ => _) (fun pf' => _) (fun pf' => _) (lt_dec len len0));
            simpl;
            [ (** [str] got smaller, so we reset the valid nonterminals list *)
              destruct (@parse_productions'
                          len
                          initial_nonterminals_data
                          (@parse_nonterminal
                             (len, nonterminals_length initial_nonterminals_data)
                             (or_introl pf')
                             initial_nonterminals_data
                             (reflexivity _))
                          str len
                          Hlen
                          (le_n _)
                          (Lookup G (to_nonterminal nt)))
              as [mp|nmp];
              [ eexists _, nil; simpl; split; [ | reflexivity ]
              | left; apply MinParseNonTerminalStrLt
              | right; intro mp ]
            | ((** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
              refine (sumbool_rect
                        (fun _ => _)
                        (fun is_valid => _)
                        (fun is_valid => _)
                        (Sumbool.sumbool_of_bool (negb (EqNat.beq_nat valid_len 0) && is_valid_nonterminal valid nt)));
              [ ((** It was valid, so we can remove it *)
                  edestruct (fun pf'' pf'''
                            => @parse_productions'
                                 len0
                                 (remove_nonterminal valid nt)
                                 (@parse_nonterminal
                                    (len0, pred valid_len)
                                    (or_intror (conj eq_refl pf''))
                                    (remove_nonterminal valid nt)
                                    pf'''
                                    (*transitivity
                                       ((_ : Proper (sub_nonterminals_listT ==> eq ==> sub_nonterminals_listT) remove_nonterminal)
                                          _ _ Hvalid _ _ eq_refl)
                                       (sub_nonterminals_listT_remove _ _)*))
                                 str len
                                 Hlen
                                 pf
                                 (Lookup G (to_nonterminal nt)))
                  as [mp|nmp];
                  [
                  |
                  | eexists _, nil; simpl; split; [ | reflexivity ]
                  | left; apply MinParseNonTerminalStrEq
                  | right; intro mp ])
              | ((** oops, we already saw this nonterminal in the past.  ABORT! *)
                simpl in *;
                right; intro mp) ])
            ];
            try solve [ clear -Hlen pf'; abstract (subst; assumption)
                      | clear -mp Hvalid rdata;
                        abstract (rewrite of_to_nonterminal by (first [ assumption | apply initial_nonterminals_correct'; assumption ]); assumption)
                      | idtac;
                        match goal with
                          | [ |- productions_valid _ ]
                            => apply gvalid, initial_nonterminals_correct'; assumption
                          | [ |- is_true (is_valid_nonterminal initial_nonterminals_data (of_nonterminal (to_nonterminal _))) ]
                            => apply initial_nonterminals_correct, initial_nonterminals_correct'; assumption
                        end
                      | clear -pf' Hvalid rdata;
                        abstract (destruct_head or; repeat subst; rewrite ?of_to_nonterminal by (first [ assumption | apply initial_nonterminals_correct'; assumption ]); first [ assumption | omega | apply initial_nonterminals_correct'; assumption ])
                      | clear -mp Hlen;
                        abstract (
                            rewrite lookup_first_index_helper in mp;
                            destruct (is_valid_nonterminal initial_nonterminals_data nt);
                            subst;
                            try solve [ reflexivity
                                      | subst; (assumption || reflexivity)
                                      | inversion mp ]
                          )
                      | simpl; clear -Hvalid rdata;
                        apply initial_nonterminals_correct; assumption
                      | clear -Hlen mp;
                        abstract (subst; assumption)
                      | simpl; clear -is_valid;
                        abstract (
                            destruct valid_len;
                            simpl in *;
                              first [ omega | discriminate ]
                          )
                      | clear -mp nmp Hlen pf';
                        abstract (
                            inversion mp; clear mp; subst;
                            solve [ rewrite lookup_first_index_helper in nmp;
                                    match goal with
                                      | [ H : is_true ?e, H' : context[?e] |- _ ] => rewrite H in H'
                                    end;
                                    auto with nocore
                                  | subst;
                                    clear -pf'; omega
                                  | eauto with nocore;
                                    omega ]
                          ) ].
            { simpl.
              clear -is_valid Hvalid_len rdata.
               abstract (
                  repeat match goal with
                           | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
                           | [ H : and _ _ |- _ ] => destruct H
                           | _ => assumption
                           | [ H : is_valid_nonterminal ?ls ?nt = true |- _ ]
                             => (apply remove_nonterminal_dec in H; hnf in H)
                           | [ H : ?x <= ?y, H' : ?y <= ?z |- _ ] => unique pose proof (transitivity H H')
                           | [ H : _ <= ?x |- _ <= pred ?x ] => apply le_pred in H
                         end
                ). }
            { clear -pf Hlen pf'.
              generalize dependent (length str).
              clear -pf pf'; intros.
              abstract omega. }
            { clear -is_valid Hvalid rdata;
              abstract (
                  repeat match goal with
                           | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
                           | [ H : and _ _ |- _ ] => destruct H
                           | _ => assumption
                           | _ => rewrite of_to_nonterminal by (first [ assumption | apply initial_nonterminals_correct'; assumption ])
                         end
                ). }
            { clear -mp nmp Hlen pf pf' rdata Hvalid HSLP.
              apply nmp; clear nmp;
               abstract (
                  inversion mp; subst;
                  repeat match goal with
                           | _ => assumption
                           | [ H : _ |- _ ] => rewrite of_to_nonterminal in H by (first [ assumption | apply initial_nonterminals_correct'; assumption ])
                           | _ => solve [ exfalso; eauto with nocore ]
                         end
                ). }
            { clear -mp is_valid Hlen pf' rdata Hvalid_len.
              abstract (
                  inversion mp; clear mp; subst;
                  [ auto with nocore
                  | repeat match goal with
                             | [ H : is_true ?e, H' : context[?e] |- _ ] => rewrite H in H'
                             | [ H : context[andb _ true] |- _ ] => rewrite Bool.andb_true_r in H
                             | [ H : negb _ = false |- _ ] => apply Bool.negb_false_iff in H
                             | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true in H
                             | [ H : is_true false |- _ ] => clear -H; hnf in H
                             | [ H : false = true |- _ ] => solve [ inversion H ]
                             | _ => progress subst
                             | [ H : _ <= 0 |- _ ] => apply le_n_0_eq in H
                             | [ H : 0 = _ |- _ ] => symmetry in H
                             | [ H : nonterminals_length ?v = 0, H' : context[is_valid_nonterminal ?v ?nt] |- _ ]
                               => rewrite nonterminals_length_zero in H' by assumption
                             | [ H : is_true (is_valid_nonterminal initial_nonterminals_data (of_nonterminal _)) |- _ ]
                               => apply initial_nonterminals_correct in H
                             | [ H : In (to_nonterminal _) (Valid_nonterminals ?G) |- _ ]
                               => apply initial_nonterminals_correct' in H
                             | [ H : context[of_nonterminal (to_nonterminal _)] |- _ ]
                               => rewrite of_to_nonterminal in H by assumption
                           end ]
                ). }
          Defined.

          Definition parse_nonterminal_step_eq
                     (valid : nonterminals_listT)
                     (Hvalid_len : nonterminals_length valid <= valid_len)
                     (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                     (str : String)
                     (len : nat)
                     (Hlen : length str = len)
                     (pf pf' : len <= len0)
                     (nt : nonterminal_carrierT)
                     (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
          : (@parse_nonterminal_step valid Hvalid_len str len Hlen pf nt)
            = (BooleanRecognizer.parse_nonterminal_step (G := G) parse_nonterminal' valid str pf' nt)
                :> bool.
          Proof.
            eq_t;
            destruct (Utils.dec (is_valid_nonterminal initial_nonterminals_data nt)) as [Hvalid'|Hvalid']; simpl;
            [ subst; repeat eq_t'; try omega;
              (match goal with
                 | [ |- context[@parse_nonterminal' ?a ?b ?c] ]
                   => erewrite <- (@parse_productions'_eq _ _ (@parse_nonterminal' a b c) (@parse_nonterminal _ _ _ _))

               end;
               [ | intros; apply (@Hmatches (_, _)); assumption ]);
              repeat eq_t';
              try reflexivity;
              repeat eq_t'
            | ].
            { repeat f_equal.
              apply Le.le_proof_irrelevance. }
            { congruence. }
          Qed.
        End step.

        Section wf.
          Definition parse_nonterminal_or_abort
          : forall (p : nat * nat)
                   (valid : nonterminals_listT)
                   (Hvalid_len : nonterminals_length valid <= snd p)
                   (str : String) (len : nat)
                   (Hlen : length str = len)
                   (pf : len <= fst p)
                   (nt : nonterminal_carrierT),
              dec (minimal_parse_of_nonterminal (G := G) (fst p) valid str (to_nonterminal nt))
            := @Fix
                 (nat * nat)
                 _
                 (well_founded_prod_relation lt_wf lt_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

          Lemma parse_nonterminal_or_abort_eq
                (p : nat * nat)
                (valid : nonterminals_listT)
                (Hvalid_len : nonterminals_length valid <= snd p)
                (str : String) (len : nat)
                (Hlen : length str = len)
                (pf : len <= fst p)
                (nt : nonterminal_carrierT)
                (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
          : (@parse_nonterminal_or_abort p valid Hvalid_len str len Hlen pf nt)
            = (BooleanRecognizer.parse_nonterminal_or_abort (G := G) p valid str pf nt)
                :> bool.
          Proof.
            expand_once.
            revert valid Hvalid_len str len Hlen pf nt Hvalid.
            match goal with
              | [ |- appcontext[Fix ?Wf _ _ ?p] ]
                => induction (Wf p) as [?? IH]; intros
            end.
            symmetry;
              rewrite Fix5_eq
              by (intros; apply parse_nonterminal_step_ext; eauto with nocore);
              symmetry.
            destruct_head prod.
            erewrite <- parse_nonterminal_step_eq
              by first [ intros; eapply IH; eassumption
                       | assumption ].
            match goal with
              | [ |- bool_of_sum ?x = bool_of_sum ?y ]
                => destruct x, y; try reflexivity; exfalso; eauto with nocore
            end.
            Grab Existential Variables.
            assumption.
            assumption.
            assumption.
            assumption.
            assumption.
          Qed.

          Definition parse_nonterminal'
                     (str : String)
                     (nt : nonterminal_carrierT)
          : dec (minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data str (to_nonterminal nt)).
          Proof.
            destruct (Utils.dec (is_valid_nonterminal initial_nonterminals_data nt)) as [Hvalid|Hvalid].
            { eapply (@parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data));
              first [ reflexivity | eassumption ]. }
            { right; intro p.
              clear -Hvalid p rdata.
              abstract (
                  inversion p; subst; try omega;
                  repeat match goal with
                           | [ H : is_true (is_valid_nonterminal initial_nonterminals_data (of_nonterminal _)) |- _ ]
                             => apply initial_nonterminals_correct in H
                           | [ |- is_valid_nonterminal initial_nonterminals_data (of_nonterminal _) = true ]
                             => apply initial_nonterminals_correct
                           | [ H : In (to_nonterminal _) (Valid_nonterminals ?G) |- _ ]
                             => apply initial_nonterminals_correct' in H
                           | [ H : context[of_nonterminal (to_nonterminal _)] |- _ ]
                             => rewrite of_to_nonterminal in H by assumption
                           | _ => congruence
                           | [ H : _ = false |- _ ] => apply Bool.not_true_iff_false in H; apply H; clear H
                         end
                ). }
          Defined.

          Lemma parse_nonterminal'_eq
                (str : String)
                (nt : nonterminal_carrierT)
          : (@parse_nonterminal' str nt)
            = (BooleanRecognizer.parse_nonterminal' (G := G) str nt)
                :> bool.
          Proof.
            expand_once.
            destruct (Utils.dec (is_valid_nonterminal initial_nonterminals_data nt)) as [H|H].
            { repeat eq_t'.
              erewrite <- parse_nonterminal_or_abort_eq; first [ reflexivity | assumption ]. }
            { simpl.
              unfold BooleanRecognizer.parse_nonterminal_or_abort.
              rewrite Fix5_eq by (intros; apply parse_nonterminal_step_ext; assumption).
              unfold BooleanRecognizer.parse_nonterminal_step at 1.
              simpl.
              rewrite H, Bool.andb_false_r; simpl.
              edestruct lt_dec; try omega; simpl.
              reflexivity. }
          Qed.

          Definition parse_nonterminal
                     (str : String)
                     (nt : String.string)
          : dec (minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data str nt).
          Proof.
            destruct (parse_nonterminal' str (of_nonterminal nt)) as [p|p]; [ left | right ].
            { clear -p rdata.
              abstract (
                  rewrite to_of_nonterminal in p; [ assumption | ];
                  inversion p; subst; try omega;
                  repeat match goal with
                           | _ => assumption
                           | [ H : is_true (is_valid_nonterminal initial_nonterminals_data (of_nonterminal _)) |- _ ]
                             => apply initial_nonterminals_correct in H
                           | [ |- is_valid_nonterminal initial_nonterminals_data (of_nonterminal _) = true ]
                             => apply initial_nonterminals_correct
                           | [ H : In (to_nonterminal _) (Valid_nonterminals ?G) |- _ ]
                             => apply initial_nonterminals_correct' in H
                           | [ H : context[of_nonterminal (to_nonterminal _)] |- _ ]
                             => rewrite of_to_nonterminal in H by assumption
                         end
                ). }
            { intro p'; apply p; clear p.
              abstract (
                  rewrite to_of_nonterminal; [ assumption | ];
                  inversion p'; subst; try omega;
                  repeat match goal with
                           | _ => assumption
                           | [ H : is_true (is_valid_nonterminal initial_nonterminals_data (of_nonterminal _)) |- _ ]
                             => apply initial_nonterminals_correct in H
                           | [ |- is_valid_nonterminal initial_nonterminals_data (of_nonterminal _) = true ]
                             => apply initial_nonterminals_correct
                           | [ H : In (to_nonterminal _) (Valid_nonterminals ?G) |- _ ]
                             => apply initial_nonterminals_correct' in H
                           | [ H : context[of_nonterminal (to_nonterminal _)] |- _ ]
                             => rewrite of_to_nonterminal in H by assumption
                         end
                ). }
          Defined.

          Lemma parse_nonterminal_eq
                (str : String)
                (nt : String.string)
          : (@parse_nonterminal str nt)
            = (BooleanRecognizer.parse_nonterminal (G := G) str nt)
                :> bool.
          Proof.
            expand_once.
            repeat eq_t'.
            rewrite parse_nonterminal'_eq; reflexivity.
          Qed.
        End wf.
      End nonterminals.
    End parts.

    Section item.
      Context (str : String)
              (it : item Char).

      Definition parse_item : dec _
        := parse_item' (@parse_nonterminal' str) it.

      Lemma parse_item_eq
      : parse_item
        = (BooleanRecognizer.parse_item (G := G) str it)
            :> bool.
      Proof.
        apply parse_item'_eq_all, parse_nonterminal'_eq.
      Qed.
    End item.

    Section production.
      Context (str : String)
              (p : production Char)
              (Hreachable : production_is_reachableT G p).

      Definition parse_production : dec (minimal_parse_of_production (G := G) (length str) initial_nonterminals_data str p).
      Proof.
        eapply parse_production'; [ | reflexivity.. | assumption ].
        intros.
        eapply (@parse_nonterminal_or_abort (length str, _));
          simpl; try reflexivity; subst; assumption.
      Defined.

      Lemma parse_production_eq
      : parse_production
        = (BooleanRecognizer.parse_production (G := G) str p)
            :> bool.
      Proof.
        apply parse_production'_eq; simpl; intros; subst; simpl.
        erewrite <- parse_nonterminal_or_abort_eq by assumption.
        reflexivity.
      Qed.
    End production.

    Section productions.
      Context (str : String)
              (ps : productions Char)
              (Hreachable : productions_is_reachable ps).

      Definition parse_productions : dec (minimal_parse_of (G := G) (length str) initial_nonterminals_data str ps).
      Proof.
        eapply parse_productions'; [ | reflexivity.. | assumption ].
        intros.
        eapply (@parse_nonterminal_or_abort (length str, _));
          simpl; try reflexivity; subst; assumption.
      Defined.

      Lemma parse_productions_eq
      : parse_productions
        = (BooleanRecognizer.parse_productions (G := G) str ps)
            :> bool.
      Proof.
        apply parse_productions'_eq; simpl; intros; subst; simpl.
        erewrite <- parse_nonterminal_or_abort_eq by assumption.
        reflexivity.
      Qed.
    End productions.
  End min.
End recursive_descent_parser.
