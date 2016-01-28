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
Require Import Fiat.Common.UIP.
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

Local Ltac subst_bool_eq_proof :=
  idtac;
  match goal with
    | [ H : ?x = ?y :> bool, H' : ?x = ?y |- _ ]
      => assert (H = H') by apply UIP_bool; subst
    | [ H : is_true ?x, H' : ?x = true |- _ ]
      => assert (H = H') by apply UIP_bool; subst
    | [ H : is_true ?x, H' : is_true ?x |- _ ]
      => assert (H = H') by apply UIP_bool; subst
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
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} (G : grammar Char).
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ _ G data}
          {rdata : @parser_removal_dataT' _ G _}
          {gvalid : grammar_valid G}.
  Context (str : String).

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

  Lemma parse_complete_stabalize' {len0 valid str' it its}
        (n m : nat)
        (Hn : n >= length str')
        (Hm : m >= length str')
  : (minimal_parse_of_item (G := G) len0 valid (take n str') it
     * minimal_parse_of_production (G := G) len0 valid (drop n str') its)
    -> (minimal_parse_of_item (G := G) len0 valid (take m str') it
        * minimal_parse_of_production (G := G) len0 valid (drop m str') its).
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

  Definition parse_complete_stabalize'' {len0 valid str' it its}
        (n m : nat)
        (Hn : n >= length str')
        (Hm : m >= length str')
    := (@parse_complete_stabalize' len0 valid str' it its n m Hn Hm,
        @parse_complete_stabalize' len0 valid str' it its m n Hm Hn).

  Definition parse_complete_stabalize {len0 valid str' it its}
        (n : nat)
        (Hn : n >= length str')
    := @parse_complete_stabalize'' len0 valid str' it its n (S n) Hn (le_S _ _ Hn).

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
              | progress subst_bool_eq_proof
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
                                        | left H => @?L H
                                        | right H' => @?R H'
                                      end) = _ ]
                    => transitivity (match x with
                                       | left H => bool_of_sum (L H)
                                       | right H' => bool_of_sum (R H')
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
                  | [ H : ?x = cons _ _ |- appcontext[match ?x with _ => _ end] ] => rewrite H
                end
              | rewrite fold_left_orb_true
              | idtac;
                let LHS := match goal with |- ?LHS = ?RHS => LHS end in
                let RHS := match goal with |- ?LHS = ?RHS => RHS end in
                match RHS with
                  | context R[bool_of_sum ?f0]
                    => match f0 with
                         | ?f ?ae ?be ?ce ?de ?ee ?ge ?he
                           => match LHS with
                                | context L[f ?a ?b ?c ?d ?e ?g ?h]
                                  => unify a ae; unify b be; unify c ce; unify d de; unify e ee; unify g ge; unify h he;
                                     let v := fresh in
                                     set (v := f a b c d e g h);
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
                  | appcontext[match ?x with _ => _ end]
                    => let H := match goal with
                                  | [ H : ?x = cons _ _ |- _ ] => H
                                end in
                       etransitivity; [ | rewrite H; reflexivity ]
                end
              | idtac;
                let LHS := match goal with |- ?LHS = ?RHS => LHS end in
                let RHS := match goal with |- ?LHS = ?RHS => RHS end in
                match LHS with
                | match Utils.dec ?x with _ => _ end
                  => match RHS with
                     | appcontext[x]
                       => destruct (Utils.dec x)
                     end
                end
              | idtac;
                match goal with
                | [ H : ?x = true |- context[?x] ] => rewrite H
                | [ H : ?x = false |- context[?x] ] => rewrite H
                end ].

      Local Ltac eq_t := expand_once; repeat eq_t'.

      (** Here are some general tactics to do variadic list_rect reasoning.  Unfortunately, they're really slow (~ 20 s), so we don't use them. *)
      Local Ltac curry_do_change HS :=
        idtac;
        match HS with
          | appcontext HS'[list_rect ?P ?N ?C]
            => (let P0 := fresh in
                let N0 := fresh in
                let C0 := fresh in
                (*set (P0 := P);*)
                set (N0 := N);
                set (C0 := C);
                let HS'' := context HS'[list_rect P(*0*) N0 C0] in
                change HS with HS'')
        end.

      Local Ltac pre_pre_curry_func :=
        idtac;
        let LHS := match goal with |- bool_of_sum ?LHS = ?RHS => LHS end in
        let RHS := match goal with |- bool_of_sum ?LHS = ?RHS => RHS end in
        curry_do_change LHS;
          curry_do_change RHS.

      Local Ltac pre_curry_func cont :=
        idtac;
        let LHS := match goal with |- bool_of_sum ?LHS = ?RHS => LHS end in
        let RHS := match goal with |- bool_of_sum ?LHS = ?RHS => RHS end in
        let ls := match LHS with
                    | appcontext[list_rect ?P ?N ?C ?ls] => ls
                  end in
        let LRL := match LHS with
                     | appcontext[list_rect ?P ?N ?C] => constr:(list_rect P N C)
                   end in
        let LRR := match RHS with
                     | appcontext[list_rect ?P ?N ?C] => constr:(list_rect P N C)
                   end in
        let F := fresh "F" in
        let G := fresh "G" in
        let F' := fresh "F'" in
        let G' := fresh "G'" in
        set (F := LRL);
          set (G := LRR);
          set (F' := fun ls (_ : unit) => F ls);
          set (G' := fun ls (_ : unit) => G ls);
          change (F ls) with (F' ls tt);
          change (G ls) with (G' ls tt);
          subst F G;
          cont F' G'.
      Local Ltac curry_func' F G n :=
        idtac;
        let LHS := match goal with |- bool_of_sum ?LHS = ?RHS => LHS end in
        let RHS := match goal with |- bool_of_sum ?LHS = ?RHS => RHS end in
        let ls := match LHS with
                    | appcontext[F ?ls ?x0 ?x] => ls
                  end in
        let x0 := match LHS with
                    | appcontext[F ?ls ?x0 ?x] => x0
                  end in
        let al := match LHS with
                    | appcontext[F ?ls ?x0 ?x] => x
                  end in
        let ar := match RHS with
                    | appcontext[G ?ls ?x0 ?x] => x
                  end in
        let T := (type of F) in
        let P := match (eval cbv beta in T) with
                   | forall (ls : ?lsT) (x0 : @?T ls) (y0 : @?T' ls x0), _ => T'
                 end in
        let F' := fresh "F'" in
        let G' := fresh "G'" in
        first [ constr_eq al ar;
                first [ set (F' := fun ls v => F ls (fst v) (snd v));
                        set (G' := fun ls (v : sigT (P ls)) => G ls (fst v) (snd v));
                        progress change (F ls x0 al) with (F' ls (x0, al));
                        progress change (G ls x0 ar) with (G' ls (x0, ar))
                      | set (F' := fun ls (v : sigT (P ls)) => F ls (projT1 v) (projT2 v));
                        set (G' := fun ls (v : sigT (P ls)) => G ls (projT1 v) (projT2 v));
                        progress change (F ls x0 al) with (F' ls (existT (P ls) x0 al));
                        progress change (G ls x0 ar) with (G' ls (existT (P ls) x0 ar)) ];
                try subst F;
                try subst G;
                idtac n
              | not constr_eq al ar;
                first [ set (F' := fun ls v => F ls (fst v) (snd v));
                        set (G' := fun ls v => G ls (fst v));
                        progress change (F ls x0 al) with (F' ls (x0, al));
                        progress change (G ls x0) with (G' ls (x0, al))
                      | set (F' := fun ls (v : sigT (P ls)) => F ls (projT1 v) (projT2 v));
                        set (G' := fun ls (v : sigT (P ls)) => G ls (projT1 v));
                        progress change (F ls x0 al) with (F' ls (existT (P ls) x0 al));
                        progress change (G ls x0) with (G' ls (existT (P ls) x0 al)) ];
                try subst F;
                try subst G ];
          cbv beta in *;
          try curry_func' F' G' (S n).
      Local Ltac curry_list_rect := pre_pre_curry_func; pre_curry_func ltac:(fun F G => curry_func' F G 0).
      Local Ltac post_resolve_list_rect :=
        idtac;
        (lazymatch goal with
        | [ |- bool_of_sum (?F ?ls ?x) = ?G ?ls ?x ]
          => (let y := fresh in
              let IH := fresh in
              refine (list_rect
                        (fun ls' => forall x', bool_of_sum (F ls' x') = G ls' x')
                        _
                        _
                        ls x);
              subst F G;
              cbv beta;
              [ intro y;
                let LHS := match goal with |- bool_of_sum ?LHS = ?RHS => LHS end in
                let RHS := match goal with |- bool_of_sum ?LHS = ?RHS => RHS end in
                match LHS with
                  | appcontext[list_rect _ ?N ?C]
                    => subst N
                end;
                  match RHS with
                    | appcontext[list_rect _ ?N ?C]
                      => subst N
                  end;
                  simpl @list_rect;
                  revert y
              | intros ?? IH y;
                let LHS := match goal with |- bool_of_sum ?LHS = ?RHS => LHS end in
                let RHS := match goal with |- bool_of_sum ?LHS = ?RHS => RHS end in
                let C := match LHS with | appcontext[list_rect _ ?N ?C] => C end in
                let C' := match RHS with | appcontext[list_rect _ ?N ?C] => C end in
                simpl @list_rect;
                  unfold C at 1, C' at 1;
                  revert y ];
              repeat match goal with
                       | [ |- forall (x : sigT ?P), _ ] => intros_destruct; simpl
                       | [ |- forall (x : _ * _), _ ] => intros_destruct; simpl
                     end;
              [
              | repeat match type of IH with
                         | forall (x : sigT ?P), _
                           => specialize (fun a b => IH (existT P a b)); simpl in IH
                         | forall (x : _ * _), _
                           => specialize (fun a b => IH (a, b)); simpl in IH
                       end ];
              intros
             )
         end).
      Local Ltac eq_list_rect_slow :=
        curry_list_rect; post_resolve_list_rect.

      (** And here's the really fast specialized version *)
      Local Ltac eq_list_rect
        := (idtac;
            lazymatch goal with
            | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls ?a ?b ?c ?d ?e ?f ?g ?h) = list_rect ?P' ?N' ?C' ?ls ?a ?e ?f ?h ]
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
                            (fun ls' => forall a' b' c' d' e' f' g' h' h'',
                                          bool_of_sum (list_rect P0 N0 C0 ls' a' b' c' d' e' f' g' h')
                                          = list_rect P1 N1 C1 ls' a' e' f' h'')
                            _
                            _
                            ls a b c d e f g h h);
                  simpl @list_rect;
                  [ subst N0 N1; simpl; intros
                  | intros; unfold C0 at 1, C1 at 1; simpl ])
            | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls ?a ?b ?c ?d ?e ?f) = list_rect ?P' ?N' ?C' ?ls ?a ?c ?d ?f ]
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
                                          = list_rect P1 N1 C1 ls' a' c' d' f'')
                            _
                            _
                            ls a b c d e f f);
                  simpl @list_rect;
                  [ subst N0 N1; simpl; intros
                  | intros; unfold C0 at 1, C1 at 1; simpl ])
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

      Local Ltac eq_list_rect_prop1 PH Hv
        := (idtac;
            lazymatch goal with
            | [ |- bool_of_sum (list_rect ?P ?N ?C ?ls ?a ?b ?c ?d ?e ?f) = list_rect ?P' ?N' ?C' ?ls ?a ?c ?d ?f ]
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
                            (fun ls' => forall a' b' c' d' e' f' f'',
                                          PH a'
                                          -> bool_of_sum (list_rect P0 N0 C0 ls' a' b' c' d' e' f')
                                             = list_rect P1 N1 C1 ls' a' c' d' f'')
                            _
                            _
                            ls a b c d e f f Hv);
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
        repeat match goal with
               | [ H : andb _ _ = true |- _ ] => apply char_at_matches_is_char_no_ex in H; [ | assumption ]
               | [ H : and _ _ |- _ ] => let H0 := fresh in
                                         let H1 := fresh in
                                         destruct H as [H0 H1]; try clear H
               | [ H : or _ _ |- _ ] => let H0 := fresh in destruct H as [H0|H0]; try clear H
               | [ H : beq_nat _ _ = true |- _ ] => apply NPeano.Nat.eqb_eq in H
               | _ => progress subst
               | _ => progress simpl in *
               | _ => congruence
               | [ H : context[match get ?n ?s with _ => _ end] |- _ ]
                 => destruct (get n s) eqn:?
               | _ => eassumption
               | [ H : minimal_parse_of_item _ _ _ (NonTerminal ?nt) |- _ ]
                 => assert (List.In nt (Valid_nonterminals G));
                   inversion H; clear H
               | [ H : minimal_parse_of_item _ _ _ (Terminal _) |- _ ]
                 => inversion H; clear H
               | [ H : minimal_parse_of_nonterminal _ _ _ ?nt |- List.In ?nt (Valid_nonterminals G) ]
                 => inversion H; clear H
               | [ H : is_true (is_char (substring _ 0 _) _) |- _ ] =>
                 apply length_singleton in H
               | [ H : context[length (substring _ 0 _)] |- _ ]
                 => rewrite take_length in H
               | [ H : beq_nat ?len 1 = false,
                       H' : ?offset + ?len <= length ?str,
                            H'' : is_true (is_char (substring ?offset ?len ?str) _)
                   |- _ ]
                 => apply length_singleton in H''; rewrite substring_length in H''
               | [ H : appcontext[min] |- _ ] => rewrite Min.min_l in H by omega
               | [ H : appcontext[min] |- _ ] => rewrite Min.min_r in H by omega
               | [ H : _ |- _ ] => rewrite NPeano.Nat.add_sub in H
               | [ H : andb (beq_nat _ 1) (char_at_matches _ _ _) = false |- False ] => contradict H
               | [ |- _ <> false ] => apply Bool.not_false_iff_true
               | [ |- andb (beq_nat _ 1) (char_at_matches _ _ _) = true ] => apply char_at_matches_is_char
               | [ |- ex _ ] => eexists; split; eassumption
               | [ H : context[to_nonterminal (of_nonterminal _)] |- _ ]
                 => rewrite to_of_nonterminal in H by assumption
               | [ H : minimal_parse_of_nonterminal _ _ _ (to_nonterminal (of_nonterminal ?nt)) |- _ ]
                 => assert (List.In nt (Valid_nonterminals G));
                   [ inversion H; clear H
                   | rewrite to_of_nonterminal in H by assumption ]
               | [ H : is_true (is_valid_nonterminal _ (of_nonterminal _)) |- _ ]
                 => apply initial_nonterminals_correct in H
               | [ H : List.In (to_nonterminal _) _ |- _ ]
                 => apply initial_nonterminals_correct' in H
               end.

      Section item.
        Context {len0 valid}
                (offset : nat) (len : nat)
                (Hlen : len = 0 \/ offset + len <= length str)
                (str_matches_nonterminal'
                 : nonterminal_carrierT -> bool)
                (str_matches_nonterminal
                 : forall nt : nonterminal_carrierT,
                     dec (minimal_parse_of_nonterminal (G := G) len0 valid (substring offset len str) (to_nonterminal nt))).

        Section valid.
          Context (Hmatches
                   : forall nt,
                       is_valid_nonterminal initial_nonterminals_data nt
                       -> str_matches_nonterminal nt = str_matches_nonterminal' nt :> bool)
                  (it : item Char)
                  (Hvalid : item_valid it).

          Definition parse_item'
          : dec (minimal_parse_of_item (G := G) len0 valid (substring offset len str) it).
          Proof.
            clear Hvalid.
            refine (match it return dec (minimal_parse_of_item len0 valid (substring offset len str) it) with
                      | Terminal P => if Sumbool.sumbool_of_bool (EqNat.beq_nat len 1 && char_at_matches offset str P)%bool
                                      then inl (match get offset str as g return get offset str = g -> _ with
                                                | Some ch => fun H => MinParseTerminal _ _ _ ch _ _ _
                                                | None => fun _ => !
                                                end eq_refl)
                                      else inr (fun _ => !)
                      | NonTerminal nt => if str_matches_nonterminal (of_nonterminal nt)
                                          then inl (MinParseNonTerminal _)
                                          else inr (fun _ => !)
                    end);
              clear str_matches_nonterminal Hmatches;
              t_item str_matches_nonterminal'.
          Defined.

          Definition parse_item'_eq
          : parse_item' = BooleanRecognizer.parse_item' str str_matches_nonterminal' offset len it :> bool.
          Proof. eq_t. Qed.
        End valid.

        Section all.
          Context (Hmatches
                   : forall nt,
                       str_matches_nonterminal nt = str_matches_nonterminal' nt :> bool)
                  (it : item Char).

          Definition parse_item'_eq_all
          : parse_item' it = BooleanRecognizer.parse_item' str str_matches_nonterminal' offset len it :> bool.
          Proof. eq_t. Qed.
        End all.
      End item.

      Definition parse_item'_ext
                 {len0 valid}
                 (offset len : nat)
                 (Hlen : len = 0 \/ offset + len <= length str)
                 (str_matches_nonterminal str_matches_nonterminal'
                  : forall nt : nonterminal_carrierT,
                      dec (minimal_parse_of_nonterminal (G := G) len0 valid (substring offset len str) (to_nonterminal nt)))
                 (ext : forall nt,
                          str_matches_nonterminal nt = str_matches_nonterminal' nt)
                (it : item Char)
      : parse_item' offset Hlen str_matches_nonterminal it
        = parse_item' offset Hlen str_matches_nonterminal' it.
      Proof.
        expand_both_once; destruct it; try reflexivity; [].
        rewrite ext.
        clear ext str_matches_nonterminal.
        reflexivity.
      Qed.

      Section production.
        Context {len0 valid}
                (parse_nonterminal
                 : forall (offset : nat) (len : nat) (Hlen : len = 0 \/ offset + len <= length str) (pf : len <= len0) (nt : nonterminal_carrierT),
                    dec (minimal_parse_of_nonterminal (G := G) len0 valid (substring offset len str) (to_nonterminal nt))).

        Lemma Hlen_helper {offset len} (Hlen : len = 0 \/ offset + len <= length str)
          : length (substring offset len str) = len.
        Proof.
          destruct Hlen; subst; rewrite substring_length; simpl;
          apply Min.min_case_strong; omega.
        Qed.

        Lemma dec_in_helper {ls it its offset len}
              (Hlen : len = 0 \/ offset + len <= length str)
        : iffT {n0 : nat &
                     (In (min (length (substring offset len str)) n0) (map (min (length (substring offset len str))) ls) *
                      minimal_parse_of_item (G := G) len0 valid (take n0 (substring offset len str)) it *
                      minimal_parse_of_production (G := G) len0 valid (drop n0 (substring offset len str)) its)%type}
               {n0 : nat &
                     (In n0 ls *
                      (minimal_parse_of_item (G := G) len0 valid (substring offset (min n0 len) str) it *
                       minimal_parse_of_production (G := G) len0 valid (substring (offset + n0) (len - n0) str) its))%type}.
        Proof.
          rewrite Hlen_helper by assumption.
          split; first [ intros [n [[H0 H1] H2]]
                       | intros [n [H0 [H1 H2]]] ].
          { destruct (le_lt_dec len n) as [pf|pf].
            { rewrite Min.min_l in H0 by assumption.
              clear -H0 H1 H2 rdata cdata pf HSLP.
              induction ls as [|x xs IHxs]; destruct_head_hnf False.
              destruct (le_lt_dec len x).
              { exists x.
                repeat split.
                { left; reflexivity. }
                { eapply expand_minimal_parse_of_item_beq; [ .. | eassumption ].
                  rewrite take_take.
                  rewrite !Min.min_r by omega.
                  reflexivity. }
                { eapply expand_minimal_parse_of_production_beq; [ .. | eassumption ].
                  rewrite drop_take, StringLike.drop_drop.
                  apply bool_eq_empty; rewrite substring_length; apply Min.min_case_strong; omega. } }
              { simpl in *.
                rewrite Min.min_r in H0 by omega.
                destruct IHxs as [n' [IH0 [IH1 IH2]]].
                { destruct H0; try omega; assumption. }
                { exists n'; repeat split; try assumption.
                  right; assumption. } } }
            { exists n; repeat split; try assumption.
              { apply in_map_iff in H0.
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
                       end. }
              { eapply expand_minimal_parse_of_item_beq; [ .. | eassumption ].
                rewrite take_take.
                reflexivity. }
              { eapply expand_minimal_parse_of_production_beq; [ .. | eassumption ].
                rewrite drop_take, StringLike.drop_drop.
                rewrite (plus_comm offset); reflexivity. } } }
          { exists n; repeat split; try assumption.
            { apply in_map; assumption. }
            { eapply expand_minimal_parse_of_item_beq; [ .. | eassumption ].
              rewrite take_take.
              reflexivity. }
            { eapply expand_minimal_parse_of_production_beq; [ .. | eassumption ].
              rewrite drop_take, StringLike.drop_drop.
              rewrite (plus_comm offset); reflexivity. } }
        Defined.

        Local Opaque dec_in_helper.

        Lemma parse_production'_helper {offset len it its} (pf : length (substring offset len str) <= len0)
        : dec {n0 : nat &
                    (minimal_parse_of_item (G := G) len0 valid (take n0 (substring offset len str)) it *
                     minimal_parse_of_production (G := G) len0 valid (drop n0 (substring offset len str)) its)%type}
          -> dec (minimal_parse_of_production (G := G) len0 valid (substring offset len str) (it :: its)).
        Proof.
          intros [H|H]; [ left; destruct H as [n [??]] | right; intro p; apply H; clear H ].
          { econstructor; eassumption. }
          { clear -p; abstract (inversion p; subst; eexists; split; eassumption). }
        Defined.

        Lemma minus_le {x y z} (H : x <= z) : x - y <= z.
        Proof. omega. Qed.

        Lemma eq_le_trans {x y z} (H : x = y) (H' : y <= z) : x <= z.
        Proof. subst; assumption. Defined.

        Lemma min_le_r {x y z} (H : y <= z) : min x y <= z.
        Proof. apply Min.min_case_strong; omega. Qed.

        Lemma lift_le {offset len n length_str} (H : len = 0 \/ offset + len <= length_str)
          : len - n = 0 \/ offset + n + (len - n) <= length_str.
        Proof.
          destruct H;
          [ left; subst
          | destruct (le_lt_dec n len); [ right | left ] ];
          omega.
        Qed.

        Lemma lift_le_min {offset n len length_str} (H : len = 0 \/ offset + len <= length_str)
          : min n len = 0 \/ offset + min n len <= length_str.
        Proof.
          apply Min.min_case_strong; [ | intro; assumption ].
          destruct H; subst; [ left | right ]; omega.
        Qed.

        Lemma lift_parse_prod {str' offset len a it its}
              (H : (minimal_parse_of_item
                      (G := G)
                      len0 valid
                      (substring offset (min a len) str') it *
                   minimal_parse_of_production
                     (G := G)
                     len0 valid
                     (substring (offset + a) (len - a) str') its)%type)
          : minimal_parse_of_item
              (G := G)
              len0 valid
              (take a (substring offset len str')) it *
            minimal_parse_of_production
              (G := G)
              len0 valid
              (drop a (substring offset len str')) its.
        Proof.
          destruct H as [pi pp]; split.
          { eapply expand_minimal_parse_of_item_beq; [ | eassumption ].
            rewrite take_take; reflexivity. }
          { eapply expand_minimal_parse_of_production_beq; [ | eassumption ].
            rewrite drop_take, StringLike.drop_drop, (plus_comm a offset).
            reflexivity. }
        Defined.

        Local Ltac parse_production'_for_t' :=
          idtac;
          match goal with
            | [ H : (beq_nat _ _) = true |- _ ] => apply EqNat.beq_nat_true in H
            | _ => progress subst
            | _ => solve [ constructor; assumption
                         | constructor;
                           rewrite substring_length; apply Min.min_case_strong; omega ]
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
            | [ H : or _ _ |- _ ] => let H0 := fresh in destruct H as [H0|H0]; try clear H
            | [ H : length (substring _ _ _) = 0 |- _ ] => rewrite substring_length in H
            | [ H : appcontext[min] |- _ ] => rewrite Min.min_l in H by omega
            | [ H : appcontext[min] |- _ ] => rewrite Min.min_r in H by omega
            | [ H : _ |- _ ] => rewrite NPeano.Nat.add_sub in H
          end.
        Local Ltac parse_production'_for_t := repeat parse_production'_for_t'.

        Definition full_production_carrierT_reachableT (prod_idx : production_carrierT)
          := { nt : _
           & { prefix_count : _
           & { pre_prod_idx : _
             & (List.In nt (Valid_nonterminals G)
                * (apply_n prefix_count production_tl pre_prod_idx = prod_idx)
                * List.InT pre_prod_idx (nonterminal_to_production (of_nonterminal nt)))%type } } }.

        Lemma production_reachable_convert idx p
              (H : to_production idx = p)
              (H' : full_production_carrierT_reachableT idx)
        : production_is_reachable G p.
        Proof.
          subst.
          destruct H' as [nt H']; exists nt.
          destruct H' as [count [idx' [[Hvalid H0] H1]]]; subst.
          erewrite <- nonterminal_to_production_correct by assumption.
          induction (nonterminal_to_production (of_nonterminal nt)) as [|x xs IHxs]; simpl in *.
          { destruct_head False. }
          { destruct_head or; destruct_head sum; subst; specialize_by assumption.
            { clear IHxs.
              induction count as [|count IHcount]; simpl.
              { eexists nil; simpl.
                split; [ assumption | left; reflexivity ]. }
              { rewrite apply_n_commute, production_tl_correct.
                destruct IHcount as [prefix IHcount].
                match goal with
                  | [ |- context[_ ++ tl ?ls] ]
                    => exists (match ls with
                                 | nil => prefix
                                 | x::_ => prefix ++ [x]
                               end);
                      destruct ls eqn:Heq; simpl in *
                end;
                  rewrite ?app_nil_r, <- ?app_assoc in IHcount;
                  rewrite ?app_nil_r, <- ?app_assoc;
                  assumption. } }
            { destruct IHxs as [prefix [H0 H1]].
              exists prefix.
              split; [ assumption | right; assumption ]. } }
        Qed.

        Lemma full_production_carrierT_reachableT_tl {idx}
              (H : full_production_carrierT_reachableT idx)
        : full_production_carrierT_reachableT (production_tl idx).
        Proof.
          destruct H as [nt H]; exists nt.
          destruct H as [count H]; exists (S count).
          destruct H as [idx' H]; exists idx'.
          destruct_head and; destruct_head Datatypes.prod; simpl; repeat split; try assumption.
          rewrite apply_n_commute; apply f_equal; assumption.
        Qed.

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Definition parse_production'_for
                 (splits : production_carrierT -> String -> nat -> nat -> list nat)
                 (Hsplits : forall offset len it its idx pf',
                     len = 0 \/ offset + len <= length str
                     -> full_production_carrierT_reachableT idx
                     -> production_carrier_valid idx
                     -> to_production idx = it::its
                     -> split_list_completeT_for (len0 := len0) (G := G) (valid := valid) it its (substring offset len str) pf' (splits idx str offset len))
                 (offset len : nat)
                 (Hlen : len = 0 \/ offset + len <= length str)
                 (pf : len <= len0)
                 (prod_idx : production_carrierT)
                 (Hreachable : full_production_carrierT_reachableT prod_idx)
                 (Hvalid : production_carrier_valid prod_idx)
        : dec (minimal_parse_of_production (G := G) len0 valid (substring offset len str) (to_production prod_idx)).
        Proof.
          revert offset len Hlen pf.
          refine
            (list_rect
               (fun ps =>
                  forall (idx : production_carrierT)
                         (Hreachable : full_production_carrierT_reachableT idx)
                         (Hvalid : production_carrier_valid idx)
                         (Hidx : to_production idx = ps)
                         (offset len : nat)
                         (Hlen : len = 0 \/ offset + len <= length str)
                         (pf : len <= len0),
                    dec (minimal_parse_of_production (G := G) len0 valid (substring offset len str) ps))
               ((** 0-length production, only accept empty *)
                 fun idx Hidx Hreachable Hvalid offset len Hlen pf
                 => match Utils.dec (beq_nat len 0) with
                      | left H => inl _
                      | right H => inr (fun p => _)
                    end)
               (fun it its parse_production' idx Hreachable Hvalid Hidx offset len Hlen pf
                => parse_production'_helper
                     (eq_le_trans (Hlen_helper Hlen) pf)
                     (let parse_item := (fun n => parse_item' offset (len := min n len) (lift_le_min Hlen) (parse_nonterminal offset (len := min n len) (lift_le_min Hlen) (min_le_r pf)) it) in
                      let parse_production := (fun n : nat => parse_production' (production_tl idx) (full_production_carrierT_reachableT_tl Hreachable) (production_tl_valid _ Hvalid) (eq_trans (production_tl_correct _) (f_equal (@tl _) Hidx)) (offset + n) (len - n) (lift_le Hlen) (minus_le pf)) in
                      match dec_In
                              (fun n => dec_prod (parse_item n) (parse_production n))
                              (splits idx str offset len)
                      with
                        | inl p => inl (existT _ (projT1 p) (lift_parse_prod (snd (projT2 p))))
                        | inr p
                          => let H := (_ : split_list_completeT_for (G := G) (len0 := len0) (valid := valid) it its (substring offset len str) (eq_le_trans (Hlen_helper Hlen) pf) (splits idx str offset len)) in
                             inr (fun p' => p (fst (dec_in_helper Hlen) (H p')))
                      end))
               (to_production prod_idx)
               prod_idx
               Hreachable
               Hvalid
               eq_refl);
            [ clear parse_nonterminal Hsplits splits rdata cdata
            | clear parse_nonterminal Hsplits splits rdata cdata
            | clear parse_item parse_production ];
            (* abstract *) try solve [ parse_production'_for_t ]. (* abstract gives universe inconsistences on Coq <= 8.5rc1 *)
        Defined.

        Definition parse_production'_for_eq
                   (parse_nonterminal'
                    : forall (offset len : nat) (pf : len <= len0) (nt : nonterminal_carrierT),
                        bool)
                   (parse_nonterminal_eq
                    : forall offset len Hlen pf nt,
                        is_valid_nonterminal initial_nonterminals_data nt
                        -> @parse_nonterminal offset len Hlen pf nt = parse_nonterminal' offset len pf nt :> bool)
                   (splits : production_carrierT -> String -> nat -> nat -> list nat)
                   (Hsplits : forall offset len it its idx pf',
                       len = 0 \/ offset + len <= length str
                       -> full_production_carrierT_reachableT idx
                       -> production_carrier_valid idx
                       -> to_production idx = it::its
                       -> split_list_completeT_for (len0 := len0) (G := G) (valid := valid) it its (substring offset len str) pf' (splits idx str offset len))
                   (offset len : nat)
                   (Hlen : len = 0 \/ offset + len <= length str)
                   (pf pf' : len <= len0)
                   (prod_idx : production_carrierT)
                   (Hreachable : full_production_carrierT_reachableT prod_idx)
                   (Hvalid : production_carrier_valid prod_idx)
        : parse_production'_for splits Hsplits offset Hlen pf Hreachable Hvalid = BooleanRecognizer.parse_production'_for str parse_nonterminal' splits offset pf' prod_idx :> bool.
        Proof.
          eq_t; eq_list_rect; repeat eq_t'; [].
          expand_onceL; repeat eq_t'; [].
          expand_onceL; eq_list_rect_fold_left_orb; repeat eq_t'; [].
          let parse_nt := match goal with
                          | [ |- appcontext[BooleanRecognizer.parse_item' str ?pnt] ] => pnt
                          end in
          erewrite <- (parse_item'_eq _ _ parse_nt);
            [
            | intros; apply parse_nonterminal_eq; assumption
            | idtac;
              match goal with
                | [ H : to_production ?idx = ?a :: ?ls,
                        Hreachable : full_production_carrierT_reachableT ?idx |- item_valid ?a ]
                  => let H' := fresh in
                     assert (H' : production_is_reachable G (a::ls)) by (eapply production_reachable_convert; eassumption);
                       apply (@reachable_production_valid _ G _ gvalid), hd_production_valid in H'; assumption
              end ];
            [].
          repeat eq_t'; simpl; repeat eq_t'; [].
          match goal with H : _ |- _ => erewrite <- H; repeat eq_t' end.
        Qed.

        Lemma split_list_completeT_production_is_reachable
              {it its offset len pf splits idx}
              (Hlen : len = 0 \/ offset + len <= length str)
              (H : split_list_completeT (G := G) splits)
              (Hreachable : full_production_carrierT_reachableT idx)
              (Hvalid : production_carrier_valid idx)
              (Heq : to_production idx = it::its)
        : split_list_completeT_for (G := G) (len0 := len0) (valid := valid) it its (substring offset len str) pf (splits idx str offset len).
        Proof.
          specialize (fun nt Hvalid => H len0 valid str offset len pf nt Hvalid Hlen).
          hnf in Hreachable.
          destruct Hreachable as [nt [count [idx' [[Hr0 Hr1] Hr2]]]].
          specialize (H nt).
          erewrite <- nonterminal_to_production_correct in H by assumption.
          apply initial_nonterminals_correct in Hr0.
          specialize_by assumption.
          subst.
          generalize dependent (nonterminal_to_production (of_nonterminal nt)).
          intro p; induction p as [|x xs IHxs]; simpl.
          { intros ? []. }
          { intros H [H'|H']; subst;
            destruct_head prod;
            specialize_by assumption; trivial; [].
            clear dependent xs.
            generalize dependent idx'.
            induction count as [|count IHcount]; simpl in *; intros.
            { repeat match goal with
                       | [ H : ?x = _::_, H' : context[match ?x with _ => _ end] |- _ ] => rewrite H in H'
                       | [ H : _ |- _ ] => apply Forall_tails_id in H
                       | _ => solve [ eauto with nocore ]
                     end. }
            { specialize (IHcount (production_tl idx')).
              specialize_by assumption.
              rewrite production_tl_correct in IHcount.
              apply IHcount; clear IHcount.
              destruct (to_production idx');
                simpl in *; destruct_head prod; trivial. } }
        Qed.

        Definition parse_production'
                 (offset len : nat)
                 (Hlen : len = 0 \/ offset + len <= length str)
                 (pf : len <= len0)
                 (prod_idx : production_carrierT)
                 (Hreachable : full_production_carrierT_reachableT prod_idx)
                 (Hvalid : production_carrier_valid prod_idx)
        : dec (minimal_parse_of_production (G := G) len0 valid (substring offset len str) (to_production prod_idx)).
        Proof.
          refine (parse_production'_for _ _ _ Hlen pf Hreachable Hvalid).
          intros offset' len' it' its' pidx' pf'' Hlen'.
          exact (@split_list_completeT_production_is_reachable it' its' offset' len' pf'' _ pidx' Hlen' split_string_for_production_complete).
        Defined.

        Definition parse_production'_eq
                    (parse_nonterminal'
                    : forall (offset len : nat) (pf : len <= len0) (nt : nonterminal_carrierT),
                        bool)
                   (parse_nonterminal_eq
                    : forall offset len Hlen pf nt,
                        is_valid_nonterminal initial_nonterminals_data nt
                        -> @parse_nonterminal offset len Hlen pf nt = parse_nonterminal' offset len pf nt :> bool)
                   (offset len : nat)
                   (Hlen : len = 0 \/ offset + len <= length str)
                   (pf pf' : len <= len0)
                   (prod_idx : production_carrierT)
                   (Hreachable : full_production_carrierT_reachableT prod_idx)
                   (Hvalid : production_carrier_valid prod_idx)
        : parse_production' offset Hlen pf Hreachable Hvalid = BooleanRecognizer.parse_production' str parse_nonterminal' offset pf' prod_idx :> bool.
        Proof.
          apply parse_production'_for_eq; try assumption.
        Qed.
      End production.

      Section productions.
        Context {len0 valid}
                (parse_nonterminal'
                 : forall (offset len : nat),
                     len <= len0
                     -> forall nt : nonterminal_carrierT,
                          bool)
                (parse_nonterminal
                 : forall (offset len : nat)
                          (Hlen : len = 0 \/ offset + len <= length str)
                          (pf : len <= len0)
                          (nt : nonterminal_carrierT),
                     dec (minimal_parse_of_nonterminal (G := G) len0 valid (substring offset len str) (to_nonterminal nt)))
                (Hmatches
                 : forall (offset len : nat)
                          (Hlen : len = 0 \/ offset + len <= length str)
                          (pf : len <= len0)
                          (nt : nonterminal_carrierT)
                          (Hvalid : is_valid_nonterminal initial_nonterminals_data nt),
                     parse_nonterminal offset len Hlen pf nt = parse_nonterminal' offset len pf nt :> bool)
                (offset len : nat).

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
                        |- full_production_carrierT_reachableT _ ]
                      => exists (projT1 Hreachable); destruct Hreachable as [nt Hreachable]; simpl
                    (*| [ Hreachable : productions_is_reachable (?p :: ?ps)
                        |- production_is_reachableT ?G ?p ]
                      => exists (projT1 Hreachable); destruct Hreachable as [nt Hreachable]; simpl*)
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
                    | _ => progress simpl in *
                  end ].

        Definition full_productions_carrierT_reachableT (prods_idx : list production_carrierT)
          := { nt : _
           & { prefix : _
             | List.In nt (Valid_nonterminals G)
               /\ prefix ++ prods_idx = nonterminal_to_production (of_nonterminal nt) } }.

        Lemma invert_full_productions_carrierT_reachableT p ps
              (H : full_productions_carrierT_reachableT (p::ps))
        : (full_production_carrierT_reachableT p * full_productions_carrierT_reachableT ps)%type.
        Proof.
          destruct H as [nt [prefix [H0 H1]]];
          split; exists nt;
          [ exists 0; exists p; simpl; repeat split; try assumption
          | exists (prefix ++ [p]); rewrite <- app_assoc; simpl; split; assumption ].
          rewrite <- H1.
          clear.
          induction prefix; simpl in *; [ left | right ]; trivial.
        Qed.

        Definition parse_productions'
                   (Hlen : len = 0 \/ offset + len <= length str)
                   (pf : len <= len0)
                   (prods : list production_carrierT)
                   (Hreachable : full_productions_carrierT_reachableT prods)
                   (Hvalid : List.Forall production_carrier_valid prods)
        : dec (minimal_parse_of (G := G) len0 valid (substring offset len str) (List.map to_production prods)).
        Proof.
          revert prods Hreachable Hvalid.
          refine (list_rect
                    (fun prods
                     => full_productions_carrierT_reachableT prods
                        -> List.Forall production_carrier_valid prods
                        -> dec (minimal_parse_of (G := G) len0 valid (substring offset len str) (List.map to_production prods)))
                    (fun _ _ => inr (fun p => _))
                    (fun p ps IHps Hreachable Hvalid
                     => match parse_production' parse_nonterminal offset Hlen pf _ _ with
                          | inl H => inl (MinParseHead _ _)
                          | inr H
                            => match IHps _ _ with
                                 | inl H' => inl (MinParseTail _ _)
                                 | inr H' => inr (fun p' => _)
                               end
                        end));
            t_prods_fin; t_prods_fin;
            try solve [ eapply invert_full_productions_carrierT_reachableT; eassumption
                      | eapply (@Forall_inv_iff _ production_carrier_valid); eassumption ].
        Defined.

        Lemma parse_productions'_eq
              (Hlen : len = 0 \/ offset + len <= length str)
              (pf pf' : len <= len0)
              (prods : list production_carrierT)
              (Hreachable : full_productions_carrierT_reachableT prods)
              (Hvalid : List.Forall production_carrier_valid prods)
        : (@parse_productions' Hlen pf prods Hreachable Hvalid)
          = (BooleanRecognizer.parse_productions' str parse_nonterminal' offset pf' prods)
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
                                 (offset len : nat)
                                 (pf : len <= fst p)
                                 (nt : nonterminal_carrierT),
                            bool)
                  (parse_nonterminal
                   : forall (p : nat * nat)
                            (pR : prod_relation lt lt p (len0, valid_len))
                            (valid : nonterminals_listT)
                            (Hvalid_len : nonterminals_length valid <= snd p)
                            (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                            (offset len : nat)
                            (Hlen : len = 0 \/ offset + len <= length str)
                            (pf : len <= fst p)
                            (nt : nonterminal_carrierT),
                       dec (minimal_parse_of_nonterminal (G := G) (fst p) valid (substring offset len str) (to_nonterminal nt)))
                  (Hmatches
                   : forall (p : nat * nat)
                            (pR : prod_relation lt lt p (len0, valid_len))
                            (valid : nonterminals_listT)
                            (Hvalid_len : nonterminals_length valid <= snd p)
                            (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                            (offset len : nat)
                            (Hlen : len = 0 \/ offset + len <= length str)
                            (pf : len <= fst p)
                            (nt : nonterminal_carrierT)
                            (Hvalid : is_valid_nonterminal initial_nonterminals_data nt),
                       (@parse_nonterminal p pR valid Hvalid_len offset len Hlen pf nt)
                       = (@parse_nonterminal' p pR valid offset len pf nt)
                           :> bool).

          Local Ltac p_step_t' :=
            idtac;
            match goal with
              | _ => assumption
              | _ => progress subst
              | _ => progress specialize_by assumption
              | _ => progress simpl in *
              | [ |- pred ?x < ?x ] => is_var x; destruct x
              | _ => omega
              | _ => discriminate
              | _ => congruence
              | _ => progress destruct_head and
              | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
              | [ H : is_true ?e, H' : context[?e] |- _ ] => rewrite H in H'
              | [ H : context[andb _ true] |- _ ] => rewrite Bool.andb_true_r in H
              | [ H : negb _ = false |- _ ] => apply Bool.negb_false_iff in H
              | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true in H
              | [ H : context[beq_nat ?x 0] |- context[pred ?x] ] => is_var x; destruct x
              | [ H : _ <= 0 |- _ ] => apply le_n_0_eq in H
              | [ H : 0 = _ |- _ ] => symmetry in H
              | [ H : nonterminals_length ?v = 0, H' : context[is_valid_nonterminal ?v ?nt] |- _ ]
                => rewrite nonterminals_length_zero in H' by assumption
              | [ H : _ |- _ ] => rewrite of_to_nonterminal in H by assumption
              | _ => rewrite of_to_nonterminal by assumption
              | [ Hvalid : is_valid_nonterminal _ ?nt = true |- _ ]
                => is_var nt; unique pose proof (proj1 (initial_nonterminals_correct' _) Hvalid)
              | [ |- context[Lookup ?G (to_nonterminal ?nt)] ]
                => is_var nt; rewrite <- nonterminal_to_production_correct by assumption
              | [ H : context[Lookup ?G (to_nonterminal ?nt)] |- _ ]
                => is_var nt; rewrite <- nonterminal_to_production_correct in H by assumption
              | [ H : is_valid_nonterminal ?valid ?nt = true
                  |- nonterminals_length (remove_nonterminal ?valid ?nt) <= _ ]
                => let H' := fresh in
                   assert (H' := remove_nonterminal_dec _ _ H);
                     hnf in H';
                     omega
              | [ H : minimal_parse_of_nonterminal _ _ _ (to_nonterminal ?nt) |- _ ]
                => inversion H; clear H
              | [ |- Forall _ _ ] => apply nonterminal_to_production_valid; assumption
              | [ H : or _ _ |- _ ] => let H0 := fresh in destruct H as [H0|H0]; try clear H
              | [ |- context[length (substring _ _ _)] ]
                => rewrite substring_length
              | _ => apply Min.min_case_strong; omega
              | [ H : ?x = 0 \/ ?T |- _ ]
                => destruct (Compare_dec.zerop x);
                  [ clear H | assert T by (destruct H; try assumption; omega); clear H ]
              | [ |- context[min ?x ?y - ?y] ]
                => rewrite <- NPeano.Nat.sub_min_distr_r, minus_diag, Min.min_0_r
              | _ => rewrite NPeano.Nat.add_sub
              | _ => rewrite Min.min_r by omega
              | _ => rewrite Min.min_l by omega
              | [ H : context[length (substring _ 0 _)] |- _ ]
                => rewrite take_length in H
              | [ H : context[length (substring _ _ _)] |- _ ]
                => rewrite substring_length, Min.min_r, NPeano.Nat.add_sub in H by omega
            end.
          Local Ltac p_step := repeat p_step_t'.

          Definition parse_nonterminal_step
                     (valid : nonterminals_listT)
                     (Hvalid_len : nonterminals_length valid <= valid_len)
                     (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                     (offset len : nat)
                     (Hlen : len = 0 \/ offset + len <= length str)
                     (pf : len <= len0)
                     (nt : nonterminal_carrierT)
          : dec (minimal_parse_of_nonterminal (G := G) len0 valid (substring offset len str) (to_nonterminal nt)).
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
                          offset len
                          Hlen
                          (le_n _)
                          (nonterminal_to_production nt))
              as [mp|nmp];
              [ eexists _, nil; simpl; split;
                [ apply initial_nonterminals_correct'; eassumption
                | rewrite of_to_nonterminal by assumption; reflexivity ]
              |
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
                                 offset len
                                 Hlen
                                 pf
                                 (nonterminal_to_production nt))
                  as [mp|nmp];
                  [
                  |
                  | eexists _, nil; simpl; split;
                    [ apply initial_nonterminals_correct'; eassumption
                    | rewrite of_to_nonterminal by assumption; reflexivity ]
                  |
                  | left; apply MinParseNonTerminalStrEq
                  | right; intro mp ])
              | ((** oops, we already saw this nonterminal in the past.  ABORT! *)
                simpl in *;
                right; intro mp) ])
            ];
            try first [ clear -is_valid; abstract p_step
                      | clear -Hlen pf'; abstract p_step
                      | clear -HSLP pf'; abstract p_step
                      | clear -HSLP Hlen pf pf'; abstract p_step
                      | clear -rdata Hvalid; abstract p_step
                      | clear -rdata Hvalid mp; abstract p_step
                      | clear -rdata Hvalid is_valid; abstract p_step
                      | clear -rdata Hvalid_len is_valid; abstract p_step
                      | clear -HSLP rdata Hvalid Hlen mp; abstract p_step
                      | clear -HSLP rdata Hvalid Hlen pf' mp nmp; abstract p_step
                      | clear -HSLP rdata Hvalid Hlen Hvalid_len is_valid pf' mp; abstract p_step ].
          Defined.

          Definition parse_nonterminal_step_eq
                     (valid : nonterminals_listT)
                     (Hvalid_len : nonterminals_length valid <= valid_len)
                     (*Hvalid : sub_nonterminals_listT valid initial_nonterminals_data*)
                     (offset len : nat)
                     (Hlen : len = 0 \/ offset + len <= length str)
                     (pf pf' : len <= len0)
                     (nt : nonterminal_carrierT)
                     (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
          : (@parse_nonterminal_step valid Hvalid_len offset len Hlen pf nt)
            = (BooleanRecognizer.parse_nonterminal_step str parse_nonterminal' valid offset pf' nt)
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
                   (offset len : nat)
                   (Hlen : len = 0 \/ offset + len <= length str)
                   (pf : len <= fst p)
                   (nt : nonterminal_carrierT),
              dec (minimal_parse_of_nonterminal (G := G) (fst p) valid (substring offset len str) (to_nonterminal nt))
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
                (offset len : nat)
                (Hlen : len = 0 \/ offset + len <= length str)
                (pf : len <= fst p)
                (nt : nonterminal_carrierT)
                (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
          : (@parse_nonterminal_or_abort p valid Hvalid_len offset len Hlen pf nt)
            = (BooleanRecognizer.parse_nonterminal_or_abort str p valid offset pf nt)
                :> bool.
          Proof.
            expand_once.
            revert valid Hvalid_len offset len Hlen pf nt Hvalid.
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

          Definition parse_nonterminal'_substring
                     (nt : nonterminal_carrierT)
          : dec (minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data (substring 0 (length str) str) (to_nonterminal nt)).
          Proof.
            destruct (Utils.dec (is_valid_nonterminal initial_nonterminals_data nt)) as [Hvalid|Hvalid].
            { eapply (@parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data));
              try first [ reflexivity | eassumption | right; reflexivity ]. }
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

          Definition parse_nonterminal'
                     (nt : nonterminal_carrierT)
          : dec (minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data str (to_nonterminal nt)).
          Proof.
            destruct (parse_nonterminal'_substring nt) as [p|np];
            [ left | right; intro p; apply np; clear np ].
            { eapply expand_minimal_parse_of_nonterminal_beq; [ | eassumption ].
              rewrite substring_correct3; reflexivity. }
            { eapply expand_minimal_parse_of_nonterminal_beq; [ | eassumption ].
              rewrite substring_correct3; reflexivity. }
          Defined.

          Lemma parse_nonterminal'_substring_eq
                (nt : nonterminal_carrierT)
          : (@parse_nonterminal'_substring nt)
            = (BooleanRecognizer.parse_nonterminal' str nt)
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

          Lemma parse_nonterminal'_eq
                (nt : nonterminal_carrierT)
          : (@parse_nonterminal' nt)
            = (BooleanRecognizer.parse_nonterminal' str nt)
                :> bool.
          Proof.
            rewrite <- parse_nonterminal'_substring_eq.
            unfold parse_nonterminal'.
            repeat eq_t'.
          Qed.

          Definition parse_nonterminal
                     (nt : String.string)
          : dec (minimal_parse_of_nonterminal (G := G) (length str) initial_nonterminals_data str nt).
          Proof.
            destruct (parse_nonterminal' (of_nonterminal nt)) as [p|p]; [ left | right ].
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
                (nt : String.string)
          : (@parse_nonterminal nt)
            = (BooleanRecognizer.parse_nonterminal str nt)
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
      Context (it : item Char).

      Definition parse_item_substring : dec _
        := parse_item' 0 (or_intror (reflexivity _)) (@parse_nonterminal'_substring) it.

      Definition parse_item
        : dec (minimal_parse_of_item (G := G) (length str) initial_nonterminals_data str it).
      Proof.
        destruct parse_item_substring as [p|np];
        [ left | right; intro p; apply np; clear np ];
        (eapply expand_minimal_parse_of_item_beq; [ | eassumption ]);
        clear -HSLP; abstract (rewrite substring_correct3'; reflexivity).
      Defined.

      Lemma parse_item_substring_eq
      : parse_item_substring
        = (BooleanRecognizer.parse_item str it)
            :> bool.
      Proof.
        apply parse_item'_eq_all, parse_nonterminal'_substring_eq.
      Qed.

      Lemma parse_item_eq
      : parse_item
        = (BooleanRecognizer.parse_item str it)
            :> bool.
      Proof.
        rewrite <- parse_item_substring_eq; unfold parse_item;
        destruct parse_item_substring; reflexivity.
      Qed.
    End item.

    Section production.
      Context (p : production_carrierT)
              (Hreachable : full_production_carrierT_reachableT p)
              (Hvalid : production_carrier_valid p).

      Definition parse_production_substring
        : dec (minimal_parse_of_production (G := G) (length str) initial_nonterminals_data (substring 0 (length str) str) (to_production p)).
      Proof.
        eapply parse_production'; [ | right; reflexivity | reflexivity.. | assumption | assumption ].
        intros.
        eapply (@parse_nonterminal_or_abort (length str, _));
          simpl; try reflexivity; subst; assumption.
      Defined.

      Definition parse_production
        : dec (minimal_parse_of_production (G := G) (length str) initial_nonterminals_data str (to_production p)).
      Proof.
        destruct parse_production_substring as [p'|np];
        [ left | right; intro p'; apply np; clear np ];
        (eapply expand_minimal_parse_of_production_beq; [ | eassumption ]);
        clear -HSLP; abstract (rewrite substring_correct3'; reflexivity).
      Defined.

      Lemma parse_production_substring_eq
      : parse_production_substring
        = (BooleanRecognizer.parse_production str p)
            :> bool.
      Proof.
        apply parse_production'_eq; simpl; intros; subst; simpl.
        erewrite <- parse_nonterminal_or_abort_eq by assumption.
        reflexivity.
      Qed.

      Lemma parse_production_eq
      : parse_production
        = (BooleanRecognizer.parse_production str p)
            :> bool.
      Proof.
        rewrite <- parse_production_substring_eq; unfold parse_production.
        destruct parse_production_substring; reflexivity.
      Qed.
    End production.

    Section productions.
      Context (ps : list production_carrierT)
              (Hreachable : full_productions_carrierT_reachableT ps)
              (Hvalid : List.Forall production_carrier_valid ps).

      Definition parse_productions_substring
        : dec (minimal_parse_of (G := G) (length str) initial_nonterminals_data (substring 0 (length str) str) (List.map to_production ps)).
      Proof.
        eapply parse_productions'; [ | right; reflexivity | reflexivity.. | assumption | assumption ].
        intros.
        eapply (@parse_nonterminal_or_abort (length str, _));
          simpl; try reflexivity; subst; assumption.
      Defined.

      Definition parse_productions
        : dec (minimal_parse_of (G := G) (length str) initial_nonterminals_data str (List.map to_production ps)).
      Proof.
        destruct parse_productions_substring as [p'|np];
        [ left | right; intro p'; apply np; clear np ];
        (eapply expand_minimal_parse_of_beq; [ | eassumption ]);
        clear -HSLP; abstract (rewrite substring_correct3'; reflexivity).
      Defined.

      Lemma parse_productions_substring_eq
      : parse_productions_substring
        = (BooleanRecognizer.parse_productions str ps)
            :> bool.
      Proof.
        apply parse_productions'_eq; simpl; intros; subst; simpl.
        erewrite <- parse_nonterminal_or_abort_eq by assumption.
        reflexivity.
      Qed.

      Lemma parse_productions_eq
      : parse_productions
        = (BooleanRecognizer.parse_productions str ps)
            :> bool.
      Proof.
        rewrite <- parse_productions_substring_eq; unfold parse_productions.
        destruct parse_productions_substring; reflexivity.
      Qed.
    End productions.
  End min.
End recursive_descent_parser.
