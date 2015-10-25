(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common Fiat.Common.Wf.
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Common.Match.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.
Require Export Fiat.Common.SetoidInstances.
Require Export Fiat.Common.List.ListMorphisms.
Require Export Fiat.Common.OptionFacts.
Require Export Fiat.Common.NatFacts.
Require Export Fiat.Common.Sigma.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Global Arguments string_dec : simpl never.
Global Arguments string_beq : simpl never.
Global Arguments parse_production' _ _ _ _ _ _ _ _ !_.
Global Arguments parse_production _ _ _ _ _ !_.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {ls : list (String.string * productions Char)}.
  Context {data : @boolean_parser_dataT Char _}.

  Class str_carrier (constT varT : Type)
    := { to_string : constT * varT -> String;
         of_string : String -> constT * varT;
         to_of : forall x, to_string (of_string x) = x;
         of_to : forall x, of_string (to_string x) = x;
         drop_const : forall x n, fst (of_string (drop n x)) = fst (of_string x);
         take_const : forall x n, fst (of_string (take n x)) = fst (of_string x)}.

  Definition str_carrier' (constT varT : Type)
    := { to_string : constT * varT -> StringLike.String
       & { of_string : StringLike.String -> constT * varT
         | (forall x, to_string (of_string x) = x)
           /\ (forall x, of_string (to_string x) = x)
           /\ (forall x n, fst (of_string (drop n x)) = fst (of_string x))
           /\ (forall x n, fst (of_string (take n x)) = fst (of_string x)) } }.

  Definition str_carrier_default {constT varT} (strC : str_carrier' constT varT)
  : str_carrier constT varT.
  Proof.
    refine {| to_string := projT1 strC;
              of_string := proj1_sig (projT2 strC) |};
    apply (proj2_sig (projT2 strC)).
  Defined.

  Context constT varT {strC : str_carrier constT varT}.

  Local Notation G := (list_to_grammar (nil::nil) ls) (only parsing).

  Definition stringlike_lite (constV : constT) : StringLike Char
    := {| String := varT;
          is_char s := is_char (to_string (constV, s));
          length s := length (to_string (constV, s));
          take n s := snd (of_string (take n (to_string (constV, s))));
          drop n s := snd (of_string (drop n (to_string (constV, s))));
          get n s := get n (to_string (constV, s));
          bool_eq s s' := bool_eq (to_string (constV, s)) (to_string (constV, s')) |}.

  Local Ltac contract_drop_take_t' :=
    idtac;
    match goal with
      | [ |- context[to_string (?x, snd ?y)] ]
        => replace (x, snd y) with y
          by (
              etransitivity; [ apply surjective_pairing | ]; apply f_equal2; trivial;
              rewrite ?take_const, ?drop_const, of_to; reflexivity
            );
          rewrite to_of
    end.

  Local Ltac contract_drop_take_t :=
    idtac;
    match goal with
      | _ => contract_drop_take_t'
      | [ H : is_true (bool_eq ?x ?y) |- _ ] => change (beq x y) in H
      | [ H : context[is_true (bool_eq ?x ?y)] |- _ ] => change (is_true (bool_eq x y)) with (beq x y) in H
      | [ |- context[is_true (bool_eq ?x ?y)] ] => change (is_true (bool_eq x y)) with (beq x y)
      | _ => progress subst
      | [ H : beq _ _ |- _ ] => rewrite !H; clear H
      | [ |- _ = _ ] => reflexivity
      | [ |- beq _ _ ] => reflexivity
      | [ |- Equivalence _ ] => split; repeat intro
    end.

  Lemma stringlikeproperties_lite (constV : constT) : @StringLikeProperties Char (stringlike_lite constV).
  Proof.
    destruct HSLP;
    split; simpl;
    unfold Proper, respectful, beq; simpl;
    repeat first [ progress contract_drop_take_t
                 | intro
                 | eauto with nocore ].
  Qed.

  Definition data_lite (constV : constT) : @boolean_parser_dataT _ (stringlike_lite constV)
    := {| predata := data;
          split_string_for_production it its s := split_string_for_production it its (to_string (constV, s)) |}.

  Inductive take_or_drop := take_of (n : nat) | drop_of (n : nat).

  Definition make_drops (ls : list take_or_drop) (str : String)
    := fold_right
         (fun td s => match td with
                        | take_of n => take n s
                        | drop_of n => drop n s
                      end)
         str
         ls.

  Arguments make_drops : simpl never.

  Lemma make_drops_eta ls' str
  : (fst (of_string str), snd (of_string (make_drops ls' str))) = of_string (make_drops ls' str).
  Proof.
    revert str; unfold make_drops; induction ls' as [|x xs IHxs]; simpl; intros.
    { rewrite <- surjective_pairing; reflexivity. }
    { etransitivity; [ | symmetry; apply surjective_pairing ].
      destruct x; simpl.
      { rewrite take_const, <- IHxs; reflexivity. }
      { rewrite drop_const, <- IHxs; reflexivity. } }
  Qed.

  Lemma make_drops_eta' ls' ls'' str
  : (fst (of_string (make_drops ls' str)), snd (of_string (make_drops ls'' str))) = of_string (make_drops ls'' str).
  Proof.
    etransitivity; [ | apply make_drops_eta ].
    f_equal.
    unfold make_drops.
    induction ls' as [|x xs IHxs]; simpl; intros; trivial.
    destruct x; rewrite ?take_const, ?drop_const, IHxs; reflexivity.
  Qed.

  Lemma make_drops_eta'' ls' str strv
  : (fst (of_string str), snd (of_string (make_drops ls' (to_string (fst (of_string str), strv))))) = of_string (make_drops ls' (to_string (fst (of_string str), strv))).
  Proof.
    etransitivity; [ | apply make_drops_eta ]; simpl.
    rewrite of_to; simpl; reflexivity.
  Qed.

  Local Ltac t_reduce_fix :=
    repeat match goal with
             | _ => progress simpl sumbool_rect
             | _ => progress simpl option_rect
             | [ |- context[lt_dec ?x ?y] ]
               => destruct (lt_dec x y)
             | [ |- context[dec ?x] ]
               => destruct (dec x)
             | [ |- @fold_right ?A ?B ?f ?x ?ls = @fold_right ?A ?B ?f ?x ?ls' ]
               => apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@fold_right A B))
             | [ |- @fold_left ?A ?B ?f ?ls ?x = @fold_left ?A ?B ?f ?ls' ?x ]
               => apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@fold_left A B))
             | [ |- @map ?A ?B ?f ?ls = @map ?A ?B ?f' ?ls' ]
               => apply (_ : Proper (pointwise_relation _ _ ==> _ ==> eq) (@map A B))
             | _ => intro
             | [ |- ?x = ?x ] => reflexivity
             | [ |- andb _ _ = andb _ _ ] => apply f_equal2
             | [ |- orb _ _ = orb _ _ ] => apply f_equal2
             | [ |- match ?it with Terminal _ => _ | _ => _ end = match ?it with _ => _ end ] => is_var it; destruct it
             | [ |- context[(fst ?x, snd ?x)] ] => rewrite <- !surjective_pairing
             | _ => contract_drop_take_t'
             | _ => rewrite make_drops_eta
             | _ => rewrite make_drops_eta'
             | _ => rewrite make_drops_eta''
             | [ |- context[to_string (of_string _)] ] => rewrite !to_of
             | [ |- context[take ?x (make_drops ?ls ?str)] ]
               => change (take x (make_drops ls str)) with (make_drops (take_of x :: ls) str)
             | [ |- context[drop ?x (make_drops ?ls ?str)] ]
               => change (drop x (make_drops ls str)) with (make_drops (drop_of x :: ls) str)
             | _ => solve [ auto with nocore ]
             | [ |- prod_relation lt lt _ _ ] => hnf; simpl; omega
             | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
             | [ H : _ = in_left |- _ ] => clear H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : context[negb (EqNat.beq_nat ?x ?y)] |- _ ] => destruct (EqNat.beq_nat x y) eqn:?
             | [ H : EqNat.beq_nat _ _ = false |- _ ] => apply EqNat.beq_nat_false in H
             | [ H : EqNat.beq_nat _ _ = true |- _ ] => apply EqNat.beq_nat_true in H
             | [ H : snd ?x = _ |- _ ] => is_var x; destruct x
             | _ => progress simpl negb in *
             | [ H : false = true |- _ ] => inversion H
             | [ |- ?f _ (match ?p with eq_refl => ?k end) = ?f' _ ?k ]
               => destruct p
           end.

  Local Ltac t_reduce_list :=
    idtac;
    match goal with
      | [ |- list_rect ?P ?n ?c ?ls (snd (of_string (make_drops ?l ?str))) ?x ?y = list_rect ?P' ?n' ?c' ?ls (make_drops ?l ?str) ?x ?y ]
        => let n0 := fresh in
           let c0 := fresh in
           let n1 := fresh in
           let c1 := fresh in
           set (n0 := n);
             set (n1 := n');
             set (c0 := c);
             set (c1 := c');
             refine (list_rect
                       (fun ls' => forall x' y' l', list_rect P n0 c0 ls' (snd (of_string (make_drops l' str))) x' y' = list_rect P' n1 c1 ls' (make_drops l' str) x' y')
                       _
                       _
                       ls
                       x y l);
             simpl list_rect;
             [ subst n0 c0 n1 c1; cbv beta
             | intros; unfold n0 at 1, c0 at 1, n1 at 1, c1 at 1 ]
      | [ |- list_rect ?P ?n ?c ?ls (snd (of_string (make_drops ?l ?str))) ?x ?y = list_rect ?P' ?n' ?c' ?ls (snd (of_string (make_drops ?l ?str))) ?x ?y ]
        => let n0 := fresh in
           let c0 := fresh in
           let n1 := fresh in
           let c1 := fresh in
           set (n0 := n);
             set (n1 := n');
             set (c0 := c);
             set (c1 := c');
             refine (list_rect
                       (fun ls' => forall x' y' l', list_rect P n0 c0 ls' (snd (of_string (make_drops l' str))) x' y' = list_rect P' n1 c1 ls' (snd (of_string (make_drops l' str))) x' y')
                       _
                       _
                       ls
                       x y l);
             simpl list_rect;
             [ subst n0 c0 n1 c1; cbv beta
             | intros; unfold n0 at 1, c0 at 1, n1 at 1, c1 at 1 ]
    end.

  Definition parse_nonterminal_opt0
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    exists (@parse_nonterminal _ _ G (data_lite (fst (of_string str))) (snd (of_string str)) nt).
    unfold parse_nonterminal, parse_nonterminal_or_abort.
    simpl.
    rewrite <- !surjective_pairing, !to_of.
    change str with (make_drops nil str).
    lazymatch goal with
      | [ |- Fix ?rwf _ ?P0 ?a ?b ?c ?d ?e ?f = Fix _ _ ?P1 _ _ ?str _ _ _ ]
        => set (a' := a); set (P0' := P0); set (P1' := P1); generalize f; generalize e; change (d <= d) with (d <= (fst a')); generalize d; generalize b; clearbody a';
           generalize (@nil take_or_drop); induction (rwf a') as [?? IH]; intros
    end.
    rewrite !Fix5_eq by (intros; apply parse_nonterminal_step_ext; assumption).
    unfold P0' at 1, P1' at 1, parse_nonterminal_step, parse_productions', parse_production', parse_item'.
    t_reduce_fix;
    t_reduce_list;
    t_reduce_fix.
    { apply IH; t_reduce_fix. }
    { apply IH; t_reduce_fix. }
  Defined.

  Local Ltac refine_Fix5_Proper_eq :=
    idtac;
    (lazymatch goal with
    | [ |- context[_ = @Fix ?A ?R ?Rwf ?T (fun a0 b0 c0 d0 e0 h0 i0 => @?f a0 b0 c0 d0 e0 h0 i0) ?a ?b ?c ?d ?e ?h] ]
      => (lazymatch T with
         | (fun a' : ?A => forall (b' :@?B a') (c' : @?C a' b') (d' : @?D a' b' c') (e' : @?E a' b' c' d') (h' : @?H a' b' c' d' e'), @?P a' b' c' d' e' h')
           => let H' := fresh in
              (*refine (_ : @Fix A R Rwf T (fun a0 b0 c0 d0 e0 h0 i0 => _) a b c d e h = _);
                 let f' := match goal with |- @Fix _ _ _ _ ?f' _ _ _ _ _ _ = _ => constr:f' end in*)
              pose proof ((fun f' H0 => @Fix5_Proper_eq A B C D E H R Rwf P f' f H0 a b c d e h)) as H';
          cbv beta in H';
          (lazymatch type of H' with
          | forall f' : ?f'T, @?H'T f' -> _
            => let H'' := fresh in
               let f'' := fresh in
               assert (H'' : { f' : f'T & H'T f' });
           [ clear H'
           | destruct H'' as [f'' H''];
             specialize (H' f'' H'');
             clear H''; eexists; exact H' ]
           end)
          end)
     end);
    unfold forall_relation, pointwise_relation, respectful;
    cbv beta;
    eexists (fun a0 b0 c0 d0 e0 h0 i0 => _); intros.

  Local Ltac fin_step_opt :=
    repeat match goal with
             | [ |- _ = true ] => reflexivity
             | [ |- _ = false ] => reflexivity
             | [ |- ?x = ?x ] => reflexivity
             | [ |- _ = ?x ] => is_var x; reflexivity
             | [ |- _ = (_::_) ] => apply f_equal2
             | [ |- _ = nil ] => reflexivity
             | [ |- _ = 0 ] => reflexivity
             | [ |- _ = 1 ] => reflexivity
             | [ |- _ = EqNat.beq_nat _ _ ] => apply f_equal2
             | [ |- _ = string_beq _ _ ] => apply f_equal2
             | [ |- _ = fst ?x ] => is_var x; reflexivity
             | [ |- _ = snd ?x ] => is_var x; reflexivity
           end.

  Local Ltac step_opt' :=
    idtac;
    match goal with
      | _ => rewrite <- !minusr_minus
      | [ |- _ = @option_rect ?A ?B (fun s => _) _ _ ]
        => refine (_ : @option_rect A B (fun s => _) _ _ = _);
          apply (_ : Proper (pointwise_relation _ _ ==> _ ==> _ ==> eq) (@option_rect A B));
          repeat intro
      | [ |- _ = @bool_rect ?A _ _ _ ]
        => refine (_ : @bool_rect A _ _ _ = _);
          apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@bool_rect A));
          repeat intro
      | [ |- _ = fold_right orb false _ ]
        => rewrite <- !(@fold_symmetric _ orb) by first [ apply Bool.orb_assoc | apply Bool.orb_comm ]
      | [ |- _ = @fold_left ?A ?B orb _ false ]
        => refine (_ : fold_left orb _ false = _);
          apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B)); repeat intro
      | [ |- _ = @fold_right ?A ?B (fun x y => _) _ _ ]
        => refine (_ : fold_right (fun x y => _) _ _ = _);
          apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_right A B)); repeat intro
      | [ |- _ = @map ?A ?B _ _ ]
        => refine (_ : @map A B (fun x => _) _ = _);
          apply (_ : Proper (pointwise_relation _ _ ==> _ ==> _) (@map A B)); repeat intro
    end;
    fin_step_opt.

  Local Ltac step_opt := repeat step_opt'.

  Local Ltac sigL_transitivity term :=
    idtac;
    (lazymatch goal with
    | [ |- ?sig (fun x : ?T => @?A x = ?B) ]
      => (let H := fresh in
          let H' := fresh in
          assert (H : sig (fun x : T => A x = term));
          [
          | assert (H' : term = B);
            [
            | let x' := fresh in
              destruct H as [x' H];
                exists x'; transitivity term; [ exact H | exact H' ] ] ])
     end).

  Local Ltac fix_trans_helper RHS x y :=
    match RHS with
      | appcontext G[y] => let RHS' := context G[x] in
                           fix_trans_helper RHS' x y
      | _ => constr:RHS
    end.

  Local Ltac fix_trans :=
    match goal with
      | [ H : forall a0 a1 a2 a3 a4 a5 a6, ?x a0 a1 a2 a3 a4 a5 a6 = ?y a0 a1 a2 a3 a4 a5 a6 |- _ = ?RHS ]
        => let RHS' := fix_trans_helper RHS x y
           in transitivity RHS'; [ clear H y | ]
    end.

  Local Ltac t_reduce_list_more :=
    idtac;
    (lazymatch goal with
    | [ str : String |- list_rect ?P ?n ?c ?ls ?str' ?x ?y = list_rect ?P' ?n' ?c' ?ls ?str' ?x ?y ]
      => (change str' with (snd (fst (of_string str), str'));
          rewrite <- (of_to (fst (of_string str), str'));
          change (to_string (fst (of_string str), str')) with (make_drops nil (to_string (fst (of_string str), str')));
          t_reduce_list)
     end).

  Definition parse_nonterminal_opt'
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt0 str nt) in
    let h := head c in
    let p := (eval cbv beta iota zeta delta [proj1_sig h] in (proj1_sig c)) in
    sigL_transitivity p; [ | abstract exact (proj2_sig c) ].
    let G := match goal with |- context[_ = parse_nonterminal (G := ?G) _ _] => constr:G end in
    let G' := head G in
    unfold G'.
    cbv beta iota zeta delta [parse_nonterminal parse_nonterminal_or_abort parse_nonterminal_step parse_productions parse_productions' parse_production parse_item parse_item' Lookup list_to_grammar list_to_productions].
    simpl.
    refine_Fix5_Proper_eq.
    unfold parse_production', parse_item'.
    fix_trans;
      [
      | solve [ t_reduce_fix;
                t_reduce_list_more;
                t_reduce_fix ] ].
    step_opt'; [ | reflexivity ].
    step_opt'.
    etransitivity_rev _.
    { step_opt'.
      match goal with
        | [ |- appcontext[fold_right (fun str_t else_case s => bool_rect (fun _ => ?T) (@?a str_t) (else_case s) (@?b str_t s))] ]
          => rewrite (@fold_right_fun _ _ _ (fun str_t else_cases s => bool_rect (fun _ => T) (a str_t) else_cases (b str_t s)))
      end.
      match goal with
        | [ |- appcontext[?f _ (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
          => rewrite (fun extra_arg init => @f_fold_right_bool_rect _ _ _ (fun k => f extra_arg k) init ls)
      end.
      reflexivity. }
    match goal with
      | [ |- appcontext[?f _ (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
        => rewrite (fun extra_arg init => @f_fold_right_bool_rect _ _ _ (fun k => f extra_arg k) init ls)
    end.
    simpl.
    rewrite fold_right_bool_rect; simpl.
    step_opt'.
    step_opt'.
    step_opt'.
    step_opt'.
    lazymatch goal with
      | [ |- _
             = list_rect
                 ?P
                 ?N
                 (fun it its parse_production' str0' len pf
                  => ?fold_orb
                      (map
                         ((fun n
                           => match it with
                                | Terminal ch
                                  => is_char
                                       (to_string (fst (of_string ?str'),
                                                   snd (of_string (take n (to_string (fst (of_string ?str'), str0'))))))
                                       ch
                                | NonTerminal nt0
                                  => @?a5 it its parse_production' str0' len pf n nt0
                              end
                                && parse_production' (@?rest0 it its parse_production' str0' len pf n) (len - n) (@?rest1 it its parse_production' str0' len pf n))%bool)
                         (@?ls it its parse_production' str0' len pf))
                      ?false)
                 ?a ?b ?c ?d ]
        => idtac;
          let lhs' :=
               constr:(
                 list_rect
                   P N
                   (fun it its parse_production' str0' len pf
                    => fold_orb
                         (map
                            ((fun n
                              => match it with
                                   | Terminal ch
                                     => is_char
                                          (take n (to_string (fst (of_string str'), str0')))
                                          ch
                                   | NonTerminal nt0
                                     => a5 it its parse_production' str0' len pf n nt0
                                 end
                                   && parse_production' (rest0 it its parse_production' str0' len pf n) (len - n)(*%natr*) ((*match eq_sym (minusr_minus len n) with eq_refl => *)rest1 it its parse_production' str0' len pf n(* end*)))%bool)
                            (ls it its parse_production' str0' len pf))
                         false)
                   a b c d) in
           etransitivity;
             [
             | refine (_ : lhs' = _); cbv beta;
               t_reduce_list_more;
               solve [ t_reduce_fix ] ];
             cbv beta
    end.
    reflexivity.
  Defined.

  Definition parse_nonterminal_opt''
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt' str nt) in
    let h := head c in
    let p := (eval cbv beta iota zeta delta [proj1_sig h] in (proj1_sig c)) in
    sigL_transitivity p; [ | abstract exact (proj2_sig c) ].
    eexists.
    rewrite <- !surjective_pairing, !to_of.
    reflexivity.
  Defined.

  Definition parse_nonterminal_opt
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    let c := constr:(parse_nonterminal_opt'' str nt) in
    let h := head c in
    let impl := (eval cbv beta iota zeta delta [h proj1_sig] in (proj1_sig c)) in
    (exists impl);
      abstract (exact (proj2_sig c)).
  Defined.
End recursive_descent_parser.

(** This tactic solves the simple case where the type of string is
    judgmentally [const_data * variable_data], and [take] and [drop]
    judgmentally preserve the constant data. *)

Ltac solve_default_str_carrier :=
  match goal with |- str_carrier _ _ => idtac end;
  eapply str_carrier_default; hnf; simpl;
  match goal with |- { to_string : _ * _ -> string * _ & _ } => idtac end;
  let T := match goal with |- { to_string : _ * _ -> string * ?T & _ } => constr:T end in
  exists (fun x : string * T => x);
    exists (fun x : string * T => x);
    simpl;
    solve [ repeat split ].

Hint Extern 1 (str_carrier _ _) => solve_default_str_carrier : typeclass_instances.
