(** First step of a splitter refinement; indexed representation, and handle all rules with at most one nonterminal; leave a reflective goal *)
Require Import Coq.Strings.String Coq.Arith.Lt Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.ParserADTSpecification.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarEquality.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Equality.
Require Import ADTSynthesis.ADTRefinement.
Require Import ADTSynthesis.Common.StringBound ADTSynthesis.Common.ilist.
Require Import ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import ADTSynthesis.Common.IterateBoundedIndex.
Require Import ADTSynthesis.Common.List.FlattenList.
Require Import ADTSynthesis.Common.List.ListFacts.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Fixpoint tails {A} (ls : list A) : list (list A)
  := match ls with
       | nil => [nil]
       | x::xs => (x::xs)::tails xs
     end.

(** Reflective version of [split_list_is_complete] and [production_is_reachable] *)
Definition forall_reachable_productions {Char} (G : grammar Char) {T} (f : production Char -> T -> T) (init : T)
: T
  := fold_right
       f
       init
       (flatten
          (flatten
             (map
                (fun nt =>
                   (map
                      tails
                      (Lookup G nt)))
                (Valid_nonterminals G)))).

Lemma forall_reachable_productions_impl_helper {Char} (G : grammar Char) (Pnil : Prop) (P1 P2 : _ -> _ -> Prop)
: forall_reachable_productions G (fun p H => (match p with
                                                | [] => True
                                                | x::xs => P1 x xs
                                              end -> match p with
                                                       | [] => Pnil
                                                       | x::xs => P2 x xs
                                                     end)
                                             /\ H) True
  -> forall_reachable_productions G (fun p H => match p with
                                                  | [] => Pnil
                                                  | x::xs => P1 x xs -> P2 x xs
                                                end /\ H) True.
Proof.
  unfold forall_reachable_productions.
  match goal with
    | [ |- _ -> fold_right _ _ ?ls ] => induction ls; simpl; trivial; []
  end.
  intros [H0 H1]; split; eauto.
  match goal with
    | [ |- match ?e with _ => _ end ] => destruct a; eauto
  end.
Qed.

Lemma forall_reachable_productions_helper {Char Char_beq}
      (Char_bl : forall x y : Char, Char_beq x y = true -> x = y)
      (Char_lb : forall x y : Char, x = y -> Char_beq x y = true)
      {T} (G : grammar Char)
      (Pnil : Prop) ct base v (P2 : _ -> _ -> Prop)
: forall_reachable_productions
    G
    (fun p H => match p with
                  | [] => Pnil
                  | x::xs => computes_to
                               (ct (x::xs))
                               v
                             -> P2 x xs
                end /\ H)
    True
  -> forall_reachable_productions
       G
       (fun p H => match p with
                     | [] => Pnil
                     | x::xs => computes_to
                                  (forall_reachable_productions
                                     G
                                     (fun p0 (else_case : Comp T)
                                      => if production_beq Char_beq p0 (x::xs)
                                         then ct p0
                                         else else_case)
                                     (base x xs))
                                  v
                                -> P2 x xs
                   end /\ H)
       True.
Proof.
  unfold forall_reachable_productions.
  repeat (
      let P := match goal with |- context[fold_right (fun x y => @?P x /\ y) _ _] => constr:P end in
      pose proof (fold_right_map P and) as H;
      unfold compose in *; simpl in *;
      rewrite <- H; clear H
    ).
  unfold forall_reachable_productions.
  match goal with
    | [ |- _ -> fold_right _ _ (map _ ?ls) ] => induction ls; simpl; trivial; []
  end.
  intros [H0 H1]; split; eauto.
  { match goal with
      | [ |- match ?e with _ => _ end ] => destruct a; eauto
    end.
    match goal with
      | [ |- context[production_beq _ ?x ?x] ] => rewrite (@production_lb Char Char_beq Char_lb x x eq_refl)
    end.
    assumption. }
  { match goal with
      | [ H : ?T, H' : ?T -> ?X |- _ ] => specialize (H' H); clear H
    end.
    match goal with
      | [ H : fold_right _ _ (map _ ?ls) |- fold_right _ _ (map _ ?ls) ]
        => revert H; apply fold_right_and_map_impl; trivial; []
    end.
    intros []; trivial; [].
    intros ??.
    match goal with
      | [ |- context[production_beq ?d ?x ?y] ] => case_eq (production_beq d x y); intro
    end;
    repeat match goal with
             | [ H : production_beq _ _ _ = true |- _ ] => apply production_bl in H; [ | assumption.. ]
             | _ => progress subst
             | _ => solve [ eauto ]
           end. }
Qed.

Lemma exists_in_map_tails {A} (P : _ -> Prop) ls
: (forall p : list A, (exists prefix, In (prefix ++ p)%list ls) -> P p)
  <-> fold_right and True (map P (flatten (map tails ls))).
Proof.
  induction ls as [ | x xs ]; simpl; split; intros; eauto;
  try solve [ eauto
            | destruct_head ex; destruct_head False ].
  { rewrite map_app, fold_right_app.
    apply fold_right_and_iff; split.
    { clear IHxs.
      specialize (fun p prefix H' => H p (ex_intro _ prefix (or_introl H'))).
      induction x; simpl; split; try tauto.
      { apply (H _ []); reflexivity. }
      { apply (H _ []); reflexivity. }
      { apply IHx; intros p prefix H'; subst.
        eapply (H _ (_::prefix)); reflexivity. } }
    { apply IHxs; intros; destruct_head ex.
      apply H; eexists; right; eassumption. } }
  { repeat match goal with
             | [ H : _ |- _ ] => rewrite map_app in H
             | [ H : _ |- _ ] => rewrite fold_right_app in H
             | [ H : fold_right _ ?init _ |- _ ] => not constr_eq init True; apply fold_right_and_iff in H
             | _ => progress destruct_head_hnf and
             | _ => progress destruct_head or
             | _ => progress destruct_head ex
             | _ => progress subst
             | _ => progress eauto
             | [ H : ?T, H' : ?T -> ?X |- _ ] => specialize (H' H)
           end.
    let H := match goal with H : fold_right and True (map P (tails (_ ++ ?p))) |- P ?p => constr:H end in
    clear -H.
    match goal with
      | [ H : fold_right and True (map P (tails (?x ++ _))) |- P ?p ] => induction x; destruct p
    end;
      simpl in *;
      destruct_head and; eauto. }
Qed.

Lemma production_is_reachable__forall_reachable_productions {Char} {G : grammar Char} (P : production Char -> Prop)
: (forall p, production_is_reachable G p -> P p)
  <-> (forall_reachable_productions G (fun p H => P p /\ H) True).
Proof.
  unfold forall_reachable_productions, production_is_reachable.
  pose proof (fold_right_map P and) as H; unfold compose in *; simpl in *.
  rewrite <- H.
  induction (Valid_nonterminals G) as [ | x xs IHG ]; simpl in *.
  { split; simpl; intros; trivial.
    destruct_head ex; destruct_head and; destruct_head False. }
  { rewrite flatten_app, map_app, fold_right_app.
    setoid_rewrite fold_right_and_iff.
    setoid_rewrite <- exists_in_map_tails.
    setoid_rewrite <- IHG; clear IHG.
    repeat (split || intro); destruct_head ex; destruct_head and; destruct_head or; subst;
    match goal with
      | [ H : _ |- _ ] => apply H
    end;
    repeat match goal with
             | [ |- ex _ ] => eexists
             | _ => eassumption
             | [ |- _ /\ _ ] => split; eassumption
             | [ |- _ /\ _ ] => split; [ left; reflexivity | eassumption ]
             | [ |- _ /\ _ ] => split; [ right; eassumption | eassumption ]
           end. }
Qed.

Lemma production_is_reachable__forall_reachable_productions' {Char} {G : grammar Char} (P : _ -> _ -> Prop)
: (forall p ps, production_is_reachable G (p::ps) -> P p ps)
  <-> (forall_reachable_productions G (fun p H => match p with
                                                    | nil => True
                                                    | x::xs => P x xs
                                                  end /\ H) True).
Proof.
  setoid_rewrite <- production_is_reachable__forall_reachable_productions.
  split; intro H.
  { intros []; intuition. }
  { intros p ps.
    specialize (H (p::ps)); eauto. }
Qed.

Section helpers.
  Section generic.
    Context {Char : Type}.

    Fixpoint has_only_terminals (its : production Char)
    : bool
      := match its with
           | nil => true
           | (Terminal _)::xs => has_only_terminals xs
           | (NonTerminal _)::_ => false
         end.
  End generic.

  Section generic_string.
    Context {Char} {HSL : StringLike Char} {HLSP : StringLikeProperties Char} (G : grammar Char).

    Lemma has_only_terminals_length {its str}
          (H0 : @has_only_terminals _ its)
          (H1 : parse_of_production G str its)
    : length str = List.length its.
    Proof.
      induction H1 as [ | ? ? ? ? pit pits IH ]; simpl in *; trivial.
      rewrite drop_length in IH.
      dependent destruction pit.
      { match goal with
          | [ H : context[(_ ~= [ _ ])%string_like] |- _ ]
            => apply length_singleton in H
        end.
        rewrite <- IH by assumption; clear IH.
        repeat match goal with
                 | _ => intro
                 | [ H : context[length (take _ _)] |- _ ] => rewrite take_length in H
                 | [ H : context[length (drop _ _)] |- _ ] => rewrite drop_length in H
                 | [ H : min ?x ?y = 1 |- _ ] => is_var x; destruct x
                 | [ H : min (S ?x) ?y = 1 |- _ ] => is_var x; destruct x
                 | [ H : min (S (S ?x)) ?y = 1 |- _ ] => revert H; apply (Min.min_case_strong (S (S x)) y)
                 | [ H : context[min _ 0] |- _ ] => rewrite Min.min_0_r in H
                 | [ H : context[min 0 _] |- _ ] => rewrite Min.min_0_l in H
                 | [ H : 0 = 1 |- _ ] => exfalso; clear -H; discriminate
                 | [ H : S (S _) = 1 |- _ ] => exfalso; clear -H; discriminate
                 | [ H : ?x = 1, H' : context[?x] |- _ ] => rewrite H in H'
                 | [ H : ?x = 1 |- context[?x] ] => rewrite H
                 | [ H : min ?x ?y = 1 |- _ ] => revert H; apply (Min.min_case_strong x y)
                 | _ => omega
               end. }
      { exfalso.
        unfold is_true in *.
        discriminate. }
    Qed.
  End generic_string.
End helpers.

Section IndexedImpl.
  Context (G : grammar Ascii.ascii).

  Local Notation T := (String.string * (nat * nat))%type (only parsing).

  Local Notation string_of_indexed s :=
    (substring (fst (snd s)) (snd (snd s)) (fst s))
      (only parsing).
  Local Notation ilength s :=
    (min (String.length (fst s) - fst (snd s)) (snd (snd s)))
      (only parsing).

  Definition expanded_fallback_list
             (s : T)
             (it : item Ascii.ascii) (its : production Ascii.ascii)
             (dummy : list nat)
  : Comp (T * list nat)
    := (ls <- (forall_reachable_productions
                 G
                 (fun p else_case
                  => if production_beq ascii_beq p (it::its)
                     then (match p return Comp (list nat) with
                             | nil => ret dummy
                             | _::nil => ret [ilength s]
                             | (Terminal _):: _ :: _ => ret [1]
                             | (NonTerminal nt):: p'
                               => if has_only_terminals p'
                                  then
                                    ret [ilength s - Datatypes.length p']
                                  else { splits : list nat
                                       | forall n,
                                           n <= ilength s
                                           -> parse_of_item G (take n (string_of_indexed s)) (NonTerminal nt)
                                           -> parse_of_production G (drop n (string_of_indexed s)) p'
                                           -> List.In n splits }
                           end)
                     else else_case)
                 (ret (match its, it with
                         | nil, _
                           => [ilength s]
                         | _::_, Terminal _
                           => [1]
                         | _::_, NonTerminal _
                           => if has_only_terminals its
                              then [ilength s - List.length its]
                              else dummy
                       end)));
        ret (s, ls))%comp.

  Global Arguments expanded_fallback_list / .


  (** Reference implementation of a [String] that can be split; has a [string], and a start index, and a length *)

  Definition rindexed_spec : ADT (string_rep Ascii.ascii) := ADTRep T {
    Def Constructor "new"(s : String.string) : rep :=
      ret (s, (0, String.length s)),

    Def Method "to_string"(s : rep, x : unit) : String.string :=
      ret (s, string_of_indexed s),

    Def Method "is_char"(s : rep, ch : Ascii.ascii) : bool  :=
      ret (s, string_beq (string_of_indexed s) (String.String ch "")),

    Def Method "length"(s : rep, x : unit) : nat :=
      ret (s, ilength s),

    Def Method "take"(s : rep, n : nat) : unit :=
      ret ((fst s, (fst (snd s), min (snd (snd s)) n)), tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret ((fst s, (fst (snd s) + n, snd (snd s) - n)), tt),

    Def Method "splits"(s : rep, p : item Ascii.ascii * production Ascii.ascii) : list nat :=
      dummy <- { ls : list nat | True };
      expanded_fallback_list s (fst p) (snd p) dummy
  }.

  Local Ltac fin :=
    repeat match goal with
             | _ => progress unfold split_list_is_complete
             | _ => progress simpl in *
             | _ => progress computes_to_inv
             | _ => progress subst
             | [ |- computes_to (Bind _ _) _ ]
               => refine ((fun H0 H1 => BindComputes _ _ _ _ H1 H0) _ _)
             | [ |- computes_to (Return ?x) ?y ]
               => cut (x = y);
                 [ let H := fresh in intro H; try rewrite H; eapply ReturnComputes | ]
             | [ |- computes_to (Pick _) _ ]
               => eapply PickComputes
             | _ => reflexivity
             | _ => assumption
           end;
    try solve [ rewrite substring_correct3'; reflexivity
              | repeat match goal with
                         | _ => intro
                         | _ => reflexivity
                         | _ => rewrite substring_substring
                         | _ => rewrite Nat.sub_0_r
                         | _ => rewrite substring_length
                         | _ => rewrite Nat.add_sub
                         | _ => rewrite <- Nat.sub_min_distr_r
                         | _ => progress simpl
                         | [ |- context[min ?x ?y] ]
                           => match goal with
                                | [ |- context[min y x] ]
                                  => rewrite (Min.min_comm x y)
                              end
                         | [ |- context[min (min _ ?x) (?x - ?y)] ]
                           => rewrite <- (Min.min_assoc _ x (x - y)), (Min.min_r x (x - y)) by omega
                         | [ |- substring (?x + ?y) _ _ = substring (?y + ?x) _ _ ]
                           => rewrite (Plus.plus_comm x y)
                         | [ |- substring ?x ?y ?z = substring ?x (min ?w ?y) ?z ]
                           => apply (@Min.min_case_strong w y)
                         | [ H : _ |- _ ] => rewrite Min.min_assoc in H
                         | _ => apply substring_correct4; omega
                       end
              | repeat match goal with
                         | _ => intro
                         | _ => progress subst
                         | [ |- List.In ?x [?y] ] => left
                         | _ => reflexivity
                         | [ H : parse_of_production _ _ nil |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_production _ _ (_::_) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_item _ _ (NonTerminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | _ => erewrite <- has_only_terminals_length by eassumption
                         | [ H : _ |- _ ] => progress rewrite ?(@drop_length _ string_stringlike string_stringlike_properties), ?(@take_length _ string_stringlike string_stringlike_properties), ?substring_length, ?Nat.add_sub, <- ?plus_n_O, ?Minus.minus_diag, ?Nat.sub_0_r, ?sub_plus in H by omega
                         | _ => progress rewrite ?drop_length, ?take_length, ?substring_length, ?Nat.add_sub, ?Minus.minus_diag, ?Nat.sub_0_r, <- ?plus_n_O, ?sub_plus by omega
                         | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
                         | [ |- _ \/ False ] => left
                         | [ H : substring _ _ _ = String.String _ _ |- _ = _ :> nat ] => apply (f_equal String.length) in H; simpl in H
                         | [ H : context[(_ ~= [ _ ])%string_like] |- _ ]
                           => apply length_singleton in H
                         | [ |- context[min ?x (?y + ?z) - ?z] ]
                           => rewrite <- (Nat.sub_min_distr_r x (y + z) z)
                         | [ H : context[min ?x (?y + ?z) - ?z] |- _ ]
                           => rewrite <- (Nat.sub_min_distr_r x (y + z) z) in H
                         | [ H : min ?x ?y = 1 |- _ ] => is_var x; revert H; apply (Min.min_case_strong x y)
                         | [ H : min ?x ?y = 1 |- _ ] => is_var y; revert H; apply (Min.min_case_strong x y)
                         | [ H : min ?x ?y = 0 |- _ ] => is_var x; revert H; apply (Min.min_case_strong x y)
                         | [ H : min ?x ?y = 0 |- _ ] => is_var y; revert H; apply (Min.min_case_strong x y)
                         | [ H : min ?x 1 = 0 |- _ ] => revert H; apply (Min.min_case_strong x 1)
                         | [ |- context[0 + ?x] ] => change (0 + x) with x
                         | [ |- context[?x - S ?y] ]
                           => not constr_eq y 0; rewrite !(Nat.sub_succ_r x y), !Minus.pred_of_minus
                         | [ H : ?x = 1 |- context[?x] ] => rewrite H
                         | [ H : ?x = 1, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : ?x <= ?y |- context[?x - ?y] ] => replace (x - y) with 0 by (clear -H; omega)
                         | [ H : context[?x - ?y], H' : ?x <= ?y |- _ ]
                           => rewrite (proj2 (@Nat.sub_0_le x y)) in H by exact H'
                         | [ H : context[min 0 ?x] |- _ ] => change (min 0 x) with 0 in H
                         | [ |- 1 = ?x ] => is_var x; destruct x
                         | [ |- 1 = S ?x ] => is_var x; destruct x
                         | [ H : _ <= 0 |- _ ] => apply Le.le_n_0_eq in H; symmetry in H
                         | [ H : context[min 1 ?x] |- _ ] => is_var x; destruct x
                         | [ H : context[min 1 (S ?x)] |- _ ] => is_var x; destruct x
                         | [ H : context[min 1 (S ?x)] |- _ ] => change (min 1 (S x)) with 1 in H
                         | [ H : context[min ?x ?y], H' : ?x <= ?y |- _ ] => rewrite Min.min_l in H by assumption
                         | [ H : context[min ?x ?y], H' : ?y <= ?x |- _ ] => rewrite Min.min_r in H by assumption
                         | [ H : context[min (?x - ?y) ?x] |- _ ] => rewrite Min.min_l in H by omega
                         | [ H : context[min ?x (?x - ?y)] |- _ ] => rewrite Min.min_r in H by omega
                         | _ => omega
                       end ].

  Lemma FirstStep
  : refineADT (string_spec G) rindexed_spec.
  Proof.
    econstructor 1 with (AbsR := (fun r_o r_n =>
                                    substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o));

        eapply Iterate_Ensemble_BoundedIndex_equiv;
        simpl; intuition; intros; try simplify with monad laws;
        repeat intro; computes_to_inv; subst; simpl;
        fin.
    { intros.
      match goal with
        | [ H' : appcontext[forall_reachable_productions], H : production_is_reachable G (?x::?xs) |- _ ]
          => move H' at top; move H at top; generalize dependent xs; intros xs H H';
             move H' at top; move H at top; generalize dependent x; intros x H; revert x xs H
      end.
      refine (proj2 (@production_is_reachable__forall_reachable_productions' Ascii.ascii G _) _).
      apply (forall_reachable_productions_helper (@ascii_bl) (@ascii_lb)).
      unfold forall_reachable_productions.
      lazymatch goal with
        | [ |- context[fold_right (fun x y => @?P x /\ y) _ _] ]
          => let H' := fresh in
             pose proof (fold_right_map P and) as H';
               unfold compose in H'; simpl in H';
               rewrite <- H'; clear H'
      end.
      generalize (flatten
                    (flatten
                       (map (fun nt : string => map tails (G nt))
                            (Valid_nonterminals G)))).
      intro ls; induction ls; simpl; trivial; [].
      { repeat match goal with
                 | [ |- _ /\ _ ] => split
                 | [ |- context[match ?e with _ => _ end] ] => atomic e; destruct e
                 | [ |- context[production_beq _ ?x ?x] ] => rewrite (production_lb (@ascii_lb) eq_refl)
                 | _ => solve [ trivial ]
               end.
        { clear IHls; intros; abstract fin. }
        { clear IHls; intros; abstract fin. }
        { clear IHls; intros; abstract fin. }
        { clear IHls.
          abstract (
              repeat match goal with
                       | _ => intro
                       | [ H : context[if has_only_terminals ?e then _ else _] |- _ ]
                         => (revert H; case_eq (has_only_terminals e))
                       | _ => progress computes_to_inv
                       | _ => progress subst
                       | [ |- In _ [_] ] => left
                       | _ => erewrite <- has_only_terminals_length by eassumption
                       | [ H : _ |- _ ] => progress rewrite ?substring_length, ?Nat.add_sub in H
                       | _ => progress rewrite ?substring_length, ?Nat.add_sub
                       | [ |- context[min ?x (?y + ?z) - ?z] ]
                         => rewrite <- (Nat.sub_min_distr_r x (y + z) z)
                       | [ H : context[min ?x (?y + ?z) - ?z] |- _ ]
                         => rewrite <- (Nat.sub_min_distr_r x (y + z) z) in H
                       | [ |- context[min (?x - ?y) ?x] ] => rewrite (Min.min_l (x - y) x) by omega
                       | [ |- context[min ?x (?x - ?y)] ] => rewrite (Min.min_r x (x - y)) by omega
                       | _ => omega
                       | _ => solve [ eauto ]
                     end
            ). } } }
  Qed.
End IndexedImpl.
