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
                             | _::nil => ret [min (String.length (fst s) - fst (snd s)) (snd (snd s))]
                             | (Terminal _):: _ :: _ => ret [1]
                             | (NonTerminal nt):: p'
                               => if has_only_terminals p'
                                  then
                                    ret [min (String.length (fst s) - fst (snd s)) (snd (snd s)) -
                                         Datatypes.length p']
                                  else { splits : list nat
                                       | forall n,
                                           n <= length (fst s)
                                           -> parse_of_item G (take n (fst s)) (NonTerminal nt)
                                           -> parse_of_production G (drop n (fst s)) p'
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

  Local Ltac fin2 :=
    repeat match goal with
             | [ H : fold_right and _ (map _ ?ls) |- fold_right and _ (map _ ?ls) ]
               => revert H; apply fold_right_and_map_impl
             | _ => intro
             | _ => progress subst
             | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
             | [ |- context[production_beq ?d ?x ?y] ]
               => case_eq (production_beq d x y); intro
             | [ H : context[if production_beq ?d ?x ?y then _ else _] |- _ ]
               => revert H; case_eq (production_beq d x y); intro
             | [ H : production_beq _ _ _ = true |- _ ] => apply (production_bl (@ascii_bl)) in H
             | [ H : (_::_) = (_::_) |- _ ] => inversion H; clear H
             | _ => progress eauto
             | [ |- context[match ?x with _ => _ end] ] => atomic x; destruct x
             | [ H : _ -> _ |- _ ] => clear H; solve [ fin ]
           end.

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
        | [ H : production_is_reachable G (?x::?xs) |- _ ]
          => move H at top; generalize dependent xs; intros xs H; move H at top; generalize dependent x; intros x H; revert x xs H
      end.
      refine (proj2 (@production_is_reachable__forall_reachable_productions' Ascii.ascii G _) _).
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
        { admit. }
        { abstract fin2. }
        { abstract fin2. }
        { abstract fin2. }
        { revert IHls; apply fold_right_and_map_impl;
          repeat match goal with
                   | [ |- ?x -> ?x ] => exact (fun y => y)
                   | [ |- forall x, @?P x ]
                     => match goal with
                          | [ |- ?A -> ?B ] => fail 1
                          | _ => intro
                        end
                   | [ |- match ?x with _ => _ end -> match ?x with _ => _ end ]
                     => destruct x
                   | [ |- (?x -> _) -> ?x -> _ ]
                     => let H := fresh in
                        let y := fresh in
                        intros H y; specialize (H y); clear y; revert H
                   | [ |- (_ -> ?x) -> _ -> ?x ]
                     => let H := fresh in
                        let y := fresh in
                        intros H y; apply H; clear H; revert y
                   | [ |- (_ -> ?x -> _) -> _ -> ?x -> _ ]
                     => let H := fresh in
                        let y := fresh in
                        let z := fresh in
                        intros H y z;
                          specialize (fun y => H y z); revert H y; clear z
                   | [ |- ?A -> ?B ]
                     => match A with
                          | context[if ?x then _ else _]
                            => match B with
                                 | context[if x then _ else _]
                                   => fail 1
                                 | _ => case_eq x; intro
                               end
                        end
                 end.
          lazymatch goal with
                   | [ |- _ -> computes_to (fold_right _ _ ?ls) ?v ]
                     => induction ls
end.
          try match goal with
                   | [ |- ?A -> ?B ]
                     => match A with
                          | context[if ?x then _ else _]
                            => match B with
                                 | context[if x then _ else _]
                                   => fail 1
                                 | _ => case_eq x; intro
                               end
                        end
end.
          refine (fun
          intros x y.
fin2.
          match goal with
             | [ H : context[if has_only_terminals ?ls then _ else _] |- _ ]
               => revert H; case_eq (has_only_terminals ls)
          end.
          { fin2.
            match goal with
            end.
            fin2.
            clear H4.
            destruct i; fin2; fin;
            try match goal with
                end.
            left; fin.
            pose has_only_terminals_length.
            Focus 2.
            { fin.
            Local Opaque has_only_terminals.
            fin.
 }
        { revert IHls; apply fold_right_and_map_impl; trivial; [].
          intros []; trivial.
          repeat match goal with
                   | _ => intro
                   | _ => progress subst
                   | [ |- context[production_beq ?d ?x ?y] ]
                     => case_eq (production_beq d x y); intro
                   | [ H : context[if production_beq ?d ?x ?y then _ else _] |- _ ]
                     => revert H; case_eq (production_beq d x y); intro
                   | [ H : production_beq _ _ _ = true |- _ ] => apply (production_bl (@ascii_bl)) in H
                   | [ H : (_::_) = (_::_) |- _ ] => inversion H; clear H
                   | _ => progress eauto
                   | [ H : _ -> _ |- _ ] => clear H; solve [ fin ]
                 end. }
        { revert IHls; apply fold_right_and_map_impl; trivial; [].
          intros []; trivial.
          repeat match goal with
                   | _ => intro
                   | _ => progress subst
                   | [ |- context[production_beq ?d ?x ?y] ]
                     => case_eq (production_beq d x y); intro
                   | [ H : context[if production_beq ?d ?x ?y then _ else _] |- _ ]
                     => revert H; case_eq (production_beq d x y); intro
                   | [ H : production_beq _ _ _ = true |- _ ] => apply (production_bl (@ascii_bl)) in H
                   | [ H : (_::_) = (_::_) |- _ ] => inversion H; clear H
                   | _ => progress eauto
                   | [ H : _ -> _ |- _ ] => clear H; solve [ fin ]
                 end. }

          { clear H1.

fin.
apply H1; eauto.


                   | [ H : parse_of_production _ _ nil |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                   | [ H : parse_of_production _ _ (_::_) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                   | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                   | [ H : parse_of_item _ _ (NonTerminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                   | _ => progress computes_to_inv
                 end.
          apply H1; eauto.
          { intros; fin. }
          { intros; fin.
            eauto. } }
{
 fin.
intros.

  intuition.
  intros init1 init2 H.
 SearchAbout fold_right.
clear IHls; intros; fin.
repeat match goal with
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
                       end.

 }
        {
          repeat match goal with
                   | [ H : parse_of_production _ _ [] |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                   | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                 end;
            fin.
          repeat match goal with
                       end.
          match goal with
          end.
SearchAbout min.
          SearchAbout (_ <= 0).
          end

SearchAbout (?x - ?y) (?x <= ?y).
SearchAbout (_ + 0).
          Check string_bl.

          admit. }
        { clear IHls; intros.
          repeat match goal with
                   | [ H : parse_of_production _ _ [] |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                   | [ H : parse_of_production _ _ (_::_) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                   | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                 end;
            fin.
          admit. }


SearchAbout string_beq.
          left; fin.
          repeat match goal with
                         | _ => intro
                         | _ => progress subst
                         | [ |- List.In ?x [?y] ] => left
                         | _ => reflexivity
                         | [ H : parse_of_production _ _ nil |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_production _ _ (_::_) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_item _ _ (NonTerminal _ _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | _ => erewrite <- has_only_terminals_length by eassumption
                         | [ H : _ |- _ ] => progress rewrite ?(@drop_length _ string_stringlike string_stringlike_properties), ?(@take_length _ string_stringlike string_stringlike_properties), ?substring_length, ?Nat.add_sub, ?Minus.minus_diag, ?Nat.sub_0_r, ?sub_plus in H by omega
                         | _ => progress rewrite ?drop_length, ?take_length, ?substring_length, ?Nat.add_sub, ?Minus.minus_diag, ?Nat.sub_0_r, ?sub_plus by omega
                         | [ H : context[(_ ~= [ _ ])%string_like] |- _ ]
                           => apply length_singleton in H
                         | [ |- context[min ?x (?y + ?z) - ?z] ]
                           => rewrite <- (Nat.sub_min_distr_r x (y + z) z)
                         | [ H : context[min ?x (?y + ?z) - ?z] |- _ ]
                           => rewrite <- (Nat.sub_min_distr_r x (y + z) z) in H
                         | [ H : min ?x ?y = 1 |- _ ] => is_var x; revert H; apply (Min.min_case_strong x y)
                         | [ |- context[0 + ?x] ] => change (0 + x) with x
                         | [ |- context[?x - S ?y] ]
                           => not constr_eq y 0; rewrite !(Nat.sub_succ_r x y), !Minus.pred_of_minus
                         | [ H : ?x = 1 |- context[?x] ] => rewrite H
                         | [ H : ?x = 1, H' : context[?x] |- _ ] => rewrite H in H'
                         | [ H : ?x <= ?y |- context[?x - ?y] ] => replace (x - y) with 0 by (clear -H; omega)
                         | _ => omega
                       end.
          repeat match goal with
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
                       end.
                     fin.
          left; fin.



  rewrite <- H.


      induction (Valid_nonterminals G) as [ | x xs ]; trivial; [].
      { simpl.
        rewrite !flatten_app, !fold_right_app.

        destruct (G x) as [ | x' xs' ]; simpl.
        { induction xs as [ | x'' xs'' ]; simpl; trivial; [].
          { rewrite !flatten_app, !fold_right_app.
      apply p.
match goal with

match goal with
        | [ H : computes_to (fold_right _ _ _) ?v |- _ ] => clear -H; generalize dependent v
      end.

      induction (Valid_nonterminals G) as [ | x xs IHnt ]; simpl in *.
      { simpl in *; intros; destruct_head ex; destruct_head and; destruct_head False. }
      { intro v1.
        rewrite flatten_app, fold_right_app.
        intros H0 n H1 H2 H3 [nt [prefix [ [H4|H4] H4'] ] ].
        { subst.
        specialize (fun v1 H0 H4 => IHnt v1 H0 n H1 H2 H3 (ex_intro _ nt (ex_intro _ prefix H4))); simpl in *.
        induction (G nt).
        { intros; destruct_head ex; destruct_head and; destruct_head or; subst;
          repeat match goal with
                   | [ H : _ |- _ ] => not constr_eq H HG; rewrite HG in H
                   | _ => progress simpl in *
                   | [ H : False |- _ ] => destruct H
                 end. }
        { destruct_head and; destruct_head or; subst.
        induction (G nt)
Goal forall P Q, (P \/ ~P) -> (((P -> Q) -> P) -> P).
  intros P Q [p|np] pq.
  exact p.
  apply pq.
  intro
  destruce

intros; destruct_head ex; destruct_head and; destruct_head or; subst.

        { apply IHnt; clear IHnt.

repeat match goal with
                 | [ H : _ |- _ ] => rewrite flatten_app in H
                 | [ H : _ |- _ ] => rewrite fold_right_app in H
               end.
        SearchAbout fold_right app.
rewrite flatten_append in H0'.

    repeat match goal with
                 | _ => progress simpl in *
                 | _ => progress computes_to_inv
                 | _ => progress subst
                 (*| [ H : context[match ?x with _ => _ end] |- _ ] => (is_var x; destruct x)
                 | [ |- context[match ?x with _ => _ end] ] => (is_var x; destruct x)
                 | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?*)
                 | [ |- computes_to (Bind _ _) _ ]
                   => refine ((fun H0 H1 => BindComputes _ _ _ _ H1 H0) _ _)
                 | [ |- computes_to (Return ?x) ?y ]
                   => cut (x = y);
                 [ let H := fresh in intro H; try rewrite H; eapply ReturnComputes | ]
                 | [ |- computes_to (Pick _) _ ]
                   => eapply PickComputes
                 | _ => reflexivity
                 | _ => assumption
               end.


      ).
  Defined.

  (*Lemma AllTheSteps
  : Sharpened (string_spec G).
    eapply SharpenStep.
    apply FirstStep.

    (*hone representation using
         (fun r_o r_n =>
                    substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o).
    hone constructor "new".
    {
      simplify with monad laws.
      refine pick val (d, (0, String.length d)).
      subst H; higher_order_reflexivity.
      simpl.
      finish honing. *)

  Admitted.
*)
End IndexedImpl.



(** * Reflective helpers for simply-typed interface of the parser *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Lt.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarProperties.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.ParserADTSpecification.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import ADTSynthesis.ADTRefinement.
Require Import ADTSynthesis.Common.StringBound ADTSynthesis.Common.ilist.
Require Import ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import ADTSynthesis.Common.IterateBoundedIndex.
Require Import ADTSynthesis.Computation.Core ADTSynthesis.Computation.ApplyMonad ADTSynthesis.Computation.Monad ADTSynthesis.Computation.SetoidMorphisms.
Require Import ADTSynthesis.Common.SetoidInstances.

Set Implicit Arguments.

Section interface.
  Context (G : grammar Ascii.ascii).

  Local Notation string_of_indexed s :=
    (substring (fst (snd s)) (snd (snd s)) (fst s))
      (only parsing).
  Local Notation ilength s :=
    (min (String.length (fst s) - fst (snd s)) (snd (snd s)))
      (only parsing).



Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

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

  (** Reference implementation of a [String] that can be split; has a [string], and a start index, and a length *)
  (** TODO: should we replace

       [string_dec (string_of_indexed s) (String.String ch "") : bool]

      with something fancier and maybe more efficient, like

        [((Nat.eq_dec (min (String.length base - fst s) (snd s)) 1) &&
  (option_dec Ascii.ascii_dec (String.get (fst s) base) (Some
  ch)))%bool] *)

  Definition indexed_spec : ADT (string_rep Ascii.ascii) := ADTRep T {
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
      fallback_ls <- { ls : list nat
                     | match fst p with
                         | Terminal _
                           => True
                         | NonTerminal _
                           => if has_only_terminals (snd p)
                              then True
                              else split_list_is_complete G (string_of_indexed s) (fst p) (snd p) ls
                       end };
      let ls := (match snd p, fst p with
                   | nil, _
                     => [ilength s]
                   | _::_, Terminal _
                     => [1]
                   | _::_, NonTerminal _
                     => if has_only_terminals (snd p)
                        then [ilength s - List.length (snd p)]
                        else fallback_ls
                 end) in
      ret (s, ls)
  }.

  Lemma FirstStep
  : refineADT (string_spec G) indexed_spec.
  Proof.
    econstructor 1 with (AbsR := (fun r_o r_n =>
                                    substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o));
    abstract (
        eapply Iterate_Ensemble_BoundedIndex_equiv;
        simpl; intuition; intros; try simplify with monad laws;
        repeat intro; computes_to_inv; subst; simpl;
        repeat match goal with
                 | _ => progress simpl in *
                 | _ => progress computes_to_inv
                 | _ => progress subst
                 | [ H : context[match ?x with _ => _ end] |- _ ] => (is_var x; destruct x)
                 | [ |- context[match ?x with _ => _ end] ] => (is_var x; destruct x)
                 | [ H : context[match ?x with _ => _ end] |- _ ] => destruct x eqn:?
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
                             | [ H : parse_of_item _ _ (NonTerminal _ _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                             | _ => erewrite <- has_only_terminals_length by eassumption
                             | [ H : _ |- _ ] => progress rewrite ?(@drop_length _ string_stringlike string_stringlike_properties), ?(@take_length _ string_stringlike string_stringlike_properties), ?substring_length, ?Nat.add_sub, ?Minus.minus_diag, ?Nat.sub_0_r, ?sub_plus in H by omega
                             | _ => progress rewrite ?drop_length, ?take_length, ?substring_length, ?Nat.add_sub, ?Minus.minus_diag, ?Nat.sub_0_r, ?sub_plus by omega
                             | [ H : context[(_ ~= [ _ ])%string_like] |- _ ]
                               => apply length_singleton in H
                             | [ |- context[min ?x (?y + ?z) - ?z] ]
                               => rewrite <- (Nat.sub_min_distr_r x (y + z) z)
                             | [ H : context[min ?x (?y + ?z) - ?z] |- _ ]
                               => rewrite <- (Nat.sub_min_distr_r x (y + z) z) in H
                             | [ H : min ?x ?y = 1 |- _ ] => is_var x; revert H; apply (Min.min_case_strong x y)
                             | [ |- context[0 + ?x] ] => change (0 + x) with x
                             | [ |- context[?x - S ?y] ]
                               => not constr_eq y 0; rewrite !(Nat.sub_succ_r x y), !Minus.pred_of_minus
                             | [ H : ?x = 1 |- context[?x] ] => rewrite H
                             | [ H : ?x = 1, H' : context[?x] |- _ ] => rewrite H in H'
                             | [ H : ?x <= ?y |- context[?x - ?y] ] => replace (x - y) with 0 by (clear -H; omega)
                             | _ => omega
                           end ]
      ).
  Defined.

  (*Lemma AllTheSteps
  : Sharpened (string_spec G).
    eapply SharpenStep.
    apply FirstStep.

    (*hone representation using
         (fun r_o r_n =>
                    substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o).
    hone constructor "new".
    {
      simplify with monad laws.
      refine pick val (d, (0, String.length d)).
      subst H; higher_order_reflexivity.
      simpl.
      finish honing. *)

  Admitted.
*)
End IndexedImpl.


  Lemma step_expanded_fallback_list {s p} dummy
  : refine (fallback_ls <- {ls : list nat |
                            match fst p with
                              | Terminal _ => True
                              | NonTerminal _ =>
                                if has_only_terminals (snd p)
                                then True
                                else
                                  split_list_is_complete G
                                                         (substring (fst (snd s))
                                                                    (snd (snd s)) (fst s))
                                                         (fst p) (snd p) ls
                            end};
            ret
              (s,
               match snd p with
                 | [] => [min (String.length (fst s) - fst (snd s)) (snd (snd s))]
                 | _ :: _ =>
                   match fst p with
                     | Terminal _ => [1]
                     | NonTerminal _ =>
                       if has_only_terminals (snd p)
                       then
                         [min (String.length (fst s) - fst (snd s)) (snd (snd s)) -
                          Datatypes.length (snd p)]
                       else fallback_ls
                   end
               end))
           (expanded_fallback_list s (fst p) (snd p) dummy).
  Proof.
    unfold expanded_fallback_list, forall_reachable_productions, split_list_is_complete, production_is_reachable.
    generalize (Valid_nonterminals G).
    match goal with
      | [ |- context[match snd p with nil => ?x | _ => _ end] ]
        => let H := fresh "nil_case" in generalize x; intro H
    end.
    generalize (has_only_terminals (snd p)); intro test.
    generalize [1]; intro one_list.
    intro ls.
    match goal with
      | [ |- context[if test then [?x - _] else _] ]
        => not constr_eq x True; let H := fresh "then_case" in generalize x; intro H
    end.
    induction ls.
    { simpl.
      repeat intro; computes_to_inv; subst.
      destruct (fst p), (snd p); simpl;
      repeat match goal with
               | [ |- computes_to (Bind _ _) _ ]
                 => refine ((fun H0 H1 => BindComputes _ _ _ _ H1 H0) _ _)
               | [ |- computes_to (Return _) _ ]
                 => apply ReturnComputes
               | [ |- computes_to (Pick _) _ ]
                 => apply PickComputes
               | _ => solve [ trivial ]
               | _ => intro
               | _ => progress destruct_head ex
               | _ => progress destruct_head and
               | _ => progress destruct_head False
               | [ |- if ?e then _ else _ ] => case_eq e
             end. }
    { simpl.
      setoid_rewrite flatten_app.
      setoid_rewrite fold_right_app.
      lazymatch goal with
        | [ |- refine _ (ls <- fold_right ?f ?x ?k; ret (?s, ls)) ]
          => transitivity (ls <- fold_right f (lss <- (ls <- x; ret (s, ls)); ret (snd lss)) k; ret (s, ls))%comp;
            [
            | setoid_rewrite refineEquiv_bind_bind;
              setoid_rewrite refineEquiv_bind_unit; simpl;
              setoid_rewrite refineEquiv_unit_bind;
              reflexivity ]
      end.
      setoid_rewrite <- IHls; clear IHls.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_unit; simpl.
      let LHS := match goal with |- refine ?LHS ?RHS => constr:LHS end in
      lazymatch LHS with
        | context G0[exists (nt : string) (prefix : list ?A),
                      (?a = nt \/ In nt ?ls) /\
                      In (prefix ++ ?rest) (Lookup ?G nt)]
          => let H := fresh in
             assert (H : (exists nt prefix, (a = nt \/ In nt ls) /\ In (prefix ++ rest) (Lookup G nt)) <-> (exists prefix, In (prefix ++ rest) (Lookup G a)) \/ (exists nt prefix, In nt ls /\ In (prefix ++ rest) (Lookup G nt)))
             by (split; intros; repeat (destruct_head ex || destruct_head or);
                   intuition (subst; eauto));
             let G' := context G0[(exists prefix, In (prefix ++ rest) (Lookup G a)) \/ (exists nt prefix, In nt ls /\ In (prefix ++ rest) (Lookup G nt))] in
             transitivity G'
      end.
      { apply refine_bind_Proper; [ | reflexivity ].
        apply refine_flip_impl_Pick_Proper.
        destruct (fst p).
        typeclasses eauto.
        destruct test.
        typeclasses eauto.
        intro.
        intros ?.

Goal forall {A B} (H : A <-> B), forall n : nat, n = n -> B.
  intros A B H.
  setoid_rewrite <- H.
        setoid_rewrite H.
        typeclasses eauto.
        intro.
        unfold flip.
        SearchAbout impl.
        destruct (fst p); trivial.
intros ??.

        destruct (fst p).
        setoid_rewrite H.
               by (split; intros; repeat (destruct_head ex || destruct_head or);
                   intuition (subst; eauto));
               let P := fresh in
               set (P := exists nt prefix, (a = nt \/ In nt ls) /\ In (prefix ++ rest) (Lookup G nt)) in *
      end.
      setoid_rewrite H.

      Typeclasses eauto := debug.
      setoid_rewrite H.
      {


      intuition.
 tauto.
      repeat intro;
        computes_to_inv; subst.
      computes_to_inv.
              setoid_rewrite refineEquiv_unit_bind;

      Typeclasses eauto := debug.
      Focus 2.


      pose proof (_ : (Proper (refine ==> _ ==> _)
   (fold_right
      (fun (p0 : production Ascii.ascii) (else_case : Comp (list nat)) =>
       if production_beq ascii_beq p0 (fst p :: snd p)
       then
        match p0 with
        | [] => ret dummy
        | [Terminal _] => ret nil_case
        | Terminal _ :: _ :: _ => ret one_list
        | [NonTerminal nt] => ret nil_case
        | NonTerminal nt :: (_ :: _) as p' =>
            if has_only_terminals p'
            then ret [then_case - Datatypes.length p']
            else
             {splits : list nat |
             forall n : nat,
             n <= String.length (fst s) ->
             parse_of_item G (substring 0 n (fst s)) (NonTerminal nt) ->
             parse_of_production G
               (substring n (String.length (fst s)) (fst s)) p' ->
             In n splits}%comp
        end
       else else_case)))).
            Typeclasses eauto := debug.
            Timeout 1 pose proof (fun A => _ : Proper (_ ==> refine ==> impl) (@refine A)).

(Proper (refine ==> flip impl)
   (refine
      (fallback_ls <- {ls0 : list nat |
                      match fst p with
                      | Terminal _ => True
                      | NonTerminal _ =>
                          if test
                          then True
                          else
                           forall n : nat,
                           n <=
                           String.length
                             (substring (fst (snd s)) (snd (snd s)) (fst s)) ->
                           parse_of_item G
                             (substring 0 n
                                (substring (fst (snd s))
                                   (snd (snd s)) (fst s)))
                             (fst p) ->
                           parse_of_production G
                             (substring n
                                (String.length
                                   (substring (fst (snd s))
                                      (snd (snd s))
                                      (fst s)))
                                (substring (fst (snd s))
                                   (snd (snd s)) (fst s)))
                             (snd p) ->
                           (exists
                              (nt : string) (prefix :
                                             list (item Ascii.ascii)),
                              (a = nt \/ In nt ls) /\
                              In (prefix ++ fst p :: snd p) (G nt)) ->
                           In n ls0
                      end};
       ret
         (s,
         match snd p with
         | [] => nil_case
         | _ :: _ =>
             match fst p with
             | Terminal _ => one_list
             | NonTerminal _ =>
                 if test
                 then [then_case - Datatypes.length (snd p)]
                 else fallback_ls
             end
         end))))

      Focus 2.
      pose proof (_ : (Proper (refineEquiv ==> _ ==> _)
   (fold_right
      (fun (p0 : production Ascii.ascii) (else_case : Comp (list nat)) =>
       if production_beq ascii_beq p0 (fst p :: snd p)
       then
        match p0 with
        | [] => ret dummy
        | [Terminal _] => ret nil_case
        | Terminal _ :: _ :: _ => ret one_list
        | [NonTerminal nt] => ret nil_case
        | NonTerminal nt :: (_ :: _) as p' =>
            if has_only_terminals p'
            then ret [then_case - Datatypes.length p']
            else
             {splits : list nat |
             forall n : nat,
             n <= String.length (fst s) ->
             parse_of_item G (substring 0 n (fst s)) (NonTerminal nt) ->
             parse_of_production G
               (substring n (String.length (fst s)) (fst s)) p' ->
             In n splits}%comp
        end
       else else_case)))).
      pose proof (_ : (ProperProxy eq (flatten (map tails (G a))))).
      setoid_rewrite refineEquiv_bind_bind.



      Check (_ : (Proper
                    (pointwise_relation (production Ascii.ascii)
      (refineEquiv ==> refineEquiv)%signature)
   (fun (p0 : production Ascii.ascii) (else_case : Comp (list nat)) =>
    if production_beq ascii_beq p0 (fst p :: snd p)
    then
     match p0 with
     | [] => ret dummy
     | [Terminal _] => ret nil_case
     | Terminal _ :: _ :: _ => ret one_list
     | [NonTerminal nt] => ret nil_case
     | NonTerminal nt :: (_ :: _) as p' =>
         if has_only_terminals p'
         then ret [then_case - Datatypes.length p']
         else
          {splits : list nat |
          forall n : nat,
          n <= String.length (fst s) ->
          parse_of_item G (substring 0 n (fst s)) (NonTerminal nt) ->
          parse_of_production G (substring n (String.length (fst s)) (fst s))
            p' -> In n splits}%comp
     end
    else else_case))).

      Focus 2.
      intro.
      match goal with
        | [ |- ?R ?f ?f ] => change (Proper R f)
      end.
      exact _.


      .
      match goal with
        | [ |- refine (u <- ?x; u' <- ret (@?f u); ret (@?g u')) _ ]
          => transitivity (u <- x; ret (g (f (u))))%comp;
            [ apply refine_bind_Proper;
              [ reflexivity | ]
            | ]
      end.
      intro; simpl.

      rewrite <- refine_unit_bind'.
      3:rewrite refineEquiv_bind_bind.
      Focus 2.
      { asse

Lemma refineEquiv_bind_bind_ret {A B C} (c1 : Comp A) (f1 : A -> Comp B) (f2 : B -> Comp C)
: refineEquiv (b <- (a <- c1; f1 a); f2 b) (a <- c1; b <- f1 a; f2 b).
Proof.
  split; repeat intro; computes_to_inv;
  repeat repeat (eassumption || refine ((fun H0 H1 => BindComputes _ _ _ _ H1 H0) _ _)).
Qed.
Lemma refine_bind_bind_ret {A B C} (c1 : Comp A) (f1 : A -> Comp B) (f2 : B -> Comp C)
: refine (b <- (a <- c1; f1 a); f2 b) (a <- c1; b <- f1 a; f2 b).
Proof.
  apply refineEquiv_bind_bind_ret.
Qed.
Lemma refine_bind_bind_ret' {A B C} (c1 : Comp A) (f1 : A -> Comp B) (f2 : B -> Comp C)
: refine (a <- c1; b <- f1 a; f2 b) (b <- (a <- c1; f1 a); f2 b).
Proof.
  apply refineEquiv_bind_bind_ret.
Qed.
Focus 2.
SearchAbout refine Bind.
apply refine_fold_right.
SearchAbout refine fold_right.
apply fold_right_refine_Proper.
setoid_rewrite refine_bind_bind_ret.

      SearchAbout (_ <- _ (_ <- _; ret _); _)%comp.
      Focus 2.
      SearchAbout refine Bind.
      simplify with setoid-y monad laws.
      end.

setoid_rewrite IHls.
      match goal with
        | [ |
      SearchAbout fold_right app.
  SearchAbout (_ ++ _ ++ _).
      SearchAbout flatten1 append.
      match goal with
      {
    intro ls; induction ls
    simplify with monad laws.

{ls : list nat |
                     match fst n with
                     | Terminal _ => True
                     | NonTerminal _ =>
                         if has_only_terminals (snd n)
                         then True
                         else
                          split_list_is_complete G
                            (substring (fst (snd r_n))
                               (snd (snd r_n)) (fst r_n))
                            (fst n) (snd n) ls
                     end}


  (** A production is reachable if it is the tail of a production
      associated to a valid nonterminal. *)
  Definition production_is_reachable (p : production Char) : Prop
    := exists nt prefix,
         List.In nt (Valid_nonterminals G)
         /\ List.In
              (prefix ++ p)
              (Lookup G nt).

  (** A list of splits is complete if, for every reachable production,
      it contains every index of the string that yields a parse tree
      for that production by splitting at that index. *)
  Definition split_list_is_complete `{HSL : StringLike Char} (str : String) (it : item Char) (its : production Char)
             (splits : list nat)
  : Prop
    := forall n,
         n <= length str
         -> parse_of_item G (take n str) it
         -> parse_of_production G (drop n str) its
         -> production_is_reachable (it::its)
         -> List.In n splits.

  Record Splitter :=
    {
      string_type :> StringLike Char;
      splits_for : String -> item Char -> production Char -> list nat;
      (** give a list of indices for splitting a given string *)

      string_type_properties :> StringLikeProperties Char;
      splits_for_complete : forall str it its,
                              split_list_is_complete str it its (splits_for str it its)
      (** [splits_for] must contain all valid indices for splitting *)
    }.

  Global Existing Instance string_type.
  Global Existing Instance string_type_properties.

  Record Parser (splitter : Splitter) :=
    {
      has_parse : @String Char splitter -> bool;
      (** does this string parse as the start symbol of the grammar? *)

      has_parse_sound : forall str,
                          has_parse str = true
                          -> parse_of_item G str (NonTerminal (Start_symbol G));

      has_parse_complete : forall str (p : parse_of_item G str (NonTerminal (Start_symbol G))),
                             Forall_parse_of_item
                               (fun _ nt => List.In nt (Valid_nonterminals G))
                               p
                             -> has_parse str = true
    }.
End interface.


Global Arguments forall_reachable_productions / .
