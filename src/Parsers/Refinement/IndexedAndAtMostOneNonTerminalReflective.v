(** First step of a splitter refinement; indexed representation, and handle all rules with at most one nonterminal; leave a reflective goal *)
Require Import Coq.Strings.String Coq.Arith.Lt Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.Refinement.FixedLengthLemmas.
Require Import Fiat.ADTNotation.BuildADT Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.Common Fiat.Common.Equality.
Require Import Fiat.ADTRefinement.
Require Import Fiat.Common.StringBound Fiat.Common.ilist.
Require Import Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import Fiat.Common.IterateBoundedIndex.
Require Import Fiat.Common.List.FlattenList.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.StringFacts.
Require Import Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Import Fiat.Computation.SetoidMorphisms.

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
                                      => If production_beq Char_beq p0 (x::xs)
                                         Then ct p0
                                         Else else_case)
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
    (String.substring (fst (snd s)) (snd (snd s)) (fst s))
      (only parsing).
  Local Notation ilength s :=
    (min (String.length (fst s) - fst (snd s)) (snd (snd s)))
      (only parsing).
  Local Notation iget n s :=
    (get n (string_of_indexed s))
      (only parsing).

  Definition expanded_fallback_list'
             (P : String -> item Ascii.ascii -> production Ascii.ascii -> item Ascii.ascii -> production Ascii.ascii -> list nat -> Prop)
             (s : T)
             (it : item Ascii.ascii) (its : production Ascii.ascii)
             (dummy : list nat)
  : Comp (T * list nat)
    := (ls <- (forall_reachable_productions
                 G
                 (fun p else_case
                  => If production_beq ascii_beq p (it::its)
                     Then (match p return Comp (list nat) with
                             | nil => ret dummy
                             | _::nil => ret [ilength s]
                             | (Terminal _):: _ :: _ => ret [1]
                             | (NonTerminal nt):: p'
                               => If has_only_terminals p'
                                  Then
                                    ret [(ilength s - Datatypes.length p')%natr]
                                  Else
                                  (option_rect
                                     (fun _ => Comp (list nat))
                                     (fun (n : nat) => ret [n])
                                     { splits : list nat
                                     | P
                                         (string_of_indexed s)
                                         (NonTerminal nt)
                                         p'
                                         it
                                         its
                                         splits }%comp
                                     (length_of_any G nt))
                           end)
                     Else else_case)
                 (ret dummy));
        ret (s, ls))%comp.

  Global Arguments expanded_fallback_list' / .

  Definition expanded_fallback_list
    := expanded_fallback_list' (fun str it its _ _ => split_list_is_complete G str it its).
  Definition split_list_is_complete_case
             str it its it' its' splits
    := forall n,
         n <= length str
         -> production_is_reachable G (it'::its')
         -> parse_of_item G (take n str) it
         -> parse_of_production G (drop n str) its
         -> List.In n (List.map (min (length str)) splits).
  Definition expanded_fallback_list_case
    := expanded_fallback_list' split_list_is_complete_case.

  Definition split_list_is_complete_alt
    := (fun str it its splits
        => forall n,
             n <= length str
             -> parse_of_item G (take n str) it
             -> parse_of_production G (drop n str) its
             -> List.In n (List.map (min (length str)) splits)).

  Definition expanded_fallback_list_alt
    := expanded_fallback_list' (fun str it its _ _ => split_list_is_complete_alt str it its).

  Global Arguments expanded_fallback_list / .
  Global Arguments expanded_fallback_list_alt / .
  Global Arguments expanded_fallback_list_case / .

  Lemma expanded_fallback_list'_ext'
        (P1 P2 : String -> item Ascii.ascii -> production Ascii.ascii -> item Ascii.ascii -> production Ascii.ascii -> list nat -> Prop)
        str it its dummy
        (H : forall splits,
               P2 (string_of_indexed str) it its it its splits
               -> P1 (string_of_indexed str) it its it its splits)
  : refine (expanded_fallback_list' P1 str it its dummy)
           (expanded_fallback_list' P2 str it its dummy).
  Proof.
    simpl.
    repeat intro; computes_to_inv; subst.
    eapply BindComputes; [ | apply ReturnComputes ].
    unfold forall_reachable_productions in *.
    induction ((flatten
                  (flatten
                     (map (fun nt : string => map tails (G nt)) (Valid_nonterminals G)))))
      as [ | x xs IHG ]; simpl in *; trivial; [].
    match goal with
      | [ |- context[production_beq ?x ?y ?z] ]
        => destruct (production_beq x y z) eqn:Heqb
    end;
      simpl in *; eauto; [].
    apply (production_bl (@ascii_bl)) in Heqb;
      instantiate; subst; unfold option_rect, If_Then_Else in *;
      repeat match goal with
               | _ => assumption
               | _ => solve [ eauto ]
               | [ |- context[match ?e with _ => _ end] ]
                 => atomic e; destruct e
               | [ |- context[match ?e with _ => _ end] ]
                 => destruct e eqn:?
               | _ => progress simpl in *
               | _ => progress computes_to_inv
               | [ |- computes_to (Pick _) _ ] => apply PickComputes
             end.
  Qed.

  Lemma expanded_fallback_list'_ext''
        (P1 P2 : String -> item Ascii.ascii -> production Ascii.ascii -> item Ascii.ascii -> production Ascii.ascii -> list nat -> Prop)
        str it its dummy
        (H : forall_reachable_productions
               G
               (fun p H
                => match p with
                     | nil => True
                     | it'::its'
                       => forall splits,
                            P2 (string_of_indexed str) it' its' it' its' splits
                            -> P1 (string_of_indexed str) it' its' it' its' splits
                   end /\ H)
               True)
  : refine (expanded_fallback_list' P1 str it its dummy)
           (expanded_fallback_list' P2 str it its dummy).
  Proof.
    simpl.
    repeat intro; computes_to_inv; subst.
    eapply BindComputes; [ | apply ReturnComputes ].
    unfold forall_reachable_productions in *.
    induction ((flatten
                  (flatten
                     (map (fun nt : string => map tails (G nt)) (Valid_nonterminals G)))))
      as [ | x xs IHG ]; simpl in *; trivial; [].
    progress destruct_head and.
    match goal with
      | [ |- context[production_beq ?x ?y ?z] ]
        => destruct (production_beq x y z) eqn:Heqb
    end;
      simpl in *; eauto; [].
    apply (production_bl (@ascii_bl)) in Heqb;
      instantiate; subst; unfold option_rect, If_Then_Else in *;
      repeat match goal with
               | _ => assumption
               | _ => solve [ eauto ]
               | [ |- context[match ?e with _ => _ end] ]
                 => atomic e; destruct e
               | [ |- context[match ?e with _ => _ end] ]
                 => destruct e eqn:?
               | _ => progress simpl in *
               | _ => progress computes_to_inv
               | [ |- computes_to (Pick _) _ ] => apply PickComputes
             end.
  Qed.

  (** Reference implementation of a [String] that can be split; has a [string], and a start index, and a length *)
  Open Scope ADTParsing_scope.

  Definition rindexed_spec' P : ADT (string_rep Ascii.ascii String.string) :=
    ADTRep T {
    Def Constructor1 "new" (s : String.string) : rep :=
      ret (s, (0, String.length s)),

    Def Method0 "to_string"(s : rep) : rep * String.string :=
      ret (s, string_of_indexed s),

    Def Method1 "is_char"(s : rep) (ch : Ascii.ascii) : rep * bool  :=
      ret (s, string_beq (string_of_indexed s) (String.String ch "")),

    Def Method1 "get"(s : rep) (n : nat) : rep * (option Ascii.ascii)  :=
      ret (s, iget n s),

    Def Method0 "length"(s : rep) : rep * nat :=
      ret (s, ilength s),

    Def Method1 "take"(s : rep) (n : nat) : rep :=
      ret ((fst s, (fst (snd s), min (snd (snd s)) n))),

    Def Method1 "drop"(s : rep) (n : nat) : rep :=
      ret ((fst s, (n + fst (snd s), (snd (snd s) - n)%natr))),

    Def Method2 "splits"(s : rep) (i : item Ascii.ascii) (p : production Ascii.ascii) : rep * (list nat) :=
      dummy <- { ls : list nat | True };
      expanded_fallback_list' P s i p dummy
  }.

  Definition rindexed_spec : ADT (string_rep Ascii.ascii String.string)
    := rindexed_spec' (fun str it its _ _ => split_list_is_complete G str it its).

  Local Ltac fin :=
    repeat match goal with
             | _ => progress unfold split_list_is_complete
             | _ => progress simpl in *
             | _ => progress computes_to_inv
             | _ => progress subst
             | _ => progress rewrite ?minusr_minus in *
             | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
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
    try solve [ rewrite !substring_correct3'; reflexivity
              | repeat match goal with
                         | _ => intro
                         | [ |- context[min ?x ?x] ]
                           => rewrite (Min.min_idempotent x)
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
                         | [ |- String.substring (?x + ?y) _ _ = String.substring (?y + ?x) _ _ ]
                           => rewrite (Plus.plus_comm x y)
                         | [ |- String.substring ?x ?y ?z = String.substring ?x (min ?w ?y) ?z ]
                           => apply (@Min.min_case_strong w y)
                         | [ H : _ |- _ ] => rewrite Min.min_assoc in H
                         | _ => apply substring_correct4; omega
                       end
              | repeat match goal with
                         | _ => intro
                         | _ => progress subst
                         | [ |- List.In ?x [?y] ] => left
                         | [ |- context[List.map ?f [?x]] ] => change (List.map f [x]) with [f x]
                         | [ |- context[min ?x ?x] ]
                           => rewrite (Min.min_idempotent x)
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
                         | [ H : String.substring _ _ _ = String.String _ _ |- _ = _ :> nat ] => apply (f_equal String.length) in H; simpl in H
                         | [ H : context[(_ ~= [ _ ])%string_like] |- _ ]
                           => apply length_singleton in H
                         | [ |- context[min ?x (?y + ?z) - ?z] ]
                           => rewrite <- (Nat.sub_min_distr_r x (y + z) z)
                         | [ H : context[min ?x (?y + ?z) - ?z] |- _ ]
                           => rewrite <- (Nat.sub_min_distr_r x (y + z) z) in H
                         | [ |- context[min ?x (?x - 1)] ] => rewrite (Min.min_r x (x - 1)) by (clear; omega)
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
                         | [ H : ?x <= ?y |- context[min ?x ?y] ]
                           => rewrite (Min.min_l x y H)
                         | [ H : ?y <= ?x |- context[min ?x ?y] ]
                           => rewrite (Min.min_r x y H)
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

  Local Arguments expanded_fallback_list' : simpl never.
  Local Opaque expanded_fallback_list'.

  Lemma FirstStep_helper_1
  : refineADT (rindexed_spec' split_list_is_complete_case) rindexed_spec.
  Proof.
    econstructor 1; try instantiate (1 := eq);
    eapply Iterate_Ensemble_BoundedIndex_equiv;
    try apply string_dec;
    simpl; intros; repeat split;
    try solve [ intuition; intros; try simplify with monad laws;
                repeat intro; computes_to_inv; subst; simpl;
                fin ].
    intros; subst.
    setoid_rewrite refineEquiv_pick_eq'.
    simplify with monad laws.
    assert (H' : forall A B (x : A * B), (fst x, snd x) = x) by (intros; destruct x; reflexivity).
    setoid_rewrite H'.
    simplify with monad laws.
    eapply refine_under_bind_helper_2; [ | reflexivity ]; instantiate; simpl.
    intros.
    etransitivity; [ | eassumption ]; instantiate; clear.
    apply expanded_fallback_list'_ext'; simpl.
    exact (fun _ x => x).
  Qed.

  Lemma FirstStep_helper_2
  : refineADT (rindexed_spec' (fun str it its _ _ => split_list_is_complete_alt str it its))
              (rindexed_spec' split_list_is_complete_case).
  Proof.
    econstructor 1; try instantiate (1 := eq);
    eapply Iterate_Ensemble_BoundedIndex_equiv;
    try apply string_dec;
    simpl; intros; repeat split;
    try solve [ intuition; intros; try simplify with monad laws;
                repeat intro; computes_to_inv; subst; simpl;
                fin ].
    intros; subst.
    Local Opaque expanded_fallback_list'.
    setoid_rewrite refineEquiv_pick_eq'.
    simplify with monad laws.
    assert (H' : forall A B (x : A * B), (fst x, snd x) = x) by (intros; destruct x; reflexivity).
    setoid_rewrite H'.
    simplify with monad laws.
    eapply refine_under_bind_helper_2; [ | reflexivity ]; instantiate; simpl.
    intros.
    etransitivity; [ | eassumption ]; instantiate; clear.
    apply expanded_fallback_list'_ext''.
    rewrite <- production_is_reachable__forall_reachable_productions'.
    unfold split_list_is_complete_case, split_list_is_complete_alt.
    eauto.
  Qed.

  Local Transparent expanded_fallback_list'.

  Lemma FirstStep
  : refineADT (string_spec G string_stringlike) rindexed_spec.
  Proof.
    refine (transitivityT _ _ _ _ FirstStep_helper_1).
    refine (transitivityT _ _ _ _ FirstStep_helper_2).
    unfold rindexed_spec', expanded_fallback_list', split_list_is_complete_alt.
    econstructor 1 with (AbsR := (fun r_o r_n =>
                                    String.substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o));

        eapply Iterate_Ensemble_BoundedIndex_equiv;
        try apply string_dec;
        simpl; intuition; intros; try simplify with monad laws;
        repeat intro; computes_to_inv; subst; simpl;
        fin.
    intros.
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
      { clear IHls; unfold If_Then_Else, option_rect.
        repeat match goal with
                 | [ |- context[if has_only_terminals ?e then _ else _] ]
                   => case_eq (has_only_terminals e)
                 | [ |- context[match ?e with None => _ | _ => _ end] ]
                   => case_eq e
               end;
          try
            abstract (
              repeat match goal with
                       | _ => intro
                       | _ => progress computes_to_inv
                       | _ => progress subst
                       | [ |- In _ [_] ] => left
                       | [ |- context[List.map ?f [?x]] ] => change (List.map f [x]) with [f x]
                       | [ |- context[min ?x ?x] ]
                         => rewrite (Min.min_idempotent x)
                       | [ H : collapse_length_result ?e = Some _ |- _ ]
                         => (revert H; case_eq e; simpl)
                       | [ H : Some _ = Some _ |- _ ]
                         => (inversion H; clear H)
                       | _ => congruence
                       | [ H : length_of_any ?G ?nt = same_length ?n,
                               p : parse_of_item ?G ?str (NonTerminal ?nt) |- _ ]
                         => (pose proof (@has_only_terminals_parse_of_item_length _ _ G n nt H str p); clear H)
                       | _ => erewrite <- has_only_terminals_length by eassumption
                       | _ => progress rewrite ?substring_length, ?Nat.add_sub, ?Nat.sub_0_r, ?Nat.add_0_r, ?minusr_minus
                       | [ H : _ |- _ ] => (generalize dependent H; progress rewrite ?substring_length, ?Nat.add_sub, ?Nat.sub_0_r, ?Nat.add_0_r, ?minusr_minus)
                       | [ H : ?y <= ?x |- context[min ?x ?y] ] => rewrite (Min.min_r x y) by assumption
                       | [ H : ?x <= ?y |- context[min ?x ?y] ] => rewrite (Min.min_l x y) by assumption
                       | [ |- context[min ?x (?y + ?z) - ?z] ]
                         => rewrite <- (Nat.sub_min_distr_r x (y + z) z)
                       | [ H : context[min ?x (?y + ?z) - ?z] |- _ ]
                         => (generalize dependent H; rewrite <- (Nat.sub_min_distr_r x (y + z) z))
                       | [ |- context[min (?x - ?y) ?x] ] => rewrite (Min.min_l (x - y) x) by omega
                       | [ |- context[min ?x (?x - ?y)] ] => rewrite (Min.min_r x (x - y)) by omega
                       | _ => omega
                       | _ => solve [ eauto ]
                     end
            ). } }
  Qed.
End IndexedImpl.
