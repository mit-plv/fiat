(** First step of a splitter refinement; indexed representation, and handle all rules with at most one nonterminal; leave a reflective goal *)
Require Import Coq.Strings.String Coq.Arith.Lt Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ParserADTSpecification.
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
Require Import Fiat.Common.List.ListMorphisms.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.StringFacts.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.LogicMorphisms.
Require Import Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Import Fiat.Computation.SetoidMorphisms.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.Enumerable.BoolProp Fiat.Common.Enumerable.ReflectiveForall.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

(** Reflective version of [split_list_is_complete] and [production_is_reachable] *)
Section forall_reachable_productions.
  Context {Char} (G : grammar Char) {T : Type}.

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Context (x : production_carrierT)
          (f : @production_carrierT _ (@rdp_list_predata _ G) -> T)
          (init : T).

  Definition forall_reachable_productions_if_eq0
  : T
    := @forall_enumerable_by_beq production_carrierT production_carrier_valid _ _ T x f init.

  Local Ltac t_flatten :=
    repeat match goal with
             | [ |- flat_map (fun _ => map _ (map _ _)) _ = _ ]
               => apply flat_map_Proper; [ intro | reflexivity ]
             | [ |- map _ (map _ _) = _ ] => rewrite map_map; simpl @proj1_sig
             | [ |- map _ (flat_map _ _) = _ ] => rewrite map_flat_map
             | [ |- map (fun x : sig ?B => @?P x) (Operations.List.sig_In _) = _ ]
               => (let P' := (eval cbv beta in (fun a b => P (exist _ a b))) in
                   let P' := (eval simpl @proj1_sig in P') in
                   let P' := match P' with fun a _ => @?P' a => P' end in
                   etransitivity;
                   [ refine (eq_sym (@map_map _ _ _ (@proj1_sig _ B) P' _))
                   | set_evars; rewrite map_proj1_sig_sig_In ])
             | [ |- map (fun x : nat => _) _ = _ ] => subst_body; reflexivity
           end.

  Definition forall_reachable_productions_if_eq_sig
  : { x : T | x = forall_reachable_productions_if_eq0 }.
  Proof.
    eexists.
    unfold forall_reachable_productions_if_eq0.
    unfold forall_enumerable_by_beq.
    unfold Equality.beq, prod_BoolDecR, dnc_BoolDecR, nat_BoolDecR, prod_beq.
    apply f_equal.
    match goal with
      | [ |- appcontext G[@enumerate ?T ?e] ]
        => let e' := (eval hnf in e) in
           let G' := context G[@enumerate T e'] in
           change G'
    end.
    cbv beta iota zeta delta [enumerate enumerable_sig_ltb enumerable_sig_andb_dep enumerable_sig_leb].
    symmetry.
    rewrite map_flat_map.
    etransitivity.
    { t_flatten. }
    etransitivity.
    { rewrite flat_map_flatten; apply f_equal.
      etransitivity.
      { t_flatten. }
      etransitivity.
      { apply (_ : Proper (pointwise_relation _ _ ==> _ ==> eq) (@map _ _));
        [ intro | reflexivity ].
        rewrite flat_map_flatten.
        rapply @f_equal.
        t_flatten. }
      etransitivity.
      { apply (_ : Proper (pointwise_relation _ _ ==> _ ==> eq) (@map _ _));
        [ intro | reflexivity ].
        rewrite <- flat_map_flatten; reflexivity. }
      reflexivity. }
    rewrite <- flat_map_flatten.
    reflexivity.
  Defined.

  Definition forall_reachable_productions_if_eq : T.
  Proof.
    let x := constr:(proj1_sig forall_reachable_productions_if_eq_sig) in
    let x := (eval cbv beta iota delta [proj1_sig forall_reachable_productions_if_eq_sig] in x) in
    exact x.
  Defined.

  Lemma forall_reachable_productions_if_eq_helper
  : forall_reachable_productions_if_eq = forall_reachable_productions_if_eq0.
  Proof.
    exact (proj2_sig forall_reachable_productions_if_eq_sig).
  Qed.

  Lemma forall_reachable_productions_if_eq_correct
  : forall_reachable_productions_if_eq = if production_carrier_valid x then f x else init.
  Proof.
    rewrite forall_reachable_productions_if_eq_helper;
    apply forall_enumerable_by_beq_correct; exact _.
  Qed.

  Definition forall_reachable_productions_if_eq_correct_reachable
             (H : production_carrier_valid x)
  : forall_reachable_productions_if_eq = f x.
  Proof.
    rewrite forall_reachable_productions_if_eq_helper;
    apply forall_enumerable_by_beq_correct_reachable;
    first [ assumption | exact _ ].
  Qed.
End forall_reachable_productions.

Local Arguments Compare_dec.leb !_ !_.

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

Module Export PrettyNotations.
  Global Arguments Compare_dec.leb !_ !_.

  Infix "=p" := default_production_carrierT_beq (at level 70, no associativity).

  Notation string_of_indexed s :=
    (substring (fst (snd s)) (snd (snd s)) (fst s))
      (only parsing).
  Notation ilength s :=
    ((*opt.*)snd ((*opt.*)snd s))
      (only parsing).
  Notation iget n s :=
    (unsafe_get (n + fst (snd s)) (fst s))
      (only parsing).
  Notation iis_char s ch :=
    (((EqNat.beq_nat (ilength s) 1)
        && ascii_beq (unsafe_get (fst (snd s)) (fst s)) ch)%bool)
      (only parsing).
End PrettyNotations.

Section IndexedImpl.
  Context {HSL : StringLike Ascii.ascii} {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii} {HSIP : StringIsoProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}.
  Context (G : grammar Ascii.ascii).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Local Notation T := (String * (nat * nat))%type (only parsing).

  Definition expanded_fallback_list'
             (P : String -> @production_carrierT _ predata -> production _ -> @production_carrierT _ predata -> production _ -> list nat -> Prop)
             (s : T)
             (idx : @production_carrierT _ predata)
             (dummy : list nat)
  : Comp (T * list nat)
    := (ls <- (forall_reachable_productions_if_eq
                 (G := G)
                 idx
                 (fun p
                  => match to_production p return Comp (list nat) with
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
                                 p
                                 (to_production p)
                                 idx
                                 (to_production idx)
                                 splits }%comp
                             (length_of_any G nt))
                     end)
                 (ret dummy));
        ret (s, ls))%comp.

  Global Arguments expanded_fallback_list' / .

  Definition expanded_fallback_list
    := expanded_fallback_list' (fun str pidx p _ _ => split_list_is_complete_idx G str pidx).
  Definition split_list_is_complete_case
             str (pidx : @production_carrierT _ predata) p (p'idx : @production_carrierT _ predata) p' splits
    := production_carrier_valid pidx
       -> forall it its,
            p = it::its
            -> forall n,
                 n <= length str
                 -> production_is_reachable G p'
                 -> parse_of_item G (take n str) it
                 -> parse_of_production G (drop n str) its
                 -> List.In n (List.map (min (length str)) splits).
  Definition expanded_fallback_list_case
    := expanded_fallback_list' split_list_is_complete_case.

  Definition split_list_is_complete_alt
    := (fun str pidx p splits
        => production_carrier_valid pidx
           -> forall it its,
                p = it::its
                -> forall n,
                     n <= length str
                     -> parse_of_item G (take n str) it
                     -> parse_of_production G (drop n str) its
                     -> List.In n (List.map (min (length str)) splits)).

  Definition expanded_fallback_list_alt
    := expanded_fallback_list' (fun str idx p _ _ => split_list_is_complete_alt str idx p).

  Global Arguments expanded_fallback_list / .
  Global Arguments expanded_fallback_list_alt / .
  Global Arguments expanded_fallback_list_case / .

  Lemma expanded_fallback_list'_ext''
        (P1 P2 : String -> production_carrierT -> production _ -> production_carrierT -> production _ -> list nat -> Prop)
        str idx dummy
        (H : production_carrier_valid idx
             -> forall splits,
                  P2 (string_of_indexed str) idx (to_production idx) idx (to_production idx) splits
                  -> P1 (string_of_indexed str) idx (to_production idx) idx (to_production idx) splits)
  : refine (expanded_fallback_list' P1 str idx dummy)
           (expanded_fallback_list' P2 str idx dummy).
  Proof.
    unfold expanded_fallback_list'.
    rewrite !forall_reachable_productions_if_eq_correct.
    simpl.
    repeat match goal with
             | [ |- ?R ?x ?x ] => reflexivity
             | [ |- context[match ?e with _ => _ end] ]
               => destruct e eqn:?
             | _ => progress subst
             | _ => progress simpl in *
             | _ => progress unfold If_Then_Else, option_rect
             | [ |- refine (a <- _; _) (b <- _; _) ]
               => apply refine_under_bind_both; [ | reflexivity ]
             | [ |- refine { a : _ | _ } { b : _ | _ } ]
               => apply refine_pick_pick
             | _ => solve [ eauto with nocore ]
             | [ H : rdp_list_to_production idx = ?x |- context[?x] ]
               => rewrite <- H
           end.
  Qed.

  Lemma expanded_fallback_list'_ext'
        (P1 P2 : String -> production_carrierT -> production _ -> production_carrierT -> production _ -> list nat -> Prop)
        str idx dummy
        (H : forall splits,
               P2 (string_of_indexed str) idx (to_production idx) idx (to_production idx) splits
               -> P1 (string_of_indexed str) idx (to_production idx) idx (to_production idx) splits)
  : refine (expanded_fallback_list' P1 str idx dummy)
           (expanded_fallback_list' P2 str idx dummy).
  Proof.
    apply expanded_fallback_list'_ext''; eauto with nocore.
  Qed.

  (** Reference implementation of a [String] that can be split; has a [string], and a start index, and a length *)
  Open Scope ADTParsing_scope.

  Definition rindexed_spec' P : ADT (string_rep Ascii.ascii String default_production_carrierT) :=
    ADTRep T {
    Def Constructor1 "new" (s : String) : rep :=
      ret (s, (0, length s)),

    Def Method0 "to_string"(s : rep) : rep * String :=
      ret (s, string_of_indexed s),

    Def Method1 "is_char"(s : rep) (ch : Ascii.ascii) : rep * bool  :=
      ret (s, iis_char s ch),

    Def Method1 "get"(s : rep) (n : nat) : rep * Ascii.ascii  :=
      ret (s, iget n s),

    Def Method0 "length"(s : rep) : rep * nat :=
      ret (s, ilength s),

    Def Method1 "take"(s : rep) (n : nat) : rep :=
      ret ((fst s, (fst (snd s), min (snd (snd s)) n))),

    Def Method1 "drop"(s : rep) (n : nat) : rep :=
      ret ((fst s, (n + fst (snd s), (snd (snd s) - n)%natr))),

    Def Method1 "splits"(s : rep) (idx : default_production_carrierT) : rep * (list nat) :=
      dummy <- { ls : list nat | True };
      expanded_fallback_list' P s idx dummy
  }.

  Definition rindexed_spec : ADT (string_rep Ascii.ascii String default_production_carrierT)
    := rindexed_spec' (fun str idx p _ _ => split_list_is_complete_idx G str idx).

  Local Ltac fin :=
    repeat match goal with
             | _ => progress unfold split_list_is_complete
             | _ => progress unfold split_list_is_complete_idx
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
             | [ |- context[substring _ _ (substring _ _ _)] ]
                 => rewrite substring_substring
             | [ |- context[_ - 0] ] => rewrite Nat.sub_0_r
             | [ |- context[substring _ (min _ (length ?str)) ?str] ]
               => rewrite substring_min_length
             | [ |- context[_ + 0] ] => rewrite Plus.plus_0_r
             | [ |- context[min ?x ?x] ]
               => rewrite (Min.min_idempotent x)
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
                         | [ |- context[List.map ?f [?x]] ] => change (List.map f [x]) with [f x]
                         | [ |- context[min ?x ?x] ]
                           => rewrite (Min.min_idempotent x)
                         | _ => reflexivity
                         | [ H : parse_of_production _ _ nil |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_production _ _ (_::_) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : parse_of_item _ _ (NonTerminal _) |- _ ] => let H' := fresh in rename H into H'; dependent destruction H'
                         | [ H : length (substring ?n ?m ?s) = _, H' : context[length (substring ?n ?m ?s)] |- _ ] => rewrite H in H'
                         | [ H : context[length (take _ _)] |- _ ] => rewrite take_length in H
                         | _ => erewrite <- has_only_terminals_length by eassumption
                         | [ H : _ |- _ ] => progress rewrite ?(@drop_length _ HSL HSLP), ?(@take_length _ HSL HSLP), ?substring_length, ?Nat.add_sub, <- ?plus_n_O, ?Minus.minus_diag, ?Nat.sub_0_r, ?sub_plus in H by omega
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
                         | [ |- context[min (min _ ?x) (?x - ?y)] ]
                           => rewrite <- (Min.min_assoc _ x (x - y)), (Min.min_r x (x - y)) by omega
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

  Lemma FirstStep_helper_gen {P Q}
        (H : forall r_n d x0,
               refine (expanded_fallback_list' P r_n d x0)
                      (expanded_fallback_list' Q r_n d x0))
  : refineADT (rindexed_spec' P)
              (rindexed_spec' Q).
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
    etransitivity; [ | eassumption ]; instantiate; clear -H.
    apply H.
  Defined.

  Lemma FirstStep_helper_1
  : refineADT (rindexed_spec' split_list_is_complete_case) rindexed_spec.
  Proof.
    apply FirstStep_helper_gen; intros.
    apply expanded_fallback_list'_ext'; simpl.
    unfold split_list_is_complete_case, split_list_is_complete; simpl.
    intro.
    let H := fresh in
    repeat first [ exact (fun x => x)
                 | let x := fresh in intros H x; specialize (H x); revert H; try rewrite x ].
  Qed.

  Lemma FirstStep_helper_2
  : refineADT (rindexed_spec' (fun str idx p _ _ => split_list_is_complete_alt str idx p))
              (rindexed_spec' split_list_is_complete_case).
  Proof.
    apply FirstStep_helper_gen; intros.
    apply expanded_fallback_list'_ext'.
    simpl.
    unfold split_list_is_complete_case, split_list_is_complete_alt; simpl.
    intro.
    repeat first [ exact (fun x => x)
                 | let H := fresh in
                   let x := fresh in
                   intros H x; specialize (H x); revert H;
                   try rewrite x in *;
                   try unique pose proof (rdp_list_production_carrier_valid_reachable _ x)
                 | let H := fresh in
                   intro H; progress specialize_by assumption; revert H ].
  Qed.

  Local Transparent expanded_fallback_list'.

  Local Ltac pre_fin' :=
    idtac;
    match goal with
      | [ |- True ] => constructor
      | _ => progress computes_to_inv
      | _ => progress subst
      | [ |- _ = _ ] => reflexivity
      | _ => progress simpl @fst
      | _ => progress simpl @snd
      | _ => progress simplify with monad laws
      | [ |- (_, _) = (_, _) ] => apply f_equal2
      | [ |- fst ?e =s ?r ]
        => is_evar e; refine (_ : fst (_, _) =s r); simpl @fst
      | [ |- computes_to (Bind _ _) _ ]
        => refine ((fun H0 H1 => BindComputes _ _ _ _ H1 H0) _ _)
      | [ |- computes_to (Return ?x) ?y ]
        => cut (x = y);
          [ let H := fresh in intro H; try rewrite H; (exact (ReturnComputes x) || exact (ReturnComputes y)) | ]
      | [ |- computes_to (Pick _) _ ]
        => eapply PickComputes
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ |- _ /\ _ ] => split
      | _ => omega
      | [ |- _ = _ :> String ] => apply bool_eq_bl
      | [ |- _ =s _ ] => reflexivity
    end.
  Local Ltac pre_fin := repeat pre_fin'.

  Local Arguments EqNat.beq_nat : simpl never.

  Local Ltac do_Iterate_Ensemble_BoundedIndex_equiv :=
    eapply Iterate_Ensemble_BoundedIndex_equiv;
    cbv beta iota zeta delta [Iterate_Ensemble_BoundedIndex Constructors Methods Iterate_Ensemble_BoundedIndex' string_spec BuildADT getConsDef getMethDef ith icons inil Vector.caseS Vector_caseS' ilist_hd ilist_tl ilist.prim_fst ilist.prim_snd consBody methBody ConstructorDom Rep string_rep DecADTSig BuildADTSig consDom Vector.nth MethodDomCod methDom methCod refineConstructor refineMethod refineMethod'];
    simpl @fst; simpl @snd;
    repeat match goal with
             | [ |- prim_and _ _ ] => split
           end;
    intros;
    try simplify with monad laws;
    repeat intro;
    pre_fin.

  Local Ltac fin_common' :=
    idtac;
    match goal with
      | [ |- ?b = ?b' :> bool ]
        => (destruct b eqn:?; destruct b' eqn:?);
          (reflexivity || exfalso)
      | _ => progress subst
      | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
      | [ |- context[min ?x ?x] ]
        => rewrite (Min.min_idempotent x)
      | [ |- List.In ?x [?y] ] => left
      | [ |- context[List.map ?f [?x]] ] => change (List.map f [x]) with [f x]
      | [ |- _ \/ False ] => left
      | [ H : context[if Compare_dec.leb ?x ?y then _ else _] |- _ ]
        => destruct (Compare_dec.leb x y) eqn:?
      | [ |- context[if Compare_dec.leb ?x ?y then _ else _] ]
        => destruct (Compare_dec.leb x y) eqn:?
      | [ H : context[option_beq _ None (Some _)] |- _ ] => unfold option_beq in H
      | [ H : appcontext[unsafe_get] |- _ ] => erewrite unsafe_get_correct in H by eassumption
      | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
      | [ H : andb _ _ = false |- _ ] => apply Bool.andb_false_iff in H
      | [ H : EqNat.beq_nat _ _ = true |- _ ] => apply EqNat.beq_nat_true in H
      | [ H : EqNat.beq_nat _ _ = false |- _ ] => apply EqNat.beq_nat_false in H
      | [ H : Compare_dec.leb _ _ = true |- _ ] => apply Compare_dec.leb_complete in H
      | [ H : Compare_dec.leb _ _ = false |- _ ] => apply Compare_dec.leb_complete_conv in H
      | [ H : context[?x - ?x] |- _ ] => rewrite Minus.minus_diag in H
      | [ H : context[min _ 0] |- _ ] => rewrite Min.min_0_r in H
      | [ H : context[min 0 _] |- _ ] => rewrite Min.min_0_l in H
      | [ H : option_beq ascii_beq _ _ = true |- _ ]
        => apply (option_bl (@ascii_bl)) in H
      | [ H : context[min ?x ?y], H' : ?x <= ?y |- _ ]
        => rewrite (Min.min_l x y) in H by assumption
      | [ H : context[min ?x ?y], H' : ?y <= ?x |- _ ]
        => rewrite (Min.min_r x y) in H by assumption
      | [ H : context[?x + ?y - ?y] |- _ ] => rewrite Nat.add_sub in H
      | [ H : context[(0 + ?x)%nat] |- _ ] => change (0 + x) with x in H
      | [ |- context[min ?x (?y + ?z) - ?z] ]
        => rewrite <- (Nat.sub_min_distr_r x (y + z) z)
      | [ H : context[min ?x (?y + ?z) - ?z] |- _ ]
        => rewrite <- (Nat.sub_min_distr_r x (y + z) z) in H
      | [ H : context[min ?x ?z - ?z] |- _ ]
        => rewrite <- (Nat.sub_min_distr_r x z z) in H
      | [ H : ascii_beq ?x ?y = true |- _ ] => apply ascii_bl in H
      | [ H : context[ascii_beq ?x ?x] |- _ ] => rewrite (ascii_lb eq_refl) in H
      | [ H : ?x = ?y, H' : option_beq _ ?x ?y' = _ |- _]
        => match constr:(y, y') with
             | (Some _, Some _) => idtac
             | (None, Some _) => idtac
             | (Some _, None) => idtac
             | (None, None) => idtac
           end;
          rewrite H in H'; unfold option_beq in H'
      | [ H : context[?x + ?y - ?y] |- _ ] => rewrite Nat.add_sub in H
      | [ |- context[?x + ?y - ?y] ] => rewrite Nat.add_sub
      | [ H : ?x <= 0 |- _ ] => assert (x = 0) by (clear -H; omega); clear H
      | [ H : ?x = 0 |- context[?x] ] => rewrite H
      | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
      | [ H : 1 = snd (snd ?x), H' : context[snd (snd ?x)] |- _ ]
        => is_var x; rewrite <- H in H'
      | [ |- context[min 0 _] ] => rewrite Min.min_0_l
      | [ |- context[min _ 0] ] => rewrite Min.min_0_r
      | [ |- context[(_ - _)%natr] ] => rewrite minusr_minus
      | [ |- context[?x - ?y + min ?y ?x] ] => rewrite minus_plus_min
      | [ |- context[?x - ?y + (min ?y ?x + _)] ] => rewrite !Plus.plus_assoc, minus_plus_min
      | [ H : ?x < S ?y |- context[?x - ?y] ]
        => rewrite (proj2 (Nat.sub_0_le x y)) by omega
      | [ H : ?x + ?y <= ?z, H' : context[min ?x (?z - ?y)] |- _ ]
        => rewrite (Min.min_l x (z - y)) in H' by (clear -H; omega)
      | [ H : ?x <= ?y |- context[min ?x ?y] ]
        => rewrite (Min.min_l x y H)
      | [ H : ?y <= ?x |- context[min ?x ?y] ]
        => rewrite (Min.min_r x y H)
      | [ |- context[min ?x (?x - _)] ] => rewrite min_minus_r
      | _ => progress destruct_head' and
      | _ => progress destruct_head' or
      | _ => omega
      | _ => discriminate
      | _ => congruence
      | _ => progress computes_to_inv
      | _ => progress specialize_by assumption
      | [ |- context[_ - 0] ] => rewrite Nat.sub_0_r
      | [ H : forall n, n <= 0 -> _ |- _ ] => specialize (H 0 (reflexivity _))
    end.
  Local Ltac fin_common := repeat fin_common'.

  Local Ltac string_from_parse' :=
    idtac;
    match goal with
      | [ H : parse_of_production _ _ nil |- _ ] => inversion H; clear H
      | [ H : parse_of_production _ _ (_::_) |- _ ] => inversion H; clear H
      | [ H : parse_of_item _ _ (Terminal _) |- _ ] => inversion H; clear H
      | [ H : parse_of_item _ _ (NonTerminal _) |- _ ] => inversion H; clear H
      | [ H : parse_of_production _ _ ?v |- _ = _ :> nat ] => is_var v; clear H
      | [ H : parse_of_item _ _ ?v |- _ = _ :> nat ] => is_var v; clear H
      | _ => progress fin_common
    end.
  Local Ltac string_from_parse := repeat string_from_parse'.

  Local Ltac fin2' :=
    idtac;
    match goal with
      | [ H : context[length (substring ?n ?m ?s)], H' : length (substring ?n ?m ?s) = _ |- _ ] => rewrite H' in H
      | [ H' : length (substring ?n ?m ?s) = _ |- context[length (substring ?n ?m ?s)] ] => rewrite H'
      | [ H : context[length (drop _ (substring _ _ _))] |- _ ] => rewrite drop_length in H
      | [ H : context[length (take _ (substring _ _ _))] |- _ ] => rewrite take_length in H
      | [ H : is_true (is_char _ _) |- _ ] => apply is_char_parts in H
      | [ |- context[length (drop _ (substring _ _ _))] ] => rewrite drop_length
      | [ |- context[length (take _ (substring _ _ _))] ] => rewrite take_length
      | [ H : length ?x = _, H' : length (substring _ _ ?x) = _ |- _ ]
        => rewrite substring_length, H in H'
      | [ H : length ?x = _ |- context[length (drop _ (drop _ ?x))] ]
        => (do 2 rewrite drop_length; rewrite H)
      | _ => rewrite Minus.pred_of_minus
      | [ H : ?x = 1 |- context[?x] ] => rewrite H
      | [ H : ?x = 1, H' : context[?x] |- _ ] => rewrite H in H'
      | [ H : min ?x ?y = 1 |- context[?x] ]
        => (revert H; apply (Min.min_case_strong x y))
      | _ => intro
      | [ |- context[?x - ?y] ]
        => rewrite (proj2 (Nat.sub_0_le x y)) by assumption
      | [ |- context[min ?x (pred ?x)] ]
        => rewrite (Min.min_r x (pred x)) by omega
      | [ |- context[?x - ?y - (?x - ?z - ?y)] ]
        => rewrite <- (Nat.sub_add_distr x z y), (Plus.plus_comm z y), (Nat.sub_add_distr x y z)
      | [ |- context[?x - (?x - _)] ]
        => rewrite sub_twice
      | [ |- context[min ?x (min (?x - ?z) ?y)] ]
        => rewrite (Min.min_assoc x (x - z)), (Min.min_r x (x - z)) by omega
      | [ |- min ?x ?y = ?y ] => rewrite Min.min_r by omega
    end.
  Local Ltac fin2 := repeat first [ progress fin_common
                                  | progress string_from_parse
                                  | progress fin2' ].


  Lemma FirstStep
  : refineADT (string_spec G HSL) rindexed_spec.
  Proof.
    refine (transitivityT _ _ _ _ FirstStep_helper_1).
    refine (transitivityT _ _ _ _ FirstStep_helper_2).
    (*hone representation using (fun r_o r_n =>
                                 (substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o)(*
                                 /\ (snd (snd r_n) + fst (snd r_n) <= length (fst r_n))*));
      repeat match goal with
               | [ H : ?T, rv : _ |- context[Pick ?P] ]
                 => unify (P rv) T;
                   let H' := fresh in
                   assert (H' : refine (Pick P) (ret rv));
                     [ repeat intro; apply PickComputes; computes_to_inv; subst; assumption
                     | setoid_rewrite H'; clear H'; try clear H rv  ]
               | _ => progress simplify with monad laws
               | [ |- context G[fst (?x, _)] ]
                 => let G' := context G[x] in change G'
               | [ |- context G[snd (_, ?x)] ]
                 => let G' := context G[x] in change G'
             end;
      simpl @fst; simpl @snd;
      try solve [ repeat match goal with
                           | [ H : _ /\ _ |- _ ] => destruct H
                           | _ => progress subst
                         end;
                  try match goal with
                        | [ |- refine ?a (?e ?x) ]
                          => let ev := (eval unfold e in e) in
                             match eval pattern x in a with
                               | ?P _ => unify ev P
                             end;
                               try (subst e; reflexivity)
                        | [ |- refine ?a (?e ?x ?y) ]
                          => let ev := (eval unfold e in e) in
                             match eval pattern x, y in a with
                               | ?P _ _ => unify ev P
                             end;
                               try (subst e; reflexivity)
                        | [ |- refine ?a (?e ?x ?y ?z) ]
                          => let ev := (eval unfold e in e) in
                             match eval pattern x, y, z in a with
                               | ?P _ _ _ => unify ev P
                             end;
                               try (subst e; reflexivity)
                      end ];
      [].
    econstructor 1 with (AbsR :=
                           fun r_o r_n =>
                             fst r_o =s fst r_n
                             /\ snd r_o = snd r_n
                             /\ (snd (snd r_n) + fst (snd r_n) <= length (fst r_n)));
      do_Iterate_Ensemble_BoundedIndex_equiv.*)
    unfold rindexed_spec', expanded_fallback_list', split_list_is_complete_alt.
    econstructor 1 with (AbsR := (fun r_o r_n =>
                                    (substring (fst (snd r_n)) (snd (snd r_n)) (fst r_n) = r_o)
                                    /\ (snd (snd r_n) = 0 \/ (snd (snd r_n) + fst (snd r_n) <= length (fst r_n)))));
      do_Iterate_Ensemble_BoundedIndex_equiv;
      change @opt.snd with @snd in *.
    { rewrite substring_correct3'; reflexivity. }
    { repeat match goal with
               | _ => progress fin_common
               | [ H : is_char _ _ = true |- _ ]
                 => let H' := fresh in
                    pose proof H as H';
                      apply length_singleton in H';
                      apply add_take_1_singleton, get_0 in H
               | [ H : context[length (substring _ _ _)] |- _ ]
                 => rewrite substring_length in H
               | [ H : context[get _ (take _ _)] |- _ ] => rewrite get_take_lt in H by omega
               | [ H : context[get _ (drop _ _)] |- _ ] => rewrite <- get_drop in H
               | [ H : is_char _ _ = false |- _ ] => apply not_is_char_options in H
               | [ H : None <> Some _ |- _ ] => clear H
               | [ H : Some _ <> Some _ |- _ ] => specialize (fun H' => H (f_equal (@Some _) H'))
               | [ H : ?x <> Some _ |- _ ] => destruct x eqn:?
               | [ H : get _ _ = None |- _ ]
                 => rewrite get_drop in H; apply no_first_char_empty in H; rewrite drop_length in H
             end. }
    { intros ch H; apply unsafe_get_correct; revert H.
      rewrite (@get_drop _ _ _ d).
      rewrite (@get_drop _ _ _ (d + _)).
      rewrite drop_take, drop_drop.
      intro H.
      rewrite get_take_lt in H; [ assumption | ].
      repeat match goal with
               | [ H : get 0 _ = Some _ |- _ ] => apply get_0 in H
               | [ H : is_true (is_char _ _) |- _ < _ ] => apply length_singleton in H
               | [ H : _ |- _ ] => progress rewrite ?take_length, ?drop_length in H
               | [ H : min 1 ?x = 1 |- _ ]
                 => assert (x >= 1) by (revert H; apply (Min.min_case_strong 1 x); intro; intro; omega);
                   clear H
               | [ H : context[min 0 _] |- _ ] => rewrite Min.min_0_l in H
               | [ H : _ \/ _ |- _ ] => destruct H
               | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
               | [ H : context[0 - ?x] |- _ ] => change (0 - x) with 0 in H
               | [ H : 0 >= S _ |- _ ] => exfalso; clear -H; omega
               | [ H : context[min _ _] |- _ ] => rewrite Min.min_l in H by omega
               | [ H : context[min _ _] |- _ ] => rewrite Min.min_r in H by omega
               | _ => omega
             end. }
    { rewrite substring_length; fin_common; rewrite Min.min_r by omega; omega. }
    { rewrite take_take, Min.min_comm; reflexivity. }
    { apply Min.min_case_strong; omega. }
    { rewrite drop_take, drop_drop, minusr_minus.
      reflexivity. }
    { fin_common. }
    unfold split_list_is_complete_idx, split_list_is_complete.
    intros.

    match goal with
      | [ H : context[length (substring ?n ?m ?s)] |- _ ]
        => let H' := fresh in
           assert (H' : length (substring n m s) = m)
             by (rewrite substring_length; fin_common; rewrite Min.min_r by omega; omega);
             rewrite !H' in H |- *
    end.

    repeat match goal with
             | [ H : appcontext[forall_reachable_productions_if_eq] |- _ ]
               => rewrite forall_reachable_productions_if_eq_correct_reachable in H by assumption
             | _ => progress simpl in *
             | _ => progress unfold rdp_list_to_production in *
             | [ H : default_to_production ?p = ?x :: ?xs,
                     H' : context[?x::?xs] |- _]
               => rewrite <- H in H'
             | [ H : context[match ?e with _ => _ end], H' : ?e = _::_ |- _ ]
               => rewrite H' in H
             | [ H : context[match ?e with _ => _ end] |- _ ]
               => is_var e; destruct e
             | _ => progress unfold If_Then_Else, option_rect in *
             | [ H : context[match ?e with _ => _ end] |- _ ]
               => destruct e eqn:?
           end.

    { abstract fin2. }
    { abstract fin2. }
    { abstract fin2. }
    { abstract (
          repeat match goal with
                   | [ H : parse_of_production _ _ (_::_) |- _ ] => (inversion H; clear H)
                   | _ => progress subst
                   | _ => erewrite <- has_only_terminals_length by eassumption
                   | [ H : context[List.length _] |- _ ]
                     => erewrite <- has_only_terminals_length in H by eassumption
                 end;
          fin2
        ). }
    { abstract (
          repeat match goal with
                   | [ H : parse_of_production _ _ (_::_) |- _ ] => (inversion H; clear H)
                   | _ => progress subst
                   | [ H : collapse_length_result ?e = Some _ |- _ ]
                     => (revert H; case_eq e; simpl; [ | intros; congruence.. ])
                   | _ => intro
                   | [ H : length_of_any ?G ?nt = same_length ?n,
                           p : parse_of_item ?G ?str (NonTerminal ?nt) |- _ ]
                     => (pose proof (@has_only_terminals_parse_of_item_length _ _ G n nt H str p); clear H)
                 end;
          fin2
        ). }
    { abstract (
          repeat match goal with
                   | _ => progress fin_common
                   | [ H : forall x y, ?z = x::y -> _, H' : ?x = _::_ |- _ ]
                     => specialize (H _ _ H')
                   | [ H : length ?x = _, H' : context[length ?x] |- _ ]
                     => rewrite H in H'
                   | _ => solve [ eauto with nocore ]
                 end
        ). }
    { abstract (
          repeat match goal with
                   | [ H : parse_of_production _ _ (_::_) |- _ ] => (inversion H; clear H)
                   | _ => progress subst
                   | [ H : collapse_length_result ?e = Some _ |- _ ]
                     => (revert H; case_eq e; simpl; [ | intros; congruence.. ])
                   | _ => intro
                   | [ H : length_of_any ?G ?nt = same_length ?n,
                           p : parse_of_item ?G ?str (NonTerminal ?nt) |- _ ]
                     => (pose proof (@has_only_terminals_parse_of_item_length _ _ G n nt H str p); clear H)
                 end;
          fin2
        ). }
    { abstract (
          repeat match goal with
                   | _ => progress fin_common
                   | [ H : forall x y, ?z = x::y -> _, H' : ?x = _::_ |- _ ]
                     => specialize (H _ _ H')
                   | [ H : length ?x = _, H' : context[length ?x] |- _ ]
                     => rewrite H in H'
                   | _ => solve [ eauto with nocore ]
                 end
        ). }
  Qed.
End IndexedImpl.
