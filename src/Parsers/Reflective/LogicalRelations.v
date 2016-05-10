Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.PartialUnfold.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.ListMorphisms.

Fixpoint related {T} : interp_TypeCode T -> normalized_of interp_TypeCode T -> Prop
  := match T return interp_TypeCode T -> normalized_of interp_TypeCode T -> Prop with
     | csimple T' => fun b e => b = interp_Term e
     | (dom --> ran)%typecode
       => fun f1 f2 => forall x1 x2, related x1 x2 -> related (f1 x1) (f2 x2)
     end.

Fixpoint interp_related {T} : interp_TypeCode T -> interp_TypeCode T -> Prop
  := match T return interp_TypeCode T -> interp_TypeCode T -> Prop with
     | csimple T' => fun b e => b = e
     | (dom --> ran)%typecode
       => fun f1 f2 => forall x1 x2, interp_related x1 x2 -> interp_related (f1 x1) (f2 x2)
     end.

Local Ltac concretize := cbv zeta.
Local Ltac simpler' := concretize; simpl in *; try subst; intros; auto; try subst; intros; auto;
  try congruence; try omega; try (elimtype False; omega).
Local Ltac simplerGoal :=
  idtac;
  match goal with
  | [ H : False |- _ ] => destruct H
  | [ x : unit |- _ ] => destruct x
  | [ x : (_ * _)%type |- _ ] => destruct x
  | [ H : ex _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ \/ _ |- _ ] => destruct H
  | _ => progress unfold eq_rect in *
  | [ H : (_ + _)%type -> _ |- _ ]
    => pose proof (fun x => H (inl x));
       pose proof (fun x => H (inr x));
       clear H
  | [ H : forall x : ?A = clist ?A, _ |- _ ] => clear H
  | [ H : forall x : csimple ?A = csimple (clist ?A), _ |- _ ] => clear H
  | [ H : False -> _ |- _ ] => clear H
  | [ H : sigT ?P -> _ |- _ ] => specialize (fun x p => H (existT P x p))
  | [ H : sig ?P -> _ |- _ ] => specialize (fun x p => H (exist P x p))
  | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
  | [ H : forall a b c, (_ + _)%type -> _ |- _ ]
    => pose proof (fun a b c x => H a b c (inl x));
       pose proof (fun a b c x => H a b c (inr x));
       clear H
  | [ H : forall a b c, False -> _ |- _ ] => clear H
  | [ H : forall a b c, sigT _ -> _ |- _ ] => specialize (fun a b c x p => H a b c (existT _ x p))
  | [ H : forall a b c, sig _ -> _ |- _ ] => specialize (fun a b c x p => H a b c (exist _ x p))
  | [ H : forall a b c (d : ?x = a), _ |- _ ] => specialize (fun b c => H _ b c eq_refl)
  | [ H : ?P -> _ |- _ ] =>
    let H' := fresh "H'" in
    assert (H' : P); [ solve [ auto ]
                     | generalize (H H'); clear H H'; intro H ]
  | [ H : ?x = ?y |- _ ]
    => pose proof (pr2_path H);
       generalize dependent (pr1_path H);
       clear H;
       intros ??
    | [ H : forall a b, _ /\ _ -> _ |- _ ]
      => specialize (fun a b c d => H a b (conj c d))
    | [ H : forall a b (c : ?v = a), _ |- _ ]
      => specialize (fun b => H _ b eq_refl)
    | [ H : forall a (b : ?v = a), _ |- _ ]
      => specialize (H _ eq_refl)
    | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
  (*| [ H : existT ?F ?T ?X = existT _ ?T ?Y |- _ ] =>
                        generalize (inj_pair2 _ F _ X Y H); clear H*)
  | [ H : Some ?X = Some ?Y |- _ ] =>
    lazymatch X with
    | Y => clear H
    | _ => injection H; try clear H; intro
    end
  | [ H : option_map _ ?x = Some _ |- _ ]
    => destruct x eqn:?; unfold option_map at 1 in H
  | [ H : Some _ = option_map _ ?x |- _ ]
    => destruct x eqn:?; unfold option_map at 1 in H
  (*| [ H : an_arg _ _ = an_arg _ _ |- _ ]
    => apply args_for_encode in H; unfold args_for_code in H
  | [ H : noargsv = noargsv |- _ ] => clear H
  | [ H : @args_for_equiv _ _ _ (carrow _ _) _ _ |- _ ]
    => apply invert_args_for_equiv in H; cbv beta iota in H
  | [ H : @args_for_equiv _ _ _ (csimple _) _ _ |- _ ]
    => apply invert_args_for_equiv in H; cbv beta iota in H*)
  | [ |- _ /\ _ ] => split

  | [ |- context[if ?E then _ else _] ] => destruct E eqn:?
  (*| [ |- context[match ?pf with refl_equal => _ end] ] => rewrite (UIP_refl _ _ pf)*)
  | [ H : context[if ?E then _ else _] |- _ ] => destruct E eqn:?
  | [ |- (_, _) = (_, _) ] => apply f_equal2
  | [ |- cons _ _ = cons _ _ ] => apply f_equal2
  (*| [ |- an_argv _ _ = an_argv _ _ ] => apply f_equal2*)
  | _ => progress simpl
  | [ |- context[interp_Term_gen ?f ?v] ]
    => change (interp_Term_gen f v)
       with (@interp_Term_gen_step f (@interp_Term_gen f) _ v)
  | [ |- context[option_map _ ?x] ]
    => destruct x eqn:?; simpl
  (*| _ => progress unfold interp_args_for, interp_Term in **)
  end.
Local Ltac simpler := simpler'; repeat (simplerGoal; simpler').
Local Ltac simpler_args_for' :=
  idtac;
  match goal with
  | [ args : args_for _ (carrow ?A ?B) |- _ ]
    => let H := fresh in
       pose proof (invert_args_for_ex args) as H; cbv beta iota in H;
       destruct H as [? [? ?]]; subst args
  | [ args : args_for _ (csimple ?B) |- _ ]
    => let H := fresh in
       pose proof (invert_args_for_ex args) as H; cbv beta iota in H;
       subst args
  end.
Local Ltac simpler_args_for := repeat simpler_args_for'.


Lemma push_var : forall t v1 v2 t' v1' v2' G,
  vars v1' v2' = vars v1 v2
  \/ List.In (vars v1 v2) G
  -> (forall t'' v1'' v2'', List.In (vars v1'' v2'') G -> @related t'' v1'' v2'')
  -> @related t' v1' v2'
  -> @related t v1 v2.
Proof.
  simpler.
Qed.

Lemma constantOf_correct
  : forall {T} (t : Term interp_TypeCode T) v
           (H : constantOf t = Some v),
    interp_Term t = interp_constantOf v.
Proof.
  unfold interp_Term;
  intros T t; induction t;
  repeat match goal with
         | [ t : RLiteralTerm _ |- _ ] => destruct t
         | [ t : RLiteralConstructor _ |- _ ] => destruct t
         | [ H : constantOf ?bv = Some ?dv, H' : forall a b c d, constantOf b = Some d -> _ |- _ ]
           => pose proof (fun c => H' _ bv c dv H); clear H
         | _ => progress simpler_args_for
         | _ => progress simpler
         end.
Qed.

Local Ltac simpler_constantOf
  := repeat match goal with
            | [ H : constantOf ?t = Some ?v |- _ ]
              => apply (@constantOf_correct _ t v) in H
            end.

Lemma fold_left_app {A B A' B'}
      (f : A -> B -> A) (ls : list B) (init : A)
      (g : A' -> B' -> A') (ha : A -> A') (hb : B -> B')
      (H : forall x y, g (ha x) (hb y) = ha (f x y))
  : List.fold_left g (List.map hb ls) (ha init)
    = ha (List.fold_left f ls init).
Proof.
  revert init; induction ls as [|x xs IHxs]; simpl; [ reflexivity | ]; intros.
  rewrite <- IHxs, H; reflexivity.
Qed.

Create HintDb partial_unfold_hints discriminated.

Hint Rewrite <- @interp_Term_syntactify_list @interp_Term_syntactify_nat @List.map_rev : partial_unfold_hints.
Hint Rewrite @nth'_nth List.map_nth List.map_map List.map_length List.map_id @combine_map_r @combine_map_l @first_index_default_map : partial_unfold_hints.
Hint Resolve map_ext_in fold_left_app : partial_unfold_hints.

Local Ltac meaning_tac_helper' :=
  idtac;
  match goal with
  | [ |- ?x = ?y ] => reflexivity
  | [ H : forall a b (c : a = _), _ |- _ ] => specialize (fun b => H _ b eq_refl)
  | [ H : forall a b c (d : b = _), _ |- _ ] => specialize (fun a c => H a _ c eq_refl)
  | [ H : forall x y, _ = _ |- _ ] => setoid_rewrite <- H
  | [ |- appcontext[Common.apply_n ?n ?f ?x] ]
    => clear;
       let IH := fresh "IH" in
       generalize x; induction n as [|? IH]; simpl;
       [ reflexivity
       | intro; rewrite <- IH; unfold interp_Term; simpl;
         first [ reflexivity
               | omega ] ]
  | [ |- context[Operations.List.list_caset_nodep _ _ ?ls] ]
    => is_var ls; destruct ls
  | [ |- Operations.List.list_caset_nodep _ _ ?ls = Operations.List.list_caset_nodep _ _ ?ls ]
    => destruct ls
  | [ H : ?x = _ |- context[?x] ] => rewrite H
  | [ |- context[Reflective.ritem_rect_nodep _ _ ?x] ]
    => destruct x eqn:?; simpl
  | [ H : forall x, _ = _ |- _ ] => rewrite <- H; reflexivity
  | [ H : forall x, _ = _ |- _ ] => setoid_rewrite <- H; reflexivity
  end.
Local Ltac meaning_tac_helper := repeat meaning_tac_helper'.

Local Ltac meaning_tac :=
  repeat first [ progress autorewrite with partial_unfold_hints
               | progress eauto with partial_unfold_hints
               | progress rewrite_strat (topdown (hints partial_unfold_hints))
               | progress meaning_tac_helper
               | progress simpl_interp_Term_in_all ].

Local Hint Resolve push_var.
Lemma meaning_correct
  : forall G t e1 e2,
    Term_equiv G e1 e2
    -> (forall t' v1 v2, List.In (vars v1 v2) G
                         -> @related t' v1 v2)
    -> @related t (interp_Term e1) (meaning e2).
Proof.
  unfold interp_Term;
  induction 1; try solve [ simpler; eauto ].
  { simpler; unfold interp_Term in *; eauto.
    repeat match goal with
           | [ |- _ = _ ] => reflexivity
           | [ x : args_for _ _ |- _ ] => clear dependent x
           | [ f : RLiteralTerm _ |- _ ] => destruct f
           | [ f : RLiteralConstructor _ |- _ ] => destruct f
           | [ f : RLiteralNonConstructor _ |- _ ] => destruct f
           end;
      repeat match goal with
             | _ => progress simpler_constantOf
             | _ => progress simpler_args_for
             | _ => progress simpler
             | [ |- context[constantOf ?x] ]
               => destruct (constantOf x) eqn:?
             | [ H : ?v = _ |- context[?v] ]
               => rewrite H
             end;
      change (@interp_Term_gen (@interp_RLiteralTerm)) with (@interp_Term) in *.
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac.
      admit. }
    { meaning_tac.
      (*SearchAbout Operations.List.list_rect_nodep.
      match goal with

      | [ |- context[Operations.List.list_rect_nodep
      move x2 at bottom.*)
      admit. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac. }
    { meaning_tac.
      match goal with
      | [ |- context[match ?x with Some _ => _ | None => _ end] ]
        => destruct x eqn:?
      end;
      meaning_tac.
(*Print Operations.List.first_index_helper.
Hint Rewrite  : partial_unfold_hints.
meaning_tac.
match goal with
| [ H : forall x, _ = _ |- _ ] => setoid_rewrite H
end.
pose (fun arg : Term interp_TypeCode A => @constantOf_correct cbool (meaning x arg)).
simpl in e.
Lemma first_index_default_first_index_partial
      {A} (test : A -> bool) (testo : A -> option bool)
      (H : forall a v, testo a = Some v -> test a = v)
      (ls : list A)
      v
      (Heq : Operations.List.first_index_partial
               testo ls = Some v)
  : Operations.List.first_index_error test ls = v.
Proof.
  revert dependent v; induction ls as [|x xs IHxs]; simpl in *; intros; [ congruence | ].
  destruct (testo x) as [[]|] eqn:H'; simpl in *;
    [ erewrite H by eassumption.. | ];
    simpl;
    [ congruence
    | | ].
  { destruct (Operations.List.first_index_partial testo xs) as [[]|] eqn:H''; simpl in *.
    specialize (IHxs _ eq_refl).

    simpl in *.

Lemma first_index_default_first_index_default_partial
      {A} (test : A -> bool) (testo : A -> option bool)
      (H : forall a v, testo a = Some v -> test a = v)
      (default : nat)
      (ls : list A)
      v
      (Heq : Operations.List.first_index_default_partial
               testo default ls = Some v)
  : Operations.List.first_index_default test default ls = v.
Proof.
  revert dependent default; induction ls as [|x xs IHxs]; simpl in *; intros.
  { unfold Operations.List.first_index_default_partial in *.

  : forall {T} (t : Term interp_TypeCode T) v
           (H : constantOf t = Some v),
    interp_Term t = interp_constantOf v.


rewrite first_index_default_map.
simpler.

Lemma first_index_default_helper_map {A' A B}
      (test : A -> bool)
      (f : A' -> A)
      (ls : list A')
      (rec : nat -> nat)
      (default : A)
      (rect := option_rect (fun _ : option (nat * B) => nat) fst default)
  : Operations.List.first_index_helper
      test rect (List.map f ls) rec
    = Operations.List.first_index_helper
        (fun x => test (f x))
        (fun na' => rect (option_map (fun na' => (fst na', f (snd na'))) na'))
        ls
        rec.
Proof.


  rewrite !first_index_helper_first_index_error; simpl.
  *)
      admit.

 }
    { meaning_tac. }
    { meaning_tac. } }
Qed.

Local Hint Extern 1 (@related ?T ?X (reflect (RVar ?Y))) =>
change (@related T (interp_Term (RVar X)) (reflect (RVar Y))).
Local Hint Extern 1 (@related _ (interp_Term_gen ?iRLT ?A ?X1) _) =>
  change (interp_Term_gen iRLT A X1)
  with (interp_Term_gen iRLT (RApp A (RVar X1))).
Lemma reify_and_reflect_correct : forall t,
    (forall v r,
        @related t v r
        -> interp_related v (interp_Term (reify _ r)))
    /\ (forall a a',
           @interp_related t (interp_Term a) (interp_Term a')
           -> @related t (interp_Term a) (reflect a')).
Proof.
  unfold interp_Term;
  induction t; simpler; eauto.
Qed.

Lemma reify_correct : forall t v r,
  @related t v r
  -> interp_related v (interp_Term (reify _ r)).
Proof.
  generalize reify_and_reflect_correct; firstorder.
Qed.

Lemma nil_context : forall t v1 v2,
  List.In (vars v1 v2) nil
  -> @related t v1 v2.
Proof.
  simpl; tauto.
Qed.

Local Hint Resolve nil_context meaning_correct reify_correct.
Theorem polynormalize_correct : forall t (E : polyTerm t),
    Term_equiv nil (E interp_TypeCode) (E (normalized_of interp_TypeCode))
    -> interp_related (interp_Term (E _)) (interp_Term (polynormalize E _)).
Proof.
  unfold interp_Term, polynormalize, normalize; eauto.
Qed.
