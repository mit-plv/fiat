Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.PartialUnfold.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.
Require Import Fiat.Parsers.Reflective.Morphisms.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.

Fixpoint related {T} : interp_TypeCode T -> normalized_of interp_TypeCode T -> Prop
  := match T return interp_TypeCode T -> normalized_of interp_TypeCode T -> Prop with
     | csimple T' => fun b e => b = interp_Term e
     | (dom --> ran)%typecode
       => fun f1 f2 => forall x1 x2, related x1 x2 -> related (f1 x1) (f2 x2)
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

Lemma bool_rect_nodep_const {P x b}
  : BoolFacts.Bool.bool_rect_nodep P x x b = x.
Proof. destruct b; reflexivity. Qed.

Create HintDb partial_unfold_hints discriminated.

Hint Rewrite <- @interp_Term_syntactify_list @interp_Term_syntactify_nat @List.map_rev : partial_unfold_hints.
Hint Rewrite @nth'_nth List.map_nth List.map_map List.map_length List.map_id @combine_map_r @combine_map_l @first_index_default_map Bool.orb_true_r Bool.orb_true_l Bool.andb_true_l Bool.andb_true_r Bool.orb_false_r Bool.orb_false_l Bool.andb_false_l Bool.andb_false_r BoolFacts.andbr_andb BoolFacts.orbr_orb @bool_rect_nodep_const @BoolFacts.uneta_bool_rect_nodep : partial_unfold_hints.
Hint Resolve map_ext_in fold_left_app (@constantOf_correct cbool) @first_index_default_first_index_partial : partial_unfold_hints.

Local Ltac meaning_tac_helper' :=
  idtac;
  match goal with
  | [ |- ?x = ?y ] => reflexivity
  | [ H : forall a b (c : a = _), _ |- _ ] => specialize (fun b => H _ b eq_refl)
  | [ H : forall a b c (d : b = _), _ |- _ ] => specialize (fun a c => H a _ c eq_refl)
  | [ H : forall x y, _ = _ |- _ ] => setoid_rewrite <- H
  | [ |- context[Common.apply_n ?n ?f ?x] ]
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
  | [ |- context[match ?x with Some _ => _ | None => _ end] ]
    => destruct x eqn:?
  end.
Local Ltac meaning_tac_helper := repeat meaning_tac_helper'.

Local Ltac meaning_tac :=
  repeat first [ progress autorewrite with partial_unfold_hints
               | progress eauto with partial_unfold_hints
               | progress rewrite_strat (topdown (hints partial_unfold_hints))
               | progress meaning_tac_helper
               | progress simpl_interp_Term_in_all ].

Local Hint Extern 1 (@related ?T ?X (reflect (RVar ?Y))) =>
change (@related T (interp_Term (RVar X)) (reflect (RVar Y))).
Local Hint Extern 1 (@related _ (interp_Term_gen ?iRLT ?A ?X1) _) =>
  change (interp_Term_gen iRLT A X1)
  with (interp_Term_gen iRLT (RApp A (RVar X1))).
Lemma reify_and_reflect_correct : forall t,
    (forall v r,
        @related t v r
        -> Proper_relation_for _ v (interp_Term (reify _ r)))
    /\ (forall a a',
           @Proper_relation_for t (interp_Term a) (interp_Term a')
           -> @related t (interp_Term a) (reflect a')).
Proof.
  unfold interp_Term;
  induction t; simpler; unfold respectful; eauto.
Qed.

Lemma reify_correct : forall t v r,
  @related t v r
  -> Proper_relation_for _ v (interp_Term (reify _ r)).
Proof.
  generalize reify_and_reflect_correct; firstorder.
Qed.

Lemma args_for_related_related_map {T v1 v2} (f := @meaning _)
  : (args_for_related
       (T := T)
       (fun T (m : Term interp_TypeCode T) (n : Term (normalized_of interp_TypeCode) T)
        => related (interp_Term m) (f T n))
       v1 v2)
    -> (args_for_related (fun T => Proper_relation_for T)
                          (map_args_for (@interp_Term) v1)
                          (map_args_for (@interp_Term) (unmeanings (meanings f v2)))).
Proof.
  subst f; revert v2.
  induction v1; intro;
    pose proof (invert_args_for_ex v2) as H'; simpl in *;
      [ destruct H' as [? [? ?]] | subst; split; reflexivity ];
      subst; simpl in *.
  intros [H0 H1]; split; try assumption;
    [ | apply IHv1; assumption ]; clear IHv1.
  apply reify_and_reflect_correct; assumption.
Qed.

Lemma interp_apply_meaning_helper
      T f f' (Hf : @related T f f')
      args args'
      (Hargs : args_for_related (fun T' m n => related (interp_Term m) (meaning n)) args args')
  : apply_args_for f (map_args_for (fun _ t => interp_Term t) args)
    = interp_Term (apply_meaning_helper (meanings (@meaning interp_TypeCode) args') f').
Proof.
  apply args_for_related_noind_ind in Hargs.
  revert f f' Hf.
  induction Hargs; [ | solve [ simpl; trivial ] ].
  apply args_for_related_noind_ind in Hargs.
  simpl in *.
  eauto with nocore.
Qed.

Local Ltac simpler_meaning :=
  repeat match goal with
         | _ => progress simpler_constantOf
         | _ => progress simpler_args_for
         | _ => progress simpl_interp_Term_in_all
         | _ => progress simpler
         | _ => progress simpl in *
         | [ H : ?x = _ |- context[?x] ] => rewrite H
         | [ H : context[match constantOf ?x with _ => _ end] |- _ ]
           => destruct (constantOf x) eqn:?
         | [ H : match ?T with cbool => _ | _ => _ end _ = Some _ |- _ ]
           => is_var T; destruct T
         end.

Lemma list_rect_nodep_meaning_correct {A : SimpleTypeCode} {P} f f' n n'
      (Hn : @related P n n')
      (Hf : @related (A --> clist A --> P --> P) f f')
      (ls : list (Term interp_TypeCode A))
  : related (Operations.List.list_rect_nodep n f (List.map (@interp_Term _) ls))
            (Operations.List.list_rect_nodep n' (fun x xs => f' x (Syntactify.syntactify_list xs)) ls).
Proof.
  induction ls; simpl in *; [ assumption | ].
  apply Hf; eauto using eq_refl, @interp_Term_syntactify_list with nocore.
Qed.

Hint Resolve @list_rect_nodep_meaning_correct : partial_unfold_hints.

Lemma specific_meaning_correct
      t r val v1 v2
      (Hrel : args_for_related
                (fun T' m n => @related T' (interp_Term m) (meaning n)) v1 v2)
      (Heq : specific_meaning r (meanings (@meaning interp_TypeCode) v2) = Some val)
  : interp_Term (@RLiteralApp _ t r v1) = interp_Term val.
Proof.
  destruct r; simpl in Heq;
    unfold specific_meaning_apply1, specific_meaning_apply2 in *;
    try solve [ simpler_meaning; meaning_tac ].
  { simpler_meaning; meaning_tac.
    apply interp_apply_meaning_helper; simpl; try assumption; [].
    apply list_rect_nodep_meaning_correct; simpl; eauto with nocore.
    simpler_meaning; meaning_tac. }
  { simpler_meaning; meaning_tac.
    rewrite Plus.plus_comm; meaning_tac. }
Qed.

Local Hint Resolve push_var.
Lemma meaning_correct
  : forall G t e1 e2,
    Term_equiv G e1 e2
    -> (forall t' v1 v2, List.In (vars v1 v2) G
                         -> @related t' v1 v2)
    -> @related t (interp_Term e1) (meaning e2).
Proof.
  unfold interp_Term;
    induction 1 (*using Term_equiv_ind_in*); try solve [ simpler; eauto ].
  { simpler.
    repeat match goal with
           | [ H : args_for_related_ind _ _ _ |- _ ]
             => apply args_for_related_noind_ind in H
           | [ H : args_for_related (fun x y z => ?P -> _) _ _ |- _ ]
             => setoid_rewrite <- args_for_related_impl in H
           | _ => progress simpl_interp_Term_in_all
           | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
           | [ f : RLiteralTerm _ |- _ ] => destruct f
           | [ |- apply_args_for _ _ = apply_args_for _ _ ]
             => apply apply_args_for_Proper;
                  [ apply RLiteralTerm_Proper | apply args_for_related_related_map; assumption ]
           | [ |- context[specific_meaning ?r ?x] ]
             => destruct (specific_meaning r x) eqn:?
           end.
    eapply specific_meaning_correct; eassumption. }
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
    -> Proper_relation_for _ (interp_Term (E _)) (interp_Term (polynormalize E _)).
Proof.
  unfold interp_Term, polynormalize, normalize; eauto.
Qed.
