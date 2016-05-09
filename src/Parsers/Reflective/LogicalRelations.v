Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.PartialUnfold.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.
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
  | [ H : ?P -> _ |- _ ] =>
    let H' := fresh "H'" in
    assert (H' : P); [ solve [ auto ]
                     | generalize (H H'); clear H H'; intro H ]
  | [ H : ?x = ?y |- _ ]
    => pose proof (pr2_path H);
       generalize dependent (pr1_path H);
       clear H;
       intros ??
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
  intros T t; induction t;
  repeat match goal with
         | [ t : RLiteralTerm _ |- _ ] => destruct t
         | [ t : RLiteralConstructor _ |- _ ] => destruct t
         | [ H : constantOf ?bv = Some ?dv, H' : forall a b c d, constantOf b = Some d -> _ |- _ ]
           => pose proof (fun c => H' _ bv c dv H); clear H
         | _ => progress simpler_args_for
         | _ => simpler
         end.
  simpler.
  apply H in Heqo.
Qed.

Local Ltac simpler_constantOf
  := repeat match goal with
            | [ H : constantOf ?t = Some ?v |- _ ]
              => apply (proj1 constantOf_correct _ t v) in H
            end.

Local Hint Resolve push_var.
Lemma meaning_correct
  : (forall G t e1 e2,
        Term_equiv G e1 e2
        -> (forall t' v1 v2, List.In (vars v1 v2) G
                             -> @related t' v1 v2)
        -> @related t (interp_Term e1) (meaning e2))
    /\ (forall G t e1 e2,
           args_for_equiv G e1 e2
           -> (forall t' v1 v2, List.In (vars v1 v2) G
                                -> @related t' v1 v2)
           -> args_for_values_related
                (fun _ => eq)
                (@interp_args_for t e1)
                (@interp_args_for t (unmeanings (meanings (@meaning interp_TypeCode) e2)))).
Proof.
  split.
  Focus 2.
  intros.
  pose (meanings (@meaning interp_TypeCode) e2).
  unfold interp_Term, interp_args_for.
  apply Term_equiv_args_for_equiv_mutind;
  try solve [ simpler; eauto ].
  Focus 2.
  Set Printing Implicit.
  unfold id.
About interp_args_for.

  intros.
  simpl.
  apply f_equal2; try solve [ simpler; eauto ].

  Print reify.
  simpler; eauto.

  { simpler; eauto.
   match goal with
    | [ H : ?v = _ |- context[?v] ]
      => rewrite H; clear H
    end.
    repeat match goal with
           | [ |- _ = _ ] => reflexivity
           | [ x : args_for _ _ |- _ ] => clear dependent x
           | [ f : RLiteralTerm _ |- _ ] => destruct f
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
             end.
      simpler_constantOf;
      simpler.
      simpler_args_for.
      simpler.
   match goal with
    end.

      {

simplerGoal.
simpl.
{ simpler.
match goal with
end.
simpler.
simpler.
unfold interp_Term in *.
rewrite H, H0.

  lazymatch goal with  | [ H : an_argv _ _ = an_argv _ _ |- _ ]
    => apply args_for_values_encode in H; unfold args_for_values_code in H
end.
simpl in *.
 (*
unfold constantOfs in *.
simpl in *.
  simpl in *.
  end.
  try .
  simpl.
  match goal with
  erewrite H; simpl in *.
  simpl
pose ((constantOfs (@constantOf interp_TypeCode) args)).
About Term_args_for_mutind.
repeat
About interp_args_for.
simpl in *.
  simpl in *
         | [ H : @constantOf _ ?T _ = Some _ |- _ ] => apply (@constantOf_correct T) in H
         end.
Guarded.

         end.
  Guarded.
Set Printing Implicit.
  eapply constantOf_correct in Heqo.
  simpl in *.
  induction t; try (simpl in *; congruence).
  simpl in H.
  destruct T as [T|]; [ | simpl in *; tauto ].

  Print constantOf.
  induction T; simpl in *.
  induction T; simpl in *.
  Print interp_constantOf.
  destruct t.
  :
      Print constantOf.
lazymatch goal with
           | [ args : args_for _ (csimple ?A) |- _ ]
             => let H := fresh in
                pose proof (invert_args_for_ex args) as H; cbv beta iota in H
end.
                  destruct H as [? [? ?]]; subst args

      Set Printing Implicit.
lazymatch goal with
end.
            destruct fespeci).
    let f := match goal with
             | [ f : RLiteralTerm _ |- _ ] => f
             end in
    destruct f; try reflexivity; [].


    match goal with
    match goal with
    destruct f; simpl.
    repeat (let f := match goal with
                     | [ f : RLiteralTerm _ |- _ ] => f
                     | [ f : RLiteralNonConstructor _ |- _ ] => f
                     end in
            destruct f).

    simpler; eauto.
    pose v1.
    pose ( (meanings (@meaning interp_TypeCode) v2)).
Print meanings.
Set Printing Implicit.
simpl.
Fixpoint args_related {T} : interp_TypeCode T -> interp_TypeCode (range_of T) -> arg_meanings_for interp_TypeCode T -> Prop
  := match T return interp_TypeCode T -> interp_TypeCode (range_of T) -> arg_meanings_for interp_TypeCode T -> Prop with
     | csimple T' => fun f v args => f = v
     | (dom --> ran)%typecode
       => fun f fargs args => forall x1 x2, related x1 x2 -> args_related f fargs (an_argm x2 args)
     end.


    cbv [interp_Term interp_RLiteralTerm].
    fold @interp_args_for.
About meanings.
    simpl.

(*
      simpler.
    { simpler.
      unfold vars in *.
Set Printing All.

    simpl in *.
    match goal with
    end.
Definition invert_args_for_equiv {var1 var2 G T v1 v2}
           (H : @args_for_equiv var1 var2 G T v1 v2)
  : match T return args_for var1 T -> args_for var2 T -> Prop
    with
    | csimple _ => fun v1 v2 => v1 = noargs /\ v2 = noargs
    | carrow A B
      => fun v1 v2
         => exists h1 t1 h2 t2,
             v1 = an_arg h1 t1 /\ v2 = an_arg h2 t2
             /\ Term_equiv G h1 h2
             /\ args_for_equiv G t1 t2
    end v1 v2.
Proof.
  destruct H; repeat esplit; assumption.
Defined.
    match goal with
    | [ args : args_for _ (carrow ?A ?B) |- _ ]
      => let H := fresh in
         pose proof (invert_args_for_ex args) as H; cbv beta iota in H;
           destruct H as [? [? ?]]; subst args
    end.
Print args_for.
Definition invert_args_for {var T} (args : args_for var T)
  : args = match T return args_for var T -> args_for var T with
           | csimple T' => fun _ => noargs
           | carrow A B => fun args' => an_arg (ahd args') (atl args')
           end args.
Proof.
  destruct args; reflexivity.
Defined.

    let RHS := match goal with |- _ = ?RHS => RHS end in
    lazymatch RHS with
    | appcontext G[?f (match ?x with
                       | RLC x' => @?c x'
                       | RLNC y' => @?nc y'
                       end ?arg1)]
      => idtac;
           let G' := context G[match x with
                               | RLC x' => fun a1 => f (c x' a1)
                               | RLNC y' => fun a1 => f (nc y' a1)
                               end arg1] in
           transitivity G';
             [ simpl | destruct x; reflexivity ]
    end.
    Print RLC.
Lemma push_apply_match_RLiteralTerm {T A}
           (t : RLiteralTerm T)
           (c : RLiteralConstructor T -> A)
           (nc
           (f : forall t : RLiteralTerm T, P t)
  : f (match
  solve [ simpler; eauto ].
  Focus 2.
  { intro H'; eapply push_var; [ left | eexact H' | ].
    unfold vars.
eapply push_var. induction T; simpl.


Qed.

Lemma reify_and_reflect_correct : forall t,
  (forall v r,
    @related t v r
    -> v = ninterp_Term (reify r))
  /\ (forall a,
    @related t (appsDenote a) (reflect a)).
  Hint Resolve ext_eq.
  Hint Extern 1 (@related ?T ?X (reflect (Var ?X))) =>
    change (@related T (appsDenote (Var X)) (reflect (Var X))).
  Hint Extern 5 (_ = _) => symmetry.

  Hint Extern 1 (@related _ (appsDenote ?A ?X1) _) =>
    match goal with
      | [ _ : @related _ X1 ?X2 |- _ ] =>
        replace (appsDenote A X1)
          with (appsDenote (App A (reify X2)))
    end.
  Hint Extern 1 (appsDenote _ = appsDenote _ _) => simpl; f_equal.

  induction t; simpler.
Qed.

Lemma reify_correct : forall t v r,
  @related t v r
  -> v = ninterp_Term (reify r).
  generalize reify_and_reflect_correct; firstorder.
Qed.

Lemma nil_context : forall t v1 v2,
  List.In (vars v1 v2) nil
  -> @related t v1 v2.
  simpl; tauto.
Qed.

Theorem Normalize_correct : forall t (E : Exp t),
  ExpDenote E = Ninterp_Term (Normalize E).
  Hint Resolve Term_equiv nil_context meaning_correct reify_correct.

  unfold Ninterp_Term, Normalize, normalize, ExpDenote; eauto.
Qed.



Lemma push_var : forall t v1 v2 t' v1' v2' G,
  Source.vars v1' v2' = Source.vars v1 v2
  \/ List.In (Source.vars v1 v2) G
  -> (forall t'' v1'' v2'', List.In (Source.vars v1'' v2'') G -> @related t'' v1'' v2'')
  -> @related t' v1' v2'
  -> @related t v1 v2.
  simpler.
Qed.

Lemma meaning_correct : forall G t e1 e2,
  Term_equiv G e1 e2
  -> (forall t' v1 v2, List.In (vars v1 v2) G
    -> @related t' v1 v2)
  -> @related t (interp_Term e1) (meaning e2).
  Hint Resolve push_var.

  induction 1; simpler; eauto.
Qed.

Lemma reify_and_reflect_correct : forall t,
  (forall v r,
    @related t v r
    -> v = ninterp_Term (reify r))
  /\ (forall a,
    @related t (appsDenote a) (reflect a)).
  Hint Resolve ext_eq.
  Hint Extern 1 (@related ?T ?X (reflect (Var ?X))) =>
    change (@related T (appsDenote (Var X)) (reflect (Var X))).
  Hint Extern 5 (_ = _) => symmetry.

  Hint Extern 1 (@related _ (appsDenote ?A ?X1) _) =>
    match goal with
      | [ _ : @related _ X1 ?X2 |- _ ] =>
        replace (appsDenote A X1)
          with (appsDenote (App A (reify X2)))
    end.
  Hint Extern 1 (appsDenote _ = appsDenote _ _) => simpl; f_equal.

  induction t; simpler.
Qed.

Lemma reify_correct : forall t v r,
  @related t v r
  -> v = ninterp_Term (reify r).
  generalize reify_and_reflect_correct; firstorder.
Qed.

Lemma nil_context : forall t v1 v2,
  List.In (vars v1 v2) nil
  -> @related t v1 v2.
  simpl; tauto.
Qed.

Theorem Normalize_correct : forall t (E : Exp t),
  ExpDenote E = Ninterp_Term (Normalize E).
  Hint Resolve Term_equiv nil_context meaning_correct reify_correct.

  unfold Ninterp_Term, Normalize, normalize, ExpDenote; eauto.
Qed.


Inductive
*)
