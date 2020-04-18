Require Import Bedrock.Heaps Bedrock.Memory.
Require Import Bedrock.PropX Bedrock.PropXTac.
Require Import Coq.Classes.RelationClasses.
Require Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SepTheoryX.
  Declare Module H : Heap.

  Parameter hprop : forall (pcType stateType : Type), list Type -> Type.

  Module HT := HeapTheory H.

Section Env.
  Variable pcType : Type.
  Variable stateType : Type.
  Parameter settings : Type.

  Parameter satisfies : forall (cs : codeSpec pcType stateType) (p : hprop pcType stateType nil) (s : settings) (m : HT.smem), Prop.

  Parameter himp : forall (cs : codeSpec pcType stateType),
    hprop pcType stateType nil -> hprop pcType stateType nil -> Prop.

  Parameter heq : forall (cs : codeSpec pcType stateType),
    hprop pcType stateType nil -> hprop pcType stateType nil -> Prop.

  Variable cs : codeSpec pcType stateType.

  Parameter Refl_himp : Reflexive (@himp cs).
  Parameter Trans_himp : Transitive (@himp cs).

  Parameter Refl_heq : Reflexive (@heq cs).
  Parameter Sym_heq : Symmetric (@heq cs).
  Parameter Trans_heq : Transitive (@heq cs).

  Notation "a ===> b" := (himp cs a b) (at level 60).
  Notation "a <===> b" := (heq cs a b) (at level 60).

  Parameter heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.

  Parameter heq_himp : forall a b, a <===> b -> a ===> b.

  (* Definitions *)
  Parameter inj : forall {sos} (p : propX pcType stateType sos),
    hprop pcType stateType sos.

  Parameter emp : forall {sos}, hprop pcType stateType sos.

  Parameter star : forall {sos} (l r : hprop pcType stateType sos),
    hprop pcType stateType sos.

  Parameter ex : forall {sos} (T : Type) (p : T -> hprop pcType stateType sos),
    hprop pcType stateType sos.

  Parameter hptsto : forall {sos} (p : H.addr) (v : B),
    hprop pcType stateType sos.

  (* satisfies lemmas *)
  Parameter satisfies_himp : forall cs P Q stn,
    himp cs P Q ->
    (forall m,
     satisfies cs P stn m ->
     satisfies cs Q stn m).

  Parameter satisfies_star : forall cs P Q stn m,
    satisfies cs (star P Q) stn m <->
    exists ml, exists mr,
      HT.split m ml mr /\
      satisfies cs P stn ml  /\ satisfies cs Q stn mr.

  Parameter satisfies_pure : forall cs p stn m,
    satisfies cs (inj p) stn m ->
    interp cs p /\ HT.semp m.

  Parameter satisfies_ex : forall cs T p stn m,
    satisfies cs (@ex _ T p) stn m ->
    exists x : T, satisfies cs (p x) stn m.

  (* himp/heq lemmas *)
  Parameter himp_star_comm : forall P Q, (star P Q) ===> (star Q P).

  Parameter himp_star_assoc : forall P Q R,
    (star (star P Q) R) ===> (star P (star Q R)).

  Parameter heq_star_comm : forall P Q,
    (star P Q) <===> (star Q P).

  Parameter heq_star_assoc : forall P Q R,
    (star (star P Q) R) <===> (star P (star Q R)).

  Parameter heq_star_emp_l : forall P, (star emp P) <===> P.
  Parameter heq_star_emp_r : forall P, (star P emp) <===> P.

  Parameter himp_star_frame : forall P Q R S,
    P ===> Q -> R ===> S -> (star P R) ===> (star Q S).

  Parameter himp_star_pure_p : forall P Q F,
    (star (inj F) P) ===> Q -> (interp cs F -> P ===> Q).

  Parameter himp_star_pure_c : forall P Q (F : Prop),
    (F -> P ===> Q) -> (star (inj (PropX.Inj F)) P) ===> Q.

  Parameter himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    P ===> Q ->
    P ===> (star (inj (PropX.Inj p)) Q).

  Parameter heq_star_frame : forall P Q R S,
    P <===> Q -> R <===> S -> (star P R) <===> (star Q S).

  Parameter himp_subst_p : forall P Q R S,
    P ===> S -> (star S Q) ===> R ->
    (star P Q) ===> R.

  Parameter himp_subst_c : forall P Q R S,
    S ===> Q -> P ===> (star S R) ->
    P ===> (star Q R).

  Parameter heq_subst : forall P Q R S,
    P <===> S -> (star S Q) <===> R ->
    (star P Q) <===> R.

  Parameter himp_star_cancel : forall P Q R,
    Q ===> R -> (star P Q) ===> (star P R).

  Parameter heq_star_cancel : forall P Q R,
    Q <===> R -> (star P Q) <===> (star P R).

  Parameter himp_ex_p : forall T (P : T -> _) Q,
    (forall v, (P v) ===> Q) -> (ex P) ===> Q.

  Parameter himp_ex_c : forall T (P : T -> _) Q,
    (exists v, Q ===> (P v)) -> Q ===> (ex P).

  Parameter heq_ex : forall T (P Q : T -> _),
    (forall v, P v <===> Q v) ->
    ex P <===> ex Q.

  Parameter himp_ex : forall T (P Q : T -> _),
    (forall v, P v ===> Q v) ->
    ex P ===> ex Q.

  Parameter heq_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) <===> (ex (fun x => star (P x) Q)).

  Parameter himp_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) ===> (ex (fun x => star (P x) Q)).

  Parameter himp'_ex : forall T (P : T -> _) Q,
    (forall x, (P x) ===> Q) ->
    ex P ===> Q.

End Env.

Existing Instance Refl_himp.
Existing Instance Trans_himp.
Existing Instance Refl_heq.
Existing Instance Sym_heq.
Existing Instance Trans_heq.

End SepTheoryX.

Module SepTheoryX_Rewrites (Import ST : SepTheoryX).

  Import Setoid Classes.Morphisms.

  Section env.
    Variable p s : Type.
    Variable cs : codeSpec p s.

    Add Parametric Relation : (@hprop p s nil) (@himp p s cs)
      reflexivity proved by (Refl_himp cs)
      transitivity proved by (@Trans_himp p s cs)
    as himp_rel.

    Add Parametric Relation : (@hprop p s nil) (@heq p s cs)
      reflexivity proved by (Refl_heq cs)
      symmetry proved by (@Sym_heq p s cs)
      transitivity proved by (@Trans_heq p s cs)
    as heq_rel.

    Global Add Parametric Morphism : (@star p s nil) with
      signature (himp cs ==> himp cs ==> himp cs)
    as star_himp_mor.
      intros. eapply himp_star_frame; eauto.
    Qed.

    Global Add Parametric Morphism : (@star p s nil) with
      signature (heq cs ==> heq cs ==> heq cs)
    as star_heq_mor.
      intros. eapply heq_star_frame; eauto.
    Qed.

    Global Add Parametric Morphism T : (@ex p s nil T) with
      signature (pointwise_relation T (heq cs) ==> heq cs)
    as ex_heq_mor.
      intros. eapply heq_ex. eauto.
    Qed.

    Global Add Parametric Morphism T : (@ex p s nil T) with
      signature (pointwise_relation T (himp cs) ==> himp cs)
    as ex_himp_mor.
      intros. eapply himp_ex. auto.
    Qed.

    Global Add Parametric Morphism : (himp cs) with
      signature (heq cs ==> heq cs ==> Basics.impl)
    as himp_heq_mor.
      intros. intro. etransitivity.
      symmetry in H. eapply heq_defn in H. eapply (proj1 H).
      etransitivity. eassumption. eapply heq_defn in H0. intuition.
    Qed.

(*
    Global Add Parametric Morphism : (himp cs) with
      signature (heq cs ==> heq cs ==> Basics.flip Basics.impl)
    as himp_heq_mor'.
      intros. intro. etransitivity.
      symmetry in H. eapply heq_defn in H. eapply (proj2 H).
      etransitivity. eassumption. eapply heq_defn in H0. intuition.
    Qed.
*)

    Global Add Parametric Morphism : (himp cs) with
      signature (himp cs --> himp cs ++> Basics.impl)
    as himp_himp_mor.
      intros. intro. repeat (etransitivity; eauto).
    Qed.

    Global Add Parametric Morphism : (satisfies cs) with
      signature (heq cs ==> @eq _ ==> @eq _ ==> Basics.impl)
    as heq_satsifies_mor.
      intros. intro. eapply satisfies_himp; eauto. eapply heq_defn in H.
      tauto.
    Qed.

  End env.

  Hint Rewrite heq_star_emp_l heq_star_emp_r : hprop.
  Existing Instance himp_rel_relation.
  Existing Instance heq_rel_relation.

End SepTheoryX_Rewrites.

Module SepTheoryX_Ext (ST : SepTheoryX).
  Import List.
  Module Import ST_RW := SepTheoryX_Rewrites ST.
  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Section param.
    Variables pcT stT : Type.

    Variable type : Type.
    Variable typeD : type -> Type.


    Definition existsEach (sos : list Type) (ts : list type) (f : list (@sigT _ typeD) -> ST.hprop pcT stT sos)
      : ST.hprop pcT stT sos :=
      @ST.ex pcT stT sos (list (@sigT _ typeD)) (fun env => ST.star (ST.inj (PropX.Inj (map (@projT1 _ _) env = ts))) (f env)).

    Ltac thinker :=
      repeat match goal with
               | [ H : forall f, ST.himp _ _ _ |- _ ] => rewrite H
               | [ |- _ ] => reflexivity
               | [ |- ST.himp _ (ST.star (ST.inj _) _) _ ] =>
                 apply ST.himp_star_pure_c ; intros
               | [ |- ST.himp _ (ST.ex _) _ ] =>
                 apply ST.himp_ex_p ; intros
               | [ |- ST.himp _ _ (ST.ex (fun x => ST.star (ST.inj (PropX.Inj (?X = _))) _)) ] =>
                 apply ST.himp_ex_c ; exists nil ; eapply ST.himp_star_pure_cc; [ solve [ eauto ] | ]
               | [ |- ST.himp _ _ (ST.ex (fun x => ST.star (ST.inj (PropX.Inj (?X = _))) _)) ] =>
                 apply ST.himp_ex_c ; eexists; eapply ST.himp_star_pure_cc; [ solve [ eauto ] | ]
             end.

    Lemma existsEach_perm : forall cs (F : list (@sigT _ typeD) -> _) x x',
        ST.heq cs (existsEach x (fun e => existsEach x' (fun e' => F (e ++ e'))))
                  (existsEach x' (fun e' => existsEach x (fun e => F (e ++ e')))).
    Proof.
      intros. eapply ST.heq_defn. split; unfold existsEach;
      revert F; revert x'; induction x; simpl; intros;
        repeat match goal with
                 | [ H : forall f, ST.himp _ _ _ |- _ ] => rewrite H
                 | [ |- _ ] => reflexivity
                 | [ |- ST.himp _ (ST.star (ST.inj _) _) _ ] =>
                   apply ST.himp_star_pure_c ; intros
                 | [ |- ST.himp _ (ST.ex _) _ ] =>
                   apply ST.himp_ex_p ; intros
                 | [ |- ST.himp _ _ (ST.ex (fun x => ST.star (ST.inj (PropX.Inj (?X = _))) _)) ] =>
                   apply ST.himp_ex_c ; eexists; eapply ST.himp_star_pure_cc; [ solve [ eauto ] | ]
               end.
    Qed.

    Lemma map_eq_app : forall T U (F : T -> U) ls x y,
      map F ls = x ++ y ->
      exists x' y', ls = x' ++ y' /\ map F x' = x /\ map F y' = y.
    Proof.
      clear. induction ls; destruct x; simpl in *; intros; subst; try congruence.
      exists nil; exists nil; simpl; auto.
      exists nil. simpl. eexists; eauto.
      inversion H; clear H; subst. eapply IHls in H2.
      destruct H2. destruct H. intuition. subst. exists (a :: x0). exists x1. simpl; eauto.
    Qed.

    Lemma existsEach_app : forall cs x x' (F : list (@sigT _ typeD) -> _) ,
      ST.heq cs (existsEach (x ++ x') F)
                (existsEach x (fun e => existsEach x' (fun e' => F (e ++ e')))).
    Proof.
      intros. eapply ST.heq_defn. split; unfold existsEach;
      revert F; revert x'; induction x; simpl; intros; thinker.
      Focus 2. destruct v; simpl in *; try congruence; reflexivity.
      Focus 2. apply ST.himp_ex_c ; eexists (v ++ v0); eapply ST.himp_star_pure_cc. rewrite map_app. rewrite H. rewrite H0. auto.
      reflexivity.
      change (a :: x ++ x') with ((a :: x) ++ x') in H.
      eapply map_eq_app in H. do 2 destruct H. intuition; subst. thinker.
    Qed.

    Lemma existsEach_nil : forall cs (F : list (@sigT _ typeD) -> _) ,
      ST.heq cs (existsEach nil F) (F nil).
    Proof.
      intros. eapply ST.heq_defn. unfold existsEach; split; thinker.
      destruct v; try reflexivity. simpl in *; congruence.
    Qed.

    Lemma heq_existsEach : forall cs x (F F' : list (@sigT _ typeD) -> _) ,
      (forall G, map (@projT1 _ _) G = x -> ST.heq cs (F G) (F' G)) ->
      ST.heq cs (existsEach x F) (existsEach x F').
    Proof.
      intros. eapply ST.heq_ex. intros. apply ST.heq_defn. split; thinker;
      eapply ST.himp_star_pure_cc; eauto; specialize (H _ H0); apply ST.heq_defn in H; intuition.
    Qed.

    Lemma himp_existsEach : forall cs x (F F' : list (@sigT _ typeD) -> _) ,
      (forall G, map (@projT1 _ _) G = x -> ST.himp cs (F G) (F' G)) ->
      ST.himp cs (existsEach x F) (existsEach x F').
    Proof.
      intros. eapply ST.himp_ex. intros. thinker;
      eapply ST.himp_star_pure_cc; eauto; specialize (H _ H0); apply ST.heq_defn in H; intuition.
    Qed.

    Lemma himp_existsEach_p : forall cs x (F : list (@sigT _ typeD) -> _) F',
      (forall G, map (@projT1 _ _) G = x -> ST.himp cs (F G) F') ->
      ST.himp cs (existsEach x F) F'.
    Proof.
      intros. eapply ST.himp_ex_p. intros. eapply ST.himp_star_pure_c. intros.
      eapply H; eauto.
    Qed.

    Lemma himp_existsEach_c : forall cs x (F : list (@sigT _ typeD) -> _) F',
      (exists G, map (@projT1 _ _) G = x /\ ST.himp cs F' (F G)) ->
      ST.himp cs F' (existsEach x F).
    Proof.
      intros. eapply ST.himp_ex_c. intros. destruct H.
      exists x0. intuition. rewrite H1. eapply ST.himp_star_pure_cc; auto. reflexivity.
    Qed.

    Lemma heq_pushIn : forall P cs x (F : list (@sigT _ typeD) -> _) ,
      ST.heq cs (ST.star P (existsEach x F)) (existsEach x (fun e => ST.star P (F e))).
    Proof.
      intros. unfold existsEach; intros.
      rewrite ST.heq_star_comm. rewrite ST.heq_ex_star. eapply ST.heq_ex. intros.
      repeat rewrite ST.heq_star_assoc. eapply ST.heq_defn; split; thinker; eapply ST.himp_star_pure_cc; eauto.
      rewrite ST.heq_star_comm. reflexivity.
      rewrite ST.heq_star_comm. reflexivity.
    Qed.

    Lemma existsEach_cons : forall cs v vs P,
      ST.heq cs (existsEach (v :: vs) P)
                (ST.ex (fun x => existsEach vs (fun env => P (@existT _ _ v x :: env)))).
    Proof.
      intros. change (v :: vs) with ((v :: nil) ++ vs). rewrite existsEach_app.
      eapply ST.heq_defn. simpl. split; unfold existsEach; thinker. eapply ST.himp_ex_c.
      destruct v0; simpl in *; try congruence.
      inversion H; clear H; subst. exists (projT2 s). destruct v0; simpl in *; try congruence.
      eapply ST.himp_ex_c. exists v1. eapply ST.himp_star_pure_cc; eauto. destruct s; simpl; reflexivity.

      eapply ST.himp_ex_c. exists (existT typeD v v0 :: nil). simpl. eapply ST.himp_star_pure_cc; eauto.
      eapply ST.himp_ex_c. exists v1. eapply ST.himp_star_pure_cc; eauto. reflexivity.
    Qed.

    Lemma existsEach_rev : forall cs v F,
      ST.heq cs (existsEach v F) (existsEach (rev v) (fun e => F (rev e))).
    Proof.
      intros; eapply ST.heq_defn; split; revert F; induction v; simpl; intros;
        repeat (rewrite existsEach_nil || rewrite existsEach_cons || rewrite existsEach_app); unfold existsEach; thinker; auto.
      { apply ST.himp_ex_c. exists (rev v1). apply ST.himp_star_pure_cc. subst. rewrite map_rev. reflexivity.
        apply ST.himp_ex_c. exists (@existT _ _ a v0 :: nil). apply ST.himp_star_pure_cc. reflexivity.
        rewrite rev_app_distr. rewrite rev_involutive. reflexivity. }
      { eapply ST.himp_ex_c. destruct v1. simpl in *; congruence. simpl in *. destruct s; simpl in *.
        inversion H0; clear H0; subst. exists t. rewrite rev_app_distr. simpl. rewrite app_ass. simpl.
        apply ST.himp_ex_c. exists (rev v0). apply ST.himp_star_pure_cc. rewrite map_rev. rewrite H. apply rev_involutive.
        destruct v1; try reflexivity. simpl in *; congruence. }
    Qed.

    Lemma interp_existsEach : forall cs vs P stn st,
      ST.satisfies cs (existsEach vs P) stn st ->
      exists G, map (@projT1 _ _) G = vs /\ ST.satisfies cs (P G) stn st.
    Proof.
      intros. apply ST.satisfies_ex in H. destruct H. exists x.
      apply ST.satisfies_star in H.
      repeat match goal with
               | [ H : exists x, _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
             end.
      apply ST.satisfies_pure in H0. intuition.
      PropXTac.propxFo. eapply ST.HT.split_semp in H; eauto. subst; auto.
    Qed.

  End param.
End SepTheoryX_Ext.
