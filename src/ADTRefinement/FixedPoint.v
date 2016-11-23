Require Import Fiat.ADT Fiat.ADTNotation.
Require Export Fiat.Computation.FixComp.

Import LeastFixedPointFun.

Instance refineFun_Reflexive fDom fCod : Reflexive (@refineFun fDom fCod).
Proof.
  intro x.
  induction fDom; simpl; intros.
  reflexivity.
  simpl in x.
  apply IHfDom.
Qed.

Add Parametric Morphism fDom fCod : (@refineFun fDom fCod)
    with signature
    ((@refineFun fDom fCod) --> (@refineFun fDom fCod) ++> impl)
      as refineFun_refineFun.
Proof.
  unfold impl; intros.
  induction fDom; simpl in *; intros.
  rewrite H, H1, H0.
  reflexivity.
  specialize (IHfDom (x t) (y t) (H t) (x0 t) (y0 t)).
  firstorder.
Qed.

Add Parametric Morphism fDom fCod : (@refineFun fDom fCod)
    with signature
    ((@refineFun fDom fCod) ==> Basics.flip (@refineFun fDom fCod)
                            ==> Basics.flip impl)
      as refineFun_refineFun_flip.
Proof.
  unfold impl; intros.
  induction fDom; simpl in *; intros.
  rewrite H, H1; assumption.
  specialize (IHfDom (x t) (y t) (H t) (x0 t) (y0 t)).
  firstorder.
Qed.

Instance refineFun_Transitive fDom fCod : Transitive (@refineFun fDom fCod).
Proof.
  intros x y z H1 H2.
  rewrite H1.
  exact H2.
Qed.

Program Instance refineFun_PreOrder fDom fCod : PreOrder (@refineFun fDom fCod).

Definition refineFunEquiv
           {fDom : list Type}
           {fCod : Type}
           (old new : funType fDom fCod) :=
  refineFun old new /\ refineFun new old.

Add Parametric Morphism fDom fCod
  : (@refineFun fDom fCod)
    with signature
    (@refineFunEquiv fDom fCod) --> (@refineFunEquiv fDom fCod) ++> impl
      as refineFun_refineFunEquiv.
Proof.
  unfold impl, refineFunEquiv; intros.
  intuition.
  rewrite H2, H1.
  assumption.
Qed.

Add Parametric Morphism fDom fCod
  : (@refineFun fDom fCod)
    with signature
    (@refineFunEquiv fDom fCod --> @refineFunEquiv fDom fCod
                     --> Basics.flip impl)
      as refineFun_refineFunEquiv'.
Proof.
  unfold impl, refineFunEquiv; intros.
  intuition.
  rewrite H3, H1.
  assumption.
Qed.

Program Instance refineFunEquiv_Equivalence fDom fCod :
  Equivalence (@refineFunEquiv fDom fCod).
Obligation 1.
unfold refineFunEquiv.
intro x.
split; reflexivity.
Defined.
Obligation 2.
unfold refineFunEquiv.
intros x y H.
intuition.
Qed.
Obligation 3.
unfold refineFunEquiv.
intros x y z H1 H2.
intuition.
transitivity y; trivial.
transitivity y; trivial.
Qed.

Instance refineFun_refineFunEquiv_subrelation fDom fCod :
  subrelation (@refineFunEquiv fDom fCod) (@refineFun fDom fCod).
Proof. intros ? ? [? ?]; assumption. Qed.

Lemma length_wf' : forall A len l,
    length l < len -> Acc (fun l1 l2 : list A => length l1 < length l2) l.
Proof.
  induction len; simpl; intros;
    constructor; intros.
  contradiction (NPeano.Nat.nlt_0_r _ H).
  apply IHlen.
  Require Import Omega.
  omega.
Qed.

Lemma length_wf : forall A,
    well_founded (fun l1 l2 : list A => length l1 < length l2).
Proof.
  red; intros; eapply length_wf'; eauto.
Qed.

(* Definition funType_to_methodType
           {rep : Type} {dom : list Type} {cod : Type} :
  funType (rep :: dom) (rep * cod) -> methodType rep dom (Some cod).
Proof.
  simpl; intro f.
  intro r'.
  specialize (f r'); clear r'.
  induction dom; simpl in *.
  exact f.
  intro r'.
  exact (IHdom (f r')).
Defined.

Definition methodType_to_funType
           {rep : Type} {dom : list Type} {cod : Type} :
  methodType rep dom (Some cod) -> funType (rep :: dom) (rep * cod).
Proof.
  simpl; intro f.
  intro r'.
  specialize (f r'); clear r'.
  induction dom; simpl in *.
  exact f.
  intro r'.
  exact (IHdom (f r')).
Defined.

Lemma methodType_to_funType_id
      {rep : Type} {dom : list Type} {cod : Type}
      (f : funType (rep :: dom) (rep * cod)) :
  methodType_to_funType (funType_to_methodType f) = f.
Proof.
  unfold methodType_to_funType, funType_to_methodType.
  extensionality r.
  induction dom; simpl in f;
    extensionality x; simpl.
  reflexivity.
  exact (IHdom (fun r => f r x)).
Qed. *)

Import EqNotations.

Require Import Fiat.Common.Frame.

Inductive hetero {A : Type} {B : A -> Type} : list A -> Type :=
| hnil : hetero []
| hcons x xs : hetero xs -> B x -> hetero (x :: xs).

Ltac under_fDom :=
  match goal with
  | [ fDom : list Type |- _ ] =>
    induction fDom; simpl in *;
    [| intros;
       repeat
         match goal with
         | [ f : ?OLDREP -> ?A -> funType ?FDOM ?FCOD |- _ ] =>
           match goal with
             [ IHfDom : (OLDREP -> funType FDOM FCOD) -> _,
                        x : A |- _ ] =>
             specialize (IHfDom (fun r => f r x));
             try exact IHfDom;
             try clear f
           end
         | [ f : ?OLDREP -> ?A -> methodType' ?OLDREP ?FDOM ?FCOD |- _ ] =>
           match goal with
             [ IHfDom : (OLDREP -> methodType' OLDREP FDOM FCOD) -> _,
                        x : A |- _ ] =>
             specialize (IHfDom (fun r => f r x));
             try exact IHfDom;
             try clear f
           end
         | [ f : ?A -> funType ?FDOM ?FCOD |- _ ] =>
           match goal with
             [ IHfDom : funType FDOM FCOD -> _,
                        x : A |- _ ] =>
             specialize (IHfDom (f x));
             try exact IHfDom;
             try clear f
           end
         end ]
  end.

Definition funApply {fDom fCod} :
  funType fDom fCod -> hetero (B:=id) fDom -> Comp fCod.
Proof.
  intros.
  induction fDom; simpl in *.
  exact X.
  inversion X0.
  exact (IHfDom (X X2) X1).
Defined.

Definition dom_old_to_new {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType (oldRep :: fDom) fCod -> funType (newRep :: fDom) fCod.
Proof.
  simpl; intros f r_n.
  induction fDom; simpl in *.
  exact ({ v | forall (r_o : oldRep),
               AbsR r_o r_n -> computes_to (f r_o) v}).
  exact (fun x => IHfDom (fun r => f r x)).
Defined.

Definition cod_old_to_new {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType fDom (oldRep * fCod) -> funType fDom (newRep * fCod).
Proof.
  simpl; intros f.
  induction fDom; simpl in *.
  exact { o : newRep * fCod |
          exists p,
          computes_to f (p, snd o) /\ AbsR p (fst o)}.
  intro x.
  exact (IHfDom (f x)).
Defined.

Definition dom_new_to_old {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType (newRep :: fDom) fCod -> funType (oldRep :: fDom) fCod.
Proof.
  simpl; intros f r_o.
  induction fDom; simpl in *.
  exact ({ v | forall (r_n : newRep),
               AbsR r_o r_n /\ computes_to (f r_n) v}).
  intro x.
  exact (IHfDom (fun r => f r x)).
Defined.

Definition cod_new_to_old {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType fDom (newRep * fCod) -> funType fDom (oldRep * fCod).
Proof.
  simpl; intros f.
  induction fDom; simpl in *.
  exact { o : oldRep * fCod |
          forall r_n',
            computes_to f (r_n', snd o) -> AbsR (fst o) r_n'}.
  intro x.
  exact (IHfDom (f x)).
Defined.

Definition domcod_old_to_new {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType (oldRep :: fDom) (oldRep * fCod) ->
  funType (newRep :: fDom) (newRep * fCod) :=
  fun k => dom_old_to_new AbsR (cod_old_to_new AbsR k).

Definition domcod_new_to_old {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType (newRep :: fDom) (newRep * fCod) ->
  funType (oldRep :: fDom) (oldRep * fCod) :=
  fun k => dom_new_to_old AbsR (cod_new_to_old AbsR k).

Definition funType_join {fDom fCod} :
  Comp (funType fDom fCod) -> funType fDom fCod.
Proof.
  intros.
  induction fDom.
  exact (v <- X; v).
  intro x.
  exact (IHfDom (f <- X; ret (f x))).
Defined.

Require Import
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements.

Fixpoint refineFun_AbsR'
         {oldRep newRep}
         (fDom : list Type)
         (fCod : Type)
         (AbsR : oldRep -> newRep -> Prop)
         (fDef : funType fDom (oldRep * fCod))
         (fDef' : funType fDom (newRep * fCod))
         {struct fDom} : Prop :=
  match fDom as fDom'
        return funType fDom' (oldRep * fCod)
               -> funType fDom' (newRep * fCod) -> Prop
  with
  | List.nil =>
    fun fDef fDef' => refine (cod_old_to_new AbsR fDef) fDef'
  | List.cons T fDom' =>
    fun fDef fDef' =>
      forall (t : T), refineFun_AbsR' fDom' fCod AbsR (fDef t) (fDef' t)
  end fDef fDef'.

Definition refineFun_AbsR
           {oldRep newRep}
           (AbsR : oldRep -> newRep -> Prop)
           {fDom : list Type}
           {fCod : Type}
           (fDef : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' : funType (newRep :: fDom) (newRep * fCod)) : Prop :=
  forall r_o r_n, AbsR r_o r_n
                  -> refineFun_AbsR' fDom fCod AbsR (fDef r_o) (fDef' r_n).

Lemma refineFun_AbsR_trans
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef fDef'' : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' : funType (newRep :: fDom) (newRep * fCod)),
    refineFun fDef fDef''
    -> refineFun_AbsR AbsR fDef'' fDef'
    -> refineFun_AbsR AbsR fDef fDef'.
Proof.
  intros.
  unfold refineFun_AbsR in *.
  induction fDom; simpl in *; intros.
  { rewrite <- H0; eauto.
    unfold refine; intros; eauto.
    computes_to_inv; subst; destruct_ex; intuition.
    eapply H in H3; eauto.
  }
  apply (IHfDom (fun r => fDef r t)
                (fun r => fDef'' r t)
                (fun r => fDef' r t)); eauto.
Qed.

Lemma refineFun_AbsR'_trans
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef fDef'' : funType fDom (oldRep * fCod))
           (fDef' : funType fDom (newRep * fCod)),
    refineFun fDef fDef''
    -> refineFun_AbsR' _ _ AbsR fDef'' fDef'
    -> refineFun_AbsR' _ _ AbsR fDef fDef'.
Proof.
  intros.
  induction fDom; simpl in *; intros; eauto.
  rewrite <- H0; eauto.
  unfold refine; intros; computes_to_inv;
    destruct_ex; intuition eauto.
Qed.

Lemma refineFun_AbsR_trans'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' fDef'' : funType (newRep :: fDom) (newRep * fCod)),
    refineFun fDef'' fDef'
    -> refineFun_AbsR AbsR fDef fDef''
    -> refineFun_AbsR AbsR fDef fDef'.
Proof.
  intros.
  unfold refineFun_AbsR in *.
  induction fDom; simpl in *; intros.
  rewrite (H0 _ _ H1).
  exact (H _).
  apply (IHfDom (fun r => fDef r t)
                (fun r => fDef' r t)
                (fun r => fDef'' r t)); eauto.
Qed.

Lemma refineFun_To_refineFunAbsR
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef  : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' : funType (newRep :: fDom) (newRep * fCod)),
    refineFun (domcod_old_to_new AbsR fDef) fDef'
    <-> refineFun_AbsR AbsR fDef fDef'.
Proof.
  simpl.
  unfold refineFun_AbsR, domcod_old_to_new; split.
  - induction fDom; simpl; intros; eauto.
    + unfold refine; intros.
      eapply H in H1; computes_to_inv; subst; eauto.
    + intros;
        eapply (IHfDom (fun r => fDef r t) (fun r => fDef' r t)); eauto.
      intros; eapply H.
  - induction fDom; simpl; intros; eauto.
    + unfold refine; intros.
      computes_to_econstructor; intros.
      eapply H in H0; computes_to_inv; subst; eauto.
    + intros;
        eapply (IHfDom (fun r => fDef r t0) (fun r => fDef' r t0)); eauto.
Qed.

Lemma refineFunAbsR_domcod_old_to_new
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType (oldRep :: fDom) (oldRep * fCod)),
    refineFun_AbsR AbsR fDef (domcod_old_to_new AbsR fDef).
Proof.
  intros.
  unfold refineFun_AbsR, domcod_old_to_new.
  under_fDom.
  { unfold refine; intros.
    computes_to_inv; destruct_ex; intuition eauto; subst.
  }
  eauto.
Qed.

Definition domcod_new_to_old'
           {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop)
           (fDef' : funType (newRep :: fDom) (newRep * fCod))
  : funType (oldRep :: fDom) (oldRep * fCod) :=
  cl_sup (fun a : funType (oldRep :: fDom) (oldRep * fCod) =>
            refineFun (domcod_old_to_new AbsR a) fDef').

Lemma cod_old_to_new_monotone
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef fDef' : funType fDom (oldRep * fCod)),
    refineFun fDef fDef'
    -> refineFun (cod_old_to_new AbsR fDef) (cod_old_to_new AbsR fDef').
Proof.
  induction fDom; simpl; intros.
  -setoid_rewrite H; reflexivity.
  - simpl; eauto.
Qed.

Lemma domcod_old_to_new_monotone
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef fDef'  : funType (oldRep :: fDom) (oldRep * fCod)),
    refineFun fDef fDef'
    -> refineFun (domcod_old_to_new AbsR fDef) (domcod_old_to_new AbsR fDef').
Proof.
  induction fDom; simpl; intros.
  - unfold domcod_old_to_new; simpl.
    setoid_rewrite H; reflexivity.
  - unfold domcod_old_to_new in *.
    simpl; eapply (IHfDom (fun r => fDef r t0) (fun r => fDef' r t0)); eauto.
    simpl; eauto.
Qed.

Lemma domcod_old_to_new_resp_inf_1'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall P,
    refineFun (@domcod_old_to_new _ _ fDom fCod AbsR (cl_inf P))
              (cl_inf (fun f (* new Point *) =>
                         exists f',
                           P f'
                           /\ refineFun (@domcod_old_to_new _ _ fDom fCod AbsR f') f)).
Proof.
  intros; eapply (glb_refineFun_inf _ (fun f (* new Point *) =>
                         exists f',
                           P f'
                           /\ refineFun (@domcod_old_to_new _ _ fDom fCod AbsR f') f)).
  simpl; intros; destruct_ex; intuition subst.
  rewrite <- H1.
  eapply domcod_old_to_new_monotone.
  eapply (glb_refineFun_inf _ P); eauto.
Qed.

Lemma domcod_old_to_new_resp_inf_2'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall P,
    P (refineFun_inf P)
    -> refineFun (cl_inf (fun f (* new Point *) =>
                         exists f',
                           P f'
                           /\ refineFun (@domcod_old_to_new _ _ fDom fCod AbsR f') f))
              (@domcod_old_to_new _ _ fDom fCod AbsR (cl_inf P))
.
Proof.
  intros; eapply (glb_refineFun_inf _ (fun f (* new Point *) =>
                         exists f',
                           P f'
                           /\ refineFun (@domcod_old_to_new _ _ fDom fCod AbsR f') f)).
  simpl; intros; destruct_ex; intuition subst.
  eexists (refineFun_inf P); split; intros; eauto.
  reflexivity.
Qed.

Lemma domcod_old_to_new_resp_sup_1'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall P,
    refineFun (cl_sup (fun f (* new Point *) =>
                         exists f',
                           P f'
                           /\ refineFun f (@domcod_old_to_new _ _ fDom fCod AbsR f')))
              (@domcod_old_to_new _ _ fDom fCod AbsR (cl_sup P))
.
Proof.
  intros; eapply (lub_refineFun_sup _ (fun f (* new Point *) =>
                         exists f',
                           P f'
                           /\ refineFun f (@domcod_old_to_new _ _ fDom fCod AbsR f'))).
  simpl; intros; destruct_ex; intuition subst.
  rewrite H1.
  eapply domcod_old_to_new_monotone.
  eapply (lub_refineFun_sup _ P); eauto.
Qed.

Lemma domcod_old_to_new_resp_sup_2'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall P,
    P (refineFun_sup P)
    -> refineFun
         (@domcod_old_to_new _ _ fDom fCod AbsR (cl_sup P))
         (cl_sup (fun f (* new Point *) =>
                    exists f',
                      P f'
                      /\ refineFun f (@domcod_old_to_new _ _ fDom fCod AbsR f'))).
Proof.
  intros.
  eapply (lub_refineFun_sup _ (fun f (* new Point *) =>
                                 exists f',
                                   P f'
                           /\ refineFun f (@domcod_old_to_new _ _ fDom fCod AbsR f'))).
  eexists (refineFun_sup P); intuition.
Qed.

Lemma refineFun_AbsR_unCurry
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType fDom (oldRep * fCod))
           (fDef' : funType fDom (newRep * fCod)),
    refineFun_AbsR' _ _ AbsR fDef fDef'
    -> refineFun_AbsR' _ _ AbsR (unCurry _ fDef) (unCurry _ fDef').
  Proof.
    induction fDom; simpl.
    - intros; eauto.
    - intros.
      eapply IHfDom; eauto.
  Qed.

Lemma refineFun_AbsR_unCurry'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType fDom (oldRep * fCod))
           (fDef' : funType fDom (newRep * fCod)),
    refineFun_AbsR' _ _ AbsR (unCurry _ fDef) (unCurry _ fDef')
    -> refineFun_AbsR' _ _ AbsR fDef fDef'.
  Proof.
    induction fDom; simpl.
    - intros; eapply (H tt).
    - intros.
      eapply IHfDom; eauto.
      simpl; intros.
      eapply (H (t, t0)).
  Qed.

  (* Here's the main refinement lemma for switching the *)
  (* representation type of a fixed point! *)
Lemma refine_LeastFixedPoint_AbsR
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
      (fDef : funType (oldRep :: fDom) (oldRep * fCod)
              -> funType (oldRep :: fDom) (oldRep * fCod))
      (fDef' : funType (newRep :: fDom) (newRep * fCod)
               -> funType (newRep :: fDom) (newRep * fCod))
  : respectful_hetero
      (funType (oldRep :: fDom) (oldRep * fCod))
      (funType (newRep :: fDom) (newRep * fCod))
      (fun _ => funType (oldRep :: fDom) (oldRep * fCod))
      (fun _ => funType (newRep :: fDom) (newRep * fCod))
      (fun f f' => @refineFun_AbsR _ _ AbsR fDom fCod f f')
      (fun rec rec' f f' =>
         @refineFun_AbsR _ _ AbsR fDom fCod f f')
      fDef fDef'
    -> forall (fDef_monotone : forall rec rec',
                  refineFun rec rec'
                  -> refineFun (fDef rec) (fDef rec'))
              (fDef'_monotone : forall rec rec',
                  refineFun rec rec'
                  -> refineFun (fDef' rec) (fDef' rec')),
      refineFun_AbsR AbsR (LeastFixedPoint fDef)
                     (LeastFixedPoint fDef').
Proof.
  unfold LeastFixedPoint, respectful_hetero; intros.
  unfold refineFun_AbsR; intros;
  simpl; eapply refineFun_AbsR'_trans.
  pose proof (proj1 (Is_GreatestFixedPoint
                       (O := @funDefOps (oldRep :: fDom) (oldRep * fCod))
                       _ (fDef_monotone))).
  simpl in *; rewrite H1; reflexivity.
  eapply refineFun_AbsR_trans'; eauto;
    [ | eapply H; eapply refineFunAbsR_domcod_old_to_new ].
  pose proof (proj2 (Is_GreatestFixedPoint
                       (O := @funDefOps (newRep :: fDom) (newRep * fCod))
                       _ (fDef'_monotone))).
  rewrite <- H1.
  eapply fDef'_monotone.
  eapply (GreatestFixedPoint_ind (O := @funDefOps (newRep :: fDom) (newRep * fCod))).
  simpl.
  eapply refineFun_To_refineFunAbsR.
  eapply refineFun_AbsR_trans; eauto.
  pose proof (proj1 (Is_GreatestFixedPoint
                       (O := @funDefOps (oldRep :: fDom) (oldRep * fCod))
                       _ (fDef_monotone))).
  eapply H2.
  eapply H.
  eapply refineFun_To_refineFunAbsR.
  reflexivity.
Qed.
