Require Import
        Coq.Sets.Ensembles
        Coq.omega.Omega
        Coq.Classes.Morphisms
        Coq.Classes.SetoidTactics
        Fiat.Computation
        Fiat.Computation.SetoidMorphisms
        Coq.Logic.FunctionalExtensionality.

Record funSig :=
  { funDom : list Type;
    funCod : Type }.

Fixpoint funType
         (fDom : list Type)
         (fCod : Type)
         {struct fDom}
  : Type :=
  match fDom with
  | nil => Comp fCod
  | cons T fDom' => T -> funType fDom' fCod
  end.

Definition funDef (fSig : funSig) :=
  funType (funDom fSig) (funCod fSig).

Fixpoint refineFun
         {fDom : list Type}
         {fCod : Type}
         (fSet' fSet : funType fDom fCod)
         {struct fDom} : Prop :=
  match fDom as fDom' return
        funType fDom' fCod
        -> funType fDom' fCod
        -> Prop
  with
  | nil =>
    fun fSet' fSet => refine fSet' fSet
  | cons T fDom' =>
    fun fSet' fSet =>
      forall (t : T), refineFun (fSet' t) (fSet t)
  end fSet' fSet.

Lemma refineFun_refl
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType fDom fCod),
    refineFun fDef fDef.
Proof.
  induction fDom; simpl; intros.
  - reflexivity.
  - eauto.
Qed.

Lemma refineFun_trans
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef fDef' fDef'' : funType fDom fCod),
    refineFun fDef fDef'
    -> refineFun fDef' fDef''
    -> refineFun fDef fDef''.
Proof.
  induction fDom; simpl; intros.
  - rewrite H; eauto.
  - eauto.
Qed.

Instance PreOrder_refineFun
         {fDom : list Type}
         {fCod : Type}
  : PreOrder (@refineFun fDom fCod).
Proof.
  constructor.
  unfold Reflexive; apply refineFun_refl.
  unfold Transitive; apply refineFun_trans.
Qed.

Definition refineEquivFun
           {fDom : list Type}
           {fCod : Type}
           (fSet' fSet : funType fDom fCod)
  : Prop :=
  refineFun fSet fSet' /\ refineFun fSet' fSet.

Add Parametric Morphism fDom fCod
  : (@refineFun fDom fCod)
    with signature (refineEquivFun
                      ==> refineEquivFun
                      ==> Basics.impl)
      as refineEquiv_iff.
  unfold Basics.impl, refineEquivFun; intuition.
  rewrite H0, <- H4; eauto.
Qed.

Fixpoint FunMax
         {fDom : list Type}
         {fCod : Type}
         (fSet' fSet : funType fDom fCod)
         {struct fDom} : funType fDom fCod :=
  match fDom as fDom' return
        funType fDom' fCod
        -> funType fDom' fCod
        -> funType fDom' fCod
  with
  | nil =>
    fun fSet' fSet => @Intersection _ fSet' fSet
  | cons T fDom' =>
    fun fSet' fSet =>
      (fun (t : T) => FunMax (fSet' t) (fSet t))
  end fSet' fSet.

Fixpoint FunMin
         {fDom : list Type}
         {fCod : Type}
         (fSet' fSet : funType fDom fCod)
         {struct fDom} : funType fDom fCod :=
  match fDom as fDom' return
        funType fDom' fCod
        -> funType fDom' fCod
        -> funType fDom' fCod
  with
  | nil =>
    fun fSet' fSet => @Union _ fSet' fSet
  | cons T fDom' =>
    fun fSet' fSet =>
      (fun (t : T) => FunMin (fSet' t) (fSet t))
  end fSet' fSet.

Module LeastFixedPointFun.
  Require Import Fiat.Common.Frame.

  Instance funDefOps
           {fDom : list Type}
           {fCod : Type}
    : Fiat.Common.Frame.Lattice.Ops (funType fDom fCod) :=
    { le := refineFun;
      eq := refineEquivFun;
      max := FunMax;
      min := FunMin
    }.

  Instance PreO_refineFun
           {fDom : list Type}
           {fCod : Type}
    : PreO.t (@refineFun fDom fCod) :=
    { le_refl := refineFun_refl;
      le_trans := refineFun_trans }.

  Lemma refineFun_Proper
        {fDom : list Type}
        {fCod : Type}
    : Proper (refineEquivFun ==> refineEquivFun ==> iff)
             (@refineFun fDom fCod).
  Proof.
    unfold Proper, respectful, refineEquivFun;
      intros; intuition.
    rewrite H1, H0; eauto.
    rewrite H2, H0; eauto.
  Qed.

  Lemma refineFun_antisym
        {fDom : list Type}
        {fCod : Type}
    : forall (x y : funType fDom fCod),
      refineFun x y -> refineFun y x ->
      refineEquivFun x y.
  Proof.
    unfold refineEquivFun; intuition.
  Qed.

  Instance PO_refineFun
           {fDom : list Type}
           {fCod : Type}
    : PO.t (@refineFun fDom fCod) refineEquivFun :=
    { PreO := PreO_refineFun;
      le_proper := refineFun_Proper;
      le_antisym := refineFun_antisym}.

  Local Transparent computes_to.

  Lemma funMax_Proper
        {fDom : list Type}
        {fCod : Type}
    : Proper (@refineEquivFun
                fDom fCod
                ==> @refineEquivFun fDom fCod
                ==> @refineEquivFun fDom fCod)
             FunMax.
  Proof.
    unfold refineEquivFun, Proper, respectful; intuition.
    - induction fDom; simpl in *.
      + intros c Comp_v; destruct Comp_v.
        apply H0 in H; apply H2 in H4;
          constructor; eauto.
      + intros. eapply IHfDom; eauto.
    - induction fDom; simpl in *.
      + intros c Comp_v; destruct Comp_v.
        apply H1 in H; apply H3 in H4;
          constructor; eauto.
      + intros. eapply IHfDom; eauto.
  Qed.

  Lemma funMin_Proper
        {fDom : list Type}
        {fCod : Type}
    : Proper (@refineEquivFun
                fDom fCod
                ==> @refineEquivFun fDom fCod
                ==> @refineEquivFun fDom fCod)
             FunMin.
  Proof.
    unfold refineEquivFun, Proper, respectful; intuition.
    - induction fDom; simpl in *.
      + intros c Comp_v; destruct Comp_v.
        * constructor; apply H0; auto.
        * constructor 2; apply H2; auto.
      + intros; eapply IHfDom; eauto.
    - induction fDom; simpl in *.
      + intros c Comp_v; destruct Comp_v.
        * constructor; apply H1; auto.
        * constructor 2; apply H3; auto.
      + intros; eapply IHfDom; eauto.
  Qed.

  Lemma FunMax_ok
        {fDom : list Type}
        {fCod : Type}
    : forall l r : funType fDom fCod,
      PreO.max (le := refineFun) l r (FunMax l r).
  Proof.
    constructor.
    - induction fDom; simpl in *.
      + intros v Comp_v; destruct Comp_v; eauto.
      + eauto.
    - induction fDom; simpl in *.
      + intros v Comp_v; destruct Comp_v; eauto.
      + eauto.
    - induction fDom; simpl in *.
      + intros.
        intros v Comp_v; econstructor.
        * apply H; eauto.
        * apply H0; eauto.
      + intros; eapply IHfDom; eauto.
  Qed.

  Lemma FunMin_ok
        {fDom : list Type}
        {fCod : Type}
    : forall l r : funType fDom fCod,
      PreO.min (le := refineFun) l r (FunMin l r).
  Proof.
    constructor.
    - induction fDom; simpl in *.
      + intros v Comp_v; econstructor; eauto.
      + eauto.
    - induction fDom; simpl in *.
      + intros v Comp_v; econstructor 2; eauto.
      + eauto.
    - induction fDom; simpl in *.
      + intros.
        intros v Comp_v; destruct Comp_v.
        * apply H; eauto.
        * apply H0; eauto.
      + intros; eapply IHfDom; eauto.
  Qed.

  Instance Lattice_funDef
           {fDom : list Type}
           {fCod : Type}
    : Lattice.t _ (@funDefOps fDom fCod) :=
    { PO := PO_refineFun;
      max_proper := funMax_Proper;
      max_ok := FunMax_ok;
      min_proper := funMin_Proper;
      min_ok := FunMin_ok
    }.

  Fixpoint unCurry_funType
           (fDom : list Type)
    : Type :=
    match fDom with
    | nil => unit
    | cons T fDom' => prod T (unCurry_funType fDom')
    end.

  Fixpoint unCurry
           (fDom : list Type)
           {fCod : Type}
           (f : funType fDom fCod)
           {struct fDom}
    : funType (cons (unCurry_funType fDom) nil) fCod :=
    match fDom return
          funType fDom fCod
          -> funType (cons (unCurry_funType fDom) nil) fCod
    with
    | nil => fun f _ => f
    | cons T fDom' => fun f t => unCurry fDom' (f (fst t)) (snd t)
    end f.

  Fixpoint Curry
           (fDom : list Type)
           {fCod : Type}
           (f : funType (cons (unCurry_funType fDom) nil) fCod)
           {struct fDom}
    : funType fDom fCod :=
    match fDom return
          funType (cons (unCurry_funType fDom) nil) fCod
          -> funType fDom fCod
    with
    | nil => fun f => f tt
    | cons T fDom' => fun f t => Curry _ (fun t' => f (t, t'))
    end f.

  Lemma refineFunEquiv_Curry
        (fDom : list Type)
        {fCod : Type}
    : forall (f : funType (cons (unCurry_funType fDom) nil) fCod),
      refineEquivFun f (unCurry _ (Curry _ f)).
  Proof.
    induction fDom; simpl.
    - split; simpl; intros; destruct t; apply PreOrder_Reflexive.
    - simpl in *; split; simpl; intros.
      + destruct t; simpl in *.
        eapply (IHfDom (fun u => f (a0, u))).
      + destruct t; simpl in *.
        eapply (IHfDom (fun u => f (a0, u))).
  Qed.

  Lemma refineFunEquiv_unCurry
        (fDom : list Type)
        {fCod : Type}
    : forall (f : funType fDom fCod),
      refineEquivFun f (Curry _ (unCurry _ f)).
  Proof.
    induction fDom; simpl.
    - split; simpl; intros; apply PreOrder_Reflexive.
    - simpl in *; split; simpl; intros.
      + eapply (IHfDom (f t)).
      + eapply (IHfDom (f t)).
  Qed.

  Lemma refineFun_Curry'
        (fDom : list Type)
        {fCod : Type}
    : forall (f f' : funType (cons (unCurry_funType fDom) nil) fCod),
      refineFun f f'
      -> refineFun (Curry _ f) (Curry _ f').
  Proof.
    induction fDom; simpl.
    - intros; simpl in *; eauto.
    - simpl in *; intros.
      + eapply IHfDom; intros; eauto.
  Qed.

  Lemma refineFunEquiv_Curry'
        (fDom : list Type)
        {fCod : Type}
    : forall (f f' : funType (cons (unCurry_funType fDom) nil) fCod),
      refineEquivFun f f'
      -> refineEquivFun (Curry _ f) (Curry _ f').
  Proof.
    induction fDom; simpl.
    - split; intros; destruct H; simpl in *; eauto.
    - split; destruct H; simpl in *; intros.
      + eapply IHfDom; split; intros; eauto.
        * simpl in *; intros; eauto.
        * simpl in *; intros; eauto.
      + eapply IHfDom; split; intros; eauto.
        * simpl in *; intros; eauto.
        * simpl in *; intros; eauto.
  Qed.

  Lemma refineFunEquiv_unCurry'
        (fDom : list Type)
        {fCod : Type}
    : forall (f f' : funType fDom fCod),
      refineEquivFun f f'
      -> refineEquivFun (unCurry _ f) (unCurry _ f').
  Proof.
    induction fDom; simpl.
    - split; intros; destruct H; simpl in *; eauto.
    - split; destruct H; simpl in *; intros.
      + eapply IHfDom; split; intros; eauto.
      + eapply IHfDom; split; intros; eauto.
  Qed.

  Lemma refineFun_unCurry
        (fDom : list Type)
        {fCod : Type}
    : forall (f f' : funType fDom fCod),
      refineFun f f'
      -> refineFun (unCurry _ f) (unCurry _ f').
  Proof.
    induction fDom; simpl.
    - intros; eauto.
    - intros.
      eapply IHfDom; eauto.
  Qed.

  Lemma refineFun_unCurry'
        (fDom : list Type)
        {fCod : Type}
    : forall (f f' : funType fDom fCod),
      refineFun (unCurry _ f) (unCurry _ f')
      -> refineFun f f'.
  Proof.
    induction fDom; simpl.
    - intros; eapply (H tt).
    - intros.
      eapply IHfDom; eauto.
      simpl; intros.
      eapply (H (t, t0)).
  Qed.

  Fixpoint refineFun_lift
           (fDom : list Type)
           {fCod : Type}
           {struct fDom}
    : ((funType fDom fCod -> Prop) -> Prop) -> funType fDom fCod :=
    match fDom return
          ((funType fDom fCod -> Prop) -> Prop)
          -> funType fDom fCod with
    | nil => fun LFP_P v => (LFP_P (fun cv => computes_to cv v))
    | cons T fDom' =>
      fun LFP_P =>
        fun (t : T) => refineFun_lift fDom' (fun cv => LFP_P (fun cv' => cv (cv' t)))
    end.

  Definition refineFun_sup
             {fDom : list Type}
             {fCod : Type}
             (f : funType fDom fCod -> Prop)
    : funType fDom fCod :=
    refineFun_lift fDom (fun z => (forall s, f s -> z s)).

  Lemma refineEquivFun_lift
        {fDom : list Type}
        {fCod : Type}
    : forall (f : (funType fDom fCod -> Prop) -> Prop),
      refineEquivFun
        (refineFun_lift fDom f)
        (Curry _ (refineFun_lift _ (fun p : funType (cons (unCurry_funType fDom) nil) fCod -> Prop => f (fun f' => p (unCurry _ f' ))))).
  Proof.
    induction fDom; simpl.
    - intros; split; reflexivity.
    - simpl; split; simpl; intros.
      destruct (IHfDom (fun f' => f (fun a' => f' (a' t)))); simpl in *.
      eapply H.
      destruct (IHfDom (fun f' => f (fun a' => f' (a' t)))); simpl in *.
      eapply H0.
  Qed.

  Instance refineFun_Proper'
           {fDom : list Type}
           {fCod : Type}
    : Proper (refineEquivFun ==> refineEquivFun ==> Basics.flip Basics.impl)
             (@refineFun fDom fCod).
  Proof.
    unfold Proper, respectful, refineEquivFun, Basics.flip,
    Basics.impl; intros; simpl; intuition.
    rewrite H3, H1; eauto.
  Qed.

  Instance refineFun_Proper''
           {fDom : list Type}
           {fCod : Type}
           a
    : Proper (refineEquivFun
                ==> Basics.flip Basics.impl)
             (@refineFun fDom fCod a).
  Proof.
    unfold Proper, respectful, refineEquivFun, Basics.flip,
    Basics.impl; intros; simpl; intuition.
    rewrite H0; eauto.
  Qed.

  Lemma lub_refineFun_sup
        (fDom : list Type)
        {fCod : Type}
        (f : funType fDom fCod -> Prop)
    : lub f (refineFun_sup f).
  Proof.
    unfold refineFun_sup.
    unfold lub; split.
    - simpl; intros.
      rewrite refineEquivFun_lift; simpl.
      etransitivity.
      eapply refineFunEquiv_unCurry.
      eapply refineFun_Curry'.
      simpl; unfold refine, computes_to; intros; eauto.
    - simpl; intros.
      etransitivity; [ eapply refineEquivFun_lift |
                       eapply refineFun_unCurry' ].
      simpl; intros.
      etransitivity.
      eapply (proj1 (refineFunEquiv_Curry  _ _)).
      simpl.
      unfold refine, computes_to; intros.
      eapply H in H1.
      eapply (refineFun_unCurry _ _ _ H1); eauto.
  Qed.

  Definition refineFun_inf
             {fDom : list Type}
             {fCod : Type}
             (f : funType fDom fCod -> Prop)
    : funType fDom fCod :=
    refineFun_lift fDom (fun z => exists s, f s /\ z s).

  Definition glb_refineFun_inf
             (fDom : list Type)
             {fCod : Type}
             (f : funType fDom fCod -> Prop)
    : glb f (refineFun_inf f).
  Proof.
    unfold refineFun_inf.
    unfold glb; split.
    - simpl; intros.
      etransitivity; [ eapply refineEquivFun_lift | ].
      etransitivity; [eapply refineFun_Curry' | ].
      simpl; unfold refine, computes_to.
      intros; eauto.
      eapply refineFunEquiv_unCurry.
    - simpl; intros.
      etransitivity; [ | eapply refineEquivFun_lift ].
      eapply refineFun_unCurry'.
      simpl; intros.
      unfold refine, computes_to; intros.
      pose proof (proj2 (refineFunEquiv_Curry _ _) t _ H0).
      simpl in H1; unfold computes_to in H1; destruct H1;
        intuition.
      apply H in H2.
      eapply refineFun_unCurry in H2; apply H2; eauto.
  Qed.

  Instance CompleteLattice_funDef
           {fDom : list Type}
           {fCod : Type}
    :  CompleteLattice (O := @funDefOps fDom fCod) :=
    { cl_sup := refineFun_sup;
      cl_inf := refineFun_inf
    }.
  Proof.
    eapply glb_refineFun_inf.
    eapply lub_refineFun_sup.
  Defined.

  (* The use of refineFun as the relation on our lattice makes  *)
  (* this definition counterintuitive: the 'standard' definition *)
  (* of least fixed point of f as the intersection of all f-closed *)
  (* sets, is in fact, the supremum (defined above as the intersection *)
  (* operator of the postfixed sets (as refineFun is pointwise *)
  (* superset relation. *)

  Definition LeastFixedPoint
             {fDom : list Type}
             {fCod : Type}
             (fDef : funType fDom fCod -> funType fDom fCod)
    : funType fDom fCod :=
    (cl_sup (postfixed_point fDef)).

  (* [unroll_LeastFixedPoint] is for unrolling one layer of *)
  (* recursion in an assumption about the result of a Fixpoint *)
  (* computation. *)

  Lemma unroll_LeastFixedPoint
        {fDom : list Type}
        {fCod : Type}
        (fDef : funType fDom fCod -> funType fDom fCod)
        (fDef_monotone : monotonic_function fDef)
    : refineFun (fDef (LeastFixedPoint fDef)) (LeastFixedPoint fDef).
  Proof.
    eapply (Is_GreatestFixedPoint fDef fDef_monotone).
  Qed.

  (* [unroll_LeastFixedPoint'] is for unrolling one layer of *)
  (* recursion in the conclusion about a Fixpoint computation. *)

  Lemma unroll_LeastFixedPoint'
        {fDom : list Type}
        {fCod : Type}
        (fDef : funType fDom fCod -> funType fDom fCod)
        (fDef_monotone : monotonic_function fDef)
    : refineFun (LeastFixedPoint fDef) (fDef (LeastFixedPoint fDef)).
  Proof.
    eapply (Is_GreatestFixedPoint fDef fDef_monotone).
  Qed.

  Lemma refine_LeastFixedPoint
        {fDom : list Type}
        {fCod : Type}
        (fDef fDef' : funType fDom fCod -> funType fDom fCod)
    : respectful (@refineFun fDom fCod)
                 (@refineFun fDom fCod)
                 fDef fDef'
      ->
      forall (fDef_monotone : forall rec rec',
                 refineFun rec rec'
                 -> refineFun (fDef rec) (fDef rec'))
             (fDef'_monotone : forall rec rec',
                 refineFun rec rec'
                 -> refineFun (fDef' rec) (fDef' rec')),
        refineFun (LeastFixedPoint fDef)
                  (LeastFixedPoint fDef').
  Proof.
    unfold LeastFixedPoint, respectful; intros.
    destruct (sup_lub (postfixed_point fDef)) as [? ?];
      destruct (sup_lub (postfixed_point fDef')) as [? ?];
      simpl in *.
    etransitivity.
    - pose proof (proj1 (Is_GreatestFixedPoint (O := @funDefOps fDom fCod) _ (fDef_monotone))); etransitivity.
      apply H4.
      eapply H; reflexivity.
    - eapply (H2 (fDef' (refineFun_sup (postfixed_point fDef)))).
      eapply fDef'_monotone.
      etransitivity.
      pose proof (proj1 (Is_GreatestFixedPoint (O := @funDefOps fDom fCod) _ (fDef_monotone))); eapply H4.
      eapply H; reflexivity.
  Qed.

  Lemma LeastFixedPoint_ind
        {fDom : list Type}
        {fCod : Type}
        (fDef : funType fDom fCod -> funType fDom fCod)
        (Inv Post : funType fDom fCod)
    : refineFun Inv (fDef Inv)
      -> (refineFun Post Inv)
      -> refineFun Post (LeastFixedPoint fDef).
  Proof.
    intros; rewrite H0; simpl in *.
    destruct (sup_lub (postfixed_point fDef)) as [? ?].
    simpl in H1; eapply H1.
    eapply H.
  Qed.

  Lemma GreatestFixedPoint_ind
        {fDom : list Type}
        {fCod : Type}
        (fDef : funType fDom fCod -> funType fDom fCod)
        (Inv Post : funType fDom fCod)
    : refineFun (fDef Inv) Inv
      -> (refineFun Inv Post)
      -> refineFun (cl_inf (prefixed_point fDef)) Post.
  Proof.
    intros; rewrite <- H0; simpl in *.
    destruct (inf_glb (prefixed_point fDef)) as [? ?].
    simpl in H1; eapply H1.
    eapply H.
  Qed.

  Fixpoint cfunType
           (fDom : list Type)
           (fCod : Type)
           {struct fDom}
    : Type :=
    match fDom with
    | nil => fCod
    | cons T fDom' => T -> cfunType fDom' fCod
    end.

  Fixpoint Lift_cfunType
           (fDom : list Type)
           (fCod : Type)
           (fDef : cfunType fDom fCod)
           {struct fDom}
    : funType fDom fCod :=
    match fDom return cfunType fDom fCod
                      -> funType fDom fCod with
    | nil => fun f => ret f
    | cons T fDom' => fun f' (t : T) => Lift_cfunType fDom' fCod (f' t)
    end fDef.

  Lemma Finish_refining_LeastFixedPoint
        {fDom : list Type}
        {recT fCod : Type}
        {P : recT -> recT -> Prop}
        (wf_P : well_founded P)
        (fDef : funType (recT :: fDom) fCod -> funType (recT :: fDom) fCod)
        (fDef_monotone : forall rec rec',
            refineFun rec rec'
            -> refineFun (fDef rec) (fDef rec'))
        (fDef' : forall r,
            (forall r', P r' r -> cfunType fDom fCod)
            -> cfunType fDom fCod)
    : (forall r,
          respectful_hetero (funType (recT :: fDom) fCod)
                            (forall r', P r' r -> cfunType fDom fCod)
                            (fun _ => funType fDom fCod)
                            (fun _ => cfunType fDom fCod)
                            (fun f f' => forall r' wf_r,
                                 @refineFun fDom fCod (f r') ((Lift_cfunType _ _ (f' r' wf_r))))
                            (fun rec rec' f f' =>
                               @refineFun fDom fCod f
                                          (Lift_cfunType _ _ f'))
                            (fun rec => fDef rec r) (fDef' r))
      ->
      refineFun (LeastFixedPoint fDef )
                (Lift_cfunType (recT :: fDom) fCod (Fix wf_P _ fDef' )).
  Proof.
    unfold LeastFixedPoint, respectful_hetero; intros.
    simpl.
    simpl in H.
    intros; pattern t; eapply (well_founded_ind wf_P).
    simpl; intros; rewrite Fix_eq.
    pose proof (proj1 (Is_GreatestFixedPoint (O := @funDefOps (recT :: fDom) fCod) _ (fDef_monotone))); etransitivity.
    eapply H1; eauto.
    eapply H; eauto.
    intros; f_equal.
    repeat (eapply functional_extensionality_dep; intros); eauto.
  Qed.

  Definition FibonacciSpec
    : funType ((nat : Type) :: @nil Type)%list nat :=
    LeastFixedPoint (fDom := (nat : Type) :: @nil Type)%list
                    (fun rec (n : nat) =>
                       match n with
                       | 0 => { x | x < 1}
                       | 1 => ret 1
                       | S (S n') =>
                         n1 <- rec n';
                           n2 <- rec (S n');
                           ret (n1 + n2)
                       end).

  Lemma refine_match_nat {A}
        {P : nat -> nat -> Prop}
        {Q : forall n,  (forall n', P n' n -> A) -> Prop}
    : forall (cO : Comp A) cS n cO'
             cS'
             (y : forall n', P n' n -> A),
      (refine cO (ret cO'))
      -> (forall n (y : forall n', P n' (S n) -> A),
             Q (S n) y
             -> refine (cS n) (ret (cS' n y)))
      ->
      Q n y
      -> refine (match n with
                 | 0 => cO
                 | S n' => cS n'
                 end)
                (ret (match n return
                            (forall n', P n' n -> A)
                            -> A
                      with
                      | 0 => fun _ => cO'
                      | S n' => fun y => cS' n' y
                      end y)).
  Proof.
    destruct n; eauto.
  Qed.

  Require Import Fiat.Common.

  Ltac solve_rec_obligation x solveTac idm :=
    lazymatch goal with
    | H : forall r' (wf_r : @?P r'), refine (x r') _
                                     |- context [x ?r] =>
      let idm' := fresh idm in
      let wf_sub' := fresh in
      let wf_subP' := (eval pattern r in (P r)) in
      let wf_subP := match wf_subP' with ?P' _ => constr:(P') end in
      assert (forall r'', wf_subP r'') as wf_sub';
      [clear; abstract solveTac using idm'
      | clear wf_sub' ]
    end.

  Definition FibonacciImpl'
    : {Impl : _ & refineFun FibonacciSpec (Lift_cfunType _ _ Impl)}.
  Proof.
    eexists.
    etransitivity.
    - eapply Finish_refining_LeastFixedPoint with (wf_P := Wf_nat.lt_wf);
        simpl; intros.
      + destruct t; try reflexivity.
        destruct t; try reflexivity.
        repeat setoid_rewrite H; reflexivity.
      + unfold respectful_hetero; simpl; intros.
        revert H.
        eapply (@refine_match_nat
                  _ lt
                  (fun r y => forall (r' : nat) (wf_r : r' < r), refine (x r') (ret (y r' wf_r))) _ _ r _ _ y).
        * refine pick val 0; auto with arith; reflexivity.
        * intros; simpl in *.
          revert H.
          eapply (@refine_match_nat _ (fun n' n => n' < S n)
                                    (fun r y => forall (r' : nat) (wf_r : r' < S r), refine (x r') (ret (y r' wf_r))) _ _ n _ _ y0).
          reflexivity.
          intros; subst; set_evars.
          simpl in *.

          (* Having to provide new, unique identifiers is not ideal. *)
          (* Have to go to ML for a better solution. *)
          solve_rec_obligation x ltac:(intros; omega) foo;
            rewrite (H _ (foo _)); simplify with monad laws.

          solve_rec_obligation x ltac:(intros; omega) foo2;
            rewrite (H _ (foo2 _)); simplify with monad laws.
          subst H0; higher_order_reflexivity.
    - simpl; intros; higher_order_reflexivity.
  Defined.

  Definition FibonacciImpl :=
    Eval simpl in (projT1 FibonacciImpl').

  Print FibonacciImpl.
End LeastFixedPointFun.
