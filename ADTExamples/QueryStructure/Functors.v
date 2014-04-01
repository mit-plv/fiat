Require Import FJ_tactics.
Require Import List.
Require Import FunctionalExtensionality.

Section Folds.

  (* ============================================== *)
  (* ALGEBRAS AND FOLDS                             *)
  (* ============================================== *)

  (* Ordinary Algebra *)
  Definition Algebra (F: Set -> Set) (A : Set) :=
    F A -> A.

  (* Mixin Algebra *)
  Definition Mixin (T: Set) (F: Set -> Set) (A : Set) :=
    (T -> A) -> F T -> A.

  (* Mendler Algebra *)
  Definition MAlgebra (F: Set -> Set) (A : Set) :=
    forall (R : Set), Mixin R F A.

   Definition Fix (F : Set -> Set) : Set :=
    forall (A : Set), MAlgebra F A -> A.

  Definition mfold {F : Set -> Set} : forall (A : Set)
    (f : MAlgebra F A), Fix F -> A:= fun A f e => e A f.

  Definition in_t {F} : F (Fix F) -> Fix F :=
    fun F_e A f => f _ (mfold _ f) F_e.

  Definition fold_ {F : Set -> Set} {functor : Functor F} :
    forall (A : Set) (f : Algebra F A), Fix F -> A :=
      fun A f e => mfold _ (fun r rec fa => f (fmap rec fa)) e.

  Definition out_t {F : Set -> Set} {fun_F : Functor F} : Fix F -> F (Fix F) :=
    @fold_ F fun_F _ (fmap in_t).

  Fixpoint boundedFix {A: Set}
    {Exp: Set -> Set}
    {fun_F: Functor Exp}
    (n : nat)
    (fM: Mixin (Fix Exp) Exp A)
    (default: A)
    (e: Fix Exp): A :=
    match n with
      | 0   => default
      | S n => fM (boundedFix n fM default) (out_t e)
    end.

    (* Indexed Algebra *)
  Definition iAlgebra {I : Type} (F : (I -> Prop) -> I -> Prop) (A : I -> Prop) :=
    forall i, F A i -> A i.

    (* Indexed Mendler Algebra *)
  Definition iMAlgebra {I : Type} (F : (I -> Prop) -> I -> Prop) (A : I -> Prop) :=
    forall i (R : I -> Prop), (forall i, R i -> A i) -> F R i -> A i.

  Definition iFix {I : Type} (F : (I -> Prop) -> I -> Prop) (i : I) : Prop :=
    forall (A : I -> Prop), iMAlgebra F A -> A i.

  Definition imfold {I : Type} (F : (I -> Prop) -> I -> Prop) :
    forall (A : I -> Prop) (f : iMAlgebra F A) (i : I),
      iFix F i -> A i := fun A f i e => e A f.

  Class iFunctor {I : Type} (F : (I -> Prop) -> I -> Prop) :=
    {ifmap :
      forall {A B : I -> Prop} i (f : forall i, A i -> B i), F A i -> F B i;
      ifmap_fusion :
        forall (A B C: I -> Prop) i (f : forall i, A i -> B i) (g : forall i, B i -> C i) (a : F A i),
          ifmap i g (ifmap i f a) = ifmap i (fun i e => g _ (f i e)) a;
      ifmap_id :
        forall (A : I -> Prop) i (a : F A i),
          ifmap i (fun _ => id) a = a
    }.

  Definition in_ti {I : Type} {F} : forall i : I, F (iFix F) i -> iFix F i :=
    fun i F_e A f => f _ _ (imfold _ _ f) F_e.

  Definition ifold_ {I : Type} (F : (I -> Prop) -> I -> Prop) {iFun_F : iFunctor F} :
    forall (A : I -> Prop) (f : iAlgebra F A) (i : I),
      iFix F i -> A i := fun A f i e => imfold _ _ (fun i' r rec fa => f i' (ifmap i' rec fa)) i e.

  Definition out_ti {I : Type} {F} {fun_F : iFunctor F} : forall i : I, iFix F i -> F (iFix F) i :=
    @ifold_ I F fun_F _ (fun i => ifmap i in_ti).

  (* Universal Property of Mendler Folds *)

  Lemma Universal_Property (F : Set -> Set) (A : Set)
    (f : MAlgebra F A) :
      forall (h : Fix F -> A),
        h = mfold _ f -> forall e, h (in_t e) = f _ h e.
  Proof.
    intros; rewrite H. unfold in_t. unfold mfold.
    reflexivity.
  Qed.

  Class Universal_Property' {F} {Fun_F : Functor F} (e : Fix F) :=
    {E_UP' : forall (A : Set) (f : MAlgebra F A)
      (h : Fix F -> A),
      (forall e, h (in_t e) = f _ h e) ->
      h e = mfold _ f e}.

  Lemma Fix_id F {fun_F : Functor F} e {UP' : Universal_Property' e} :
    mfold _ (fun _ rec x => in_t (fmap rec x)) e = e.
  Proof.
    intros; apply sym_eq.
    fold (id e); unfold id at 2; apply (E_UP'); intros.
    unfold id.
    unfold in_t.
    eapply (@functional_extensionality_dep Set).
    intros; eapply @functional_extensionality_dep; intros.
    rewrite fmap_id.
    reflexivity.
  Defined.

  Definition MAlg_to_Alg {F : Set -> Set} {A : Set} :
    MAlgebra F A -> Algebra F A := fun MAlg f => MAlg A id f.

  (* Universal Property of regular folds. *)

  Lemma Universal_Property_fold (F : Set -> Set) {fun_F : Functor F} (B : Set)
    (f : Algebra F B) : forall (h : Fix F -> B), h = fold_ _ f ->
      forall e, h (in_t e) = f (fmap h e).
    intros; rewrite H; reflexivity.
  Qed.

  Class Universal_Property'_fold {F} {fun_F : Functor F} (e : Fix F) :=
    {E_fUP' : forall (B : Set) (f : Algebra F B) (h : Fix F -> B),
      (forall e, h (in_t e) = f (fmap h e)) ->
      h e = fold_ _ f e
    }.

  Lemma Fix_id_fold F {fun_F : Functor F} e {UP' : Universal_Property'_fold e} :
    fold_ _ (@in_t F) e = e.
    intros; apply sym_eq.
    fold (id e); unfold id at 2; apply (E_fUP'); intros.
    rewrite fmap_id.
    unfold id.
    reflexivity.
  Qed.

  Lemma Fusion F {fun_F : Functor F} e {e_UP' : Universal_Property'_fold e} :
    forall (A B : Set) (h : A -> B) (f : Algebra F A) (g : Algebra F B),
      (forall a, h (f a) = g (fmap h a)) ->
      (fun e' => h (fold_ _ f e')) e = fold_ _ g e.
    intros; eapply E_fUP'; try eassumption; intros.
    rewrite (Universal_Property_fold F _ f _ (refl_equal _)).
    rewrite H.
    rewrite fmap_fusion; reflexivity.
  Qed.

  Lemma in_out_inverse : forall (F : Set -> Set) (Fun_F : Functor F) (e : Fix F)
    {fUP' : Universal_Property'_fold e},
    in_t (out_t e) = e.
    intros.
    rewrite <- (@Fix_id_fold _ _ e fUP') at -1.
    eapply E_fUP' with (h := fun e => in_t (out_t e)).
    intro.
    cut (out_t (in_t e0) = fmap (fun e1 => in_t (out_t e1)) e0); intros.
    rewrite H; reflexivity.
    unfold out_t.
    rewrite Universal_Property with (f := (fun (R : Set) (rec : R -> F (Fix F)) (fp : F R) =>
      fmap (fun r : R => in_t (rec r)) fp)); eauto.
    unfold fold_; unfold mfold.
    eapply functional_extensionality; intro.
    cut ((fun (r : Set) (rec : r -> F (Fix F)) (fa : F r) =>
      fmap in_t (fmap rec fa)) =
      fun (R : Set) (rec : R -> F (Fix F)) (fp : F R) =>
      fmap (fun r : R => in_t (rec r)) fp).
    intro; rewrite H; reflexivity.
    eapply (@functional_extensionality_dep Set); intro.
    eapply functional_extensionality_dep; intro.
    eapply functional_extensionality_dep; intro.
    rewrite fmap_fusion; reflexivity.
  Qed.

  Definition in_t_UP' : forall (F : Set -> Set)
    (Fun_F : Functor F),
    F (sig (@Universal_Property'_fold F Fun_F)) ->
    sig (@Universal_Property'_fold F Fun_F).
    intros F Fun_F e.
    intros; constructor 1 with (x := in_t (fmap (@proj1_sig _ _) e)).
    constructor; intros.
    rewrite H.
    unfold fold_, mfold.
    unfold in_t.
    repeat rewrite fmap_fusion.
    assert ((fun e0 : sig Universal_Property'_fold => h (proj1_sig e0)) =
      (fun e0 : sig Universal_Property'_fold =>
         mfold B (fun (r : Set) (rec : r -> B) (fa : F r) => f (fmap rec fa))
           (proj1_sig e0))) by
    (eapply @functional_extensionality_dep; intros e'; destruct e' as [e' e'_UP'];
      simpl; eapply E_fUP'; eauto).
    rewrite H0; reflexivity.
  Defined.

  Definition out_t_UP' :
    forall (F : Set -> Set)
      (Fun_F : Functor F)
      (e : Fix F),
      F (sig (@Universal_Property'_fold F Fun_F)).
    intros.
    eapply fold_; try assumption.
    unfold Algebra; intros.
    eapply fmap.
    apply in_t_UP'.
    assumption.
  Defined.

  Lemma out_in_inverse : forall (F : Set -> Set)
    (Fun_F : Functor F)
    (e : F (sig (@Universal_Property'_fold F Fun_F))),
    out_t (in_t (fmap (@proj1_sig _ _) e)) = fmap (@proj1_sig _ _) e.
    intros.
    unfold out_t.
    erewrite Universal_Property_fold; try reflexivity.
    rewrite fmap_fusion.
    rewrite fmap_fusion.
    assert ((fun e0 : sig Universal_Property'_fold =>
      in_t (fold_ (F (Fix F)) (fmap in_t) (proj1_sig e0))) =
    @proj1_sig _ _) by
    (eapply functional_extensionality; intros;
      fold (out_t (proj1_sig x));
        rewrite in_out_inverse; destruct x; simpl; eauto).
    rewrite H; reflexivity.
  Qed.

  Lemma in_t_UP'_inject : forall (F : Set -> Set)
    (Fun_F : Functor F)
    (e e' : F (sig (@Universal_Property'_fold F Fun_F))),
    in_t (fmap (@proj1_sig _ _) e) = in_t (fmap (@proj1_sig _ _) e') ->
    fmap (@proj1_sig _ _) e = fmap (@proj1_sig _ _) e'.
    intros; apply (f_equal out_t) in H;
      repeat rewrite out_in_inverse in H; eauto.
  Qed.

  Lemma in_out_UP'_inverse : forall (H : Set -> Set)
    (Fun_H : Functor H)
    (h : Fix H),
    Universal_Property'_fold h ->
    proj1_sig (in_t_UP' H Fun_H (out_t_UP' H Fun_H h)) = h.
    intros; simpl.
    assert ((fmap (@proj1_sig _ _) (out_t_UP' H Fun_H h)) = out_t h).
    unfold out_t.
    eapply E_fUP' with (h0 := fun e => fmap (@proj1_sig _ _) (out_t_UP' H Fun_H e)).
    intros.
    rewrite fmap_fusion.
    assert (out_t_UP' H Fun_H (in_t e) =
      fmap (fun e => in_t_UP' _ _ (out_t_UP' _ _ e)) e).
    unfold out_t_UP' at 1.
    erewrite Universal_Property_fold with
      (f := (fun H2 : H (H (sig Universal_Property'_fold)) =>
        fmap (in_t_UP' H Fun_H) H2)) (fun_F := Fun_H); eauto.
    rewrite fmap_fusion; reflexivity.
    rewrite H1; rewrite fmap_fusion; simpl; reflexivity.
    rewrite H1.
    rewrite in_out_inverse; unfold mfold; eauto.
  Qed.

  Lemma out_in_fmap : forall (F : Set -> Set)
    (Fun_F : Functor F)
    (e : F (Fix F)),
    out_t_UP' F _ (in_t e) =
    fmap (fun e => in_t_UP' _ _ (out_t_UP' _ _ e)) e.
    intros; unfold out_t_UP' at 1.
    erewrite Universal_Property_fold with
    (f := (fun H2 : F (F (sig Universal_Property'_fold)) =>
      fmap (in_t_UP' F Fun_F) H2)) (fun_F := Fun_F); eauto.
    rewrite fmap_fusion; reflexivity.
  Qed.

  Definition UP'_P {F : Set -> Set} {Fun_F : Functor F}
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop) (e : Fix F) :=
    sigT (P e).

  Definition UP'_P2 {F F' : Set -> Set}
    {Fun_F : Functor F} {Fun_F' : Functor F'}
    (P : forall e : (Fix F) * (Fix F'),
      Universal_Property'_fold (fst e) /\ Universal_Property'_fold (snd e) -> Prop)
    (e : (Fix F) * (Fix F')) := sig (P e).

  Definition UP'_SP {F : Set -> Set} {Fun_F : Functor F}
    (SP : forall e : Fix F, Universal_Property'_fold e -> Set)
    (e : Fix F) : Set := sigT (SP e).

  Definition UP'_F (F : Set -> Set) {Fun_F : Functor F} :=
    sig (Universal_Property'_fold (F := F)).

  Fixpoint boundedFix_UP {A: Set}
    {Exp: Set -> Set}
    {fun_F: Functor Exp}
    (n : nat)
    (fM: Mixin (UP'_F Exp) Exp A)
    (default: A)
    (e: UP'_F Exp): A :=
    match n with
      | 0   => default
      | S n => fM (boundedFix_UP n fM default) (out_t_UP' _ _ (proj1_sig e))
    end.

  Lemma bF_UP_in_out : forall {A: Set}
    {Exp: Set -> Set}
    {fun_F: Functor Exp}
    (n : nat)
    (fM: Mixin (UP'_F Exp) Exp A)
    (default: A)
    (e: Fix Exp)
    (e_UP' : Universal_Property'_fold e),
    boundedFix_UP n fM default (in_t_UP' _ _ (out_t_UP' _ _ e)) =
    boundedFix_UP n fM default (exist _ e e_UP').
  Proof.
    induction n; simpl; intros; eauto.
    generalize in_out_UP'_inverse as H0; intro; simpl in H0; rewrite H0; auto.
  Qed.

  Lemma out_in_inverse_UP'_P : forall (F : Set -> Set)
    (Fun_F : Functor F)
    (P : forall e : Fix F, Universal_Property'_fold e -> Prop)
    (e : F (sig (UP'_P P))),
    out_t (in_t (fmap (@proj1_sig _ _) e)) = fmap (@proj1_sig _ _) e.
    intros.
    unfold out_t.
    erewrite Universal_Property_fold; try reflexivity.
    rewrite fmap_fusion.
    rewrite fmap_fusion.
    assert ((fun e0 : sig (UP'_P P) =>
      in_t (fold_ (F (Fix F)) (fmap in_t) (proj1_sig e0))) =
    @proj1_sig _ _) by
    (eapply functional_extensionality; intros;
      fold (out_t (proj1_sig x));
        rewrite in_out_inverse; destruct x as [x [UP_x P_x]]; simpl; eauto).
    rewrite H; reflexivity.
  Qed.

  (* ============================================== *)
  (* FUNCTOR COMPOSITION                            *)
  (* ============================================== *)

  Definition inj_Functor {F G : Set -> Set} {A : Set} : Set := sum (F A) (G A).

  Notation "A :+: B"  := (@inj_Functor A B) (at level 80, right associativity).

  Global Instance Functor_Plus G H {fun_G : Functor G} {fun_H : Functor H} : Functor (G :+: H).
    econstructor 1 with (fmap :=
      fun (A B : Set) (f : A -> B) (a : (G :+: H) A) =>
        match a with
          | inl G' => inl _ (fmap f G')
          | inr H' => inr _ (fmap f H')
        end).
    (* fmap_fusion *)
    intros; destruct a;
    rewrite fmap_fusion; reflexivity.
    (* fmap_id *)
    intros; destruct a;
    rewrite fmap_id; reflexivity.
  Defined.

  Class Sub_Functor (sub_F sub_G : Set -> Set) : Set :=
    { inj : forall {A : Set}, sub_F A -> sub_G A;
      prj : forall {A : Set}, sub_G A -> option (sub_F A);
      inj_prj : forall {A : Set} (ga : sub_G A) (fa : sub_F A),
        prj ga = Some fa -> ga = inj fa;
      prj_inj : forall {A : Set} (fa : sub_F A),
        prj (inj fa) = Some fa
    }.

  Notation "A :<: B"  := (Sub_Functor A B) (at level 80, right associativity).

  (* Need the 'Global' modifier so that the instance survives the Section.*)
  Global Instance Sub_Functor_inl (F G H : Set -> Set) (sub_F_G : F :<: G) :
    F :<: (G :+: H) :=
    {| inj :=  (fun (A : Set) (e : F A) => inl _ (@inj F G sub_F_G _ e));
       prj := fun (A: Set) (e : (G :+: H) A) =>
        match e with
         | inl e' => prj e'
         | inr _  => None
        end
     |}.
    intros; destruct ga; [rewrite (inj_prj _ _ H0); reflexivity | discriminate].
    intros; simpl; rewrite prj_inj; reflexivity.
  Defined.

  Global Instance Sub_Functor_inr (F G H : Set -> Set) (sub_F_H : F :<: H) :
    F :<: (G :+: H) :=
    {| inj := fun (A : Set) (e : F A) => inr _ (@inj F H sub_F_H _ e);
       prj := fun (A : Set) (e : (G :+: H) A) =>
        match e with
         | inl _  => None
         | inr e' => prj e'
        end
     |}.
    intros; destruct ga; [discriminate | rewrite (inj_prj _ _ H0); reflexivity ].
    intros; simpl; rewrite prj_inj; reflexivity.
  Defined.

  Global Instance Sub_Functor_id {F : Set -> Set} : F :<: F :=
    {| inj := fun A => @id (F A);
       prj := fun A => @Some (F A) |}.
    unfold id; congruence.
    reflexivity.
  Defined.

  (* ============================================== *)
  (* WELL-FORMEDNESS OF FUNCTORS                    *)
  (* ============================================== *)

  Class WF_Functor (F G: Set -> Set)
    (subfg: F :<: G)
    (Fun_F: Functor F)
    (Fun_G: Functor G): Set :=
    { wf_functor :
      forall (A B : Set) (f : A -> B) (fa: F A) ,
        fmap f (inj fa) (F := G) = inj (fmap f fa) }.

  Global Instance WF_Functor_id {F : Set -> Set} {Fun_F : Functor F} :
    WF_Functor F F Sub_Functor_id _ _.
    econstructor; intros; reflexivity.
  Defined.

  Global Instance WF_Functor_plus_inl {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {subfg : F :<: G}
    {WF_Fun_F : WF_Functor F _ subfg Fun_F Fun_G}
    :
    WF_Functor F (G :+: H) (Sub_Functor_inl F G H _ ) _ (Functor_Plus G H).
    econstructor; intros.
    simpl; rewrite wf_functor; reflexivity.
  Defined.

  Global Instance WF_Functor_plus_inr {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {subfh : F :<: H}
    {WF_Fun_F : WF_Functor F _ subfh Fun_F Fun_H}
    :
    WF_Functor F (G :+: H) (Sub_Functor_inr F G H _ ) _ (Functor_Plus G H).
    econstructor; intros.
    simpl; rewrite wf_functor; reflexivity.
  Defined.

  (* ============================================== *)
  (* INJECTION + PROJECTION                         *)
  (* ============================================== *)


  Definition inject' {F G: Set -> Set} {Fun_F : Functor F} {subGF: G :<: F} :
    G (sig (@Universal_Property'_fold F Fun_F)) -> (sig (@Universal_Property'_fold F Fun_F)) :=
    fun gexp => in_t_UP' _ _ (inj gexp).

  Definition inject {F G: Set -> Set} {Fun_F : Functor F} {subGF: G :<: F} :
    G (sig (@Universal_Property'_fold F Fun_F)) -> Fix F :=
      fun gexp => proj1_sig (in_t_UP' _ _ (inj gexp)).

  Definition project {F G: Set -> Set} {Fun_F: Functor F} {subGF : G :<: F } :
    Fix F -> option (G (sig (@Universal_Property'_fold F Fun_F))) :=
      fun exp => prj (out_t_UP' _ _ exp).

  Lemma project_inject : forall (G H : Set -> Set)
    (Fun_G : Functor G)
    (Fun_H : Functor H)
    (sub_G_H : G :<: H)
    (h : Fix H) (g : G (sig (@Universal_Property'_fold H Fun_H))),
    Universal_Property'_fold h ->
    project h = Some g -> h = inject g.
    intros.
    apply inj_prj in H1.
    unfold inject; rewrite <- H1.
    erewrite in_out_UP'_inverse; eauto.
  Qed.

  Lemma inject_project : forall (F G  : Set -> Set)
    (Fun_F : Functor F)
    (Fun_G : Functor G)
    (sub_G_F : G :<: F)
    (g : G (sig (@Universal_Property'_fold F Fun_F))),
    fmap (@proj1_sig _ _) (out_t_UP' _ _ (inject g)) =
    (fmap (@proj1_sig _ _) (inj g)).
    unfold inject; intros; simpl.
    rewrite out_in_fmap.
    rewrite fmap_fusion.
    assert (forall e : sig Universal_Property'_fold,
      proj1_sig (in_t_UP' F Fun_F (out_t_UP' F Fun_F (proj1_sig e))) = proj1_sig e).
    intros; eapply in_out_UP'_inverse.
    intros; destruct e as [e e_UP']; eassumption.
    rewrite fmap_fusion.
    rewrite (functional_extensionality _ _ H).
    reflexivity.
  Qed.

  Class Distinct_Sub_Functor {F G H : Set -> Set}
    (Fun_H : Functor H)
    (sub_F_H : F :<: H)
    (sub_G_H : G :<: H)
    : Set :=
    {inj_discriminate : forall A f g,
      inj (Sub_Functor := sub_F_H) (A := A) f <> inj (Sub_Functor := sub_G_H) (A := A) g}.

  Global Instance Distinct_Sub_Functor_plus
    (F G H I : Set -> Set)
    (Fun_G : Functor G)
    (Fun_I : Functor I)
    (sub_F_G : F :<: G)
    (sub_H_I : H :<: I)
    :
    @Distinct_Sub_Functor F H (G :+: I) _ _ _.
    econstructor; intros.
    unfold not; simpl; unfold id; intros.
    discriminate.
  Defined.

  Global Instance Distinct_Sub_Functor_plus'
    (F G H I : Set -> Set)
    (Fun_G : Functor G)
    (Fun_I : Functor I)
    (sub_F_G : F :<: G)
    (sub_H_I : H :<: I)
    :
    @Distinct_Sub_Functor F H (I :+: G) _ _ _.
    econstructor; intros.
    unfold not; simpl; unfold id; intros.
    discriminate.
  Defined.

  Global Instance Distinct_Sub_Functor_inl
    (F G H I : Set -> Set)
    (Fun_G : Functor G)
    (Fun_I : Functor I)
    (sub_F_G : F :<: G)
    (sub_H_G : H :<: G)
    (Dist_inl : @Distinct_Sub_Functor F H G Fun_G sub_F_G sub_H_G)
    :
    @Distinct_Sub_Functor F H (G :+: I) _ _ _.
    econstructor; intros.
    unfold not; intros.
    simpl in H0; injection H0; intros.
    eapply (inj_discriminate (Distinct_Sub_Functor := Dist_inl) _ f g H1).
  Defined.

  Global Instance Distinct_Sub_Functor_inr
    (F G H I : Set -> Set)
    (Fun_G : Functor G)
    (Fun_I : Functor I)
    (sub_F_G : F :<: G)
    (sub_H_G : H :<: G)
    (Dist_inl : @Distinct_Sub_Functor F H G Fun_G sub_F_G sub_H_G)
    :
    @Distinct_Sub_Functor F H (I :+: G) _ _ _.
    econstructor; intros.
    unfold not; intros.
    simpl in H0; injection H0; intros.
    eapply (inj_discriminate (Distinct_Sub_Functor := Dist_inl) _ f g H1).
  Defined.

  Lemma inject_discriminate : forall {F G H : Set -> Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {sub_F_H : F :<: H}
    {sub_G_H : G :<: H}
    {WF_F : WF_Functor _ _ sub_F_H Fun_F Fun_H}
    {WF_G : WF_Functor _ _ sub_G_H Fun_G Fun_H},
    Distinct_Sub_Functor Fun_H sub_F_H sub_G_H ->
    forall f g, inject (subGF := sub_F_H) f <> inject (subGF := sub_G_H) g.
    unfold inject; simpl; intros.
    unfold not; intros H3; apply in_t_UP'_inject in H3.
    repeat rewrite wf_functor in H3.
    eapply (inj_discriminate _ _ _ H3).
  Qed.

  (* ============================================== *)
  (* INDEXED FUNCTOR COMPOSITION                    *)
  (* ============================================== *)

  Definition inj_iFunctor {I : Type} {F G : (I -> Prop) -> I -> Prop} {A : I -> Prop} : I -> Prop :=
    fun i => or (F A i) (G A i).

  Notation "A ::+:: B"  := (@inj_iFunctor _ A B) (at level 80, right associativity).

  Global Instance iFunctor_Plus {I : Type} (G H : (I -> Prop) -> I -> Prop)
    {fun_G : iFunctor G} {fun_H : iFunctor H} : iFunctor (G ::+:: H).
    econstructor 1 with (ifmap :=
      fun (A B : I -> Prop) (i : I) (f : forall i, A i -> B i) (a : (G ::+:: H) A i) =>
        match a with
          | or_introl G' => or_introl _ (ifmap i f G')
          | or_intror H' => or_intror _ (ifmap i f H')
        end).
    (* ifmap_fusion *)
    intros; destruct a;
    rewrite ifmap_fusion; reflexivity.
    (* ifmap_id *)
    intros; destruct a;
    rewrite ifmap_id; reflexivity.
  Defined.

  Class Sub_iFunctor {I : Type} (sub_F sub_G : (I -> Prop) -> I -> Prop) : Prop :=
    { inj_i : forall {A : I -> Prop} i, sub_F A i -> sub_G A i;
         prj_i : forall {A : I -> Prop} i, sub_G A i -> (sub_F A i) \/ True
    }.

  Notation "A ::<:: B"  := (Sub_iFunctor A B) (at level 80, right associativity).

  (* Need the 'Global' modifier so that the instance survives the Section.*)

  Global Instance Sub_iFunctor_inl {I' : Type} (F G H : (I' -> Prop) -> I' -> Prop) (sub_F_G : F ::<:: G) :
    F ::<:: (G ::+:: H) :=
    {| inj_i :=  (fun (A : I' -> Prop) i (e : F A i) =>
      or_introl _ (@inj_i _ F G sub_F_G _ _ e));
    prj_i := fun (A: I' -> Prop) i (e : (G ::+:: H) A i) =>
      match e with
        | or_introl e' => prj_i _ e'
        | or_intror _  => or_intror _ I
      end
    |}.

  Global Instance Sub_iFunctor_inr {I' : Type} (F G H : (I' -> Prop) -> I' -> Prop) (sub_F_H : F ::<:: H) :
    F ::<:: (G ::+:: H) :=
    {| inj_i :=  (fun (A : I' -> Prop) i (e : F A i) =>
      or_intror _ (@inj_i _ F H sub_F_H _ _ e));
    prj_i := fun (A: I' -> Prop) i (e : (G ::+:: H) A i) =>
      match e with
        | or_intror e' => prj_i _ e'
        | or_introl _  => or_intror _ I
      end
    |}.

  Global Instance Sub_iFunctor_id {I : Type} {F : (I -> Prop) -> I -> Prop} : F ::<:: F :=
    {| inj_i := fun A i e => e;
       prj_i := fun A i e => or_introl _ e |}.

  Definition inject_i {I : Type} {F G: (I -> Prop) -> I -> Prop} {subGF: Sub_iFunctor G F} :
    forall i, G (iFix F) i -> iFix F i:=
    fun i gexp => in_ti i (inj_i i gexp).

  Definition project_i {I : Type} {F G: (I -> Prop) -> I -> Prop}
    {fun_F: iFunctor F}
    {subGF: Sub_iFunctor G F} :
    forall i, iFix F i -> (G (iFix F) i) \/ True :=
      fun i fexp => prj_i i (out_ti i fexp).

End Folds.

Notation "A :+: B"  := (@inj_Functor A B) (at level 80, right associativity).
Notation "A :<: B"  := (Sub_Functor A B) (at level 80, right associativity).
Notation "A ::+:: B"  := (@inj_iFunctor _ A B) (at level 80, right associativity).
Notation "A ::<:: B"  := (Sub_iFunctor _ A B) (at level 80, right associativity).

Definition inj'' {F G : Set -> Set} (sub_F_G: F :<: G) {A : Set} := @inj F G sub_F_G A.

Section FAlgebra.

  (* ============================================== *)
  (* OPERATIONS INFRASTRUCTURE                      *)
  (* ============================================== *)

  Class FAlgebra (Name : Set) (T: Set) (A: Set) (F: Set -> Set) : Set :=
    { f_algebra : Mixin T F A }.

  (* Definition FAlgebra_Plus (Name: Set) (T: Set) (A : Set) (F G : Set -> Set)
    {falg: FAlgebra Name T A F} {galg: FAlgebra Name T A G} :
    FAlgebra Name T A (F :+: G) :=
    Build_FAlgebra Name T A _
    (fun f fga =>
      (match fga with
         | inl fa => f_algebra f fa
         | inr ga => f_algebra f ga
       end)). *)

  Global Instance FAlgebra_Plus (Name: Set) (T: Set) (A : Set) (F G : Set -> Set)
    {falg: FAlgebra Name T A F} {galg: FAlgebra Name T A G} :
    FAlgebra Name T A (F :+: G) | 6 :=
    {| f_algebra := fun f fga=>
         (match fga with
           | inl fa => f_algebra f fa
           | inr ga => f_algebra f ga
          end) |}.

  (* The | 6 gives the generated Hint a priority of 6. If this is
     less than that of other instances for FAlgebra, the
     typeclass inference algorithm will loop.
     *)

  Class WF_FAlgebra (Name T A: Set) (F G: Set -> Set)
    (subfg: F :<: G)
    (falg: FAlgebra Name T A F)
    (galg: FAlgebra Name T A G): Set :=
    { wf_algebra :
      forall rec (fa: F T),
        @f_algebra Name T A G galg rec (@inj F G subfg T fa) = @f_algebra Name T A F falg rec fa }.

  Global Instance WF_FAlgebra_id {Name T A : Set} {F} {falg: FAlgebra Name T A F}:
    WF_FAlgebra Name T A F F Sub_Functor_id falg falg.
      econstructor. intros.
      unfold inj.
      unfold Sub_Functor_id.
      unfold id.
      reflexivity.
  Defined.

  Global Instance WF_FAlgebra_inl
    {Name A T : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_G: F :<: G}
    {wf_F_G: WF_FAlgebra Name T A F G sub_F_G falg galg}
    :
    WF_FAlgebra Name T A F (G :+: H) (Sub_Functor_inl F G H sub_F_G) falg (@FAlgebra_Plus Name T A G H galg halg).
      econstructor. intros.
      unfold inj. unfold Sub_Functor_inl.
      simpl.
      rewrite (wf_algebra rec fa).
      reflexivity.
  Defined.

  Global Instance WF_FAlgebra_inr
    {Name T A : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_H: F :<: H}
    {wf_G_H: WF_FAlgebra Name T A F H sub_F_H falg halg}
    :
    WF_FAlgebra Name T A F (G :+: H) (Sub_Functor_inr F G H sub_F_H) falg (@FAlgebra_Plus Name T A G H galg halg).
      econstructor. intros.
      unfold inj.
      unfold Sub_Functor_inr.
      simpl.
      rewrite (wf_algebra rec fa).
      reflexivity.
    Defined.

End FAlgebra.

  (* ============================================== *)
  (* INDUCTION PRINCIPLES INFRASTRUCTURE            *)
  (* ============================================== *)

Section PAlgebras.

  Class PAlgebra (Name : Set) (F G: Set -> Set)
    {Fun_F : Functor F} {Fun_G : Functor G}
    (P : Fix G -> Prop) {sub_F_G : F :<: G} : Set :=
    { p_algebra : Algebra F (sig P);
      WF_Ind : forall e, proj1_sig (p_algebra e) =
      in_t (inj (Sub_Functor := sub_F_G) (fmap (@proj1_sig _ _) e))}.

  (* Definition PAlgebra_Plus (Name: Set) (A : Set) (F G : Set -> Set)
    {falg: PAlgebra Name A F} {galg: PAlgebra Name A G} :
    PAlgebra Name A (F :+: G) :=
    Build_PAlgebra Name A _
    (fun fga =>
      (match fga with
         | inl fa => p_algebra fa
         | inr ga => p_algebra ga
       end)). *)

  Definition Sub_Functor_inl' (F G H : Set -> Set) (sub_F_G : (F :+: G) :<: H) :
    F :<: H.
    econstructor 1 with
      (inj := fun (A : Set) (e : F A) => (@inj _ _ sub_F_G A (inl _ e)))
      (prj := fun (A : Set) (ha : H A) =>
        match @prj _ _ sub_F_G A ha with
          | Some (inl f) => Some f
          | Some (inr g) => None
          | None => None
        end).
    intros until fa; caseEq (prj ga);
      [rewrite (inj_prj _ _ H0); destruct i; congruence | discriminate].
    intros; rewrite prj_inj; reflexivity.
  Defined.

  Definition Sub_Functor_inr' (F G H : Set -> Set) (sub_F_G : (F :+: G) :<: H) :
    G :<: H.
    econstructor 1 with
      (inj := fun (A : Set) (e : G A) => (@inj _ _ sub_F_G A (inr _ e)))
      (prj := fun (A : Set) (H0 : H A) =>
          match @prj _ _ sub_F_G A H0 with
            | Some (inl f) => None
            | Some (inr g) => Some g
            | None => None
          end).
    intros until fa; caseEq (prj ga);
      [rewrite (inj_prj _ _ H0); destruct i; congruence | discriminate].
    intros; rewrite prj_inj; reflexivity.
  Defined.

  Global Instance WF_Functor_Sub_Functor_inl'
    (F G H : Set -> Set) (sub_F_G_H : (F :+: G) :<: H)
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {WF_sub_F_G_H : WF_Functor _ _ sub_F_G_H _ _ } :
    WF_Functor F H (Sub_Functor_inl' _ _ _ sub_F_G_H) _ _.
  Proof.
    econstructor; intros.
    simpl; erewrite wf_functor; simpl; reflexivity.
  Qed.

  Global Instance WF_Functor_Sub_Functor_inr'
    (F G H : Set -> Set) (sub_F_G_H : (F :+: G) :<: H)
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {WF_sub_F_G_H : WF_Functor _ _ sub_F_G_H _ _ } :
    WF_Functor G H (Sub_Functor_inr' _ _ _ sub_F_G_H) _ _.
  Proof.
    econstructor; intros.
    simpl; erewrite wf_functor; simpl; reflexivity.
  Qed.

  Global Instance WF_FAlgebra_inl'
    {Name T A : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_FAlgebra Name T A (F :+: G) H sub_F_G_H (FAlgebra_Plus _ _ _ F G) halg}
    :
    WF_FAlgebra Name T A F H (Sub_Functor_inl' F G H sub_F_G_H)
    falg halg.
    constructor; intros; simpl; rewrite wf_algebra; reflexivity.
  Qed.

  Global Instance WF_FAlgebra_inr'
    {Name T A : Set}
    {F G H}
    {falg: FAlgebra Name T A F}
    {galg: FAlgebra Name T A G}
    {halg: FAlgebra Name T A H}
    {sub_F_H: F :<: H}
    {sub_G_H: G :<: H}
    {sub_F_G_H: (F :+: G) :<: H}
    {wf_F_H: WF_FAlgebra Name T A (F :+: G) H sub_F_G_H (FAlgebra_Plus _ _ _ F G) halg}
    :
    WF_FAlgebra Name T A G H (Sub_Functor_inr' F G H sub_F_G_H)
    galg halg.
    constructor; intros; simpl; rewrite wf_algebra; reflexivity.
  Qed.

  Global Instance PAlgebra_Plus (Name: Set)
    (F G H : Set -> Set)
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    (P : Fix H -> Prop)
    {sub_F_G_H : (F :+: G) :<: H}
    {falg: @PAlgebra Name F H _ _ P (Sub_Functor_inl' _ _ _ sub_F_G_H)}
    {galg: @PAlgebra Name G H _ _ P (Sub_Functor_inr' _ _ _ sub_F_G_H)}

    :
    PAlgebra Name (F :+: G) H P | 6:=
      {| p_algebra := fun fga : (F :+: G) (sig P) =>
        (match fga with
           | inl fa => p_algebra (PAlgebra := falg) fa
           | inr ga => p_algebra (PAlgebra := galg) ga
         end) |}.
  Proof.
    intros; destruct e; simpl; rewrite WF_Ind; simpl; auto.
  Qed.

    (* The key reasoning lemma. *)
    Lemma Ind {F : Set -> Set}
      {Fun_F : Functor F}
      {P : Fix F -> Prop}
      {N : Set}
      {Ind_Alg : PAlgebra N F F P}
      :
      forall (f : Fix F)
        (fUP' : Universal_Property'_fold f),
        P f.
      intros.
      cut (proj1_sig (fold_ _ p_algebra f) = id f).
      unfold id.
      intro f_eq; rewrite <- f_eq.
      eapply (proj2_sig (fold_ _ p_algebra f)).
      erewrite (@Fusion _ Fun_F f fUP' _ _ (@proj1_sig (Fix F) P) p_algebra in_t).
      eapply Fix_id_fold; unfold id; assumption.
      intros; rewrite WF_Ind.
      simpl; unfold id; reflexivity.
    Defined.

  Class DAlgebra (Name : Set) (F G: Set -> Set)
    {Fun_F : Functor F} {Fun_G : Functor G}
    (P : Fix G -> Set) {sub_F_G : F :<: G} : Set :=
    { d_algebra : Algebra F (sigT P);
      WF_DInd : forall e, projT1 (d_algebra e) =
      in_t (inj (Sub_Functor := sub_F_G) (fmap (@projT1 _ _) e))}.

  Global Instance DAlgebra_Plus (Name: Set)
    (F G H : Set -> Set)
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    (P : Fix H -> Set)
    {sub_F_G_H : (F :+: G) :<: H}
    {falg: @DAlgebra Name F H _ _ P (Sub_Functor_inl' _ _ _ sub_F_G_H)}
    {galg: @DAlgebra Name G H _ _ P (Sub_Functor_inr' _ _ _ sub_F_G_H)}

    :
    DAlgebra Name (F :+: G) H P | 6:=
      {| d_algebra := fun fga : (F :+: G) (sigT P) =>
        (match fga with
           | inl fa => d_algebra (DAlgebra := falg) fa
           | inr ga => d_algebra (DAlgebra := galg) ga
         end) |}.
  Proof.
    intros; destruct e; simpl; rewrite WF_DInd; simpl; auto.
  Qed.

    (* The key reasoning lemma. *)
    Lemma IndD {F : Set -> Set}
      {Fun_F : Functor F}
      {P : Fix F -> Set}
      {N : Set}
      {Ind_Alg : DAlgebra N F F P}
      :
      forall (f : Fix F)
        (fUP' : Universal_Property'_fold f),
        P f.
      intros.
      cut (projT1 (fold_ _ d_algebra f) = id f).
      unfold id.
      intro f_eq; rewrite <- f_eq.
      eapply (projT2 (fold_ _ d_algebra f)).
      erewrite (@Fusion _ Fun_F f fUP' _ _ (@projT1 (Fix F) P) d_algebra in_t).
      eapply Fix_id_fold; unfold id; assumption.
      intros; rewrite WF_DInd.
      simpl; unfold id; reflexivity.
    Defined.

  Class P2Algebra (Name : Set) (F G G' : Set -> Set)
    {Fun_F : Functor F} {Fun_G : Functor G} {Fun_G' : Functor G'}
    (P : (Fix G) * (Fix G') -> Prop)
    {sub_F_G : F :<: G}
    {sub_F_G' : F :<: G'} : Set :=
    { p2_algebra : Algebra F (sig P);
      proj1_WF_Ind : forall e, fst (proj1_sig (p2_algebra e)) =
        in_t (inj (Sub_Functor := sub_F_G) (fmap (fun e => fst (proj1_sig e)) e));
      proj2_WF_Ind : forall e, snd (proj1_sig (p2_algebra e)) =
        in_t (inj (Sub_Functor := sub_F_G') (fmap (fun e => snd (proj1_sig e)) e))
    }.

  Global Instance P2Algebra_Plus {F G H H'}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    {Fun_H : Functor H}
    {Fun_H' : Functor H'}
    {sub_F_G_H : (F :+: G) :<: H}
    {sub_F_G_H' : (F :+: G) :<: H'}
    {Name : Set}
    {P : (Fix H) * (Fix H') -> Prop}
    {falg: @P2Algebra Name F H H' _ _ _ P (Sub_Functor_inl' _ _ _ sub_F_G_H) (Sub_Functor_inl' _ _ _ sub_F_G_H')}
    {galg: @P2Algebra Name G H H' _ _ _ P (Sub_Functor_inr' _ _ _ sub_F_G_H) (Sub_Functor_inr' _ _ _ sub_F_G_H')}
    :
    @P2Algebra Name (F :+: G) H H' _ _ _ P sub_F_G_H sub_F_G_H' :=
    {| p2_algebra := fun fga : (F :+: G) (sig P) =>
      (match fga with
         | inl fa => p2_algebra (P2Algebra := falg) fa
         | inr ga => p2_algebra (P2Algebra := galg) ga
       end) |}.
  Proof.
    intros; destruct e; simpl; rewrite proj1_WF_Ind; simpl; reflexivity.
    intros; destruct e; simpl; rewrite proj2_WF_Ind; simpl; reflexivity.
  Defined.

  Lemma Ind2 {F : Set -> Set}
    {Fun_F : Functor F}
    {P : (Fix F) * (Fix F) -> Prop}
    {N : Set}
    {Ind_Alg : P2Algebra N F F F P}
    :
    forall (f : Fix F)
      (fUP' : Universal_Property'_fold f),
      P (f, f).
    intros.
    cut (fst (proj1_sig (fold_ _ p2_algebra f)) = f).
    cut (snd (proj1_sig (fold_ _ p2_algebra f)) = f).
    intros f2_eq f1_eq; rewrite <- f1_eq at 1; rewrite <- f2_eq at -1.
    generalize (proj2_sig (fold_ _ p2_algebra f)).
    destruct (proj1_sig (fold_ (sig P) p2_algebra f)); simpl; auto.
    erewrite (@Fusion _ Fun_F f fUP' _ _ (fun e => snd (proj1_sig e)) p2_algebra in_t).
    eapply Fix_id_fold; unfold id; assumption.
    intros; rewrite proj2_WF_Ind.
    simpl; unfold id; reflexivity.
    erewrite (@Fusion _ Fun_F f fUP' _ _ (fun e => fst (proj1_sig e)) p2_algebra in_t).
    eapply Fix_id_fold; unfold id; assumption.
    intros; rewrite proj1_WF_Ind.
    simpl; unfold id; reflexivity.
  Defined.

  Class iPAlgebra (Name : Set) {I : Type} (A : I -> Prop) (F: (I -> Prop) -> I -> Prop) : Prop :=
    { ip_algebra : iAlgebra F A}.

    (* Definition iPAlgebra_Plus (Name: Set) {I : Set} (A : I -> Prop)
      (F G : (I -> Prop) -> I -> Prop)
      {falg: iPAlgebra Name A F} {galg: iPAlgebra Name A G} :
      iPAlgebra Name A (F ::+:: G) :=
        Build_iPAlgebra Name _ A _
        (fun f fga =>
          (match fga with
             | or_introl fa => ip_algebra f fa
             | or_intror ga => ip_algebra f ga
           end)). *)

    Global Instance iPAlgebra_Plus (Name: Set) {I : Type} (A : I -> Prop)
      (F G : (I -> Prop) -> I -> Prop)
      {falg: iPAlgebra Name A F} {galg: iPAlgebra Name A G} :
      iPAlgebra Name A (F ::+:: G) | 6 :=
        {| ip_algebra := fun f fga =>
          (match fga with
             | or_introl fa => ip_algebra f fa
             | or_intror ga => ip_algebra f ga
           end) |}.

End PAlgebras.

(* ============================================== *)
(* ADDTIONAL MENDLER ALGEBRA INFRASTRUCTURE       *)
(* ============================================== *)

Section WF_MAlgebras.

  Class WF_MAlgebra {Name : Set} {F : Set -> Set} {A : Set}
    {Fun_F : Functor F}(MAlg : forall R, FAlgebra Name R A F) :=
    {wf_malgebra : forall (T T' : Set) (f : T' -> T) (rec : T -> A) (ft : F T'),
      f_algebra (FAlgebra := MAlg T) rec (fmap f ft) =
      f_algebra (FAlgebra := MAlg T') (fun ft' => rec (f ft')) ft}.

  Global Instance WF_MAlgebra_Plus {Name : Set} {F G : Set -> Set} {A : Set}
    {Fun_F : Functor F}
    {Fun_G : Functor G}
    (MAlg_F : forall R, FAlgebra Name R A F)
    (MAlg_G : forall R, FAlgebra Name R A G)
    {WF_MAlg_F : WF_MAlgebra MAlg_F}
    {WF_MAlg_G : WF_MAlgebra MAlg_G}
    :
    @WF_MAlgebra Name (F :+: G) A _ (fun R => FAlgebra_Plus Name R A F G).
  Proof.
    constructor; intros.
    destruct ft; simpl; apply wf_malgebra.
  Qed.

End WF_MAlgebras.

Definition Smarked (S: Set) : Set := S.

Ltac Smark H :=
  let t := type of H in
  let n:= fresh in
    (assert (n:Smarked t); [exact H | clear H; rename n into H]).

Ltac unSmark H := unfold Smarked in H.

Ltac unSmark_all := unfold Smarked in *|-.

Ltac WF_Falg_rewrite' :=
  match goal with
    | H : WF_FAlgebra _ _ _ _ _ _ _ |- _ =>
      try rewrite (wf_algebra (WF_FAlgebra := H)); Smark H; WF_Falg_rewrite'
    | _ => simpl
  end;
  unSmark_all.

Ltac WF_Falg_rewrite := unfold inject, in_t; WF_Falg_rewrite'.

Ltac fold_ind := eapply Ind.

Hint Extern 0 (FAlgebra _ _ _ (_ :+: _)) =>
  apply FAlgebra_Plus; eauto with typeclass_instances : typeclass_instances.

Hint Extern 0 (forall _, FAlgebra _ _ _ _) =>
  intros; eauto with typeclass_instances : typeclass_instances.

Hint Extern 0 (forall _, PAlgebra _ _ _ _) =>
  intros; eauto with typeclass_instances : typeclass_instances.

Hint Extern 0 (PAlgebra _ (_ :+: _) _ _) =>
  apply PAlgebra_Plus; eauto with typeclass_instances : typeclass_instances.

Hint Extern 0 (iPAlgebra _ _ (_ :+: _)) =>
  apply iPAlgebra_Plus; eauto with typeclass_instances : typeclass_instances.

(* Hint Extern 0 (WF_Ind _) =>
  let e := fresh in
    constructor; intro e; destruct e; reflexivity : typeclass_instances.

Hint Extern 0 (WF_Ind2 _) =>
  let e := fresh in
    constructor; intro e; destruct e; reflexivity : typeclass_instances. *)

Hint Extern 0 (WF_MAlgebra _) =>
  let T := fresh in
    let T' := fresh in
      let f' := fresh in
        let rec' := fresh in
          let ft := fresh in
            constructor; intros T T' f' rec' ft; destruct ft;
              simpl; auto; fail : typeclass_instances.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)
