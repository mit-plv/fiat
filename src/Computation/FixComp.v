Require Import
        Coq.Sets.Ensembles
        Coq.Classes.Morphisms
        Coq.Classes.SetoidTactics
        Fiat.Computation.

Section FixComp.

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

  Fixpoint cfunType
           (fDom : list Type)
           (fCod : Type)
           {struct fDom}
    : Type :=
    match fDom with
    | nil => fCod
    | cons T fDom' => T -> cfunType fDom' fCod
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

  Definition FixedPointP
             {fDom : list Type}
             {fCod : Type}
             (fDef : funType fDom fCod -> funType fDom fCod)
             (fSet : funType fDom fCod)
    : Prop :=
    refineFun (fDef fSet) fSet /\ refineFun fSet (fDef fSet).

  Definition LeastFixedPointP
             {fDom : list Type}
             {fCod : Type}
             (fDef : funType fDom fCod -> funType fDom fCod)
             (fSet : funType fDom fCod)
    : Prop :=
    FixedPointP fDef fSet /\
    forall fSet', FixedPointP fDef fSet'
                  -> refineFun fSet' fSet.

  Local Transparent computes_to.

  (*
  Definition LeastFixedPoint {A}
             (f : Comp A -> Comp A)
    : Comp A :=
    fun a =>
      forall (ca : Comp A),
        refine ca (f ca)
        -> In _ ca a.

  Lemma refine_LeastFixedPoint {A}
    : forall (f : Comp A -> Comp A)
             (f_monotone : forall rec rec',
                 refine rec rec'
                 -> refine (f rec) (f rec')),
      refineEquiv (f (LeastFixedPoint f)) (LeastFixedPoint f).
  Proof.
    split; eauto.
    unfold LeastFixedPoint, refine, computes_to in *; intros.
    apply H0.
    eapply f_monotone.
    unfold computes_to.
    apply f_monotone in H.

    eapply f_monotone in H.

    intros v' Comp_v'.
    apply Comp_v'.
    unfold computes_to in H.
    apply H.
    split; unfold refine; intros.




  Defined.

  Fixpoint LeastFixedPointFun'
           (fDom : list Type)
           {fCod : Type}
           {struct fDom}
    : (funType fDom fCod -> funType fDom fCod) -> funType fDom fCod.
    refine match fDom return
          (funType fDom fCod -> funType fDom fCod)
          -> funType fDom fCod with
    | nil => fun fDef => LeastFixedPoint fDef
    | cons T fDom' =>
      fun fDef (t : T) => LeastFixedPointFun' fDom' fCod _
           end.
    simpl in *.
    intros.
    apply LeastFixedPointFun'.
    intro.

    apply fDef.
    intros.
    apply X.
    apply t.
  Defined.


   Definition LeastFixedPointFun
             {fDom : list Type}
             {fCod : Type}
             (fDef : funType fDom fCod -> funType fDom fCod)
    : funType fDom fCod :=
    LeastFixedPointFun' fDom fDef.

  Lemma refine_LeastFixedPointFun
        {fDom : list Type}
        {fCod : Type}
        (fDef fDef' : funType fDom fCod -> funType fDom fCod)
      : respectful (@refineFun fDom fCod)
                   (@refineFun fDom fCod)
                   fDef fDef'
        -> refineFun (LeastFixedPointFun fDef)
                     (LeastFixedPointFun fDef').
  Proof.
    induction fDom; simpl; intros.
    - unfold LeastFixedPointFun; simpl in *.
      unfold refine; intros v Comp_v; intuition.
      unfold computes_to, LeastFixedPoint,
      FixedPointP, respectful in *; simpl in *.
      intros.
      eapply H; eauto.
      2: eapply (Comp_v ca).
      reflexivity.
    - simpl in *.
      eapply IHfDom; eauto.
      unfold respectful in *; intros.
      eapply H.
      intro.
      apply H0.
  Qed.


*)

  Fixpoint LeastFixedPoint'
           (fDom : list Type)
           {fCod : Type}
           {struct fDom}
    : ((funType fDom fCod -> Prop) -> Prop) ->  funType fDom fCod :=
    match fDom return
          ((funType fDom fCod -> Prop) -> Prop)
          -> funType fDom fCod with
    | nil => fun LFP_P v => (LFP_P (fun cv => computes_to cv v))
    | cons T fDom' =>
      fun LFP_P =>
        fun (t : T) => LeastFixedPoint' fDom' (fun cv => LFP_P (fun cv' => cv (cv' t)))
    end.

  Definition LeastFixedPoint''
             {fDom : list Type}
             {fCod : Type}
             (fDef : funType fDom fCod -> funType fDom fCod)
    : funType fDom fCod :=
    LeastFixedPoint' fDom (fun z => exists s, LeastFixedPointP fDef s /\ z s).

  Definition FibonacciSpec
    : funType ((nat : Type) :: @nil Type)%list nat :=
    LeastFixedPoint'' (fDom := (nat : Type) :: @nil Type)%list
      (fun rec (n : nat) =>
         match n with
         | 0 => ret 0
         | 1 => ret 1
         | S (S n') =>
           n1 <- rec n';
           n2 <- rec (S n');
           ret (n1 + n2)
         end).

  Fixpoint FibonacciImpl
           (n : nat)
    : Comp nat :=
    match n with
    | 0 => ret 0
    | (S p) =>
      match p with
      | 0 => ret 1
      | (S m) => n1 <- FibonacciImpl p;
                 n2 <- FibonacciImpl m;
                 ret (n1 + n2)
      end
    end.

  Lemma foo
    : refineFun FibonacciSpec FibonacciImpl.
  Proof.
    unfold refineFun; unfold refine; intros.
    unfold FibonacciSpec, LeastFixedPoint''; simpl.
    unfold LeastFixedPointP, FixedPointP, computes_to; simpl.
    exists FibonacciImpl; split; eauto.
    clear H.
    intuition.
    admit.
    admit.
    admit.
  Admitted.
  (*rewrite H1.
    induction t0.
    - reflexivity.
    - simpl.
      assert (refine (fSet' t0) (FibonacciImpl t0)).
      intros; rewrite H1.
      apply IHt0.
      revert H.
      destruct t0; intros.
      * reflexivity.
      * simpl in *.
        setoid_rewrite H.
        intros v' Comp_v'.
        computes_to_inv; subst.
        rewrite H1.
        eapply BindComputes with (a := v1);
        repeat computes_to_econstructor.
        2: apply Comp_v'.
        2: rewrite plus_comm; repeat computes_to_econstructor.


        eapply H1 in IHt0.
      assert (refine
                (match t0 with
                 | 0 => ret 1
                 | S m => n1 <- match t0 with
                                | 0 => ret 0
                                | 1 => ret 1
                                | S (S n') => n1 <- fSet' n';
                                              n2 <- fSet' (S n');
                                              ret (n1 + n2)
                                end;
                          n2 <- FibonacciImpl m;
                          ret (n1 + n2)
                 end)
                match t0 with
                | 0 => ret 1
                | S m => n1 <- FibonacciImpl t0;
                         n2 <- FibonacciImpl m;
                         ret (n1 + n2)
     end).
      destruct t0.
      reflexivity.
      rewrite IHt0.
      reflexivity.
      etransitivity; try eauto.
      clear H.

      apply
      rewrite <- IHt0.
      induction t0.
    reflexivity.
    rewrite H1.
    setoid_rewrite H1.
    rewrite <- IHt0.
    destruct t0.
    Focus 2.

    unfold FibonacciImpl.
    unfold
    - induction t0; simpl in *.
      + simpl; reflexivity.
      + induction t0.
        reflexivity.
        rewrite <- IHt0.

        intros v Comp_v; computes_to_inv.
        subst.
        apply IHt in Comp_v.
        computes_to_econstructor; eauto.
        destruct t.
        computes_to_econstructor; eauto.
        rewrite plus_comm; computes_to_econstructor.
        simpl in *.
        computes_to_inv; subst.
        repeat computes_to_econstructor.
        apply Comp_v'0.
        apply Comp_v.
        rewrite plus_assoc.
        rewrite plus_comm.
        rewrite (plus_comm v1 v2).
        rewrite plus_assoc.
        computes_to_econstructor; eauto.
      + induction t.
        * reflexivity.
        * simpl.
          destruct t; eauto.
          reflexivity.
          rewrite IHt.
          induction t.
          intros v Comp_v.
          simpl in *; computes_to_inv; subst.
          repeat computes_to_econstructor; eauto.
          simpl in *.
          simpl in
          apply IHt in Comp_v.
          computes_to_econstructor; eauto.
          destruct t.
          computes_to_econstructor; eauto.
          rewrite plus_comm; computes_to_econstructor.
          simpl in *.
          computes_to_inv; subst.
          repeat computes_to_econstructor.
          apply Comp_v'0.
          apply Comp_v.
          rewrite plus_assoc.
          rewrite plus_comm.
          rewrite (plus_comm v1 v2).
          rewrite plus_assoc.
          computes_to_econstructor; eauto.

        reflexivity.
        simpl.

        setoid_rewrite <- IHt.
      intros.

        simpl.

    - unfold FibonacciSpec, LeastFixedPoint''; simpl.
        unfold LeastFixedPointP, FixedPointP; simpl.
      unfold refine; intros.
      computes_to_inv; subst.
      unfold computes_to; intuition.
      eexists.
    - unfold FibonacciSpec, LeastFixedPointFun in *; simpl in *.
      destruct t.
      + unfold refine, LeastFixedPoint; simpl; intros.
        computes_to_inv; subst.
        unfold computes_to; intuition.
      + simpl in *.
        rewrite <- IHt.
        clear.
        destruct t; simpl.

  Lemma refine_LeastFixedPoint''
        {fDom : list Type}
        {fCod : Type}
        (fDef fDef' : funType fDom fCod -> funType fDom fCod)
        (f_monotone : forall rec rec',
            refineFun rec rec'
            -> refineFun (fDef rec) (fDef rec'))
      : respectful (@refineFun fDom fCod)
                   (@refineFun fDom fCod)
                   fDef fDef'
        -> refineFun (LeastFixedPoint'' fDef)
                     (LeastFixedPoint'' fDef').
  Proof.
    induction fDom; simpl; intros.
    - unfold LeastFixedPoint''; simpl in *.
      unfold refine; intros v Comp_v; intuition.
      unfold computes_to, FixedPointP, respectful in *; simpl in *.
      destruct Comp_v as [Fix' [LFP_Fix' computes_to_v] ].
      unfold LeastFixedPointP, FixedPointP in LFP_Fix'; simpl in *;
        intuition.
      exists Fix'; split; eauto.
      unfold LeastFixedPointP, FixedPointP; repeat split.
      simpl.
      etransitivity; eauto.
      Focus 3.
      simpl.
      apply H1.



      simpl in *.
      unfold FixedPoint

      exists (LeastFixedPoint fDef).
      unfold LeastFixedPointP; repeat split.
      + apply refine_LeastFixedPoint; admit.
      + apply refine_LeastFixedPoint; admit.
      + unfold FixedPointP; intros; simpl in *.
        intros v' Comp_v'.
        unfold LeastFixedPoint in Comp_v'.
        apply H0; apply Comp_v'.
      + unfold LeastFixedPoint; intros.
        destruct Comp_v; intuition.
        rewrite H; try reflexivity.
        unfold LeastFixedPointP in H1; simpl in *.
        intuition.
        unfold FixedPointP in H0.
        admit.
    - simpl in *.
      pose (
      unfold respectful in H.
      rewrite IHfDom.
      unfold LeastFixedPoint''; simpl.

      eapply IHfDom; eauto.
      unfold respectful in *; intros.
      eapply H.
      intro.
      apply H0.
  Qed.
   *)
End FixComp.
