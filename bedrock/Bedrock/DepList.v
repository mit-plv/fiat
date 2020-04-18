Require Import Coq.Lists.List Bedrock.EqdepClass.
Require Export Coq.Classes.EquivDec.
Require Import Bedrock.Decidables.

Set Implicit Arguments.
Set Strict Implicit.

Section fin.
  Variable A : Type.

  Inductive fin : list A -> Type :=
  | FO : forall x ls, fin (x :: ls)
  | FS : forall x ls, fin ls -> fin (x :: ls).

  Fixpoint lift (ls : list A) e : fin ls -> fin (e ++ ls) :=
    match e as e return fin ls -> fin (e ++ ls) with
      | nil => fun x => x
      | a :: b => fun x => FS a (@lift ls b x)
    end.

  Definition finOut ls (f : fin ls) : match ls return fin ls -> Type with
                                        | nil => fun _ => Empty_set
                                        | _ => fun f => {f' : _ & f = FS _ f'} + {f = FO _ _}
                                      end f :=
  match f with
    | FO _ _ => inright _ (refl_equal _)
    | FS _ _ f' => inleft _ (existT _ f' (refl_equal _))
  end.

  Definition finIfz t (ls : list A) (d : fin (t :: ls))
    : forall (R : fin (t :: ls) -> Type) (h : R (@FO _ _)) (n : forall c, R (@FS _ _ c)),
    R d :=
    match d as d' in fin ls' return match ls' return fin ls' -> Type with
                                | nil => fun _ => Empty_set
                                | a :: b => fun d =>
                                  forall (R : fin (a :: b) -> Type) (h : R (@FO _ _)) (n : forall c, R (@FS _ _ c)), R d
                              end d'
      with
      | FO _ _ => fun _ h _ => h
      | FS _ _ x => fun _ _ f => f x
    end.

  Definition finArg ls (f : fin ls) : option (fin (tl ls)) :=
    match f with
      | FO _ _ => None
      | FS _ _ f' => Some f'
    end.

  Lemma fin_inj : forall z ls (x y : fin ls),
    x <> y
    -> FS z x <> FS z y.
    red; intros.
    assert (finArg (FS z x) = finArg (FS z y)) by congruence.
    simpl in *; congruence.
  Qed.

  Hint Immediate fin_inj.


  Definition finEq : forall ls (x y : fin ls), {x = y} + {x <> y}.
    refine (fix finEq ls : forall x y : fin ls, {x = y} + {x <> y} :=
      match ls return forall x y : fin ls, {x = y} + {x <> y} with
        | nil => fun x _ => match finOut x with end
        | _ :: _ => fun x y => match finOut x, finOut y with
                                 | inleft (existT x' _), inleft (existT y' _) => if finEq _ x' y' then left _ _ else right _ _
                                 | inright _, inright _ => left _ _
                                 | _, _ => right _ _
                               end
      end); clear finEq; (subst; auto; try congruence;
        match goal with
          | [ H : sigT _ |- _ ] => destruct H
        end; subst; discriminate).
  Defined.

  Global Instance EquivDec_fin ls : EqDec (fin ls) (@eq _) :=
  { equiv_dec := @finEq ls }.

  Definition dcomp_option T (a b : T) (d : dcomp a b) : option (a = b) :=
    match d with
      | Eq pf => Some pf
      | _ => None
    end.

  Global Instance Comparable_fin ls : Comparable (fin ls).
  constructor.
  refine ((fix finCmp ls (x : fin ls) : forall y : fin ls, dcomp x y :=
    match x in fin ls return forall y : fin ls, dcomp x y with
      | FO a b => fun y : fin (a :: b) =>
        @finIfz _ _ y (dcomp (FO a b)) (Eq (refl_equal _)) (fun _ => Lt _ _)
      | FS a ls r => fun y : fin (a :: ls) =>
        @finIfz _ _ y (dcomp (FS a r)) (Gt _ _)
          (fun r' => match finCmp _ r r' with
                       | Eq pf => Eq (match pf in _ = t return FS a r = FS a t with
                                        | refl_equal => refl_equal _
                                      end)

                       | Gt => Gt _ _
                       | Lt => Lt _ _
                     end)
    end) ls).
  Defined.

  Fixpoint get (ls : list A) : fin ls -> A :=
    match ls return fin ls -> A with
      | nil => fun f => match f in fin N return match N with
                                                  | nil => A
                                                  | _ => unit
                                                end with
                          | FO _ _ => tt
                          | FS _ _ _ => tt
                        end
      | x :: ls' => fun f => match f in fin N return match N with
                                                       | nil => Empty_set
                                                       | _ :: ls' => (fin ls' -> A) -> A
                                                     end with
                               | FO _ _ => fun _ => x
                               | FS _ _ f' => fun get_ls' => get_ls' f'
                             end (@get ls')
    end.

  Fixpoint liftD (ls : list A) e : forall i : fin ls, { x : fin (e ++ ls) & get x = get i } :=
    match e as e return forall i : fin ls, { x : fin (e ++ ls) & get x = get i } with
      | nil => fun x => existT _ x (refl_equal _)
      | a :: b => fun x =>
        match @liftD ls b x with
          | existT x pf =>
            existT _ (FS a x) (match pf in _ = t
                                 return get (FS a x) = t with
                                 | refl_equal => refl_equal _
                               end)
        end
    end.

  Fixpoint pf_list_simpl A b c (a : list A) : (a ++ b :: nil) ++ c = a ++ b :: c :=
    match a as a return (a ++ b :: nil) ++ c = a ++ b :: c with
      | nil => refl_equal (nil ++ b :: nil ++ c)
      | a' :: b' => match eq_sym (@pf_list_simpl A b c b') in _ = t return a' :: t = a' :: b' ++ b :: c
                      with
                      | refl_equal => refl_equal _
                    end
    end.

  Fixpoint fin_remove (U : Type) ls t ls' : forall (f : fin (ls ++ t :: ls')),
    (t = get f -> U) -> (forall f' : fin (ls ++ ls'), get f' = get f -> U) -> U :=
    match ls as ls
      return forall f : fin (ls ++ t :: ls'), (t = get f -> U) -> (forall f' : fin (ls ++ ls'), get f' = get f -> U) -> U
      with
      | nil => fun (f : fin (t :: ls')) =>
        match f in fin z
          return match z with
                   | nil => unit
                   | a :: b => (a = get f -> U) -> (forall f' : fin b, get f' = get f -> U) -> U
                 end
          with
          | FO _ _ => fun D _ => D refl_equal
          | FS _ _ f => fun _ F => F _ refl_equal
        end
      | a :: b => fun (f : fin (a :: b ++ t :: ls')) D F =>
        match finOut f with
          | inleft s =>
            @fin_remove _ _ _ _ (projT1 s)
              (match eq_sym (projT2 s) in _ = t' return (t = get t' -> U) -> (t = get (projT1 s)) -> U with
                 | refl_equal => fun x => x
               end D)
              (fun x' pf => F (FS _ x')
                match eq_sym (projT2 s) in _ = t return get (FS a x') = get t with
                  | refl_equal => pf
                end)
          | inright l => F (FO _ _) match eq_sym l in _ = t return get (FO _ _) = get t with
                                      | refl_equal => refl_equal
                                    end
        end
    end.

  Fixpoint fin_remove_range' (U : Type) ls'' ls' : forall (f : fin (ls'' ++ ls')),
    (forall x' : fin ls'', get x' = get f -> U) -> (forall f' : fin (ls'), get f' = get f -> U) -> U :=
    match ls'' as ls''
      return forall f : fin (ls'' ++ ls'), (forall x' : fin ls'', get x' = get f -> U) -> (forall f' : fin ls', get f' = get f -> U) -> U
      with
      | nil => fun (f : fin ls') => fun _ z => z f refl_equal
      | a :: b => fun (f : fin (a :: b ++  ls')) D F =>
        match finOut f with
          | inleft s =>
            @fin_remove_range' _ b ls' (projT1 s)
              (fun x' pf => D (FS _ x') match eq_sym (projT2 s) in _ = t return get (FS a x') = get t with
                                          | refl_equal => pf
                                        end)
              (fun x' pf => F x' match eq_sym (projT2 s) in _ = t return get x' = get t with
                                   | refl_equal => pf
                                 end)
          | inright l => D (FO _ _) match eq_sym l in _ = t return get (FO a b) = get t with
                                      | refl_equal => refl_equal
                                    end
        end
    end.

  Fixpoint fin_remove_range (U : Type) ls ls'' ls' : forall (f : fin (ls ++ ls'' ++ ls')),
    (forall x' : fin ls'', get x' = get f -> U) -> (forall f' : fin (ls ++ ls'), get f' = get f -> U) -> U :=
    match ls as ls
      return forall f : fin (ls ++ ls'' ++ ls'), (forall x' : fin ls'', get x' = get f -> U) -> (forall f' : fin (ls ++ ls'), get f' = get f -> U) -> U
      with
      | nil => fun (f : fin (ls'' ++ ls')) => @fin_remove_range' U ls'' ls' f
      | a :: b => fun (f : fin (a :: b ++ ls'' ++  ls')) D F =>
        match finOut f with
          | inleft s =>
            @fin_remove_range _ _ _ _ (projT1 s)
              (fun x' pf => D x' match eq_sym (projT2 s) in _ = t return get x' = get t with
                                   | refl_equal => pf
                                 end)
              (fun x' pf => F (FS _ x') match eq_sym (projT2 s) in _ = t return get (FS _ x') = get t with
                                          | refl_equal => pf
                                        end)
          | inright l => F (FO _ _)
              match eq_sym l in _ = t return get (FO _ _) = get t with
                | refl_equal => refl_equal
              end
        end
    end.


  Fixpoint liftDmid (ls ls' : list A) e : forall (i : fin (ls' ++ ls)),
    { x : fin (ls' ++ e ++ ls) & get x = get i }.
  refine (
    match ls' as ls' return forall (i : fin (ls' ++ ls)),
      { x : fin (ls' ++ e ++ ls) & get x = get i } with
      | nil => fun i => liftD e i
      | a :: b => fun i : fin (a :: b ++ ls) =>
        match finOut i with
          | inleft (existT r pf) =>
            match liftDmid ls b e r with
              | existT rr pf' =>
                @existT _ _ (FS a rr) _
            end
          | inright pf => @existT _ _ (FO _ _) _
        end
    end).
  rewrite pf; simpl; assumption.
  rewrite pf; reflexivity.
  Defined.

  Fixpoint liftDend (ls : list A) e (i : fin ls) :
    { x : fin (ls ++ e) & get x = get i } :=
    match i as i in fin ls return { x : fin (ls ++ e) & get x = get i } with
      | FO _ _ => existT _ (FO _ _) refl_equal
      | FS _ _ f =>
        match liftDend e f with
         | existT _ e => existT _ (FS _ _) e
        end
    end.

  Section liftD_Proofs.
    Variable EQ : EqDec A (@eq A).

    Lemma liftD_liftD_app : forall (a z y : list A) x0,
      projT1 (liftD y (projT1 (liftD a x0))) =
      match app_assoc_reverse y a z in (_ = t) return (fin t) with
        | eq_refl => projT1 (liftD (y ++ a) x0)
      end.
    Proof.
      induction y; simpl in *; uip_all.
        simpl in *. uip_all. reflexivity.
        simpl in *. case_eq (liftD y (projT1 (liftD a x0))).
        simpl. intros. assert (projT1 (liftD y (projT1 (liftD a x0))) = x).
        rewrite H; auto.
        rewrite IHy in H0. subst.
        destruct (liftD (y ++ a) x0). simpl. uip_all.
        generalize e e2. rewrite <- e2. uip_all. reflexivity.
    Qed.

    Lemma liftDmid_lift_nil : forall (a b : list A) x0,
      projT1 (liftDmid a b nil x0) = x0.
    Proof.
      induction b; simpl; intros; auto.
      destruct (finOut x0). destruct s. subst.
      specialize (IHb x). destruct (liftDmid a b nil x). simpl in *. subst; auto.

      subst. simpl. reflexivity.
    Qed.


    Lemma liftDmid_liftDmid_app : forall x y z a x0,
      projT1 (liftDmid (a ++ z) x y (projT1 (liftDmid z x a x0)))
      = match app_ass _ _ _ in _ = t return fin (_ ++ t) with
          | refl_equal => projT1 (liftDmid z x (y ++ a) x0)
        end.
    Proof.
      induction x.
        simpl; intros; apply liftD_liftD_app.
        intros. simpl in x0. destruct (finOut x0).

        destruct s. specialize (IHx y z a0 x1). subst. simpl in *.
        destruct (liftDmid z x a0 x1); simpl in *. destruct (liftDmid (a0 ++ z) x y x0); simpl in *.
        subst. destruct (liftDmid z x (y ++ a0) x1). simpl. uip_all. generalize e2 x2. rewrite e2.
        intros. rewrite (UIP_refl e3). reflexivity.

        subst; simpl. uip_all. generalize e. rewrite e. uip_all. reflexivity.
    Qed.
  End liftD_Proofs.


  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall x ls, B x -> hlist ls -> hlist (x :: ls).

  Definition hlist_hd (T : A) (ls : list A) (v : hlist (T :: ls)) : B T :=
    match v in hlist ls return match ls with
                                 | nil => unit
                                 | a :: _ => B a
                               end with
      | HNil => tt
      | HCons _ _ x _ => x
    end.

  Definition hlist_tl (T : A) (ls : list A) (v : hlist (T :: ls)) : hlist ls :=
    match v in hlist ls return match ls with
                                 | nil => unit
                                 | _ :: ls => hlist ls
                               end with
      | HNil => tt
      | HCons _ _ _ x => x
    end.

  Fixpoint hlist_app ll lr : hlist ll -> hlist lr -> hlist (ll ++ lr) :=
    match ll with
      | nil => fun _ x => x
      | _ :: _ => fun l r => HCons (hlist_hd l) (hlist_app (hlist_tl l) r)
    end.

  Fixpoint hlist_All ls (P : forall t, B t -> Prop) (h : hlist ls) {struct h} : Prop :=
    match h with
      | HNil => True
      | HCons _ _ a b => P _ a /\ hlist_All P b
    end.

  Variable dec : forall x (y z : B x), option (y = z).

  Definition hlistEq : forall x (y z : hlist x), option (y = z).
    refine (fix hlistEq x (y : hlist x) : forall z : hlist x, option (y = z) :=
      match y in hlist x return forall z : hlist x, option (y = z) with
        | HNil => fun z => match z in hlist x return match x return hlist x -> Type with
                                                       | nil => fun z => option (HNil = z)
                                                       | _ => fun _ => unit
                                                     end z with
                             | HNil => Some _
                             | _ => tt
                           end
        | HCons _ _ v1 y' => fun z => match z in hlist x return match x return hlist x -> Type with
                                                                  | nil => fun _ => unit
                                                                  | t :: x' => fun z => forall (v1 : B t) (y' : hlist x'),
                                                                    (forall v2, option (v1 = v2))
                                                                    -> (forall z', option (y' = z'))
                                                                    -> option (HCons v1 y' = z)
                                                                end z with
                                        | HNil => tt
                                        | HCons _ _ v2 z' => fun v1 _ dec' self => if dec' v2 then if self z' then Some _ else None else None
                                      end v1 y' (dec v1) (hlistEq _ y')
      end); clear hlistEq; abstract congruence.
  Defined.


  Variable cmp : forall x (y z : B x), dcomp y z.
  Definition hlistCmp : forall x (y z : hlist x), dcomp y z.
    refine (fix hlistCmp x (y : hlist x) : forall z : hlist x, dcomp y z :=
      match y in hlist x return forall z : hlist x, dcomp y z with
        | HNil => fun z => match z in hlist x return match x return hlist x -> Type with
                                                       | nil => fun z => dcomp HNil z
                                                       | _ => fun _ => unit
                                                     end z with
                             | HNil => Eq _
                             | _ => tt
                           end
        | HCons _ _ v1 y' => fun z => match z in hlist x return match x return hlist x -> Type with
                                                                  | nil => fun _ => unit
                                                                  | t :: x' => fun z => forall (v1 : B t) (y' : hlist x'),
                                                                    (forall v2, dcomp v1 v2)
                                                                    -> (forall z', dcomp y' z')
                                                                    -> dcomp (HCons v1 y') z
                                                                end z with
                                        | HNil => tt
                                        | HCons _ _ v2 z' => fun v1 _ cmp' self =>
                                          match cmp' v2 with
                                            | Eq _ =>
                                              match self z' with
                                                | Gt => Gt _ _
                                                | Lt => Lt _ _
                                                | Eq _ => Eq _
                                              end
                                            | Gt => Gt _ _
                                            | Lt => Lt _ _
                                          end
                                      end v1 y' (cmp v1) (hlistCmp _ y')
      end); clear hlistCmp; abstract congruence.
  Defined.

  Variable ocmp : forall x (y z : B x), option (dcomp y z).
  Fixpoint hlistOCmp x (y : hlist x) : forall (z : hlist x), option (dcomp y z).
    refine (
      match y as y in hlist x return forall z : hlist x, option (dcomp y z) with
        | HNil => fun z =>
          match z in hlist x return match x return hlist x -> Type with
                                      | nil => fun z => option (dcomp HNil z)
                                      | _ => fun _ => unit
                                    end z with
            | HNil => Some (Eq _)
            | _ => tt
          end
        | HCons _ _ v1 y' => fun z =>
          match z in hlist x return match x return hlist x -> Type with
                                      | nil => fun _ => unit
                                      | t :: x' => fun z => forall (v1 : B t) (y' : hlist x'),
                                        (forall v2, option (dcomp v1 v2))
                                        -> (forall z', option (dcomp y' z'))
                                        -> option (dcomp (HCons v1 y') z)
                                    end z with
            | HNil => tt
            | HCons _ _ v2 z' => fun v1 _ cmp' self =>
              match cmp' v2 with
                | None =>
                  match self z' with
                    | None => None
                    | Some Gt => Some (Gt _ _)
                    | Some Lt => Some (Lt _ _)
                    | Some (Eq _) => None
                  end
                | Some (Eq _) =>
                  match self z' with
                    | None => None
                    | Some Gt => Some (Gt _ _)
                    | Some Lt => Some (Lt _ _)
                    | Some (Eq _) => Some (Eq _)
                  end
                | Some Gt => Some (Gt _ _)
                | Some Lt => Some (Lt _ _)
              end
          end v1 y' (ocmp v1) (hlistOCmp _ y')
      end); clear hlistOCmp; abstract congruence.
  Defined.

  Fixpoint hlist_get (ls : list A) (i : fin ls) : hlist ls -> B (get i) :=
    match i in fin ls return hlist ls -> B (get i) with
      | FO _ _ => fun hl => hlist_hd hl
      | FS _ _ f' => fun hl => hlist_get f' (hlist_tl hl)
    end.

  Section hlist_Proofs.
    Variable EQ : EqDec A (@eq A).
    Lemma hlist_nil_only : forall (h : hlist nil),
      h = HNil.
    Proof.
      intros.
      change h with (match refl_equal in _ = t return hlist t with
                       | refl_equal => h
                     end).
      generalize (refl_equal (@nil A)). generalize h.
      assert (forall k (h : hlist k) (e : k = nil),
        match e in (_ = t) return (hlist t) with
          | eq_refl => h
        end = HNil).
      destruct h0.
      uip_all. reflexivity.
      congruence.
      eauto.
    Qed.

    Lemma hlist_eta : forall a b (h : hlist (a :: b)),
      h = HCons (hlist_hd h) (hlist_tl h).
    Proof.
      intros.
      assert (forall k (h : hlist k) (e : k = a :: b),
        match e in (_ = t) return (hlist t) with
          | eq_refl => h
        end = HCons (hlist_hd match e in _ = t return hlist t with
                                | eq_refl => h
                              end)
        (hlist_tl match e in _ = t return  hlist t with
                    | eq_refl => h
                  end)).
      destruct h0. congruence.
      intros. inversion e. subst.
      generalize e. uip_all. reflexivity.

      specialize (H _ h (refl_equal _)). assumption.
    Qed.

    Theorem hlist_get_lift : forall ls ls' ls'' (f : fin (ls ++ ls'')) G G' G'',
      hlist_get f (hlist_app G G'') =
      match liftDmid ls'' ls ls' f with
        | existT f' pf =>
          match pf in _ = t return B t with
            | refl_equal =>
              hlist_get f' (hlist_app G (hlist_app G' G''))
          end
      end.
    Proof.
      induction ls. simpl. intros. unfold liftDmid; simpl.
        Focus.
        generalize dependent ls'. induction ls'; simpl; auto.
          intros. specialize (IHls' (hlist_tl G')). rewrite IHls'. destruct (liftD ls' f).
          simpl. generalize (hlist_get x (hlist_app (hlist_tl G') G'')). generalize e. rewrite e.
          intros. rewrite (UIP_refl e0). reflexivity.

        intros. simpl in f. destruct (finOut f). destruct s; subst. simpl.
        specialize (@IHls ls' _ x (hlist_tl G) G' G''). rewrite IHls. clear IHls.
        destruct (liftDmid ls'' ls ls' x). reflexivity.
        subst. reflexivity.
    Qed.

    Theorem hlist_get_lift_end : forall ls' G' ls (f : fin ls) G,
      hlist_get f G =
      match liftDend ls' f with
        | existT f' pf =>
          match pf in _ = t return B t with
            | refl_equal =>
              hlist_get f' (hlist_app G G')
          end
      end.
    Proof.
      clear dec cmp ocmp.
      induction f; simpl; auto.
      destruct f; simpl in *. auto.
      intros. rewrite IHf. clear IHf. destruct (liftDend ls' f).
      generalize e. rewrite <- e. uip_all. auto.
    Qed.

    Lemma hlist_get_remove_range' : forall U a b (A : hlist a) (B' : hlist b) x P
      (D : forall x' : fin a, get x' = get x -> U) F,
      (forall x' (pf : get x' = get x),
        hlist_get x (hlist_app A B') =
          match pf in _ = z return B z with
            | refl_equal => hlist_get x' A
          end ->
        P (D x' pf)) ->
      (forall x' pf,
        hlist_get x (hlist_app A B') =
          match pf in _ = t return B t with
            | refl_equal => hlist_get x' B'
          end ->
        P (F x' pf)) ->
      P (@fin_remove_range' U a b x D F).
    Proof.
      clear dec cmp ocmp.
      induction a; simpl; intros; eauto.
      destruct (finOut x) as [ [ ? ? ] | ? ]; subst; simpl; eauto.
      eapply IHa; eauto.
    Qed.


    Theorem hlist_get_remove_range : forall U a b c (A : hlist a) (B' : hlist b) (C : hlist c) x P (D : forall x' : fin b, get x' = get x -> U) F,
      (forall x' (pf : get x' = get x),
        hlist_get x (hlist_app A (hlist_app B' C)) =
          match pf in _ = z return B z with
            | refl_equal => hlist_get x' B'
          end ->
        P (D x' pf)) ->
      (forall x' pf,
        hlist_get x (hlist_app A (hlist_app B' C)) =
          match pf in _ = t return B t with
            | refl_equal => hlist_get x' (hlist_app A C)
          end ->
        P (F x' pf)) ->
      P (@fin_remove_range U a b c x D F).
    Proof.
      clear dec cmp ocmp.
      induction a; simpl; intros.
      eapply hlist_get_remove_range'; eauto.
      destruct (finOut x); subst; simpl.
        destruct s; subst; simpl. eapply IHa; eauto.
        eapply X0. auto.
    Qed.

  End hlist_Proofs.

  Fixpoint absAll (ls : list A) :
    (hlist ls -> Type) -> Type :=
    match ls return (hlist ls -> Type) -> Type with
      | nil => fun R => R (HNil)
      | a :: b => fun R =>
        forall x : B a, absAll (fun y => R (HCons x y))
    end.

  Fixpoint hlistDestruct (ls : list A) (args : hlist ls) {struct args}
    : forall K : hlist ls -> Type, absAll K -> K args :=
      match
        args as args0 in hlist ls0
          return (forall K : hlist ls0 -> Type, absAll K -> K args0)
        with
        | HNil =>
          fun (K : hlist nil -> Type) (cc : absAll K) => cc
        | HCons x0 ls0 x args =>
          fun (K : hlist (x0 :: ls0) -> Type) (cc : absAll K) =>
            hlistDestruct args
            (fun y : hlist ls0 => K (HCons x y))
            (cc x)
      end.

  Variable a : A.
  Variable b : B a.
  Fixpoint hlistIn (ls : list A) : hlist ls -> Prop :=
    match ls as ls return hlist ls -> Prop with
      | nil => fun _ => False
      | hd :: tl => fun hl =>
        (exists pf : a = hd, hlist_hd hl = match pf in _ = t return B t with
                                             | refl_equal => b
                                           end)
        \/ hlistIn (hlist_tl hl)
    end.

End fin.

Implicit Arguments FO [A x ls].
Implicit Arguments FS [A x ls].
Implicit Arguments finIfz [A t ls].

Implicit Arguments get [A].
Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].

Section hlist_map.
  Variable A : Type.
  Variable F : A -> Type.
  Variable G : A -> Type.
  Variable ff : forall x, F x -> G x.

  Fixpoint hlist_map (ls : list A) (hl : hlist F ls) {struct hl} : hlist G ls :=
    match hl in @hlist _ _ ls return hlist G ls with
      | HNil => HNil
      | HCons _ _ hd tl =>
        HCons (ff hd) (hlist_map tl)
    end.
End hlist_map.

Section hlist_fold2.
  Variables T U V : Type.
  Variables F G : T -> Type.
  Variable f : U -> forall t : T, F t -> G t -> U.

  Fixpoint hlist_fold2 ls (l : hlist F ls) {struct l} : hlist G ls -> U -> U :=
    match l in hlist _ ls
      return hlist G ls -> U -> U
      with
      | HNil => fun _ acc => acc
      | HCons _ _ fr hr => fun r acc =>
        hlist_fold2 hr (hlist_tl r) (f acc fr (hlist_hd r))
    end.
End hlist_fold2.

Export Decidables.
