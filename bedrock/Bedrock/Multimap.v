Require Import Coq.FSets.FMapInterface Coq.FSets.FMapFacts.
Require Import Coq.Lists.List.
Require Import Bedrock.NatMap.
Require Coq.Sorting.Permutation.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (FM : WS).
  Module FACTS := FMapFacts.WFacts_fun FM.E FM.
  Module PROPS := FMapFacts.WProperties_fun FM.E FM.
  Module MFACTS := NatMap.MoreFMapFacts FM.

  Lemma find_Empty : forall T (m : FM.t T) x,
    FM.Empty m -> FM.find x m = None.
  Proof.
    intros.
    apply PROPS.F.not_find_in_iff.
    unfold FM.In, FM.Empty in *. specialize (H x).
    intro. destruct H0. eapply H. eauto.
  Qed.

  Section typed.
    Variable T : Type.

    Definition mmap := FM.t (list T).

    Definition mmap_Equiv : mmap -> mmap -> Prop :=
      FM.Equiv (@Permutation.Permutation _).

    Global Instance Equivalence_mmap_Equiv : RelationClasses.Equivalence mmap_Equiv.
    Proof.
      unfold mmap_Equiv. econstructor; eauto with typeclass_instances.
    Qed.

    Definition empty : mmap := FM.empty _.

    Definition mmap_add (k : FM.key) (v : T) (m : mmap) : mmap :=
      match FM.find k m with
        | None => FM.add k (v :: nil) m
        | Some v' => FM.add k (v :: v') m
      end.

    Hint Constructors Permutation.Permutation : perms.
    Ltac think :=
      repeat (rewrite FACTS.add_o in * ||
        match goal with
          | [ H : FM.MapsTo _ _ _ |- _ ] => apply FACTS.find_mapsto_iff in H
          | [ H : context [ FM.E.eq_dec ?X ?Y ] |- _ ] => destruct (FM.E.eq_dec X Y)
          | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *
          | [ H : ?X = Some _ , H' : ?X = Some _ |- _ ] =>
            rewrite H in H'; inversion H'; clear H'; subst
          | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
        end); eauto with perms.


    Global Add Parametric Morphism : mmap_add with
      signature (FM.E.eq ==> @eq _ ==> mmap_Equiv ==> mmap_Equiv)
      as mmap_add_mor.
    Proof.
      unfold mmap_Equiv, mmap_add, FM.Equiv. intros. destruct H0.
      case_eq (FM.find x x0); case_eq (FM.find y y1); intros;
        rewrite H in * ;
        repeat match goal with
                 | [ H : FM.find _ _ = _ |- _ ] =>
                   apply FACTS.find_mapsto_iff in H ||
                   apply FACTS.not_find_in_iff in H
                 | [ |- _ ] =>
                   rewrite H in *
               end.
      { generalize (@H1 _ _ _ H3 H2).
        intuition (try rewrite H in *).
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H5.
        destruct H5; auto. right. eapply H0. auto.
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H5.
        destruct H5; auto. right. eapply H0. auto.
        think; eauto.
        eapply H1. eapply FACTS.find_mapsto_iff; eauto.  eapply FACTS.find_mapsto_iff; eauto. }
      { exfalso. apply H2. eapply H0. eexists; eauto. }
      { exfalso. apply H3. eapply H0. eexists; eauto. }
      { intuition; try rewrite H in *.
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H4.
        destruct H4; auto. right. eapply H0; eauto.
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H4.
        destruct H4; auto. right. eapply H0; eauto.
        think. eauto.
        eapply H1; eapply FACTS.find_mapsto_iff; eauto. }
    Qed.

    Lemma mmap_add_comm : forall k1 v1 k2 v2 m,
      mmap_Equiv (mmap_add k1 v1 (mmap_add k2 v2 m)) (mmap_add k2 v2 (mmap_add k1 v1 m)).
    Proof.
      unfold mmap_Equiv, mmap_add; intros.
      repeat match goal with
               | [ |- _ ] => rewrite FACTS.add_o in *
               | [ H : _ = _ |- _ ] => rewrite H in *
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
               | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *; clear H
               | [ |- context [ FM.find ?X ?Y ] ] =>
                 match Y with
                   | match _ with | _ => _ end => fail 1
                   | _ => case_eq (FM.find X Y)
                 end; intros
             end; try solve [ exfalso; auto ];
      repeat match goal with
               | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                 destruct (FM.E.eq_dec X Y)
             end; try solve [ exfalso; auto ]; unfold FM.Equiv;
      intuition;
        try solve [ repeat match goal with
                             | [ |- FM.In _ _ ] => apply FACTS.add_in_iff
                             | [ H : FM.In _ _ |- _ ] =>
                               apply FACTS.add_in_iff in H; destruct H
                             | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *
                             | [ |- _ \/ _ ] => solve [ left; auto ] || right; auto
                           end ];
        think; try solve [ congruence | exfalso; auto ].
    Qed.

    Definition mmap_extend (k : FM.key) (v : list T) (m : mmap) : mmap :=
      match FM.find k m with
        | None => FM.add k v m
        | Some v' => FM.add k (v ++ v') m
      end.

    Global Add Parametric Morphism : mmap_extend with
      signature (FM.E.eq ==> (@Permutation.Permutation _) ==> mmap_Equiv ==> mmap_Equiv)
      as mmap_extend_mor.
    Proof.
      unfold mmap_Equiv, mmap_extend, FM.Equiv. intros. destruct H1.
      case_eq (FM.find x x1); case_eq (FM.find y y1); intros;
        rewrite H in * ;
        repeat match goal with
                 | [ H : FM.find _ _ = _ |- _ ] =>
                   apply FACTS.find_mapsto_iff in H ||
                   apply FACTS.not_find_in_iff in H
                 | [ |- _ ] =>
                   rewrite H in *
               end.
      { generalize (@H2 _ _ _ H4 H3).
        intuition (try rewrite H in *).
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H6.
        destruct H6; auto. right. eapply H1. auto.
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H6.
        destruct H6; auto. right. eapply H1. auto.
        think; eauto.
        eapply Permutation.Permutation_app; eauto.
        eapply H2. eapply FACTS.find_mapsto_iff; eauto.  eapply FACTS.find_mapsto_iff; eauto. }
      { exfalso. apply H3. eapply H1. eexists; eauto. }
      { exfalso. apply H4. eapply H1. eexists; eauto. }
      { intuition; try rewrite H in *.
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H5.
        destruct H5; auto. right. eapply H1; eauto.
        apply FACTS.add_in_iff; apply FACTS.add_in_iff in H5.
        destruct H5; auto. right. eapply H1; eauto.
        think; eauto.
        eapply H2; eapply FACTS.find_mapsto_iff; eauto. }
    Qed.

    Lemma Proper_mmap_extend : Proper (FM.E.eq ==> eq ==> FM.Equal ==> FM.Equal) mmap_extend.
    Proof.
      unfold mmap_extend.
      repeat (red; intros; subst). rewrite H; rewrite H0. destruct (FM.find (elt:=list T) y y1); rewrite H; rewrite H0; auto.
    Qed.

    Lemma transpose_neqkey_mmap_extend : PROPS.transpose_neqkey FM.Equal mmap_extend.
    Proof.
      unfold mmap_extend. repeat (red; intros; subst).
      (repeat match goal with
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                | [ H : _ = _ |- _ ] => rewrite H
                | [ H : _ = _ |- _ ] => rewrite H in *
                | [ H : FM.E.eq _ _ |- _ ] => rewrite H
                | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *
                | [ H : context [ FM.find _ _ ] |- _ ] =>
                  rewrite FACTS.add_o in H
                | [ |- context [ FM.find ?k ?a ] ] =>
                  match a with
                    | match _ with
                        | Some _ => _
                        | None => _
                      end => fail 1
                    | _ => case_eq (FM.find k a); intros
                  end
              end);
      repeat match goal with
               | [ H : ~ FM.E.eq ?X ?X |- _ ] => exfalso; apply H; reflexivity
               | [ H : FM.E.eq _ _ |- _ ] => rewrite H
               | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *
               | [ H : Some _ = Some _ |- _ ] => inversion H ; clear H; subst
               | [ H : context [ FM.E.eq_dec ?A ?B ] |- _ ] =>
                 destruct (FM.E.eq_dec A B); try congruence
             end.
    Qed.
    Existing Instance Proper_mmap_extend.
    Existing Class PROPS.transpose_neqkey.
    Existing Instance transpose_neqkey_mmap_extend.

    Definition mmap_join : mmap -> mmap -> mmap :=
      FM.fold mmap_extend.

    Lemma mmap_join_o : forall (a b : mmap) x,
      FM.find x (mmap_join a b) =
      match FM.find x a with
        | Some a =>
          match FM.find x b with
            | Some b => Some (a ++ b)
            | None => Some a
          end
        | None => FM.find x b
      end.
    Proof.
      clear. unfold mmap_join.
      do 2 intro. apply PROPS.map_induction with (m := a); intros.
      rewrite PROPS.fold_Empty; eauto with typeclass_instances.
      symmetry.
      repeat rewrite find_Empty by assumption; auto.

      rewrite PROPS.fold_Add; try solve [ clear; eauto with typeclass_instances ].
      unfold mmap_extend at 1. rewrite H.
      apply PROPS.F.not_find_in_iff in H0. rewrite H0.

      specialize (H1 x0). rewrite H1.
      case_eq (FM.find x b); intros; rewrite FACTS.add_o; destruct (FM.E.eq_dec x x0);
        try rewrite H;
          repeat match goal with
                   | [ H : FM.E.eq _ _ |- _ ] => rewrite H in *; clear H
                   | [ H : ~FM.E.eq ?X ?X |- _ ] => exfalso; apply H; reflexivity
                   | [ H : _ = _ |- _ ] => rewrite H
                   | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                     destruct (FM.E.eq_dec X Y); try congruence
                   | _ => rewrite FACTS.add_o in *
                 end.
    Qed.

    Lemma mmap_join_remove_acc : forall k (a b : mmap),
      ~FM.In k a ->
      FM.Equal (FM.remove k (mmap_join a b)) (mmap_join a (FM.remove k b)).
    Proof.
      unfold FM.Equal. intros.
      repeat (rewrite FACTS.remove_o || rewrite mmap_join_o).
      destruct (FM.E.eq_dec k y); try reflexivity.
      apply PROPS.F.not_find_in_iff in H.
      rewrite e in *.
      rewrite H. reflexivity.
    Qed.

  End typed.

  Definition mmap_map T U (F : T -> U) : mmap T -> mmap U :=
    FM.map (map F).

  Definition mmap_mapi T U (F : FM.key -> T -> U) : mmap T -> mmap U :=
    FM.mapi (fun k => map (F k)).


End Make.
