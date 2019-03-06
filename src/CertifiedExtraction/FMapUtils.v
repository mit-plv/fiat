Require Import Coq.FSets.FMaps.
Require Import CertifiedExtraction.PureUtils.

Module WMoreFacts_fun (E:DecidableType) (Import M:WSfun E).
  Module Export BasicFacts := WFacts_fun E M.
  Module Export BasicProperties := WProperties_fun E M.

  Set Implicit Arguments.

  Notation "∅" := (empty _) : map_scope.
  Notation "A  ∈  B" := (In A B) (at level 10, no associativity) : map_scope.
  Notation "A  ∉  B" := (not (In A B)) (at level 10, no associativity) : map_scope.

  Notation "[ k  |>  v ]  ::  m" :=
    (add k v m) (at level 21, right associativity, arguments at next level) : map_scope.
  Local Open Scope map_scope.

  Lemma remove_mapsto :
    forall (elt : Type) (m : t elt) (x y : key) (e : elt),
      MapsTo y e (remove (elt:=elt) x m) ->
      (not (E.eq x y)) /\ MapsTo y e m.
  Proof.
    intros; rewrite <- remove_mapsto_iff; assumption.
  Qed.

  Lemma MapsTo_In :
    forall {A: Type} key (val: A) tree,
      MapsTo key val tree -> In key tree.
  Proof.
    intros; eexists; eassumption.
  Qed.

  Lemma In_MapsTo :
    forall A m key,
      In key m ->
      exists (value: A), MapsTo key value m.
  Proof.
    intros A m key H;
    apply in_find_iff in H.
    destruct (find key m) as [value | ] eqn:eq_option;
      try rewrite <- find_mapsto_iff in eq_option;
      intuition eauto.
  Qed.

  Lemma add_remove_cancel:
    forall (elt : Type) (k k' : key) (v : elt) (m : t elt),
      k = k' -> Equal ([k |> v] :: remove k' m) ([k |> v] :: m).
  Proof.
    intros.
    rewrite Equal_mapsto_iff.
    intros *; map_iff; intuition (subst; tauto).
  Qed.

  Ltac msubst :=
    subst;
    repeat match goal with
           | [ H: E.eq ?k ?k', H': E.eq ?k' ?k |- _ ] => clear H
           | [ H: E.eq ?k ?k' |- MapsTo ?k _ _ ] => rewrite H
           | [ H: E.eq ?k ?k', H': MapsTo ?k _ _ |- _ ] => rewrite H in H'
           | [ H: E.eq ?k ?k' |- In ?k _ ] => rewrite H
           | [ H: E.eq ?k ?k', H': not (In ?k _) |- _ ] => rewrite H in H'
           | [ H: E.eq ?k ?k', H': (In ?k _ -> False) |- _ ] => rewrite H in H'
           | [ H: E.eq ?k ?k |- _ ] => clear H
           end.

  Ltac map_iff_in H :=
    repeat match goal with
           | _ => rewrite add_mapsto_iff in H
           | _ => rewrite add_in_iff in H
           | _ => rewrite remove_mapsto_iff in H
           | _ => rewrite remove_in_iff in H
           | _ => rewrite empty_mapsto_iff in H
           | _ => rewrite empty_in_iff in H
           | _ => rewrite map_mapsto_iff in H
           | _ => rewrite map_in_iff in H
           | _ => rewrite mapi_in_iff in H
           end.

  Lemma remove_notIn_Equal :
    forall (elt : Type) (k : key) (m : t elt),
      k ∉ m -> Equal (remove k m) m.
  Proof.
    intros;
    rewrite Equal_mapsto_iff;
    intros *; map_iff;
    repeat match goal with
           | _ => progress msubst
           | _ => progress intuition
           | [ H: MapsTo _ _ _ |- _ ] => learn (MapsTo_In H)
           end.
  Qed.

  (* Lemma remove_redundant_cancel : (* duplicate of remove_notIn_Equal *) *)
  (*   forall elt k fmap, *)
  (*     k ∉ fmap -> *)
  (*     Equal (elt:=elt) (remove k fmap) fmap. *)
  (* Proof. *)
  (*   intros ** k'; rewrite remove_o; *)
  (*   destruct (E.eq_dec k k'). *)
  (*   + rewrite <- e; symmetry; rewrite <- not_find_in_iff; assumption. *)
  (*   + reflexivity. *)
  (* Qed. *)

  Lemma remove_add_comm:
    forall (elt : Type) (k k' : M.key) (v' : elt) (m : M.t elt),
      not (E.eq k k') ->
      Equal (remove k (add k' v' m))
            (add k' v' (remove k m)).
  Proof.
    intros.
    rewrite Equal_mapsto_iff.
    intros *; map_iff.
    destruct (E.eq_dec k' k0); msubst;
    intuition subst;
    repeat match goal with
           | _ => progress msubst
           | _ => progress intuition
           | [ H: MapsTo _ _ _ |- _ ] => learn (MapsTo_In H)
           end.
    eauto using E.eq_trans, E.eq_sym.
  Qed.

  Lemma remove_add_cancel:
    forall (elt : Type) (k k' : key) (v : elt) (m : t elt),
      k ∉ m ->
      k = k' ->
      Equal (remove k' ([k |> v] :: m)) m.
  Proof.
    intros.
    rewrite Equal_mapsto_iff.
    intros *; map_iff.
    destruct (E.eq_dec k' k0); msubst;
    intuition subst;
    repeat match goal with
           | _ => progress msubst
           | _ => progress intuition
           | [ H: MapsTo _ _ _ |- _ ] => learn (MapsTo_In H)
           end.
  Qed.

  Lemma add_redundant_cancel:
    forall (elt : Type) (k : key) (v : elt) (m : t elt),
      MapsTo k v m -> Equal m ([k |> v] :: m).
  Proof.
    intros.
    rewrite Equal_mapsto_iff.
    intros *; map_iff.

    match goal with
    | [ k: key, k': key |- _ ] => destruct (E.eq_dec k k')
    end;
      repeat match goal with
             | _ => congruence
             | _ => progress msubst
             | [ H: MapsTo ?k ?v ?m, H': MapsTo ?k ?v' ?m |- _ ] => learn (MapsTo_fun H H')
             | _ => intuition
             end.
  Qed.

  Lemma remove_remove_redundant :
    forall elt k fmap,
      Equal (@remove elt k (remove k fmap)) (remove k fmap).
  Proof.
    intros; apply remove_notIn_Equal.
    eauto using remove_1, E.eq_refl.
  Qed.

  Lemma MapsTo_remove :
    forall {av} k k' v (m: t av),
      MapsTo k v (remove k' m) -> MapsTo k v m.
  Proof.
    intros * H; map_iff_in H.
    intuition eauto using MapsTo_In.
  Qed.

  Lemma In_remove :
    forall {av} k k' (m: t av),
      k ∈ (remove k' m) -> k ∈ m.
  Proof.
    intros * H; apply In_MapsTo in H; destruct H; eauto using MapsTo_remove, MapsTo_In.
  Qed.

  Lemma In_add :
    forall {av} k k' v (m: t av),
      k = k' ->
      k ∈ (add k' v m).
  Proof.
    intros; subst; map_iff; eauto.
  Qed.

  Lemma In_remove_neq: forall {av} k k' m,
      k ∈ (@remove av k' m) ->
      k <> k'.
  Proof.
    intros * H; apply In_MapsTo in H; destruct H; map_iff_in H.
    intuition. rewrite H0 in *; intuition.
  Qed.

  Lemma MapsTo_add_eq_inv :
    forall T {k v v' m},
      @MapsTo T k v' (add k v m) ->
      v = v'.
  Proof.
    intros *.
    map_iff; intros.
    intuition.
    exfalso; eauto using E.eq_refl.
  Qed.

  Lemma MapsTo_NotIn_inv :
    forall T {k k' v m},
      not (In k m) ->
      @MapsTo T k' v m ->
      k <> k'.
  Proof.
    intros * ? maps_to;
    destruct (E.eq_dec k k'); subst;
    apply MapsTo_In in maps_to;
    msubst; congruence.
  Qed.

  Lemma In_remove_inv:
    forall {av : Type} {k k' : key} {m : t av},
      k ∉ m -> k ∉ (@remove av k' m).
  Proof.
    intros; red; intros h; apply In_remove in h; congruence.
  Qed.

  Lemma NotIn_add :
    forall {elt k k'} {v: elt} {m},
      k ∉ (add k' v m) -> k ∉ m.
  Proof.
    intros.
    rewrite add_in_iff in H.
    tauto.
  Qed.

  Lemma MapsTo_add_remove :
    forall {elt k} {v: elt} {m},
      MapsTo k v m ->
      Equal m (add k v (remove k m)).
  Proof.
    intros; rewrite Equal_mapsto_iff;
    intros k' v'; destruct (E.eq_dec k k'); msubst; map_iff; split; intros;
    try assert (v = v') by eauto using MapsTo_fun; subst;
    map_iff; intuition; subst; eauto.
  Qed.

  Lemma remove_trickle :
    forall {elt : Type} (k k' : M.key) (v' : elt) (m : M.t elt),
      k = k' ->
      Equal (remove k ([k' |> v']::m)) (remove k m).
  Proof.
    intros.
    rewrite Equal_mapsto_iff; intros; map_iff.
    intuition (subst; congruence).
  Qed.

  Ltac rewrite_in equality target :=
    let h := fresh in
    pose proof target as h;
      setoid_rewrite equality in h;
      clear dependent target;
      rename h into target.

  Ltac normalize :=
    match goal with
    | [  |- context[find ?k (add ?k ?v ?m)] ] => rewrite (@add_eq_o _ m k k v eq_refl) by reflexivity
    | [ H: context[find ?k (add ?k ?v ?m)] |- _ ] => may_touch H; rewrite (@add_eq_o _ m k k v eq_refl) in H by reflexivity
    | [ H: ?k <> ?k'    |- context[find ?k (add ?k' _ _)] ] => rewrite add_neq_o by congruence
    | [ H: ?k <> ?k', H': context[find ?k (add ?k' _ _)] |- _ ] => may_touch H; rewrite add_neq_o in H' by congruence
    | [ H: ?k' <> ?k    |- context[find ?k (add ?k' _ _)] ] => rewrite add_neq_o by congruence
    | [ H: ?k' <> ?k, H': context[find ?k (add ?k' _ _)] |- _ ] => may_touch H; rewrite add_neq_o in H' by congruence
    | [ H: ?k <> ?k' |- context[find ?k (remove ?k' ?m)] ] => rewrite (remove_neq_o m (x := k') (y := k)) by congruence
    | [ H: ?k' <> ?k |- context[find ?k (remove ?k' ?m)] ] => rewrite (remove_neq_o m (x := k') (y := k)) by congruence

    | [ |-  context[remove ?k (add ?k ?v ?m)] ]     => rewrite (@remove_trickle _ k k v m eq_refl) by congruence
    | [ H: context[remove ?k (add ?k ?v ?m)] |- _ ] => may_touch H; rewrite (@remove_trickle _ k k v m eq_refl) in H by congruence
    | [ H: ?k' <> ?k    |- context[remove ?k (add ?k' ?v ?m)] ]     => rewrite (@remove_add_comm _ k k' v m) by congruence
    | [ H: ?k' <> ?k, H': context[remove ?k (add ?k' ?v ?m)] |- _ ] => may_touch H; rewrite (@remove_add_comm _ k k' v m) in H' by congruence
    | [ H: ?k <> ?k'    |- context[remove ?k (add ?k' ?v ?m)] ]     => rewrite (@remove_add_comm _ k k' v m) by congruence
    | [ H: ?k <> ?k', H': context[remove ?k (add ?k' ?v ?m)] |- _ ] => may_touch H; rewrite (@remove_add_comm _ k k' v m) in H' by congruence
    | [ H': ?k ∉ ?m   |- context[remove ?k ?m] ]     => rewrite (remove_notIn_Equal H') by congruence
    | [ H': ?k ∉ ?m, H: context[remove ?k ?m] |- _ ] => may_touch H; rewrite (remove_notIn_Equal H') in H by congruence

    | [ H: Equal ?st ?st |- _ ] => clear dependent H
    | [ H: Equal ?st ?st', H': context[?st] |- _ ] => rewrite_in H H'
    | [ H: Equal ?st ?st' |- context[?st] ] => rewrite H
    | [ H: find ?k ?m = Some ?v |- _ ] => apply find_2 in H
    | [ H: MapsTo ?k ?v ?m |- context[find ?k ?m] ] => rewrite (find_1 H)
    | [ H: MapsTo ?k ?v ?m, H': context[find ?k ?m] |- _ ] => may_touch H'; rewrite_in (find_1 H) H'
    | [ H: MapsTo ?k ?v ?m, H': MapsTo ?k ?v' ?m |- _ ] => learn (MapsTo_fun H H')
    | [ H: MapsTo ?k ?v (add ?k ?v' ?m) |- _ ] => learn (MapsTo_add_eq_inv H)
    | [ H: MapsTo ?k ?v (add ?k' ?v' ?m), H': ?k' <> ?k |- _ ] => learn (add_3 H' H)

    | [ H: find _ _ = Some _ |- _ ] => rewrite <- find_mapsto_iff in H
    | [ H: find _ _ = None |- _ ] => rewrite <- not_find_in_iff in H

    | [ H: ?k ∉ (add _ _ _) |- _ ] => learn (NotIn_add H)
    | [ H: ?k ∉ ?m, H': MapsTo ?k _ ?m |- _ ] => learn (MapsTo_In H')
    | [ H: ?k ∉ ?m, H': MapsTo ?k' _ ?m |- _ ] => learn (MapsTo_NotIn_inv H H')
    | [ H: ?k ∉ ?st |- ?k ∉ (remove ?k' ?st) ] => eapply (In_remove_inv H); solve [eauto]

    | [ H: MapsTo ?k ?v (remove ?k' _) |- _ ] => learn (remove_3 H)
    | [ H: ?k ∉ (remove ?k' ?m), H': ?k' <> ?k |- _ ] => rewrite remove_neq_in_iff in H by congruence
    | [ H: ?k ∉ (remove ?k' ?m), H': ?k <> ?k' |- _ ] => rewrite remove_neq_in_iff in H by congruence
    end.

  Ltac repeat_rec tac :=
    (progress repeat tac); try (repeat_rec tac).

  Tactic Notation "Repeat" tactic(tac) :=
    repeat_rec tac.

  Ltac decide_mapsto :=
    map_iff; intuition congruence.

  Ltac unfold_head_until term target :=
    let hd := head_constant term in
    match hd with
    | target => constr:(term)
    | _ => let reduced := (eval cbv beta iota delta [hd] in term) in
          unfold_head_until reduced target
    end.

  Ltac decide_mapsto_maybe_instantiate :=
    Repeat (idtac;
             match goal with (* Recursive repeat for things that are only solvable after instantiating properly *)
             | _ => eassumption
             | _ => progress autounfold with MapUtils_unfold_db
             | [  |- ?a <> ?b ] => discriminate
             | [ H: ?a = ?b |- context[?a] ] => rewrite H
             | [  |- find ?k ?m = Some ?v ] => apply find_1
             | [  |- MapsTo ?k ?v (add ?k' ?v' ?m) ] => apply add_1; reflexivity
             | [  |- MapsTo ?k ?v (add ?k' ?v' ?m) ] => apply add_2
             | [  |- MapsTo ?k ?v ?m ] => let reduced := unfold_head_until m @add in
                                        change m with reduced
             end).

  Lemma NotIn_noteq :
    forall {A} k k' v (tail: t A),
      ~ (E.eq k k') ->
      k ∉ tail ->
      k ∉ (add k' v tail).
  Proof.
    intros; rewrite add_in_iff; intuition.
  Qed.

  Lemma NotIn_empty :
    forall {A} k,
      k ∉ (empty A).
  Proof.
    intros; rewrite empty_in_iff; intuition.
  Qed.

  Ltac not_evar x :=
    first [ is_evar x; fail 1 | idtac ].

  Ltac decide_not_in :=
    progress repeat match goal with
                    | |- ?k ∉ (empty _) => not_evar k; apply NotIn_empty
                    | |- ?k ∉ ?m => not_evar k; not_evar m; apply NotIn_noteq
                    | |- _ => discriminate
                    | |- _ => congruence
                    end.

  Ltac reduce_or_fallback term continuation fallback :=
    match nat with
    | _ => let term' := (eval red in term) in let res := continuation term' in constr:(res)
    | _ => constr:(fallback)
    end.

  Ltac find_fast value fmap :=
    match fmap with
    | @empty _       => constr:(@None key)
    | add ?k ?v _    => let eq := constr:(eq_refl v : v = value) in
                       constr:(Some k)
    | add ?k _ ?tail => let ret := find_fast value tail in constr:(ret)
    | ?other         => let ret := reduce_or_fallback fmap ltac:(fun reduced => find_fast value reduced) (@None key) in
                       constr:(ret)
    end.

  Ltac matches_pattern observation pattern :=
    constr:(eq_refl observation: observation = pattern _).

  Ltac find_pattern pattern fmap :=
    match fmap with
    | @empty _       => constr:(@None key)
    | add ?k ?v _    => let pr := matches_pattern v pattern  in
                       constr:(Some k)
    | add ?k _ ?tail => let ret := find_pattern pattern tail in constr:(ret)
    | ?other         => let ret := reduce_or_fallback fmap ltac:(fun reduced => find_pattern pattern reduced) (@None key) in
                       constr:(ret)
    end.
End WMoreFacts_fun.
