(* Require Import Bedrock.Platform.Facade.Examples.FiatADTs. *)
(* Require Export Bedrock.Platform.Facade.Notations. *)
Require Export Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.StringMapFacts Bedrock.Platform.Cito.SyntaxExpr Bedrock.Memory.
Require Export Bedrock.Platform.Facade.DFacade.
(* Require Export FacadeNotations. *)
(* Require Import FiatToFacade.Compiler. *)

(* Require Import Superset. *)

(* Require Import BedrockUtilities. *)
(* Require Import Utf8. *)

Require Import Computation.Core.
Require Import ADTRefinement.
Require Import ADTRefinement.GeneralRefinements.

(* Definition ADTEquiv s A B (r: @refineADT s A B) v v' := @AbsR _ A B r v v'. *)

(* Inductive ValueComp av := *)
(* | SCAComp : Comp W  -> ValueComp av *)
(* | ADTComp : Comp av -> ValueComp av. *)
(* | ADTComp : Comp av (* Set of admissible values *) ->  *)
(*             c: Comp av | forall x, c computesto x -> \exists x', x = wrapper x' (* Actual value *) -> ValueComp av. *)

Require Import Coq.Strings.String.
Local Open Scope string.

Inductive Telescope av : Type :=
| Nil : Telescope av
| Cons : forall (key: option string)
           (val: Comp (Value av))
           (tail: Value av -> Telescope av),
    Telescope av.

Arguments Nil {av}.

Definition SameADTs {av} m1 m2 :=
  (forall k v, StringMap.MapsTo k (@ADT av v) m1 <-> StringMap.MapsTo k (@ADT av v) m2).

Definition SameSCAs {av} m1 m2 :=
  (forall k v, StringMap.MapsTo k (@SCA av v) m1 -> StringMap.MapsTo k (@SCA av v) m2).

Definition WeakEq {av} m1 m2 :=
  @SameADTs av m1 m2 /\ @SameSCAs av m1 m2.

Fixpoint SameValues {av} ext fmap (tenv: Telescope av) :=
  match tenv with
  | Nil => WeakEq ext fmap
  | Cons key val tail =>
    match key with
      | Some k => match StringMap.find k fmap with
                 | Some v => val ↝ v /\ SameValues ext (StringMap.remove k fmap) (tail v)
                 | None => False
                 end
      | None => exists v', val ↝ v' /\ SameValues ext fmap (tail v')
    end
  end.

Notation "ENV ≲ TENV ∪ EXT" := (SameValues EXT ENV TENV) (at level 50).

Definition ProgOk {av} ext env prog (initial_tstate final_tstate: Telescope av) :=
  forall initial_state: State av,
    (initial_state ≲ initial_tstate ∪ ext) ->
    Safe env prog initial_state /\
    forall final_state: State av,
      @RunsTo _ env prog initial_state final_state ->
      (final_state ≲ final_tstate ∪ ext).

(* Arguments Scope ProgOk [type_scope _ facade_scope _ _ _ _]. *)

(* Require Export ADTSynthesis.Computation.Core ADTSynthesis.Common. *)

Notation "{{ A }} P {{ B }} ∪ {{ ext }} // EV" :=
  (ProgOk ext EV P A B)
    (at level 60, format "'[v' '{{'  A  '}}' '/'    P '/' '{{'  B  '}}'  ∪  '{{'  ext  '}}'  //  EV ']'").

Check (forall (av : Type) vars (ev : Env av) (p : Stmt) (a b : Telescope av)
  (ext : StringMap.t (Value av)), {{ a }} p {{ b }} ∪ {{ext}} // ev).

Notation "A ∉ B" := (not (StringMap.In A B)) (at level 10, no associativity).
Notation "A ∈ B" := (StringMap.In A B) (at level 10, no associativity).

Ltac exact_after_rewrite :=
  match goal with
  | [ H: ?rel ?a ?b, H': context f [?a] |- context f [?b] ] => rewrite <- H; exact H'
  | [ H: ?rel ?a ?b, H': context f [?b] |- context f [?a] ] => rewrite H; exact H'
  end.

Ltac destruct_find k s :=
  let eq0 := fresh "eqn" in
  destruct (StringMap.find k s) eqn:eq0;
    [ rewrite <- StringMapFacts.find_mapsto_iff in eq0 |
      rewrite <- StringMapFacts.not_find_in_iff in eq0 ];
    simpl in *.

Ltac destruct_finds :=
  repeat lazymatch goal with
| [ H: context[StringMap.find ?k ?s] |- _ ] => destruct_find k s
| [ |- context[StringMap.find ?k ?s]      ] => destruct_find k s
end.

Open Scope comp.

Notation "[ k <-- v ] :: m" :=
  (StringMap.add k v m) (at level 21, right associativity, arguments at next level) : map_scope.

Local Open Scope map_scope.

Lemma Some_inj : forall A x y, @Some A x = @Some A y <-> x = y.
Proof.
  split; inversion 1; eauto.
Qed.

Ltac rewrite_trivial x y op :=
  let h := fresh in
  assert (op x y) as h by tauto;
    rewrite h; clear h.

Ltac rewrite_trivial_in x y op target :=
  let h := fresh in
  assert (op x y) as h by tauto;
    rewrite h in target; clear h.

(*
Ltac deep_simpl := (* TODO use autorewrite for this *)
  repeat match goal with
         | [ H: context[?a = ?a] |- _ ]              => rewrite_trivial_in (a = a) True iff H
         | [ |- context[?a = ?a] ]                   => rewrite_trivial (a = a) True iff
         | [ H: context[True /\ ?a] |- _ ]               => rewrite_trivial_in (True /\ a) a iff H
         | [ |- context[True /\ ?a] ]                    => rewrite_trivial (True /\ a) a iff
         | [ H: context[True \/ ?a] |- _ ]               => rewrite_trivial_in (True \/ a) True iff H
         | [ |- context[True \/ ?a] ]                    => rewrite_trivial (True \/ a) True iff
         | [ H: context[not True] |- _ ]                => rewrite_trivial_in (not True) False iff H
         | [ |- context[not True] ]                     => rewrite_trivial (not True) False iff
         | [ H0: ?x, H: context[?x] |- _ ]            => rewrite_trivial_in x True iff H
         | [ H0: not ?x, H: context[?x] |- _ ]        => rewrite_trivial_in x False iff H
         | [ |- context[not True] ]                     => rewrite_trivial (not True) False iff
         | [ H: context[False /\ ?a] |- _ ]               => rewrite_trivial_in (False /\ a) False iff H
         | [ |- context[False /\ ?a] ]                    => rewrite_trivial (False /\ a) False iff
         | [ H: context[?a \/ False] |- _ ]               => rewrite_trivial_in (a \/ False) a iff H
         | [ |- context[?a \/ False] ]                    => rewrite_trivial (a \/ False) a iff
         | [ H: context[False \/ ?a] |- _ ]               => rewrite_trivial_in (False \/ a) a iff H
         | [ |- context[False \/ ?a] ]                    => rewrite_trivial (False \/ a) a iff
         | [ H: ?a <> ?b, H': context[?a <> ?b] |- _ ] => rewrite_trivial_in (a <> b) True iff H'
         | [ H: ?a <> ?b |- context[?a <> ?b] ]        => rewrite_trivial (a <> b) True iff
         | [ H: ?a <> ?b, H': context[?a = ?b] |- _ ] => rewrite_trivial_in (a = b) False iff H'
         | [ H: ?a <> ?b |- context[?a = ?b] ]        => rewrite_trivial (a = b) False iff
         end.
 *)

Lemma SameValues_MapsTo:
  forall {av} (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)),
    state ≲ Cons (Some key) value tail ∪ ext ->
    exists v : Value av, value ↝ v /\ StringMap.MapsTo key v state.
Proof.
  simpl; intros.
  destruct (StringMap.find _ _) eqn: eq0; try tauto.
  rewrite <- find_mapsto_iff in *.
  eexists; intuition eauto.
Qed.

Ltac no_duplicates :=
  match goal with
  | [ H: ?P, H': ?P' |- _ ] =>
    match type of P with
    | Prop => unify P P'; fail 2 "Duplicates found:" H "and" H' ":" P
    | _ => fail
    end
  | _ => idtac
  end.

Ltac deduplicate :=
  repeat match goal with
         | [ H: ?P, H': ?P' |- _ ] =>
           match type of P with
           | Prop => unify P P'; clear H' (* Fixme don't set evars? *)
           | _ => fail
           end
         | _ => idtac
         end.

(* Inductive Learnt : Prop -> Type := *)
(*   | AlreadyKnown : forall A, Learnt A. *)

(* Ltac learn fact := *)
(*   let type := type of fact in *)
(*   match goal with *)
(*   | [ H: Learnt type |- _ ] => fail 1 fact "of type" type "is already known" *)
(*   | _ => pose proof (AlreadyKnown type); pose proof fact *)
(*   end. *)

(* Definition Learnt {A} (a: A) := *)
(*   True. *)

(* Ltac learn fact := *)
(*   match goal with *)
(*   | [ H: Learnt fact |- _ ] => fail 1 fact "is already known" *)
(*   | _ => assert (Learnt fact) by exact I; pose proof fact *)
(*   end. *)

Inductive Learnt {A: Type} (a: A) :=
  | AlreadyKnown : Learnt a.

Ltac learn fact :=
  lazymatch goal with
  | [ H: Learnt fact |- _ ] => fail 0 "fact" fact "has already been learnt"
  | _ => let type := type of fact in
        lazymatch goal with
        | [ H: @Learnt type _ |- _ ] => fail 0 "fact" fact "of type" type "was already learnt through" H
        | _ => pose proof (AlreadyKnown fact); pose proof fact
        end
  end.

Ltac step :=
  match goal with
  | _ => progress intros; simpl in *
  | _ => progress split
  | [ H: ?a /\ ?b |- _ ] => destruct H
  | [ H: StringMap.MapsTo ?k ?v ?m |- Some ?v = StringMap.find ?k ?m ] => symmetry; rewrite <- find_mapsto_iff; assumption
  | [ H: StringMap.MapsTo ?k ?v ?m |- context[StringMap.find ?k ?m] ] => replace (StringMap.find k m) with (Some v) in *
  | [ H: context[match StringMap.find ?k ?m with | Some _ => _ | None => _ end] |- _ ] => let eq0 := fresh in progress (destruct (StringMap.find k m) eqn:eq0; deduplicate)
  | [ H: ret _ ↝ _ |- _ ] => inversion H; clear H; subst
  | _ => solve [intuition eauto]
  end.

Ltac t :=
  repeat step.

Lemma SameValues_MapsTo_ret:
  forall {av}
    (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)) (x : Value av),
    StringMap.MapsTo key x state ->
    state ≲ Cons (Some key) value tail ∪ ext ->
    state ≲ Cons (Some key) (ret x) tail ∪ ext.
Proof. t. Qed.

Lemma SameValues_MapsTo_ret_inv:
  forall {av}
    (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)) (x : Value av),
    value ↝ x ->
    state ≲ Cons (Some key) (ret x) tail ∪ ext ->
    state ≲ Cons (Some key) value tail ∪ ext.
Proof. t. Qed.

Lemma SameValues_MapsTo_ret_ex:
  forall {av}
    (key : String.string) (value : Comp (Value av))
    (tail : Value av -> Telescope av)
    (ext state : StringMap.t (Value av)),
    state ≲ Cons (Some key) value tail ∪ ext ->
    exists v, value ↝ v /\ state ≲ Cons (Some key) (ret v) tail ∪ ext.
Proof. t. Qed.

Example ProkOk_specialize_to_ret :
  forall {av} env key value prog
    (tail1: Value av -> Telescope av)
    (tail2: Value av -> Telescope av)
    ext,
    (forall v, value ↝ v -> {{ Cons (Some key) (ret v) tail1 }} prog {{ Cons (Some key) (ret v) tail2 }} ∪ {{ ext }} // env) ->
    ({{ Cons (Some key) value tail1 }} prog {{ Cons (Some key) value tail2 }} ∪ {{ ext }} // env).
Proof.
  repeat match goal with
         | _ => progress intros
         | [  |- ?a /\ ?b] => split
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [ |- context[@ProgOk] ] =>
           let h := fresh "init_equiv" in
           intros ? h; destruct (SameValues_MapsTo_ret_ex _ _ _ _ _ h) as (? & ? & ?)
         | [ H: ?st ≲ _ ∪ _, H': forall v, ?val ↝ v -> _, H'': ?val ↝ ?x |- _ ] => progress (destruct (H' x H'' st H); deduplicate)
         | _ => intuition eauto using SameValues_MapsTo_ret_inv
         end.
Qed.

Require Import FMaps.
Module WUtils_fun (E:DecidableType) (Import M:WSfun E).
  Module Export BasicFacts := WFacts_fun E M.
  Module Export BasicProperties := WProperties_fun E M.

  Notation "A ∈ B" := (In A B) (at level 10, no associativity) : map_scope.
  Notation "A ∉ B" := (not (In A B)) (at level 10, no associativity) : map_scope.
  Notation "[ k <-- v ] :: m" :=
    (add k v m) (at level 21, right associativity, arguments at next level) : map_scope.
  Local Open Scope map_scope.

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
      k = k' -> Equal ([k <-- v] :: remove k' m) ([k <-- v] :: m).
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
    intros.
    rewrite Equal_mapsto_iff.
    intros *; map_iff;
      repeat match goal with
             | _ => progress msubst
             | _ => progress intuition
             | [ H: MapsTo _ _ _ |- _ ] => learn (MapsTo_In H)
             end.
  Qed.

  Lemma remove_add_cancel:
    forall (elt : Type) (k k' : key) (v : elt) (m : t elt),
      k ∉ m ->
      k = k' ->
      Equal (remove k' ([k <-- v] :: m)) m.
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
      MapsTo k v m -> Equal m ([k <-- v] :: m).
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
      Equal (remove k ([k' <-- v']::m)) (remove k m).
  Proof.
    intros.
    rewrite Equal_mapsto_iff; intros; map_iff.
    intuition (subst; congruence).
  Qed.

  Ltac rewrite_in equality target :=
  (*! TODO is this still needed? !*)
  let h := fresh in
  pose proof target as h;
    setoid_rewrite equality in h;
    clear dependent target;
    rename h into target.

  Ltac normalize :=
    match goal with
    | [  |- context[find ?k (add ?k ?v ?m)] ] => rewrite (@add_eq_o _ m k k v eq_refl) by reflexivity
    | [ H: context[find ?k (add ?k ?v ?m)] |- _ ] => rewrite (@add_eq_o _ m k k v eq_refl) in H by reflexivity
    | [ H: ?k <> ?k' |- context[find ?k (add ?k' _ _)] ] => rewrite add_neq_o by congruence
    | [ H: ?k <> ?k', H': context[find ?k (add ?k' _ _)] |- _ ] => rewrite add_neq_o in H' by congruence

    | [ H: Equal ?st ?st |- _ ] => clear dependent H
    | [ H: Equal ?st ?st', H': context[?st] |- _ ] => rewrite_in H H'
    | [ H: Equal ?st ?st' |- context[?st] ] => rewrite H
    | [ H: find ?k ?m = Some ?v |- _ ] => apply find_2 in H
    | [ H: MapsTo ?k ?v ?m |- context[find ?k ?m] ] => rewrite (find_1 H)
    | [ H: MapsTo ?k ?v ?m, H': context[find ?k ?m] |- _ ] => rewrite_in (find_1 H) H'
    | [ H: MapsTo ?k ?v ?m, H': MapsTo ?k ?v' ?m |- _ ] => learn (MapsTo_fun H H'); clear dependent H'
    | [ H: MapsTo ?k ?v (add ?k ?v' ?m) |- _ ] => learn (MapsTo_add_eq_inv H)
    | [ H: MapsTo ?k ?v (add ?k' ?v' ?m), H': ?k' <> ?k |- _ ] => learn (add_3 H' H)

    | [ |- context[remove ?k (add ?k ?v ?m)] ] => rewrite (remove_trickle (k := k) (k' := k) v m eq_refl)
    | [ H: context[remove ?k (add ?k ?v ?m)] |- _ ] => rewrite_in (remove_trickle (k := k) (k' := k) v m eq_refl) H

    | [ H: find _ _ = Some _ |- _ ] => rewrite <- find_mapsto_iff in H
    | [ H: find _ _ = None |- _ ] => rewrite <- not_find_in_iff in H

    | [ H: ?k ∉ (add _ _ _) |- _ ] => learn (NotIn_add H)
    | [ H: ?k ∉ ?m, H': MapsTo ?k _ ?m |- _ ] => learn (MapsTo_In H')
    | [ H: ?k ∉ ?m, H': MapsTo ?k' _ ?m |- _ ] => learn (MapsTo_NotIn_inv H H')
    | [ H: ?k ∉ ?st |- ?k ∉ (remove ?k' ?st) ] => eapply (In_remove_inv H); solve [eauto]
    end.

  Ltac repeat_rec tac :=
    (progress repeat tac); try (repeat_rec tac).

  Tactic Notation "Repeat" tactic(tac) :=
    repeat_rec tac.

  Ltac decide_mapsto :=
    map_iff; intuition congruence.

  Ltac decide_mapsto_maybe_instantiate :=
    Repeat (idtac;
             match goal with (* Recursive repeat for things that are only solvable after instantiating properly *)
             | _ => eassumption
             | [  |- ?a <> ?b ] => discriminate
             | [ H: ?a = ?b |- context[?a] ] => rewrite H
             | [ H: ?k <> ?k' |- MapsTo ?k ?v (add ?k' ?v' ?m) ] => apply add_mapsto_iff
             | [  |- MapsTo ?k ?v (add ?k' ?v ?m) ] => apply add_1; try reflexivity
             | [  |- MapsTo ?k ?v (add ?k' ?v' ?m) ] => apply add_2
             | [  |- find ?k ?m = Some ?v ] => apply find_1
             end).

  Lemma not_or : forall (A B: Prop), not A /\ not B -> not (A \/ B).
  Proof.
    tauto.
  Qed.

  Ltac decide_not_in :=
    (* map_iff; intuition congruence. *)
    repeat match goal with
           | _                      => assumption
           | [  |- _ /\ _ ]           => split
           | [  |- _ <> _ ]           => abstract congruence
           | [  |- not False ]           => intro; assumption
           | [  |- not (_ \/ _) ]     => apply not_or
           | [  |- _ ∉ (empty _) ]   => rewrite empty_in_iff
           | [  |- _ ∉ (add _ _ _) ] => rewrite add_in_iff
           end.
End WUtils_fun.

Module StringMapUtils := WUtils_fun (StringMap.E) (StringMap).

Ltac cleanup :=
  match goal with
  | _ => tauto
  | _ => discriminate
  | _ => progress intros
  | _ => progress computes_to_inv
  | [ |- ?a <-> ?b ] => split
  | [  |- ?a /\ ?b ] => split
  | [ H: ?a /\ ?b |- _ ] => destruct H
  end.

Ltac t_SameValues_Morphism :=
  repeat match goal with
         | _ => progress intros
         | _ => progress split
         | _ => progress simpl in *
         | [ H: StringMap.Equal ?m1 ?m2, H': StringMap.Equal ?m1 ?ext |- StringMap.Equal ?m2 ?ext ] =>
           symmetry in H
         | [ H: match ?k with _ => _ end |- match ?k with _ => _ end ] => destruct k
         | [ H: match StringMap.find ?k ?m1 with _ => _ end, H': StringMap.Equal ?m1 ?m2 |-
             match StringMap.find ?k ?m2 with _ => _ end ] => rewrite <- H'
         | [ IH: _, H: StringMap.remove ?k ?m1 ≲ (?t ?v) ∪ ?ext, H': StringMap.Equal ?m1 ?m2 |-
             StringMap.remove ?k ?m2 ≲ (?t ?v) ∪ ?ext ] => rewrite (IH v m1 m2 _ H')
         | [ IH: _, H: StringMap.remove ?k ?m1 ≲ (?t ?v) ∪ ?ext, H': StringMap.Equal ?m1 ?m2 |-
             StringMap.remove ?k ?m2 ≲ (?t ?v) ∪ ?ext ] => apply (IH _ _ _ _ (remove_m eq_refl H')); exact H
         | [ H: exists v, _ |- exists v, _ ] => destruct H; eexists
         | _ => progress (intuition eauto)
         end.

Require Import Setoid.

Ltac rewriteP hyp := first [rewrite hyp | setoid_rewrite hyp].
Ltac rewriteP_in hyp target := first [rewrite hyp in target | setoid_rewrite hyp in target].

Ltac rewrite_equalities :=
  match goal with
  | _ => progress subst
  | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H

  | [ H: ?a = ?b |- context[?a] ] => rewrite H
  | [ H: ?a = ?b, H': context[?a] |- _ ] => rewrite H in H'

  | [ H: StringMap.Equal ?a ?b |- context[?a] ] => rewriteP H
  | [ H: StringMap.Equal ?a ?b, H': context[?a] |- _ ] => rewriteP_in H H'

  | [ H: forall (k : StringMap.key) (v : _), StringMap.MapsTo k (ADT v) ?y <-> StringMap.MapsTo k (ADT v) ?y'
      |- context[StringMap.MapsTo _ (ADT _) ?y] ] => rewriteP H
  | [ H: forall (k : StringMap.key) (v : _), StringMap.MapsTo k (ADT v) ?y <-> StringMap.MapsTo k (ADT v) ?y',
      H': context[StringMap.MapsTo _ (ADT _) ?y] |- _ ] => rewriteP_in H H'
  end.

Ltac t_Morphism_step :=
  match goal with
  | _ => cleanup
  | _ => rewrite_equalities

  | [ |- context[?m ≲ Nil ∪ ?ext] ] => simpl
  | [ H: context[?m ≲ Nil ∪ ?ext] |- _ ] => simpl in H

  | [ |- context[?m ≲ Cons ?k ?v ?t ∪ ?ext] ] => let h := fresh in destruct k eqn:h; simpl
  | [ H: context[?m ≲ Cons ?k ?v ?t ∪ ?ext] |- _ ] => let h := fresh in destruct k eqn:h; simpl in H

  | [ |- context[match StringMap.find ?k ?m with _ => _ end] ] => let h := fresh in destruct (StringMap.find k m) eqn:h; simpl
  | [ H: context[match StringMap.find ?k ?m with _ => _ end] |- _ ] => let h := fresh in destruct (StringMap.find k m) eqn:h; simpl in H

  | [ H: exists v, _ |- exists v, _ ] => destruct H; eexists
  end.

Ltac t_Morphism := repeat t_Morphism_step.

Add Parametric Morphism {av} : (@StringMap.find av)
    with signature (eq ==> StringMap.Equal ==> eq)
      as find_Morphism.
Proof.
  intros; erewrite find_m; intuition.
Qed.

Add Parametric Morphism {av} : (@SameADTs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as SameADTs_Morphism.
Proof.
  unfold SameADTs in *; t_Morphism.
Qed.

Add Parametric Morphism {av} : (@SameSCAs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> Basics.impl)
      as SameSCAs_Morphism.
Proof.
  unfold SameSCAs, Basics.impl in *; t_Morphism; eauto.
Qed.

Add Parametric Morphism {av} : (@WeakEq av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as WeakEq_Morphism.
Proof.
  unfold WeakEq; t_Morphism.
Qed.

Lemma SameValues_Equal :
  forall {av} tenv m1 m2 ext,
    @StringMap.Equal (Value av) m1 m2 ->
    (m1 ≲ tenv ∪ ext ->
     m2 ≲ tenv ∪ ext).
Proof.
  induction tenv as [ | ? ? ? IH ];
  repeat match goal with
         | [ IH: _, H: StringMap.remove ?k ?m1 ≲ (?t ?v) ∪ ?ext, H': StringMap.Equal ?m1 ?m2 |-
             StringMap.remove ?k ?m2 ≲ (?t ?v) ∪ ?ext ] => apply (IH _ _ _ _ (remove_m eq_refl H')); exact H
         | _ => t_Morphism_step
         | _ => eauto
         end.
Qed.

Lemma SameValues_Equal_iff :
  forall {av} tenv m1 m2 ext,
    @StringMap.Equal (Value av) m1 m2 ->
    (m1 ≲ tenv ∪ ext <->
     m2 ≲ tenv ∪ ext).
Proof.
  intros * H; split; [ | symmetry in H ]; eauto using SameValues_Equal.
Qed.

Lemma SameValues_Equal_Ext :
  forall {av} tenv state m1 m2,
    @StringMap.Equal (Value av) m1 m2 ->
    (state ≲ tenv ∪ m1 ->
     state ≲ tenv ∪ m2).
Proof.
  induction tenv as [ | ? ? ? IH ];
  repeat match goal with
  | [ H: forall v st m1 m2, StringMap.Equal m1 m2 -> st ≲ ?tail v ∪ m1 -> st ≲ ?tail v ∪ m2, H': StringMap.Equal ?m1 ?m2,
        H'': ?st ≲ ?tail ?v ∪ (StringMap.add ?k ?v ?m1) |- ?st ≲ ?tail ?v ∪ (StringMap.add ?k ?v ?m2) ] =>
    apply (fun pr => IH v st _ _ pr H'')
  | [  |- StringMap.Equal (StringMap.add ?k ?v ?m1) (StringMap.add ?k ?v ?m2) ] => solve [eauto using add_m, Equal_refl]
  | _ => solve [eauto]
  | _ => t_Morphism_step
  end.
Qed.

Lemma SameValues_Equal_Ext_iff :
  forall {av} tenv state m1 m2,
    @StringMap.Equal (Value av) m1 m2 ->
    (state ≲ tenv ∪ m1 <->
     state ≲ tenv ∪ m2).
Proof.
  intros * H; split; [ | symmetry in H ]; eauto using SameValues_Equal_Ext.
Qed.

Lemma SameADTs_Trans:
  forall (av : Type) (m0 m1 m2 : StringMap.t (Value av)),
    SameADTs m0 m1 -> SameADTs m1 m2 -> SameADTs m0 m2.
Proof.
  unfold SameADTs; t_Morphism.
Qed.

Lemma SameSCAs_Trans:
  forall (av : Type) (m0 m1 m2 : StringMap.t (Value av)),
    SameSCAs m0 m1 -> SameSCAs m1 m2 -> SameSCAs m0 m2.
Proof.
  unfold SameSCAs; t_Morphism; eauto.
Qed.

Lemma WeakEq_Trans:
  forall (av : Type) (m0 m1 m2 : StringMap.t (Value av)),
    WeakEq m0 m1 -> WeakEq m1 m2 -> WeakEq m0 m2.
Proof.
  unfold WeakEq; t_Morphism; eauto using SameSCAs_Trans, SameADTs_Trans.
Qed.

Lemma SameADTs_Refl:
  forall (av : Type) (m : StringMap.t (Value av)),
    SameADTs m m.
Proof.
  unfold SameADTs; t_Morphism.
Qed.

Lemma SameSCAs_Refl:
  forall (av : Type) (m : StringMap.t (Value av)),
    SameSCAs m m.
Proof.
  unfold SameSCAs; t_Morphism; eauto.
Qed.

Lemma WeakEq_Refl:
  forall (av : Type) (m : StringMap.t (Value av)),
    WeakEq m m.
Proof.
  unfold WeakEq; t_Morphism; eauto using SameSCAs_Refl, SameADTs_Refl.
Qed.

Import StringMapUtils.

Ltac t_Same :=
  repeat match goal with
  | [  |- context[StringMap.MapsTo _ _ _] ] => progress map_iff
  | [ H: context[StringMap.MapsTo _ _ _] |- _ ] => progress map_iff_in H
  | [ k: StringMap.key, k': StringMap.key |- _ ] => learn (StringMap.E.eq_dec k k')
  | [ H: { _ } + { _ } |- _ ] => destruct H; subst
  | _ => progress t_Morphism
  | _ => solve [intuition]
  end.

Lemma SameADTs_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av)) 
    (s0 : StringMap.key) (v : Value av),
    SameADTs m2 m1 -> SameADTs ([s0 <-- v]::m2) ([s0 <-- v]::m1).
Proof.
  unfold SameADTs; t_Same.
Qed.

Lemma SameSCAs_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av)) 
    (s0 : string) (v : Value av),
    SameSCAs m2 m1 -> SameSCAs ([s0 <-- v]::m2) ([s0 <-- v]::m1).
Proof.
  unfold SameSCAs; t_Same.
Qed.

Lemma WeakEq_add:
  forall (av : Type) (m1 m2 : StringMap.t (Value av)) 
    (s0 : string) (v : Value av),
    WeakEq m2 m1 -> WeakEq ([s0 <-- v]::m2) ([s0 <-- v]::m1).
Proof.
  unfold WeakEq; t_Morphism;
  eauto using SameSCAs_add, SameADTs_add.
Qed.

Lemma SameADTs_remove:
  forall (av : Type) (m1 m2 : StringMap.t (Value av)) 
    (k : StringMap.key),
    SameADTs m2 m1 -> SameADTs (StringMap.remove k m2) (StringMap.remove k m1).
Proof.
  unfold SameADTs; t_Same.
Qed.

Lemma SameSCAs_remove:
  forall (av : Type) (m1 m2 : StringMap.t (Value av)) 
    (k : StringMap.key),
    SameSCAs m2 m1 -> SameSCAs (StringMap.remove k m2) (StringMap.remove k m1).
Proof.
  unfold SameSCAs; t_Same.
Qed.

Lemma WeakEq_remove:
  forall (av : Type) (m1 m2 : StringMap.t (Value av)) 
    (k : StringMap.key),
    WeakEq m2 m1 -> WeakEq (StringMap.remove k m2) (StringMap.remove k m1).
Proof.
  unfold WeakEq; t_Morphism;
  eauto using SameSCAs_remove, SameADTs_remove.
Qed.

Lemma SameValues_WeakEq_Ext :
  forall {av} tenv state m1 m2,
    @WeakEq av m2 m1 ->
    (state ≲ tenv ∪ m1 ->
     state ≲ tenv ∪ m2).
Proof.
  induction tenv as [ | ? ? ? IH ]; 
  repeat match goal with
         | _ => t_Morphism_step
         | _ => solve [eauto using WeakEq_Trans]
         end.
Qed.

Add Parametric Morphism {av} : (@SameValues av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> eq ==> iff)
      as SameValues_Morphism.
Proof.
  split; intros; subst;
  eapply SameValues_Equal; eauto using Equal_sym;
  eapply SameValues_Equal_Ext; eauto using Equal_sym.
Qed.

Lemma WeakEq_Mapsto_MapsTo:
  forall {av : Type} {key : StringMap.key} {ext st : StringMap.t (Value av)} {v : Value av},
    StringMap.MapsTo key v ext ->
    WeakEq ext st ->
    StringMap.MapsTo key v st.
Proof.
  unfold WeakEq, SameSCAs, SameADTs.
  intros ** v ? ?.
  destruct v; firstorder.
Qed.

Lemma SameADTs_impl {av} {m1 m2} :
  SameADTs m1 m2 ->
  (forall k v, StringMap.MapsTo k (@ADT av v) m1 -> StringMap.MapsTo k (@ADT av v) m2).
Proof.
  unfold SameADTs; firstorder.
Qed.

Lemma SameADTs_impl' {av} {m1 m2} :
  SameADTs m1 m2 ->
  (forall k v, StringMap.MapsTo k (@ADT av v) m2 -> StringMap.MapsTo k (@ADT av v) m1).
Proof.
  unfold SameADTs; firstorder.
Qed.

Lemma SameValues_MapsTo_Ext_State:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key)
    {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ ext ->
    forall v, StringMap.MapsTo key v ext ->
         StringMap.MapsTo key v st.
Proof.
  induction tel;
  repeat match goal with
         | _ => progress intros
         | _ => tauto
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [ H: _ ≲ Nil ∪ _ |- _ ] => simpl in H
         | [ H: StringMap.Equal ?b ?a, H': StringMap.MapsTo ?k _ _ |- StringMap.MapsTo ?k _ _ ] => rewrite H
         | [ H: ?st ≲ Cons ?key ?val ?tail ∪ ?ext |- _ ] => simpl in H; destruct key
         | [ H: forall a key ext st, st ≲ ?tail a ∪ ext -> _,
             H': ?st ≲ ?tail ?v ∪ ?ext,
             H'': StringMap.MapsTo ?key ?v' _  |- _ ] => specialize (H v key ext st H' v' H'')
         | [ H: StringMap.MapsTo ?k ?v (StringMap.remove _ ?s) |- StringMap.MapsTo ?k ?v ?s ] => solve[eauto using MapsTo_remove]
         | [ H: match StringMap.find ?s ?st with _ => _ end |- _ ] => let a := fresh in destruct (StringMap.find s st) eqn:a
         | [ H: exists v, _ |- _ ] => destruct H
         end; eauto using WeakEq_Mapsto_MapsTo. (*! FIXME why does adding the eauto at the end of the match make things slower? *)
Qed.

Lemma SameValues_MapsTo_Ext_State_add:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key)
    {v} {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ [key <-- v]::ext ->
    StringMap.MapsTo key v st.
Proof.
  intros; eauto using SameValues_MapsTo_Ext_State, StringMap.add_1.
Qed.

Lemma SameValues_In_Ext_State:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key)
    {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ ext ->
    StringMap.In key ext ->
    StringMap.In key st.
Proof.
  intros ** h.
  apply In_MapsTo in h; destruct h.
  eapply MapsTo_In; eauto using SameValues_MapsTo_Ext_State.
Qed.

Lemma SameValues_In_Ext_State_add:
  forall {av : Type} {tel: Telescope av} (key : StringMap.key) v
    {ext st : StringMap.t (Value av)},
    st ≲ tel ∪ [key <-- v]::ext ->
    StringMap.In key st.
Proof.
  intros; eapply MapsTo_In; eauto using SameValues_MapsTo_Ext_State_add.
Qed.

Add Parametric Relation {A} : _ (@WeakEq A)
    reflexivity proved by (@WeakEq_Refl A)
    transitivity proved by (@WeakEq_Trans A)
      as WeakEq_Rel.

(*************************)
(** Telescope notations **)
(*************************)

Notation "[[ k <~~ v 'as' kk ]] :: t" :=
  (Cons k v (fun kk => t)) (at level 21, right associativity, arguments at next level) : map_scope.

Notation "[[ ` k <~~ v 'as' kk ]] :: t" :=
  ([[ Some k <~~ v as kk ]] :: t) (at level 21, right associativity, arguments at next level) : map_scope.

Notation "[[ k <-- v 'as' kk ]] :: t" :=
  ([[ `k <~~ (ret v) as kk ]] :: t) (at level 21, right associativity, arguments at next level) : map_scope.

Notation "[[ v 'as' kk ]] :: t" :=
  ([[ None <~~ v as kk ]] :: t) (at level 21, right associativity, arguments at next level) : map_scope.

Create HintDb SameValues_Fiat_db discriminated.

Lemma computes_to_match_SCA:
  forall (av : Type) (compA : Comp W) (v0 : W),
    compA ↝ v0 ->
    (fun a : Value av =>
       match a with
       | SCA aa => compA aa
       | ADT _ => False
       end) ↝ SCA av v0.
Proof.
  trivial.
Qed.
Hint Resolve computes_to_match_SCA : SameValues_Fiat_db.

Lemma computes_to_match_SCA_inv:
  forall av (compA : Comp W) x,
    (fun a : Value av =>
       match a with
       | SCA aa => compA aa
       | ADT _ => False
       end) ↝ x ->
    exists xx, x = SCA av xx /\ compA xx.
Proof.
  intros; destruct x; vm_compute in H; intuition eauto.
Qed.

Definition TelEq {A} ext (T1 T2: Telescope A) :=
  forall st, st ≲ T1 ∪ ext <->
        st ≲ T2 ∪ ext.

Ltac TelEq_rel_t :=
  red; unfold TelEq; intuition;
  repeat match goal with
  | [ H: forall _, _ <-> _ |- _ ] => rewrite H
  | [ H: forall _, _ <-> _, H': _ |- _ ] => rewrite H in H'
  | _ => solve [intuition]
  end.

Lemma TelEq_refl {A ext}:
  Reflexive (@TelEq A ext).
Proof.
  TelEq_rel_t.
Qed.

Lemma TelEq_sym {A ext}:
  Symmetric (@TelEq A ext).
Proof.
  TelEq_rel_t.
Qed.

Lemma TelEq_trans {A ext}:
  Transitive (@TelEq A ext).
Proof.
  TelEq_rel_t.
Qed.

Add Parametric Relation {A} ext : _ (@TelEq A ext)
    reflexivity proved by TelEq_refl
    symmetry proved by TelEq_sym
    transitivity proved by TelEq_trans
      as TelEqRel.

Add Parametric Morphism {A} ext : (@SameValues A ext)
    with signature (eq ==> (TelEq ext) ==> iff)
      as SameValues_TelEq_morphism.
Proof.
  TelEq_rel_t.
Qed.

Ltac SameValues_Fiat_t :=
  repeat (idtac "step";
           match goal with
           | _ => cleanup
           | [ H: exists _, _ |- _ ] => destruct H

           | [  |- _ ≲ Cons _ _ _ ∪ _ ] => simpl
           | [ H: _ ≲ Cons _ _ _ ∪ _ |- _ ] => simpl in H

           | [ H: match ?k with _ => _ end |- _ ] => let eqn := fresh in destruct k eqn:eqn
           | [  |- context[match SCA _ _ with _ => _ end] ] => simpl
           | [ H: _ ↝ _ |- _ ] => apply computes_to_match_SCA_inv in H

           | [ H: ?a = ?b |- context[?a] ] => rewrite H
           | [ H: ?a = ?b, H': context[?a] |- _ ] => rewrite H in H'
           | [ H: forall a, TelEq _ (?x a) (?y a) |- _ ≲ (?x _) ∪ _ ] => red in H; rewrite H
           | [ H: forall a, TelEq _ (?x a) (?y a), H': _ ≲ (?x _) ∪ _ |- _ ] => red in H; rewrite H in H'
           | [ H: Monad.equiv ?b ?a |- ?b ↝ ?A ] => red in H; rewrite H
           | [ H: Monad.equiv ?a ?b, H': ?a ↝ ?A |- _ ] => red in H; rewrite H in H'

           | [  |- exists _, _ ] => eexists
           | _ => eauto with SameValues_Fiat_db
           end).

Lemma Cons_PopAnonymous:
  forall {av : Type} val tail (ext : StringMap.t (Value av)) (state : StringMap.t (Value av)),
    state ≲ [[val as _]]::tail ∪ ext ->
    state ≲ tail ∪ ext.
Proof.
  SameValues_Fiat_t.
Qed.

Lemma SameValues_Nil:
  forall {A} state ext,
    state ≲ (@Nil A) ∪ ext ->
    WeakEq ext state.
Proof.
  simpl; intros; assumption.
Qed.

Lemma SameValues_Nil_always:
  forall {A} state,
    state ≲ (@Nil A) ∪ state.
Proof.
  simpl; firstorder.
Qed.

Require Import Setoid Coq.Classes.Morphisms.

Add Parametric Morphism {av} {env} {prog} : (@Safe av env prog)
    with signature (StringMap.Equal ==> iff)
      as Safe_Morphism.
Proof.
Admitted.

Add Parametric Morphism {av} {env} {prog} : (@RunsTo av env prog)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as RunsTo_Morphism.
Proof.
Admitted.

Add Parametric Morphism {av} : (@eval av)
    with signature (StringMap.Equal ==> eq ==> eq)
      as eval_Morphism.
Proof.
  intros;
  match goal with
  | [ e: Expr |- _ ] => induction e
  end; simpl; repeat rewrite_equalities; try reflexivity.
Qed.

Ltac isDeterministicStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "This statement has multiple RunsTo and Safe constructors"
  end.

Ltac isStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | If _ _ _ => idtac
  | While _ _ => idtac
  | Call _ _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "No constructor found"
  end.

Lemma SameSCAs_refl:
  forall (av : Type) (t : StringMap.t (Value av)), SameADTs t t.
Proof.
  firstorder.
Qed.

Lemma SameADTs_refl:
  forall (av : Type) (t : StringMap.t (Value av)), SameSCAs t t.
Proof.
  firstorder.
Qed.

Lemma WeakEq_refl:
  forall (av : Type) (t : StringMap.t (Value av)), WeakEq t t.
Proof.
  firstorder.
Qed.

Lemma not_in_adts_not_mapsto_adt :
  forall {av} var (state: StringMap.t (Value av)),
    var ∉ state ->
    not_mapsto_adt var state = true.
Proof.
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p; intros.
  rewrite not_in_find; tauto.
Qed.

Lemma SameValues_Fiat_Bind_TelEq :
  forall {av} key compA compB tail ext,
    TelEq ext
          (Cons key (@Bind (Value av) (Value av) compA compB) tail)
          (Cons None compA (fun a => Cons key (compB a) tail)).
Proof.
  unfold TelEq; SameValues_Fiat_t.
Qed.

Definition WrapComp_W {av} (cmp: Comp W) :=
  fun (a: Value av) => match a with
                    | SCA a => cmp ↝ a
                    | _ => False
                    end.

Definition WrapCons_W {av} key (cmp: W -> Comp (Value av)) tail :=
  fun (a: Value av) => match a with
                    | SCA a => Cons key (cmp a) tail
                    | _ => Nil
                    end.

Definition WrappedCons {av A} Wrapper (key: option string) (cmp: A -> Comp (Value av)) (tail: Value av -> Telescope av)
  : Value av -> Telescope av :=
  Wrapper key cmp tail.

Lemma SameValues_Fiat_Bind_TelEq_W :
  forall {av} key (compA: Comp W) (compB: W -> Comp (Value av)) tail ext,
    @TelEq av ext
           (Cons key (@Bind _ _ compA compB) tail)
           (Cons None (WrapComp_W compA) (WrappedCons WrapCons_W key compB tail)).
Proof.
  unfold TelEq, WrappedCons, WrapCons_W; SameValues_Fiat_t.
Qed.

Add Parametric Morphism {av} : (@is_mapsto_adt av)
    with signature (eq ==> StringMap.Equal ==> eq)
      as is_mapsto_adt_morphism.
Proof.
  intros * H; unfold is_mapsto_adt; rewrite H; reflexivity.
Qed.

Add Parametric Morphism {av} : (@not_mapsto_adt av)
    with signature (eq ==> StringMap.Equal ==> eq)
      as not_mapsto_adt_morphism.
Proof.
  intros * H; unfold not_mapsto_adt; rewrite H; reflexivity.
Qed.

Hint Resolve not_in_adts_not_mapsto_adt : SameValues_db.

Lemma eval_AssignVar_MapsTo:
  forall (av : Type) (var : StringMap.key) (val : W) (state : State av),
    StringMap.MapsTo var (SCA av val) state ->
    eval state (Var var) = Some (SCA av val).
Proof.
  (*! eauto using? *)
  intros; apply find_mapsto_iff; assumption.
Qed.

Hint Resolve eval_AssignVar_MapsTo : SameValues_db.

Lemma eval_Binop_Some:
  forall (av : Type) (var1 var2 : StringMap.key) (val1 val2 : W)
    (ext : StringMap.t (Value av)) op
    (H1 : StringMap.MapsTo var2 (SCA av val2) ext)
    (H0 : StringMap.MapsTo var1 (SCA av val1) ext),
    eval ext (Binop op (Var var1) (Var var2)) = Some (SCA av (eval_binop (inl op) val1 val2)).
Proof.
  intros;
  rewrite find_mapsto_iff in *;
  unfold eval, eval_binop_m;
  repeat match goal with
         | [ H: ?a = ?b |- context[?a] ] => rewrite H
         end;
  reflexivity.
Qed.

Hint Resolve eval_Binop_Some : SameValues_db.

Lemma not_mapsto_adt_add:
  forall av (k k' : StringMap.key) v (fmap: _ (_ av)),
    k <> k' ->
    not_mapsto_adt k (StringMap.add k' v fmap) =
    not_mapsto_adt k fmap.
Proof.
  intros.
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p.
  rewrite add_neq_o by congruence.
  reflexivity.
Qed.

Ltac facade_cleanup :=
  progress match goal with
  | [  |- eval _ _ = Some _ ] => first [ reflexivity | progress simpl ]
  | [ H: eval _ _ = Some _ |- _ ] => simpl in H
  | [ H: eval_binop_m _ _ _ = Some _ |- _ ] => simpl in H
  | [ H: context[match Some _ with _ => _ end] |- _ ] => simpl in H
  | [ H: ?k <> ?k' |- context[not_mapsto_adt ?k (StringMap.add ?k' _ _)] ] => rewrite not_mapsto_adt_add by congruence
  | [ H: ?k' <> ?k |- context[not_mapsto_adt ?k (StringMap.add ?k' _ _)] ] => rewrite not_mapsto_adt_add by congruence
  | [ H: ?k ∉ ?m |- context[not_mapsto_adt ?k ?m] ] => rewrite not_in_adts_not_mapsto_adt by assumption
  end.

Ltac unfold_and_subst :=       (* Work around https://coq.inria.fr/bugs/show_bug.cgi?id=3259 *)
  repeat match goal with
         | [ H := _ |- _ ] => progress (unfold H in *; clear H)
         end; subst.

Ltac facade_inversion :=
  (*! TODO Why does inversion_clear just delete RunsTo Skip a b? !*)
  progress match goal with
  | [ H: Safe _ ?p _ |- _ ]     => isStmtConstructor p; inversion H; unfold_and_subst; clear H
  | [ H: RunsTo _ ?p _ _ |- _ ] => isStmtConstructor p; inversion H; unfold_and_subst; clear H
  | [ H: Some _ = Some _ |- _ ] => inversion H; unfold_and_subst; clear H
  | [ H: SCA _ _ = SCA _ _ |- _ ] => inversion H; unfold_and_subst; clear H
  end.


Definition bool2w b :=
  match b with
  | true => (Word.natToWord 32 1)
  | false => (Word.natToWord 32 0)
  end.

Definition bool2val {av} b :=
  SCA av (bool2w b).

Definition isTrueExpr var :=
  TestE IL.Eq (Const (bool2w true)) (Var var).

Require Import GLabelMap.
Module GLabelMapUtils := WUtils_fun (GLabelMap.E) (GLabelMap).

Ltac facade_construction_if_helper test trueLemma falseLemma :=
  match test with
  | true => apply trueLemma
  | false => apply falseLemma
  | _ => destruct test
  end.

Ltac facade_construction :=
  progress match goal with
           | [  |- Safe _ ?p _]          => isDeterministicStmtConstructor p; econstructor
           | [  |- RunsTo _ ?p _ _ ]     => isDeterministicStmtConstructor p; econstructor
           | [ H: GLabelMap.MapsTo ?fname (@Axiomatic _ ?spec) ?env |- Safe ?env (Call ?retv ?fname ?args) ?st ] =>
             eapply (@SafeCallAx _ env retv fname args st spec)
           | [ H: GLabelMap.MapsTo ?fname (@Operational _ ?spec) ?env |- Safe ?env (Call ?retv ?fname ?args) ?st ] =>
             eapply (@SafeCallOp _ env retv fname args st spec)
           | [ H: StringMap.MapsTo ?k (bool2val ?test) ?st |- Safe _ (If (isTrueExpr ?k) _ _) ?st ] =>
             facade_construction_if_helper test SafeIfTrue SafeIfFalse
           | [ H: StringMap.MapsTo ?k (bool2val ?test) ?st |- RunsTo _ (If (isTrueExpr ?k) _ _) ?st ] =>
             facade_construction_if_helper test RunsToIfTrue RunsToIfFalse
           end.

Ltac StringMap_t :=
  match goal with
  | _ => progress StringMapUtils.normalize
  | [ H: StringMap.MapsTo ?k (ADT ?v) ?st, H': SameADTs ?st _ |- _ ] => learn (SameADTs_impl H' H)
  | [ H: StringMap.MapsTo ?k (ADT ?v) ?st, H': SameADTs _ ?st |- _ ] => learn (SameADTs_impl' H' H)
  | [ H: StringMap.MapsTo ?k ?v ?m, H': WeakEq ?m ?m' |- _ ] => learn (WeakEq_Mapsto_MapsTo H H') 
  end.

Lemma SameValues_WeakEq :
  forall {av} tenv st1 st2 m,
    @WeakEq av st1 st2 ->
    (st1 ≲ tenv ∪ m ->
     st2 ≲ tenv ∪ m).
Proof.
  induction tenv as [ | ? ? ? IH ]; 
  repeat match goal with
         | _ => t_Morphism_step
         | _ => StringMap_t
         | _ => solve [eauto using WeakEq_Trans, WeakEq_remove]
         end.
Qed.

Add Parametric Morphism {av} : (@SameValues av)
    with signature (WeakEq --> WeakEq ==> eq ==> Basics.impl)
      as SameValues_WeakMorphism.
Proof.
  unfold Basics.impl; intros; subst;
  eapply SameValues_WeakEq; eauto;
  eapply SameValues_WeakEq_Ext; eauto using Equal_sym.
Qed.

Ltac push_pop IH :=
  repeat match goal with
         | _ => eassumption
         | _ => apply IH
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [  |- ?a /\ ?b ] => split
         | [ H: context[StringMap.find ?k (StringMap.remove ?k' ?st)] |- context[StringMap.find ?k ?st] ] =>
           let _eq := fresh in destruct (StringMap.find k (StringMap.remove k' st)) eqn:_eq; [ | tauto]
         | [ H: (StringMap.find ?k (StringMap.remove ?k' ?st)) = Some _ |- _ ] =>
           rewrite <- find_mapsto_iff in H; rewrite remove_mapsto_iff in H
         | [ H: context[StringMap.find ?k ?st] |- context[StringMap.find ?k (StringMap.remove ?k' ?st)] ] =>
           let _eq := fresh in destruct (StringMap.find k st) eqn:_eq; [| tauto]
         | [ H: StringMap.MapsTo ?k ?v ?m |- context[StringMap.find ?k ?m] ] => rewrite find_mapsto_iff in H; rewrite H
         | [ H: StringMap.MapsTo ?k ?v ?s, H': ?k <> ?k' |- StringMap.MapsTo ?k ?v (StringMap.remove ?k' ?s)] =>
           rewrite remove_neq_mapsto_iff by congruence
         | [ H: StringMap.remove ?k (StringMap.remove ?k' ?s) ≲ _ ∪ _ |- StringMap.remove ?k' (StringMap.remove ?k ?s) ≲ _ ∪ _ ] =>
           rewrite remove_remove_comm
         | [ H: exists v, _ |- exists v, _ ] => destruct H; eexists
         | _ => rewrite SameValues_Equal_iff; eauto using remove_remove_comm
         | [ H: StringMap.find ?k ?m = _ |- match StringMap.find ?k ?m with _ => _ end ] => rewrite H
         | [ H: StringMap.remove ?k ?st ≲ ?tel ∪ [?k' <-- ?v]::?ext |- _ ] =>
           assert (k' ∈ (StringMap.remove k st)) by eauto using SameValues_In_Ext_State_add; no_duplicates;
           assert (k' <> k) by eauto using In_remove_neq;
           rewrite remove_neq_o by eassumption
         | _ => eauto using remove_remove_comm
         end.

Lemma SameValues_PushExt:
  forall (av : Type) (key : StringMap.key)
    (tail : Value av -> Telescope av) (v0 : Value av)
    (ext initial_state : StringMap.t (Value av)),
    StringMap.MapsTo key v0 initial_state ->
    StringMap.remove key initial_state ≲ tail v0 ∪ ext ->
    initial_state ≲ tail v0 ∪ [key <-- v0]::ext.
Proof.
  intros until v0.
  induction (tail v0) as [ | k ? ? IH ]; intros.

  - simpl in *;
    lazymatch goal with
    | [ H: StringMap.MapsTo _ _ _ |- _ ] => rewrite (MapsTo_add_remove H)
    end; eauto using WeakEq_add.
  - simpl in *. destruct k; push_pop IH.
Qed.

Lemma Cons_PushExt:
  forall (av : Type) (key : StringMap.key) (tail : Value av -> Telescope av)
    (ext : StringMap.t (Value av)) (v : Value av)
    (initial_state : StringMap.t (Value av)),
    initial_state ≲ Cons (Some key) (ret v) tail ∪ ext ->
    initial_state ≲ tail v ∪ [key <-- v]::ext.
Proof.
  t; apply SameValues_PushExt; try rewrite find_mapsto_iff; eauto.
Qed.

Lemma SameValues_PopExt:
  forall (av : Type) (key : StringMap.key)
    (tail : Value av -> Telescope av) (v0 : Value av)
    (ext initial_state : StringMap.t (Value av)),
    (* StringMap.MapsTo key v0 initial_state -> *)
    key ∉ ext ->
    initial_state ≲ tail v0 ∪ [key <-- v0]::ext ->
    StringMap.remove key initial_state ≲ tail v0 ∪ ext.
Proof.
  intros until v0.
  induction (tail v0) as [ | k ? ? IH ]; intros.

  - simpl in *;
    lazymatch goal with
    | [ H: ?k ∉ ?ext |- _ ] => rewrite <- (fun x => remove_add_cancel x H eq_refl)
    end; eauto using WeakEq_remove.
  - simpl in *. destruct k; push_pop IH.
Qed.

Lemma Cons_PopExt:
  forall (av : Type) (key : StringMap.key) (tail : Value av -> Telescope av)
    (ext : StringMap.t (Value av)) (v : Value av)
    (initial_state : StringMap.t (Value av)),
    key ∉ ext ->
    initial_state ≲ tail v ∪ [key <-- v]::ext ->
    initial_state ≲ Cons (Some key) (ret v) tail ∪ ext.
Proof.
  t.
  repeat match goal with
         | [ H: ?st ≲ ?tel ∪ [?k <-- ?v]::ext |- _ ] =>
           let h := fresh in pose proof H0 as h; apply SameValues_MapsTo_Ext_State_add in h; no_duplicates
         | [ H: StringMap.MapsTo ?k ?v ?m |- match StringMap.find ?k ?m with _ => _ end] =>
           rewrite find_mapsto_iff in H; rewrite H
         end.
  t.
  
  eauto using SameValues_PopExt.
Qed.

Lemma SameValues_Add_Cons:
  forall (av : Type) (key : StringMap.key) value (ext state : StringMap.t (Value av)),
    key ∉ ext -> WeakEq ext state -> [key <-- value]::state ≲ [[ key <-- value as _]]::Nil ∪ ext.
Proof.
  intros; apply Cons_PopExt; simpl; eauto using WeakEq_refl, WeakEq_add.
Qed.

Hint Resolve SameValues_Add_Cons : SameValues_db.
Hint Resolve WeakEq_add : SameValues_db.

Inductive Learnt_FromWeakEq {A} (F1 F2: StringMap.t A) :=
| LearntFromWeakEq: Learnt_FromWeakEq F1 F2.

Ltac learn_from_WeakEq_internal HWeakEq fmap1 fmap2 :=
  match fmap1 with
  | StringMap.add ?k ?v ?map =>
    assert (StringMap.MapsTo k v fmap2);
      [ apply (fun mp => WeakEq_Mapsto_MapsTo mp HWeakEq); decide_mapsto | ];
      learn_from_WeakEq_internal HWeakEq map fmap2
  | _ => idtac
  end.

Ltac learn_from_WeakEq HWeakEq fmap1 fmap2 :=
  lazymatch goal with
  | [ H: Learnt_FromWeakEq fmap1 fmap2 |- _ ] => fail
  | _ => pose proof (LearntFromWeakEq fmap1 fmap2); learn_from_WeakEq_internal HWeakEq fmap1 fmap2
  end.


Add Parametric Morphism {av} : (@is_mapsto_adt av)
    with signature (eq ++> WeakEq ==> eq)
      as is_mapsto_adt_weak_morphism.
Proof.
  intros * H; unfold not_mapsto_adt, is_mapsto_adt, is_some_p, is_adt in *.
  destruct (StringMap.find y x) eqn:eq0.
  - rewrite <- find_mapsto_iff in eq0;
    pose proof (WeakEq_Mapsto_MapsTo eq0 H) as eq1;
    rewrite find_mapsto_iff in eq1; rewrite eq1; reflexivity.
  - destruct (StringMap.find y y0) eqn:eq1; try reflexivity.
    destruct v; try reflexivity.
    destruct H as [H _]; unfold SameADTs in H.
    rewrite <- find_mapsto_iff, <- H, find_mapsto_iff in eq1.
    congruence.
Qed.

Add Parametric Morphism {av} : (@not_mapsto_adt av)
    with signature (eq ++> WeakEq ==> eq)
      as not_mapsto_adt_weak_morphism.
Proof.
  intros * H; unfold not_mapsto_adt; rewrite H; reflexivity.
Qed.

Ltac SameValues_Facade_t_step :=
  match goal with
  | _ => cleanup
  | _ => facade_cleanup
  | _ => facade_inversion
  | _ => facade_construction

  | [ |- @ProgOk _ _ _ _ _ _ ] => red

  | _ => StringMap_t
  | _ => progress subst

  | [ H: TelEq _ ?x _ |- context[?st ≲ ?x ∪ _] ] => rewrite (H st)
  | [ H: TelEq _ ?x _, H': context[?st ≲ ?x ∪ _] |- _ ] => rewrite_in (H st) H'

  (* Specialize ProgOk *)
  | [ H: ProgOk ?ext _ _ ?tel _, H': ?st ≲ ?tel ∪ ?ext |- _ ] => learn (H st H')
  | [ H: forall st : State _, RunsTo ?env ?p ?ext st -> _, H': RunsTo ?env ?p ?ext ?st |- _ ] => learn (H st H')
  (* Cleanup Cons *)
  | [ H: ?st ≲ Cons (Some _) _ _ ∪ _ |- _ ] => learn (Cons_PushExt _ _ _ _ _ H)
  | [ H: ?st ≲ Cons None _ _ ∪ _ |- _ ] => learn (Cons_PopAnonymous H)
  | [ H: ?st ≲ (fun _ => _) _ ∪ _ |- _ ] => progress cbv beta in H

  | [ H: ?st ≲ Nil ∪ ?ext |- _ ] => learn (SameValues_Nil H)
  | [ H: WeakEq _ ?st |- not_mapsto_adt _ ?st = _ ] => rewrite <- H
  | [ H: WeakEq ?st1 ?st2 |- _ ] => learn_from_WeakEq H st1 st2 (* Learn MapsTo instances *)
  | [ H: ?a -> _, H': ?a |- _ ] => match type of a with Prop => specialize (H H') end

  | _ => solve [eauto 3 with SameValues_db]
  end.

Ltac SameValues_Facade_t :=
  repeat SameValues_Facade_t_step.

Add Parametric Morphism {A} ext : (@Cons A)
    with signature (eq ==> Monad.equiv ==> pointwise_relation _ (TelEq ext) ==> (TelEq ext))
      as Cons_MonadEquiv_morphism.
Proof.
  unfold pointwise_relation; intros; unfold TelEq;
  SameValues_Fiat_t.
Qed.

Add Parametric Morphism {A} ext : (fun x y z t => @ProgOk A ext x y z t)
    with signature (eq ==> eq ==> (TelEq ext) ==> (TelEq ext) ==> iff)
      as ProgOk_TelEq_morphism.
Proof.
  unfold ProgOk; repeat match goal with
                        | [ H: ?a -> _, H': ?a |- _ ] => learn (H H')
                        | _ => SameValues_Facade_t_step
                        end.
Qed.

Lemma SameADTs_find_iff {av} m1 m2 :
  SameADTs m1 m2 <->
  (forall k v, StringMap.find k m1 = Some (@ADT av v) <-> StringMap.find k m2 = Some (@ADT av v)).
Proof.
  unfold SameADTs; setoid_rewrite find_mapsto_iff; reflexivity.
Qed.

Lemma SameSCAs_find_iff {av} m1 m2 :
  SameSCAs m1 m2 <->
  (forall k v, StringMap.find k m1 = Some (@SCA av v) -> StringMap.find k m2 = Some (@SCA av v)).
Proof.
  unfold SameSCAs; setoid_rewrite find_mapsto_iff; reflexivity.
Qed.

Ltac not_mapsto_adt_t :=
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p, is_adt;
  repeat match goal with
         | _ => cleanup
         | _ => reflexivity
         | _ => congruence
         | _ => StringMap_t
         | [  |- context[match ?a with _ => _ end] ] => let h := fresh in destruct a eqn:h; subst
         | [ H: context[match ?a with _ => _ end]  |- _ ] => let h := fresh in destruct a eqn:h; subst
         end.

Lemma not_in_SameADTs_not_mapsto_adt:
  forall {av : Type} (name : StringMap.key) (ext : StringMap.t (Value av))
    (initial_state : State av),
    name ∉ ext ->
    SameADTs ext initial_state ->
    not_mapsto_adt name initial_state = true.
Proof.
  not_mapsto_adt_t.
Qed.

Lemma not_mapsto_adt_not_MapsTo_ADT :
  forall {av k st},
    @not_mapsto_adt av k st = true ->
    forall {v: av}, not (StringMap.MapsTo k (ADT v) st).
Proof.
  not_mapsto_adt_t; red; intros; not_mapsto_adt_t.
Qed.

Lemma ProgOk_Chomp_lemma :
  forall {av} env key prog
    (tail1 tail2: Value av -> Telescope av)
    ext v,
    key ∉ ext ->
    ({{ tail1 v }} prog {{ tail2 v }} ∪ {{ [key <-- v] :: ext }} // env <->
     {{ Cons (Some key) (ret v) tail1 }} prog {{ Cons (Some key) (ret v) tail2 }} ∪ {{ ext }} // env).
Proof.
  repeat match goal with
         | _ => progress intros
         | _ => progress split
         | _ => tauto
         | [ H: ?a /\ ?b |- _ ] => destruct H
         | [ H: ?a ≲ Cons _ _ _ ∪ _ |- _ ] => learn (Cons_PushExt _ _ _ _ _ H)
         | [ H: ProgOk ?fmap _ _ ?t1 ?t2, H': _ ≲ ?t1 ∪ ?fmap |- _ ] => destruct (H _ H'); no_duplicates
         | [ H: RunsTo _ _ ?from ?to, H': forall st, RunsTo _ _ ?from st -> _ |- _ ] => specialize (H' _ H)
         | [ H: _ ≲ _ ∪ [_ <-- _] :: _ |- _ ] => apply Cons_PopExt in H1
         | _ => solve [eauto using Cons_PopExt]
         end.
Qed.

Lemma ProgOk_Chomp_Some :
  forall {av} env key value prog
    (tail1: Value av -> Telescope av)
    (tail2: Value av -> Telescope av)
    ext,
    key ∉ ext ->
    (forall v, value ↝ v -> {{ tail1 v }} prog {{ tail2 v }} ∪ {{ [key <-- v] :: ext }} // env) ->
    ({{ Cons (Some key) value tail1 }} prog {{ Cons (Some key) value tail2 }} ∪ {{ ext }} // env).
Proof.
  intros; apply ProkOk_specialize_to_ret; intros; apply ProgOk_Chomp_lemma; eauto.
Qed.

Lemma ProgOk_Chomp_None :
  forall {av} env value prog
    (tail1: Value av -> Telescope av)
    (tail2: Value av -> Telescope av) ext,
    (forall v, value ↝ v -> {{ tail1 v }} prog {{ tail2 v }} ∪ {{ ext }} // env) ->
    ({{ Cons None value tail1 }} prog {{ Cons None value tail2 }} ∪ {{ ext }} // env).
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => progress SameValues_Fiat_t
         | [ H: forall v, ?val ↝ v -> _, H': ?val ↝ ?v |- _ ] => learn (H _ H')
         end.
Qed.

Lemma SameADTs_pop_SCA_util:
  forall (av : Type) (st : StringMap.t (Value av)) 
    (k : StringMap.key)
    (v : W),
    not_mapsto_adt k st = true ->
    SameADTs st ([k <-- SCA av v]::st).
Proof.
  intros ** k' v; destruct (StringMap.E.eq_dec k k'); subst; split; intros;
  repeat match goal with
         | _ => progress map_iff
         | _ => progress not_mapsto_adt_t
         | [ H: not_mapsto_adt ?k ?st = true, H': StringMap.MapsTo ?k (ADT ?v) ?st |- _ ] => destruct (not_mapsto_adt_not_MapsTo_ADT H H')
         | [ H: context[@StringMap.MapsTo] |- _ ] => progress map_iff_in H
         end.
Qed.

Lemma SameADTs_pop_SCA:
  forall (av : Type) (st : StringMap.t (Value av)) 
    (k : StringMap.key) (v : W) ext,
    not_mapsto_adt k st = true ->
    SameADTs ext st ->
    SameADTs ext ([k <-- SCA av v]::st).
Proof.
  eauto using SameADTs_Trans, SameADTs_pop_SCA_util.
Qed.

Lemma SameSCAs_pop_SCA_util:
  forall (av : Type) (st : StringMap.t (Value av))
    (k : StringMap.key) (v : W),
    k ∉ st ->
    SameSCAs st ([k <-- SCA av v]::st).
Proof.
  unfold SameSCAs; intros; map_iff;
  match goal with
  | [ k: StringMap.key, k': StringMap.key |- _ ] => destruct (StringMap.E.eq_dec k k'); subst
  end; SameValues_Facade_t.
Qed.

Lemma SameSCAs_pop_SCA:
  forall (av : Type) (st : StringMap.t (Value av)) 
    (k : StringMap.key) (ext : StringMap.t (Value av)) 
    (v : W),
    k ∉ st ->
    SameSCAs ext st ->
    SameSCAs ext ([k <-- SCA av v]::st).
Proof.
  eauto using SameSCAs_Trans, SameSCAs_pop_SCA_util.
Qed.

Lemma WeakEq_pop_SCA:
  forall (av : Type) (st : StringMap.t (Value av)) 
    (k : StringMap.key) (ext : StringMap.t (Value av)) 
    (v : W),
    k ∉ st ->
    WeakEq ext st ->
    WeakEq ext ([k <-- SCA av v]::st).
Proof.
  unfold WeakEq;
  intuition eauto using SameSCAs_pop_SCA, SameADTs_pop_SCA, not_in_adts_not_mapsto_adt.
Qed.

Lemma SameADTs_pop_SCA':
  forall (av : Type) (st : StringMap.t (Value av)) 
    (k : StringMap.key) (v : W) ext,
    k ∉ ext ->
    SameADTs ext st ->
    SameADTs ext ([k <-- SCA av v]::st).
Proof.
  unfold SameADTs; split; map_iff; intros;
  repeat match goal with
         | [ H: ?k ∉ ?m, H': StringMap.MapsTo ?k' _ ?m |- _ ] => learn (MapsTo_NotIn_inv H H')
         | [ H: forall _ _ , _ <-> _, H': _ |- _ ] => rewrite_in H H'
         | [ H: forall _ _ , _ <-> _ |- _ ] => rewrite H
         | _ => solve [intuition discriminate]
         end.
Qed.

Lemma SameSCAs_pop_SCA':
  forall (av : Type) (st : StringMap.t (Value av)) 
    (k : StringMap.key) (ext : StringMap.t (Value av)) 
    (v : W),
    k ∉ ext ->
    SameSCAs ext st ->
    SameSCAs ext ([k <-- SCA av v]::st).
Proof.
  unfold SameSCAs; map_iff; intros;
  repeat match goal with
         | [ H: ?k ∉ ?m, H': StringMap.MapsTo ?k' _ ?m |- _ ] => learn (MapsTo_NotIn_inv H H')
         | [ H: forall _ _ , _ <-> _, H': _ |- _ ] => rewrite_in H H'
         | [ H: forall _ _ , _ <-> _ |- _ ] => rewrite H
         | _ => solve [intuition discriminate]
         end.
  eauto using StringMap.add_2.
Qed.

Lemma WeakEq_pop_SCA':
  forall (av : Type) (st : StringMap.t (Value av)) 
    (k : StringMap.key) (ext : StringMap.t (Value av)) 
    (v : W),
    k ∉ ext ->
    WeakEq ext st ->
    WeakEq ext ([k <-- SCA av v]::st).
Proof.
  unfold WeakEq;
  intuition eauto using SameSCAs_pop_SCA', SameADTs_pop_SCA'.
Qed.

Hint Resolve SameADTs_pop_SCA : SameValues_db.
Hint Resolve SameSCAs_pop_SCA : SameValues_db.
Hint Resolve WeakEq_pop_SCA : SameValues_db.

Lemma SameValues_add_SCA:
  forall av tel st k ext v,
    k ∉ st ->
    st ≲ tel ∪ ext ->
    (StringMap.add k (SCA av v) st) ≲ tel ∪ ext.
Proof.
  induction tel;
  repeat match goal with
         | _ => progress t_Morphism
         | _ => progress SameValues_Facade_t
         end.

  rewrite remove_add_comm by congruence.
  apply H; eauto.
  repeat match goal with
         | _ => progress t_Morphism
         | _ => progress SameValues_Facade_t
         end.
Qed.

Definition AlwaysComputesToSCA {av} (v: Comp (Value av)) :=
  forall vv, v ↝ vv -> is_adt vv = false.

Lemma SameValues_Dealloc_SCA_Some :
  forall {av} st k (v: Comp (Value av)) tail ext,
    AlwaysComputesToSCA v ->
    st ≲ Cons (Some k) v tail ∪ ext ->
    st ≲ Cons None v tail ∪ ext.
Proof.
  SameValues_Fiat_t.
  StringMap_t.
  repeat match goal with
         | [ H: StringMap.MapsTo _ _ ?st |- ?st ≲ _ ∪ _ ] => rewrite (MapsTo_add_remove H)
         | [ H: ?v ↝ ?vv, H': AlwaysComputesToSCA ?v |- _ ] => specialize (H' _ H)
         | [ H: is_adt ?v = false |- _ ] => destruct v; simpl in H; try congruence
         end.
  apply SameValues_add_SCA; eauto using StringMap.remove_1.
Qed.

Lemma SameValues_Dealloc_SCA :
  forall {av} st k (v: Comp (Value av)) tail ext,
    AlwaysComputesToSCA v ->
    st ≲ Cons k v tail ∪ ext ->
    st ≲ Cons None v tail ∪ ext.
Proof.
  intros; destruct k; eauto using SameValues_Dealloc_SCA_Some.
Qed.

Lemma not_in_WeakEq_not_mapsto_adt:
  forall {av : Type} (name : StringMap.key) (ext : StringMap.t (Value av))
    (initial_state : State av),
    name ∉ ext ->
    WeakEq ext initial_state ->
    not_mapsto_adt name initial_state = true.
Proof.
  unfold WeakEq; intros; intuition (eauto using not_in_SameADTs_not_mapsto_adt).
Qed.

Hint Resolve not_in_WeakEq_not_mapsto_adt : SameValues_db.

Ltac empty_remove_t :=
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | [ H: StringMap.MapsTo ?k _ (StringMap.empty _) |- _ ] => learn (StringMap.empty_1 H)
         | [ H: StringMap.MapsTo ?k ?v (StringMap.remove ?k' ?m) |- _ ] => learn (StringMap.remove_3 H)
         | [ H: forall k v, StringMap.MapsTo _ _ ?m <-> _ |- StringMap.MapsTo _ _ ?m ] => rewrite H
         end.

Notation "∅" := (StringMap.empty _).

Lemma SameSCAs_empty_remove:
  forall av (var : string) (initial_state : State av),
    SameSCAs ∅ initial_state ->
    SameSCAs ∅ (StringMap.remove var initial_state).
Proof.
  unfold SameSCAs; empty_remove_t.
Qed.

Lemma SameADTs_empty_remove:
  forall av (var : string) (initial_state : State av),
    SameADTs ∅ initial_state ->
    SameADTs ∅ (StringMap.remove var initial_state).
Proof.
  unfold SameADTs; empty_remove_t.
Qed.

Lemma WeakEq_empty_remove:
  forall av (var : string) (initial_state : State av),
    WeakEq ∅ initial_state ->
    WeakEq ∅ (StringMap.remove var initial_state).
Proof.
  unfold WeakEq; intuition eauto using SameADTs_empty_remove, SameSCAs_empty_remove.
Qed.

Lemma SameSCAs_remove_SCA:
  forall av (var : StringMap.key) (initial_state : State av),
    var ∉ initial_state ->
    SameSCAs initial_state (StringMap.remove var initial_state).
Proof.
  unfold SameSCAs; intros; rewrite remove_notIn_Equal; eauto.
Qed.

Lemma SameADTs_remove_SCA:
  forall av (var : StringMap.key) (initial_state : State av),
    var ∉ initial_state ->
    SameADTs initial_state (StringMap.remove var initial_state).
Proof.
  unfold SameADTs; intros; rewrite remove_notIn_Equal; eauto using iff_refl.
Qed.

Lemma WeakEq_remove_SCA:
  forall av (var : StringMap.key) (initial_state : State av),
    var ∉ initial_state ->
    WeakEq initial_state (StringMap.remove var initial_state).
Proof.
  unfold WeakEq; intuition (eauto using SameADTs_remove_SCA, SameSCAs_remove_SCA).
Qed.

Lemma WeakEq_remove_notIn:
  forall av (k : StringMap.key) (st1 st2 : State av),
    k ∉ st1 ->
    WeakEq st1 st2 ->
    WeakEq st1 (StringMap.remove k st2).
Proof.
  intros. rewrite <- (remove_notIn_Equal (k := k)  (m := st1)) by assumption.
  eauto using WeakEq_remove.
Qed.

Hint Resolve WeakEq_remove_notIn : SameValues_db.

Lemma CompileConstant:
  forall {av} name env w ext,
    name ∉ ext ->
    {{ Nil }}
      (Assign name (Const w))
    {{ [[name <-- (SCA av w) as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileRead:
  forall {av} name var (val: W) ext,
    name ∉ ext ->
    StringMap.MapsTo var (SCA av val) ext ->
    forall env,
    {{ Nil }}
      (Assign name (Var var))
    {{ [[name <-- (SCA _ val) as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileSkip:
  forall {av} (ext : StringMap.t (Value av)) env,
    {{ Nil }}
      Skip
    {{ Nil }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileBinop:
  forall {av} name var1 var2 (val1 val2: W) ext op,
    name ∉ ext ->
    StringMap.MapsTo var1 (SCA av val1) ext ->
    StringMap.MapsTo var2 (SCA av val2) ext ->
    forall env,
    {{ Nil }}
      Assign name (Binop op (Var var1) (Var var2))
    {{ [[name <-- (SCA _ (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Lemma CompileBinopB_util:
  forall {T} k1 k2 k3 {v1 v2 v3} (fmap: StringMap.t T),
    k1 <> k2 -> k2 <> k3 -> k1 <> k3 ->
    StringMap.Equal ([k3 <-- v3] ::[k2 <-- v2]::[k1 <-- v1]::fmap)
                    ([k1 <-- v1] ::[k2 <-- v2]::[k3 <-- v3]::fmap).
Proof.
  unfold StringMap.Equal; intros;
  destruct (StringMap.E.eq_dec y k1);
  destruct (StringMap.E.eq_dec y k2);
  destruct (StringMap.E.eq_dec y k3);
  SameValues_Facade_t.
Qed.

Lemma CompileBinopB_util2:
  forall {av : Type} (var1 var2 var3 : StringMap.key)
    (val1 val2 val3 : _) (ext : StringMap.t (Value av)),
    var1 <> var2 ->
    var2 <> var3 ->
    var1 <> var3 ->
    var1 ∉ ext ->
    var2 ∉ ext ->
    var3 ∉ ext ->
    [var1 <-- val1]
      ::[var2 <-- val2]
      ::[var3 <-- val3]::ext
      ≲ [[var1 <-- val1 as _]]
      ::[[var2 <-- val2 as _]]
      ::[[var3 <-- val3 as _]]::Nil ∪ ext.
Proof.
  intros.
  repeat apply Cons_PopExt; try decide_not_in.
  rewrite CompileBinopB_util by assumption.
  apply SameValues_Nil_always.
Qed.

Lemma CompileBinop_with_dealloc_USELESS:
  forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2 p3,
    name ∉ ext ->
    var1 ∉ ext ->
    var2 ∉ ext ->
    var1 <> var2 ->
    var1 <> name ->
    var2 <> name ->
    {{ Nil }}
      p1
    {{ [[var1 <-- SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ [[var1 <-- SCA _ val1 as _]]::Nil }}
      p2
    {{ [[var1 <-- SCA _ val1 as _]]::[[var2 <-- SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ [[var1 <-- SCA _ val1 as _]]::[[var2 <-- SCA _ val2 as _]]::[[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }}
      p3
    {{ [[ret (SCA _ val1) as _]]::[[ret (SCA _ val2) as _]]::[[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ Nil }}
      (Seq p1 (Seq p2 (Seq (Assign name (Binop op (Var var1) (Var var2))) p3)))
    {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  Time SameValues_Facade_t;

  assert ([name <-- SCA av (IL.evalBinop op val1 val2)]::st'0
        ≲ [[var1 <-- SCA av val1 as _]]
          ::[[var2 <-- SCA av val2 as _]]
            ::[[name <-- SCA av (eval_binop (inl op) val1 val2) as _]]::Nil
            ∪ ext) by (repeat apply Cons_PopExt;
                        try decide_not_in;
                        simpl;
                        SameValues_Facade_t);

  SameValues_Facade_t.
Qed.

Lemma CompileBinop_left:
  forall {av} name var1 var2 (val1 val2: W) env ext op p2,
    name ∉ ext ->
    StringMap.MapsTo var1 (SCA av val1) ext ->
    var2 ∉ ext ->
    var1 <> var2 ->
    var2 <> name ->
    {{ Nil }}
      p2
    {{ [[var2 <-- SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ Nil }}
      (Seq p2 (Assign name (Binop op (Var var1) (Var var2))))
    {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  Time SameValues_Facade_t.

  rewrite (add_redundant_cancel H0) in H19; SameValues_Facade_t.
  apply Cons_PopExt; [ SameValues_Facade_t | ].

  cut (st' ≲ Nil ∪ ext);
  repeat match goal with
         | _ => reflexivity
         | _ => solve [simpl; SameValues_Facade_t]
         | _ => apply WeakEq_pop_SCA; [decide_not_in|]
         | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H
         | _ => progress simpl
         end.
Qed.

Lemma CompileBinop_right:
  forall {av} name var1 var2 (val1 val2: W) env ext op p2,
    name ∉ ext ->
    var1 ∉ ext ->
    StringMap.MapsTo var2 (SCA av val2) ext ->
    var1 <> var2 ->
    var1 <> name ->
    {{ Nil }}
      p2
    {{ [[var1 <-- SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ Nil }}
      (Seq p2 (Assign name (Binop op (Var var1) (Var var2))))
    {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  Time SameValues_Facade_t.

  rewrite (add_redundant_cancel H1) in H19; SameValues_Facade_t.
  apply Cons_PopExt; [ SameValues_Facade_t | ].

  cut (st' ≲ Nil ∪ ext);
  repeat match goal with
         | _ => reflexivity
         | _ => solve [simpl; SameValues_Facade_t]
         | _ => apply WeakEq_pop_SCA; [decide_not_in|]
         | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H
         | _ => progress simpl
         end.
Qed.

Lemma CompileBinop_full:
  forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2,
    name ∉ ext ->
    var1 ∉ ext ->
    var2 ∉ ext ->
    var1 <> var2 ->
    var1 <> name ->
    var2 <> name ->
    {{ Nil }}
      p1
    {{ [[var1 <-- SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ [[var1 <-- SCA _ val1 as _]]::Nil }}
      p2
    {{ [[var1 <-- SCA _ val1 as _]]::[[var2 <-- SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ Nil }}
      (Seq p1 (Seq p2 (Assign name (Binop op (Var var1) (Var var2)))))
    {{ [[name <-- (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  Time SameValues_Facade_t.
  apply Cons_PopExt; [ SameValues_Facade_t | ].

  cut (st'0 ≲ Nil ∪ ext);
  repeat match goal with
         | _ => reflexivity
         | _ => solve [simpl; SameValues_Facade_t]
         | _ => apply WeakEq_pop_SCA; [decide_not_in|]
         | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H
         | _ => progress simpl
         end.
Qed.

Lemma CompileDeallocSCA:
  forall {av} (env : Env av) k compSCA tail tail' ext prog,
    AlwaysComputesToSCA compSCA ->
    {{ [[compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[k <~~ compSCA as kk]]::(tail kk)}}
      prog
    {{ [[compSCA as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t;
  apply SameValues_Dealloc_SCA in H1;
  SameValues_Facade_t.
Qed.

Lemma AlwaysComputesToSCA_ret_SCA:
  forall (av : Type) (v : W), AlwaysComputesToSCA (ret (SCA av v)).
Proof.
  red; intros; computes_to_inv; subst; reflexivity.
Qed.

Hint Resolve AlwaysComputesToSCA_ret_SCA : SameValues_db.

Lemma AlwaysComputesToSCA_WrapComp_W {av} (cmp: Comp W) :
  AlwaysComputesToSCA (@WrapComp_W av cmp).
Proof.
  Transparent computes_to.
  red; unfold WrapComp_W, computes_to; intros.
  destruct vv; simpl; (reflexivity || (exfalso; assumption)).
Qed.

Lemma CompileDeallocSCA_ret:
  forall {av} (env : Env av) k v tail tail' ext
    prog,
    {{ [[(ret (SCA _ v)) as kk]]::(tail kk)}}
      prog
    {{ [[(ret (SCA _ v)) as kk]]::(tail' kk) }} ∪ {{ ext }} // env ->
    {{ [[k <~~ ret (SCA _ v) as kk]]::(tail kk)}}
      prog
    {{ [[ret (SCA _ v) as kk]]::(tail' kk) }} ∪ {{ ext }} // env.
Proof.
  intros; apply CompileDeallocSCA;
  SameValues_Facade_t.
Qed.

Lemma ProgOk_Transitivity_Cons :
  forall {av} env ext t1 t2 prog1 prog2 k (v: Comp (Value av)),
    {{ t1 }}                        prog1      {{ [[k <~~ v as _]]::t1 }}     ∪ {{ ext }} // env ->
    {{ [[k <~~ v as _]]::t1 }}       prog2      {{ [[k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                   Seq prog1 prog2 {{ [[k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Unset Implicit Arguments.

Lemma ProgOk_Transitivity_Name :
  forall {av} k env ext t1 t2 prog1 prog2 (v: Comp (Value av)),
    {{ t1 }}                             prog1       {{ [[`k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ v as kk]]::t2 kk }}       prog2       {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
    {{ t1 }}                       Seq prog1 prog2  {{ [[v as kk]]::t2 kk }} ∪ {{ ext }} // env.
Proof.
  SameValues_Facade_t.
Qed.

Section GenSym.
  Require Import NPeano String Coq.Arith.Lt Coq.Arith.Compare_dec.
  Local Open Scope string.

  Lemma digitLtBase m {n} : not (m + n < m).
  Proof.
    red; intros; eapply Le.le_Sn_n; eauto using Le.le_trans, Plus.le_plus_l.
  Qed.

  Definition DigitToString (n: {n | n < 10}) :=
    match n with
    | exist 0 _ => "0" | exist 1 _ => "1" | exist 2 _ => "2" | exist 3 _ => "3" | exist 4 _ => "4"
    | exist 5 _ => "5" | exist 6 _ => "6" | exist 7 _ => "7" | exist 8 _ => "8" | exist 9 _ => "9"
    | exist n pr => False_rect _ (digitLtBase 10 pr)
    end.

  Fixpoint NumberToString_rec (fuel: nat) (n: nat) :=
    match fuel with
    | O => ""
    | S fuel =>
      match (lt_dec n 10) with
      | left pr  => DigitToString (exist _ n pr)
      | right pr => NumberToString_rec fuel (n / 10) ++ NumberToString_rec fuel (n mod 10)
      end
    end.

  Definition NumberToString (n: nat) :=
    NumberToString_rec (S n) n.
End GenSym.

Ltac gensym_rec base start :=
  let name := (eval compute in (base ++ NumberToString start)%string) in
  lazymatch goal with
  | |- context[name] => gensym_rec base (S start)
  | H : context[name] |- _ => gensym_rec base (S start)
  | H := context[name] |- _ => gensym_rec base (S start)
  | _ => constr:(name)
  end.

Ltac gensym base :=
  gensym_rec base 0.

Tactic Notation "debug" constr(msg) :=
  idtac msg.

Tactic Notation "debug" constr(m1) constr(m2) :=
  idtac m1 m2.

Ltac compile_do_bind k compA compB tl :=
  debug "Transforming Fiat-level bind into telescope-level Cons";
  first [rewrite (SameValues_Fiat_Bind_TelEq k compA compB tl) | (* FIXME use a smarter procedure for rewriting here *)
         rewrite (SameValues_Fiat_Bind_TelEq_W k compA compB tl)].

Ltac compile_do_alloc cmp tail :=
  let name := gensym "v" in
  debug "Naming nameless head variable";
  apply (ProgOk_Transitivity_Name name).

Hint Resolve AlwaysComputesToSCA_ret_SCA : dealloc_db.
Hint Resolve AlwaysComputesToSCA_WrapComp_W : dealloc_db.

Ltac compile_dealloc key cmp :=
  debug "Deallocating head binding" key;
  match cmp with
  | _ => apply CompileDeallocSCA; [ solve [eauto with dealloc_db] | ]
  | ret (@ADT _ ?x) => fail
  end.

Ltac compile_do_cons :=
  debug "Moving head of Cons to separate goal";
  apply ProgOk_Transitivity_Cons.

Ltac compile_do_chomp key :=
  debug "Applying chomp rule";
  match key with
  | @Some _ _ => apply ProgOk_Chomp_Some
  | @None _   => apply ProgOk_Chomp_None
  end; intros; computes_to_inv.

Ltac find_in_fmap value fmap :=
  match fmap with
  | StringMap.add ?k value _ => constr:(Some k)
  | StringMap.add ?k _ ?tail => find_in_fmap value tail
  | _ => constr:(@None string)
  end.

Ltac compile_constant value :=
  debug "-> constant value";
  apply CompileConstant.

Ltac compile_read value ext :=
  debug "-> read from the environment";
  let location := find_in_fmap value ext in
  match location with
  | Some ?k => apply (CompileRead (var := k))
  end.

Ltac translate_op gallina_op :=
  match gallina_op with
  | @Word.wplus 32 => constr:(IL.Plus)
  | @Word.wminus 32 => constr:(IL.Minus)
  | @Word.wmult 32 => constr:(IL.Times)
  | _ => fail 1 "Unknown operator" gallina_op
  end.

Ltac compile_binop av op lhs rhs ext :=
  let facade_op := translate_op op in
  let vlhs := find_in_fmap (SCA unit lhs) ext in
  let vrhs := find_in_fmap (SCA unit rhs) ext in
  match constr:(vlhs, vrhs) with
  | (Some ?vlhs, Some ?vrhs) =>
    apply (CompileBinop (var1 := vlhs) (var2 := vrhs) facade_op)
  | (Some ?vlhs, None) =>
    let vrhs := gensym "r" in
    apply (CompileBinop_left (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, Some ?vrhs) =>
    let vlhs := gensym "l" in
    apply (CompileBinop_right (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, None) =>
    let vlhs := gensym "l" in
    let vrhs := gensym "r" in
    apply (CompileBinop_full (var1 := vlhs) (var2 := vrhs) facade_op)
  end.

Ltac compile_do_side_conditions :=
  match goal with
  | _ => abstract decide_not_in
  | [  |- StringMap.find _ _ = Some _ ] => solve [decide_mapsto_maybe_instantiate]
  | [  |- StringMap.MapsTo _ _ _ ] => solve [decide_mapsto_maybe_instantiate]
  end.

Lemma WrapComp_W_rewrite:
  forall (av : Type) (w : Word.word 32),
    Monad.equiv (WrapComp_W (ret w)) (ret (SCA av w)).
Proof.
  unfold WrapComp_W; unfold Monad.equiv; SameValues_Fiat_t;
  repeat match goal with
         | [ H: ret ?a0 ?a |- _ ] => replace (ret a0 a) with (ret a0 ↝ a) in H by reflexivity
         | [ |- context[ret ?a0 ?a] ] => replace (ret a0 a) with (ret a0 ↝ a) by reflexivity
         end; computes_to_inv; SameValues_Fiat_t.
  Transparent computes_to.
  unfold computes_to; subst; SameValues_Fiat_t; reflexivity.
  Opaque computes_to.
Qed.

Hint Rewrite WrapComp_W_rewrite : compile_simple_db.

Ltac compile_simple_internal cmp ext :=
  match cmp with
  | ret (SCA ?av (?op ?lhs ?rhs)) => compile_binop av op lhs rhs ext
  | ret (SCA _ ?w) => compile_constant w; compile_do_side_conditions
  | ret (SCA ?av ?w) => compile_read (SCA av w) ext; compile_do_side_conditions
  end.

(* Hint Extern 1 => solve [decide_not_in] : compile_simple_db. *)
(* Hint Extern 1 => solve [decide_mapsto_maybe_instantiate] : compile_simple_db. *)
(* Hint Extern 1 ({{ Nil }} _ {{ [[ `?s <~~ ?cmp as _ ]] :: Nil }} ∪ {{ ext }} // _) => compile_simple_defaults cmp ext : compile_simple_db. *)

Ltac compile_simple name cmp :=
  debug "Compiling simple pattern";
  (* Rewrite using user-provided lemmas *)
  autorewrite with compile_simple_db;
  (* Recapture cmp after rewriting *)
  lazymatch goal with
  | [  |- {{ Nil }} ?prog {{ Cons ?s ?cmp (fun _ => Nil) }} ∪ {{ ?ext }} // _ ] => compile_simple_internal cmp ext
  end.

Ltac compile_skip :=
  debug "Compiling empty program";
  apply CompileSkip.

Lemma WrapComp_W_computes_to {av} {cmp: Comp W} {v: Value av} :
  WrapComp_W cmp ↝ v ->
  { v' | cmp ↝ v' /\ v = SCA _ v' }.
Proof.
  intros; destruct v.
  - exists w; intuition congruence.
  - exfalso; assumption.
Qed.

Ltac compile_do_unwrap_W val :=
  progress repeat match goal with
  | [ H: WrapComp_W _ ↝ val |- _ ] =>
    let eqn := fresh in
    destruct (WrapComp_W_computes_to H) as [? (? & eqn)];
      rewrite eqn in *; clear eqn H
  end.

Ltac head_constant expr :=
  match expr with
  | ?f _ => head_constant f
  | ?f => f
  end.

Ltac compile_do_unwrap type wrapper key cmp tail val :=
  lazymatch type with
  | W => compile_do_unwrap_W val
  | _ => fail 1 "Don't know how to unwrap" type
  end;
  let wrapper_head := head_constant wrapper in
  cbv beta iota delta [WrappedCons wrapper_head].

(*! FIXME: Why is this first [ ... | fail] thing needed? If it's removed then the lazy match falls through *)
Ltac compile_ProgOk p pre post ext :=
  is_evar p;
  lazymatch constr:(pre, post, ext) with
  | (_,                     (@WrappedCons _ ?T ?wrapper ?k ?cmp ?tl) ?v, _) => first [compile_do_unwrap T wrapper k cmp tl v | fail ]
  | (Cons ?k ?cmp _,        Cons ?k ?cmp _,                              _) => first [compile_do_chomp k | fail ]
  | (Cons (Some ?k) ?cmp _, Cons None ?cmp _,                            _) => first [compile_dealloc k cmp | fail ]
  | (_,                     Cons None ?cmp ?tl,                          _) => first [compile_do_alloc cmp tl | fail ]
  | (_,                     Cons ?k (Bind ?compA ?compB) ?tl,            _) => first [compile_do_bind k compA compB tl | fail ]
  | (Nil,                   Cons (Some ?k) ?cmp (fun _ => Nil),            _) => first [compile_simple k cmp | fail ]
  | (Nil,                   Cons ?k ?cmp ?tl,                            _) => first [compile_do_cons | fail ]
  | (Nil,                   Nil,                                         _) => first [compile_skip | fail ]
  end.

(* Ltac debug_match_ProgOk := *)
(*   lazymatch goal with *)
(*   | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] => *)
(*     pose prog as debug_prog; pose post as debug_post; pose ext as debug_ext; pose env as debug_env; pose pre as debug_pre *)
(*   | _ => fail "Goal does not look like a ProgOk statement" *)
(*   end. *)

Ltac match_ProgOk continuation :=
  lazymatch goal with
  | [  |- {{ ?pre }} ?prog {{ ?post }} ∪ {{ ?ext }} // ?env ] => continuation prog pre post ext
  | _ => fail "Goal does not look like a ProgOk statement"
  end.

Ltac compile_step :=
  idtac;
  match goal with
  | _ => compile_do_side_conditions
  | _ => match_ProgOk compile_ProgOk
  end.

Example simple :
  forall env,
    sigT (fun prog =>
            {{ @Nil unit }}
              prog
            {{ [[`"ret" <~~ (x <- ret (SCA unit (Word.natToWord 32 1));
                             y <- ret (SCA unit (Word.natToWord 32 5));
                             ret (SCA _ (Word.wplus (Word.natToWord 32 1) (Word.natToWord 32 5))))%comp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env).
Proof.
  intros; econstructor.
  repeat compile_step.
Defined.

Definition EmptyEnv : Env unit := (GLabelMap.GLabelMap.empty (FuncSpec unit)).

Opaque Word.natToWord.
Eval simpl in (proj1_sig (simple EmptyEnv)).

(* Definition ExtractSCA (cmp: Comp W) `(v: Value av) (H: WrapComp_W cmp ↝ v) : W. *)
(* Proof. *)
(*   destruct v. *)
(*   - exact w. *)
(*   - exfalso; exact H. *)
(* Defined. *)

(* Lemma ExtractSCA_correct (cmp: Comp W) `(v: Value av): *)
(*   forall (H: WrapComp_W cmp ↝ v), *)
(*     cmp ↝ ExtractSCA cmp v H. *)
(* Proof. *)
(*   intros; destruct v; [ | exfalso ]; exact H. *)
(* Qed. *)

Example simple_binop :
  forall env,
    sigT (fun prog =>
            {{ @Nil unit }}
              prog
            {{ [[`"ret" <~~ (x <- ret (Word.natToWord 32 1);
                             y <- ret (Word.natToWord 32 5);
                             ret (SCA _ (Word.wplus x y)))%comp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env).
Proof.
  intros; econstructor;
  repeat compile_step.
Defined.

Example harder_binop :
  forall env,
    sigT (fun prog =>
            {{ @Nil unit }}
              prog
            {{ [[`"ret" <~~ (x <- ret (Word.natToWord 32 1);
                             y <- ret (Word.natToWord 32 5);
                             z <- ret (Word.natToWord 32 8);
                             t <- ret (Word.natToWord 32 12);
                             ret (SCA _ (Word.wplus x (Word.wplus z (Word.wminus y t)))))%comp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env).
Proof.
  econstructor; repeat compile_step.
Defined.

Ltac spec_t :=
  repeat match goal with
         | _ => red
         | _ => progress intros
         | _ => progress subst
         | [ H: exists t, _ |- _ ] => destruct H
         end; intuition.

Ltac facade_cleanup_call :=
  match goal with
  | [ H: Axiomatic ?s = Axiomatic ?s' |- _ ] => inversion H; subst; clear H
  | [ H: PreCond _ _ _ |- _ ] => progress simpl in H
  | [ H: PostCond _ _ _ |- _ ] => progress simpl in H
  | [ H: context[ListFacts4.mapM] |- _ ] => progress simpl in H
  | [ H: exists w, _ |- _ ] => destruct H
  | _ => GLabelMapUtils.normalize
  | _ => progress cbv beta iota delta [add_remove_many] in *
  | _ => solve [GLabelMapUtils.decide_mapsto_maybe_instantiate]
  | _ => solve [eauto 3 with call_helpers_db]
  | _ => solve [eauto 3 with call_preconditions_db]
  end.

Require Import Program List.

Definition Random := { x: W | True }%comp.

Definition FRandom {av} : AxiomaticSpec av.
Proof.
  refine {|
      PreCond := fun args => args = nil;
      PostCond := fun args ret => args = nil /\ exists w, ret = SCA av w
    |}; spec_t.
Defined.

Lemma FRandom_Precond {av}:
  PreCond (@FRandom av) [].
Proof.
  reflexivity.
Qed.

Lemma Random_caracterization {av}:
  forall x : W, WrapComp_W Random ↝ SCA av x.
Proof.
  constructor.
Qed.

Hint Immediate FRandom_Precond : call_preconditions_db.
Hint Immediate Random_caracterization : call_helpers_db.
Hint Resolve WeakEq_empty_remove : call_helpers_db.

Set Implicit Arguments.

Lemma isTrueExpr_is_true:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (bool2val true) st' -> is_true st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, bool2val, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma isTrueExpr_is_false:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (bool2val false) st' -> is_false st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, bool2val, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma is_true_isTrueExpr:
  forall {av} (gallinaTest : bool) (tmp : StringMap.key) (st' : State av),
    is_true st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (bool2val gallinaTest) st' ->
    gallinaTest = true.
Proof.
  unfold isTrueExpr, bool2val, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Lemma is_false_isTrueExpr:
  forall {av} (gallinaTest : bool) (tmp : StringMap.key) (st' : State av),
    is_false st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (bool2val gallinaTest) st' ->
    gallinaTest = false.
Proof.
  unfold isTrueExpr, bool2val, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Lemma CompileCallRandom:
  forall env : GLabelMap.t (FuncSpec ()),
  forall key var ext,
    var ∉ ext ->
    GLabelMap.MapsTo key (Axiomatic FRandom) env ->
    {{ Nil }}
      Call var key []
    {{ [[ ` var <~~ WrapComp_W Random as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => facade_cleanup_call
         | _ => SameValues_Facade_t_step
         | _ => progress simpl
         end.
Qed.

Example random_sample :
  forall env,
    GLabelMap.MapsTo ("std", "rand") (Axiomatic FRandom) env ->
    sigT (fun prog =>
            {{ @Nil unit }}
              prog
              {{ [[`"ret" <~~ ( x <- Random;
                                y <- Random;
                                ret (SCA _ (Word.wminus (Word.wplus x x) (Word.wplus y y))))%comp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env).
Proof.
  econstructor; repeat compile_step;
  apply (CompileCallRandom (key :=  ("std", "rand"))); compile_step.
Defined.

Definition EnvContainingRandom :=
  GLabelMap.add ("std", "rand") (Axiomatic FRandom) (GLabelMap.empty (FuncSpec unit)).

Lemma p :
  GLabelMap.MapsTo ("std", "rand") (Axiomatic FRandom) EnvContainingRandom.
Proof.
  eauto using GLabelMap.add_1.
Qed.

Notation "A ;; B" := (Seq A B) (at level 76, left associativity, format "'[v' A ';;' '/' B ']'") : facade_scope.
Notation "x := F . G A" := (Call x (F, G) (A)) (at level 76, no associativity, format "x  ':='  F '.' G  A") : facade_scope.
Notation "x := A" := (Assign x A) (at level 61, no associativity) : facade_scope.
Notation "x + A" := (Binop IL.Plus x A) (at level 50, left associativity) : facade_scope.
Notation "x - A" := (Binop IL.Minus x A) (at level 50, left associativity) : facade_scope.
Notation ", x" := (Var x) (at level 20, no associativity, format "',' x") : facade_scope.
Notation "'__'" := (Skip) (at level 20, no associativity) : facade_scope.

(* Local Open Scope facade_scope. *)
Eval simpl in (proj1_sig (random_sample p)).

Lemma SameValues_add_to_ext:
  forall {av} (k : string) (cmp : Comp (Value av)) val
    (tmp : StringMap.key) (ext : StringMap.t (Value av))
    (final_state : State av),
    tmp ∉ ext ->
    final_state ≲ [[ ` k <~~ cmp as _]]::Nil ∪ [tmp <-- SCA _ val]::ext ->
    final_state ≲ [[ ` k <~~ cmp as _]]::Nil ∪ ext.
Proof.
  simpl; intros. SameValues_Fiat_t.
  eauto using WeakEq_pop_SCA, WeakEq_refl, WeakEq_Trans.
Qed.

Hint Resolve SameValues_add_to_ext : SameValues_db.

Lemma CompileIf :
  forall {av} k (gallinaTest: bool) gallinaT gallinaF tmp facadeTest facadeT facadeF env (ext: StringMap.t (Value av)),
    tmp ∉ ext ->
    {{ Nil }}
      facadeTest
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::Nil }}
      facadeT
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaT as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::Nil }}
      facadeF
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaF as _]]::Nil }} ∪ {{ ext }} // env ->
    {{ Nil }}
      (Seq facadeTest (If (isTrueExpr tmp) facadeT facadeF))
    {{ [[`k <~~ if gallinaTest then gallinaT else gallinaF as _]]::Nil }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | [ H: is_true ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (bool2val ?test) ?st |- _ ] => learn (is_true_isTrueExpr H H')
         | [ H: is_false ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (bool2val ?test) ?st |- _ ] => learn (is_false_isTrueExpr H H')
         | _ => solve [eauto using isTrueExpr_is_false, isTrueExpr_is_true]
         end.
Qed.

Lemma push_if :
  forall {A B} (f: A -> B) (x y: A) (b: bool),
    f (if b then x else y) = (if b then f x else f y).
Proof.
  intros; destruct b; reflexivity.
Qed.

Ltac is_pushable_head_constant f :=
  let hd := head_constant f in
  match hd with
  | Cons => fail 1
  | _ => idtac
  end.

Ltac compile_random :=
  match_ProgOk ltac:(fun prog pre post ext =>
                       match constr:(pre, post) with
                       | (Nil, Cons ?s (WrapComp_W Random) (fun _ => Nil)) => apply CompileCallRandom
                       end).

Ltac compile_if :=
  match_ProgOk ltac:(fun prog pre post ext =>
                       match constr:(pre, post) with
                       | (Nil, Cons ?s (if ?a then ret ?b else ret ?c) (fun _ => Nil)) =>
                         let test := gensym "test" in
                         apply (CompileIf (tmp := test))
                       end).

Example random_test :
  forall env,
    GLabelMap.MapsTo ("std", "rand") (Axiomatic FRandom) env ->
    sigT (fun prog =>
            {{ @Nil unit }}
              prog
            {{ [[`"ret" <~~ ( x <- Random;
                              y <- Random;
                              z <- Random;
                              ret (SCA _ (if Word.weqb x (Word.natToWord 32 0) then y else z)))%comp as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // env).
Proof.
  econstructor.

  repeat match goal with
         | _ => compile_step
         | _ => compile_random
         | _ => compile_if
         | [  |- appcontext[?f (if ?b then ?x else ?y)] ] => is_pushable_head_constant f; rewrite (push_if f x y b)
         | _ => eassumption
         end.

Eval simpl in (proj1_sig (simple_binop EmptyEnv)).
Eval simpl in (proj1_sig (harder_binop EmptyEnv)).

