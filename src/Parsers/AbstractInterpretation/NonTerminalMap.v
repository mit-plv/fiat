Require Import Coq.PArith.BinPos Coq.PArith.Pnat.
Require Import Coq.Arith.Arith.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapPositive.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.List.ListMorphisms.
Require Import Fiat.Common.Prod.

Set Implicit Arguments.

Definition nonterminal_to_positive (nt : default_nonterminal_carrierT) : positive
  := Pos.of_nat (S nt).
Definition positive_to_nonterminal (nt : positive) : default_nonterminal_carrierT
  := pred (Pos.to_nat nt).
Lemma positive_to_nonterminal_to_positive nt : nonterminal_to_positive (positive_to_nonterminal nt) = nt.
Proof.
  unfold nonterminal_to_positive, positive_to_nonterminal.
  erewrite <- S_pred by apply Pos2Nat.is_pos.
  rewrite Pos2Nat.id.
  reflexivity.
Qed.
Lemma nonterminal_to_positive_to_nonterminal nt : positive_to_nonterminal (nonterminal_to_positive nt) = nt.
Proof.
  unfold nonterminal_to_positive, positive_to_nonterminal.
  rewrite Nat2Pos.id_max; simpl.
  reflexivity.
Qed.
Lemma nonterminal_to_positive_eq x y
  : nonterminal_to_positive x = nonterminal_to_positive y <-> x = y.
Proof.
  split; try congruence.
  rewrite <- (nonterminal_to_positive_to_nonterminal x), <- (nonterminal_to_positive_to_nonterminal y) at 2.
  congruence.
Qed.
Lemma positive_to_nonterminal_eq x y
  : positive_to_nonterminal x = positive_to_nonterminal y <-> x = y.
Proof.
  split; try congruence.
  rewrite <- (positive_to_nonterminal_to_positive x), <- (positive_to_nonterminal_to_positive y) at 2.
  congruence.
Qed.
Lemma positive_to_nonterminal_eq_iff_l x y
  : positive_to_nonterminal x = y <-> x = nonterminal_to_positive y.
Proof.
  rewrite <- positive_to_nonterminal_eq, nonterminal_to_positive_to_nonterminal; reflexivity.
Qed.
Lemma positive_to_nonterminal_eq_iff_r x y
  : x = positive_to_nonterminal y <-> nonterminal_to_positive x = y.
Proof.
  rewrite <- positive_to_nonterminal_eq, nonterminal_to_positive_to_nonterminal; reflexivity.
Qed.

Local Ltac nonterminal_iff_t :=
  repeat match goal with
         | _ => intro
         | [ |- iff _ _ ] => split
         | [ |- prod _ _ ] => split
         | [ H : ex _ |- _ ] => destruct H
         | [ H : forall k : default_nonterminal_carrierT, _, k' : positive |- _ ]
           => specialize (H (positive_to_nonterminal k'))
         | [ H : forall k : positive, _, k' : default_nonterminal_carrierT |- _ ]
           => specialize (H (nonterminal_to_positive k'))
         | [ k' : positive |- exists k : default_nonterminal_carrierT, _ ]
           => exists (positive_to_nonterminal k')
         | [ k' : default_nonterminal_carrierT |- exists k : positive, _ ]
           => exists (nonterminal_to_positive k')
         | _ => assumption
         | _ => rewrite nonterminal_to_positive_to_nonterminal in *
         end.

Lemma forall_nonterminal_iffP (P : default_nonterminal_carrierT -> Prop)
  : (forall k, P k) <-> (forall k, P (positive_to_nonterminal k)).
Proof. nonterminal_iff_t. Qed.
Local Notation iffT A B := ((A -> B) * (B -> A))%type (only parsing).
Lemma forall_nonterminal_iffT (P : default_nonterminal_carrierT -> Type)
  : iffT (forall k, P k) (forall k, P (positive_to_nonterminal k)).
Proof. nonterminal_iff_t. Qed.
Lemma exists_nonterminal_iff (P : default_nonterminal_carrierT -> Prop)
  : (exists k, P k) <-> (exists k, P (positive_to_nonterminal k)).
Proof. nonterminal_iff_t. Qed.

Module NonTerminalMap <: WS.
  Module E <: DecidableType.
    Definition t := default_nonterminal_carrierT.
    Definition eq : t -> t -> Prop := eq.
    Definition eq_refl : forall x, eq x x := @eq_refl _.
    Definition eq_sym : forall x y, eq x y -> eq y x := @eq_sym _.
    Definition eq_trans : forall x y z, eq x y -> eq y z -> eq x z := @eq_trans _.
    Definition eq_dec : forall x y, {eq x y} + {~eq x y} := Nat.eq_dec.
  End E.
  Definition key := default_nonterminal_carrierT.
  Definition t := PositiveMap.t.
  Definition empty := PositiveMap.empty.
  Definition is_empty := PositiveMap.is_empty.
  Definition add elt (k : key) := @PositiveMap.add elt (nonterminal_to_positive k).
  Definition find elt (k : key) := @PositiveMap.find elt (nonterminal_to_positive k).
  Definition remove elt (k : key) := @PositiveMap.remove elt (nonterminal_to_positive k).
  Definition mem elt (k : key) := @PositiveMap.mem elt (nonterminal_to_positive k).
  Definition map := PositiveMap.map.
  Definition mapi elt elt' f := @PositiveMap.mapi elt elt' (fun k => f (positive_to_nonterminal k)).
  Definition map2 := PositiveMap.map2.
  Definition elements elt (m : t elt) : list (key * elt)
    := List.map (fun xy => (positive_to_nonterminal (fst xy), snd xy)) (PositiveMap.elements m).
  Definition cardinal := PositiveMap.cardinal.
  Definition fold elt A (f : key -> elt -> A -> A)
    := @PositiveMap.fold elt A (fun k => f (positive_to_nonterminal k)).
  Definition equal := PositiveMap.equal.
  Definition MapsTo elt (k : key) := @PositiveMap.MapsTo elt (nonterminal_to_positive k).
  Definition In elt (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.
  Definition Empty elt m := forall (a : key)(e:elt) , ~ MapsTo a e m.
  Definition eq_key elt (p p':key*elt) := E.eq (fst p) (fst p').
  Definition eq_key_elt elt (p p':key*elt) :=
    E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition Equal elt (m m' : t elt) := forall y, find y m = find y m'.
  Definition Equiv elt (eq_elt:elt->elt->Prop) m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb elt (cmp: elt->elt->bool) := Equiv (Cmp cmp).

  Definition MapsTo_iff1 elt k v (m : t elt) : MapsTo k v m <-> PositiveMap.MapsTo (nonterminal_to_positive k) v m
    := reflexivity _.
  Lemma MapsTo_iff2 elt k v (m : t elt) : MapsTo (positive_to_nonterminal k) v m <-> PositiveMap.MapsTo k v m.
  Proof.
    unfold MapsTo.
    rewrite positive_to_nonterminal_to_positive; reflexivity.
  Qed.

  Lemma Empty_iff elt (m : t elt) : Empty m <-> PositiveMap.Empty m.
  Proof.
    unfold Empty, PositiveMap.Empty, key, MapsTo.
    rewrite forall_nonterminal_iffP.
    setoid_rewrite positive_to_nonterminal_to_positive; reflexivity.
  Qed.

  Local Ltac t_app :=
    first [ reflexivity
          | apply PositiveMap.find_1
          | apply PositiveMap.find_2
          | apply PositiveMap.MapsTo_1
          | apply PositiveMap.empty_1
          | apply PositiveMap.is_empty_1
          | apply PositiveMap.is_empty_2
          | apply PositiveMap.add_1
          | apply PositiveMap.add_2
          | apply PositiveMap.add_3
          | apply PositiveMap.remove_1
          | apply PositiveMap.remove_2
          | apply PositiveMap.remove_3
          | apply PositiveMap.map_1
          | apply PositiveMap.map_2
          | apply PositiveMap.elements_1
          | apply PositiveMap.elements_2
          | apply PositiveMap.elements_3w
          | apply PositiveMap.cardinal_1
          | apply PositiveMap.fold_1
          | apply PositiveMap.equal_1
          | apply PositiveMap.equal_2
          | refine (PositiveMap.mapi_1 _)
          | refine (PositiveMap.mapi_2 _ _)
          | apply PositiveMap.map2_1
          | apply PositiveMap.map2_2
          | intro; t_app ].
  Local Ltac conv :=
    clear;
    repeat match goal with k : key |- _ => revert k end;
    cbv [E.eq MapsTo Empty add remove In find eq_key_elt elements eq_key] in *;
    repeat first [ progress rewrite
                            ?forall_nonterminal_iffP,
                   ?exists_nonterminal_iff,
                   ?positive_to_nonterminal_to_positive,
                   ?nonterminal_to_positive_to_nonterminal,
                   ?positive_to_nonterminal_eq_iff_l,
                   ?positive_to_nonterminal_eq_iff_r,
                   ?NoDupA_map_iff,
                   ?map_length
                 | setoid_rewrite forall_nonterminal_iffP
                 | setoid_rewrite exists_nonterminal_iff
                 | setoid_rewrite positive_to_nonterminal_to_positive
                 | setoid_rewrite nonterminal_to_positive_to_nonterminal
                 | setoid_rewrite positive_to_nonterminal_eq_iff_l
                 | setoid_rewrite positive_to_nonterminal_eq_iff_r
                 | rewrite (@InA_map_iff _ _ _ _ _ _ (_, _)) by reflexivity
                 | rewrite <- fold_map
                 | progress simpl @fst in *
                 | progress simpl @snd in *
                 | lazymatch goal with
                   | [ |- ?A -> ?B ] => fail
                   | [ |- forall x, _ ] => intro
                   end ].
  Local Ltac t := conv; t_app.

  Section Spec.
    Context (elt elt' elt'' : Type)
            (m m' m'' : t elt)
            (x y z : key)
            (e e' : elt).

    Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
    Proof. t. Qed.
    Definition mem_1 : In x m -> mem x m = true := @PositiveMap.mem_1 _ _ _.
    Definition mem_2 : mem x m = true -> In x m := @PositiveMap.mem_2 _ _ _.
    Lemma empty_1 : Empty (empty elt).
    Proof. t. Qed.
    Lemma is_empty_1 : Empty m -> is_empty m = true.
    Proof. t. Qed.
    Lemma is_empty_2 : is_empty m = true -> Empty m.
    Proof. t. Qed.
    Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
    Proof. t. Qed.
    Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
    Proof. t. Qed.
    Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
    Proof. t. Qed.
    Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
    Proof. t. Qed.
    Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
    Proof. t. Qed.
    Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
    Proof. t. Qed.
    Lemma find_1 : MapsTo x e m -> find x m = Some e.
    Proof. t. Qed.
    Lemma find_2 : find x m = Some e -> MapsTo x e m.
    Proof. t. Qed.
    Lemma elements_1 :
      MapsTo x e m -> InA (@eq_key_elt _) (x,e) (elements m).
    Proof. t. Qed.
    Lemma elements_2 :
      InA (@eq_key_elt _) (x,e) (elements m) -> MapsTo x e m.
    Proof. t. Qed.
    Lemma elements_3w : NoDupA (@eq_key _) (elements m).
    Proof. t. Qed.
    Local Ltac elements_n_eq lem :=
      let H := fresh in
      intro H; first [ apply lem in H | apply lem ];
      cbv [eq_key_elt E.eq] in *;
      repeat match goal with
             | _ => assumption
             | _
               => first [ setoid_rewrite prod_and_iff
                        | setoid_rewrite <- path_prod_uncurried_iff
                        | rewrite Common.InA_In_eq ]
             | [ H : _ |- _ ]
               => first [ setoid_rewrite prod_and_iff in H
                        | setoid_rewrite <- path_prod_uncurried_iff in H
                        | rewrite Common.InA_In_eq in H ]
             end.

    Lemma elements_1_eq :
      MapsTo x e m -> List.In (x,e) (elements m).
    Proof. elements_n_eq elements_1. Qed.
    Lemma elements_2_eq :
      List.In (x,e) (elements m) -> MapsTo x e m.
    Proof. elements_n_eq elements_2. Qed.
    Lemma find_elements_iff
      : find x m = Some e <-> List.In (x, e) (elements m).
    Proof.
      split; intro H;
        [ apply elements_1_eq, find_2, H
        | apply find_1, elements_2_eq, H ].
    Qed.
    Lemma cardinal_1 : cardinal m = length (elements m).
    Proof. t. Qed.
    Lemma fold_1 :
      forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
    Proof. t. Qed.

    Variable cmp : elt -> elt -> bool.

    Lemma Equal_iff (m0 m1 : t elt) : Equal m0 m1 <-> PositiveMap.Equal m0 m1.
    Proof. unfold Equal, PositiveMap.Equal; t. Qed.
    Lemma Equiv_iff eq_elt (m0 m1 : t elt) : Equiv eq_elt m0 m1 <-> PositiveMap.Equiv eq_elt m0 m1.
    Proof. unfold Equiv, PositiveMap.Equiv, In, PositiveMap.In; t. Qed.
    Lemma equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
    Proof. unfold Equivb. rewrite Equiv_iff; t. Qed.
    Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
    Proof. unfold Equivb; rewrite Equiv_iff; t. Qed.
  End Spec.

  Lemma elements_find_iff elt kv (m : t elt)
    : List.In kv (elements m) <-> find (fst kv) m = Some (snd kv).
  Proof.
    destruct kv; symmetry; apply find_elements_iff.
  Qed.

  Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
      MapsTo x e m -> MapsTo x (f e) (map f m).
  Proof. t. Qed.
  Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
      In x (map f m) -> In x m.
  Proof. t. Qed.
  Lemma mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
                        (f:key->elt->elt'), MapsTo x e m ->
                                            exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Proof. t. Qed.
  Lemma mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
                        (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Proof. t. Qed.
  Lemma mapi_1_eq
        (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt')
    : MapsTo x e m -> MapsTo x (f x e) (mapi f m).
  Proof.
    intro H; eapply mapi_1 in H; unfold E.eq in *.
    destruct H as [? [? ?]]; subst; eassumption.
  Qed.
  Lemma map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	                (x:key)(f:option elt->option elt'->option elt''),
      In x m \/ In x m' ->
      find x (map2 f m m') = f (find x m) (find x m').
  Proof. t. Qed.
  Lemma map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	                (x:key)(f:option elt->option elt'->option elt''),
      In x (map2 f m m') -> In x m \/ In x m'.
  Proof. t. Qed.
End NonTerminalMap.
