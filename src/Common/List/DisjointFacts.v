Require Import Coq.Lists.List.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.

Lemma disjoint_nil_l {A} beq (ls : list A)
  : disjoint beq nil ls = true.
Proof. reflexivity. Qed.
Lemma disjoint_nil_r {A} beq (ls : list A)
  : disjoint beq ls nil = true.
Proof. rewrite disjoint_comm, disjoint_nil_l; reflexivity. Qed.
Lemma disjoint_cons_l {A} beq x (xs ls : list A)
  : disjoint beq (x::xs) ls = (negb (Equality.list_bin beq x ls) && disjoint beq xs ls)%bool.
Proof. reflexivity. Qed.
Lemma disjoint_cons_r {A} beq x (xs ls : list A)
  : disjoint beq ls (x::xs) = (negb (Equality.list_bin (fun a b => beq b a) x ls) && disjoint beq ls xs)%bool.
Proof. rewrite disjoint_comm, disjoint_cons_l, <- disjoint_comm; reflexivity. Qed.
Lemma disjoint_uniquize {A} beq
      (bl : forall x y, beq x y = true -> x = y)
      (lb : forall x y, x = y -> beq x y = true)
      (ls1 ls2 : list A)
  : disjoint beq ls1 ls2 = disjoint beq (uniquize beq ls1) (uniquize beq ls2).
Proof.
  revert ls2; induction ls1 as [|l ls1 IHls1]; simpl; intro ls2.
  { rewrite !disjoint_nil_l; reflexivity. }
  { repeat match goal with
           | _ => reflexivity
           | _ => rewrite !disjoint_cons_l
           | [ IH : forall ls, disjoint _ _ _ = disjoint _ _ _ |- _ ]
             => rewrite IH; clear IH
           | [ |- andb _ _ = andb _ _ ] => apply f_equal2
           | _ => progress unfold negb
           | _ => progress simpl
           | [ |- context[if ?b then _ else _] ]
             => destruct b eqn:?
           | [ H : Equality.list_bin _ _ _ = true |- _ ]
             => apply (@Equality.list_in_bl _ _ bl) in H
           | [ H : List.In _ (uniquize _ _) |- _ ]
             => apply ListFacts.uniquize_In in H
           | [ |- context[disjoint ?beq ?ls1 ?ls2] ]
             => destruct (disjoint beq ls1 ls2) eqn:?
           | [ H : disjoint _ _ _ = true |- _ ]
             => pose proof (@disjoint_bl _ _ lb _ _ H); clear H
           | [ H : Equality.list_bin _ _ _ = false |- _ ]
             => apply Equality.list_in_bl_false in H; [ | assumption.. ]
           | [ |- false = true ] => exfalso
           | [ |- true = false ] => exfalso
           | _ => solve [ eauto using uniquize_In_refl ]
           | [ H : _ |- _ ] => solve [ eapply H; eauto using uniquize_In_refl ]
           end. }
Qed.
