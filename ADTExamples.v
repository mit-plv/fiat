Require Import String Omega.
Require Import FunctionalExtensionality.
Require Export ADT ADTRefinement.

Generalizable All Variables.
Set Implicit Arguments.

(** * Basic ADT definitions *)
Section comp_env.
  (** * An example, composing binary commutative associative calculators for computable nat multisets *)

  Definition multiset := nat -> nat.
  Definition add (s : multiset) (n : nat) : multiset
    := fun m => if eq_nat_dec n m
                then S (s m)
                else s m.

  Require Import Min Max List.

  Coercion sumbooltobool A B : {A} + {B} -> bool := fun x => if x then true else false.

  Infix "<=" := le_dec : bool_scope.
  Infix "<" := lt_dec : bool_scope.
  Infix ">=" := ge_dec : bool_scope.
  Infix ">" := gt_dec : bool_scope.

  Definition add_spec : mutatorMethodSpec multiset
    := fun m x m' => forall k, m' k = (add m x) k.

  Arguments add_spec / .

  Definition bin_op_spec (op : nat -> nat -> nat) (default_value : nat)
  : observerMethodSpec multiset
    := fun m x n => exists l : list nat,
                      (forall v, m v = count_occ eq_nat_dec l v)
                      /\ match l with
                           | nil => n = default_value
                           | cons z zs => n = fold_right op z zs
                         end.

  Arguments bin_op_spec / .

  Definition NatBinOpSpec
             (op : nat -> nat -> nat)
             (is_assoc : forall x y z, op x (op y z) = op (op x y) z)
             (is_comm : forall x y, op x y = op y x)
             (default_value : nat)
  : ADT
    := pickImpl (fun _ : unit => add_spec) (fun _ : unit => bin_op_spec op default_value).

  Local Obligation Tactic :=
    eauto with arith;
    try solve [ repeat match goal with
                         | _ => progress (simpl; rewrite_hyp'; trivial)
                         | [ |- _ -> _ ] => let x := fresh in intro x; induction x; trivial
                       end
              | intros; omega ].

  Program Definition NatLower default_value : ADT
    := NatBinOpSpec min _ _ default_value.

  Program Definition NatUpper default_value : ADT
    := NatBinOpSpec max _ _ default_value.

  Program Definition NatSum default_value : ADT
    := NatBinOpSpec plus _ _ default_value.

  Program Definition NatProd default_value : ADT
    := NatBinOpSpec mult _ _ default_value.

  Hint Immediate le_min_l le_min_r le_max_l le_max_r.

  Lemma min_trans : forall n m v,
                      n <= v
                      -> min n m <= v.
    intros; destruct (min_spec n m); omega.
  Qed.

  Lemma max_trans : forall n m v,
                      n >= v
                      -> max n m >= v.
    intros; destruct (max_spec n m); omega.
  Qed.

  Hint Resolve min_trans max_trans.

  Arguments add _ _ _ / .

  Section def_NatBinOpI.

    Local Ltac induction_list_then tac :=
      lazymatch goal with
  | [ l : list _ |- _ ]
    => repeat match goal with
                | [ H : appcontext[l] |- _ ] => clear H
              end;
      induction l; tac
    end.

    Local Ltac manipulate_op op_assoc op_comm :=
      match goal with
        | _ => reflexivity
        | _ => progress simpl in *
        | _ => apply op_comm
        | _ => rewrite <- ?op_assoc; revert op_assoc op_comm; rewrite_hyp'; intros
        | _ => rewrite ?op_assoc; revert op_assoc op_comm; rewrite_hyp'; intros
        | _ => rewrite <- ?op_assoc; f_equal; []
        | _ => rewrite ?op_assoc; f_equal; []
        | _ => apply op_comm
      end.

    Local Ltac deep_manipulate_op op op_assoc op_comm can_comm_tac :=
      repeat match goal with
               | _ => progress repeat manipulate_op op_assoc op_comm
               | [ |- appcontext[op ?a ?b] ]
                 => can_comm_tac a b;
                   rewrite (op_comm a b);
                   let new_can_comm_tac :=
                       fun x y =>
                         can_comm_tac x y;
                         try (unify x a;
                              unify y b;
                              fail 1 "Cannot commute" a "and" b "again")
                   in deep_manipulate_op op op_assoc op_comm new_can_comm_tac
             end.

    Local Ltac solve_after_induction_list op op_assoc op_comm :=
      solve [ deep_manipulate_op op op_assoc op_comm ltac:(fun a b => idtac) ].


    Local Ltac t :=
      repeat match goal with
               | _ => assumption
               | _ => intro
               | _ => progress simpl in *
               | [ |- appcontext[if string_dec ?A ?B then _ else _ ] ]
                 => destruct (string_dec A B)
               | _ => progress subst
               | [ H : ex _ |- _ ] => destruct H
               | [ H : and _ _ |- _ ] => destruct H
               | _ => split
               | [ H : option _ |- _ ] => destruct H
               | [ H : _ |- _ ] => solve [ inversion H ]
               | [ |- appcontext[match ?x with _ => _ end] ] => destruct x
               | [ H : appcontext[match ?x with _ => _ end] |- _  ] => destruct x
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
               | _ => progress f_equal; []
               | _ => progress intuition
               | _ => repeat esplit; reflexivity
               | [ H : _ |- _ ] => rewrite H; try (rewrite H; fail 1)
             end.

    Local Ltac t' op op_assoc op_comm :=
      repeat first [ progress t
                   | progress induction_list_then ltac:(solve_after_induction_list op op_assoc op_comm) ].

    Definition NatBinOpImpl op is_assoc is_comm default_value :  
      { impl : ADT | refineADT impl (NatBinOpSpec op is_assoc is_comm default_value)}.
    Proof.
      eexists.
      set_evars.

      set_evars.

    | forall l, refineADT { x : _ | is_min_max l x }%comp (f l) }.
    Proof.

    Definition NatBinOpImpl
               (op : nat -> nat -> nat)
               (is_assoc : forall x y z, op x (op y z) = op (op x y) z)
               (is_comm : forall x y, op x y = op y x)
               (default_value : nat) : ADT.
    Proof.
      intros.
      refine {|
          Model := option nat;
          MutatorMethods u val x := (ret (match val with
                                                 | None => Some x
                                                 | Some x' => Some (op x x')
                                               end,
                                               0))%comp;
          ObserverMethods u val x := (ret (val,
                                                match val with
                                                  | None => default_value
                                                  | Some x => x
                                                end))%comp
        |};
        intros [];
        solve [ (intros m [n|] [l [H0 H1] ] x ? ?);
                inversion_by computes_to_inv; subst; simpl in *;
                (exists (add m x));
                repeat split;
                try (exists (x::l));
                abstract t' op op_assoc op_comm
              | intros m [n|] [l [H0 H1] ] x ? ?;
                       inversion_by computes_to_inv; subst; simpl in *;
                repeat (split || exists m || exists l);
                abstract t' op op_assoc op_comm
              | intros m [n|] [l [H0 H1] ] x ? ?;
                       inversion_by computes_to_inv; subst; simpl in *;
                [ repeat split;
                  try (exists (add (fun _ => 0) n));
                  repeat split;
                  try (exists (n::nil));
                  abstract (repeat split)
                | repeat split;
                  try (exists m);
                  repeat split;
                  try (exists l);
                  abstract (repeat split; assumption) ]
              ].
    Defined.
  End def_NatBinOpI.

  Section nat_op_ex.
    Variable default_val : nat.

    Definition NatLowerI : ADTimpl (NatLower default_val)
      := NatBinOpI _ _ _ _.

    Definition NatUpperI : ADTimpl (NatUpper default_val)
      := NatBinOpI _ _ _ _.

    Definition NatSumI : ADTimpl (NatSum default_val)
      := NatBinOpI _ _ _ _.

    Definition NatProdI : ADTimpl (NatProd default_val)
      := NatBinOpI _ _ _ _.
  End nat_op_ex.

  Local Open Scope string_scope.

  Definition NatSumProd_spec : ADT
    := {| Model := multiset;
          MutatorIndex := unit;
          ObserverIndex := unit + unit;
          MutatorMethodSpecs u := add_spec;
          ObserverMethodSpecs u m x n :=
            match u with
              | inl _ => bin_op_spec plus 0 m x n
              | inr _ => bin_op_spec mult 1 m x n
            end
       |}.
End comp_env.
