Require Import String Omega.
Require Import FunctionalExtensionality.
Require Export ADT ADTImplementation ADTPartialImplementation.

Generalizable All Variables.
Set Implicit Arguments.

(** * Basic ADT definitions *)
Section comp_env.
  (** We have one ambiant [funcs] and [denote_funcs] around for everything. *)
  Variable funcs : string -> Type * Type.
  Variable denote_funcs : forall name, fst (funcs name) -> Comp funcs (snd (funcs name)).

  (** We set up some notations so we don't need to think about [funcs] and [denote_funcs]. *)
  Local Notation methodTypeD := (methodTypeD funcs).
  Local Notation mutatorMethodCorrect := (@mutatorMethodCorrect funcs denote_funcs).
  Local Notation observerMethodCorrect := (@observerMethodCorrect funcs denote_funcs).
  Local Notation ADTimpl := (@ADTimpl funcs denote_funcs).
  Local Notation PartialADTimpl := (@PartialADTimpl funcs denote_funcs).

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
  (*Infix "->" := implb : bool_scope.*)

  (*
Fixpoint make_specs model (spec_list : list (string * methodSpec model))
  := fun s
     => match spec_list with
          | cons spec specs
            => if string_dec s (fst spec)
               then snd spec
               else make_specs specs s
          | nil => fun _ _ _ _ => True
        end.

Arguments make_specs / .

Definition common_multiset_specs (addname : string) : list (string * methodSpec multiset)
  := (addname,
      fun d x d' y
      => y = 0
         /\ d' = add d x)::nil.

Arguments common_multiset_specs / .

Definition make_accessor
           (model : Type) (f : nat -> model -> nat -> Prop)
: methodSpec model
  := fun d n d' n'
     => d = d'
        /\ f n d n'.

Arguments make_accessor / .
   *)


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

  Definition NatBinOp
             (op : nat -> nat -> nat)
             (is_assoc : forall x y z, op x (op y z) = op (op x y) z)
             (is_comm : forall x y, op x y = op y x)
             (default_value : nat)
  : ADT
    := {|
        Model := multiset;
        MutatorIndex := unit;
        ObserverIndex := unit;
        MutatorMethodSpecs u := add_spec;
        ObserverMethodSpecs u := bin_op_spec op default_value
      |}.

  Local Obligation Tactic :=
    eauto with arith;
    try solve [ repeat match goal with
                         | _ => progress (simpl; rewrite_hyp'; trivial)
                         | [ |- _ -> _ ] => let x := fresh in intro x; induction x; trivial
                       end
              | intros; omega ].

  Program Definition NatLower default_value : ADT
    := NatBinOp min _ _ default_value.

  Program Definition NatUpper default_value : ADT
    := NatBinOp max _ _ default_value.

  Program Definition NatSum default_value : ADT
    := NatBinOp plus _ _ default_value.

  Program Definition NatProd default_value : ADT
    := NatBinOp mult _ _ default_value.


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

    Definition NatBinOpI
    : `(ADTimpl (@NatBinOp op op_assoc op_comm default_value)).
    Proof.
      intros.
      refine {|
          State := option nat;
          RepInv := fun (m : Model (NatBinOp op op_assoc op_comm default_value)) n
                    => exists l : list nat,
                         (forall v, m v = count_occ eq_nat_dec l v)
                         /\ match l with
                              | nil => n = None
                              | cons x xs => n = Some (fold_right op x xs)
                            end;
          MutatorMethodBodies u val x := (ret (match val with
                                                 | None => Some x
                                                 | Some x' => Some (op x x')
                                               end,
                                               0))%comp;
          ObserverMethodBodies u val x := (ret (val,
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

  Local Ltac nat_sum_prod_pi_t :=
    repeat match goal with
             | _ => intro
             | _ => eassumption
             | _ => esplit
             | _ => apply functional_extensionality_dep; intro
             | _ => rewrite_hyp; exact eq_refl
             | _ => progress destruct_sum_in_match
             | _ => progress destruct_head_hnf Empty_set
           end.

  Definition NatSumProdPI : PartialADTimpl NatSumProd_spec.
  Proof with try solve [ nat_sum_prod_pi_t ]; simpl.
    eapply (add_component NatSumProd_spec
                          (NatSumI 0)
                          (later := unit)
                          (fun x => x)
                          (fun x => inr x)
                          (fun x => x) (fun x => x))...
    let A := match goal with |- PartialADTimpl ?A => constr:(A) end in
    eapply (add_component A
                          (NatProdI 1) (later := Empty_set)
                          (fun x => inl x)
                          (fun x => match x with end)
                          (fun x => x)
                          (fun x => x))...
    apply no_observers...
  Defined.

  Definition NatSumProdI : ADTimpl NatSumProd_spec
    := ADTimpl_of_PartialADTimpl NatSumProdPI.
End comp_env.
