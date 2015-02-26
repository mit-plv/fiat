Require Import String Omega.
Require Import FunctionalExtensionality.
Require Export ADT ADTRefinement ADTCache ADTRepInv ADTExamples.BinaryOperationSpec
        ADTExamples.BinaryOperationImpl ADTExamples.BinaryOperationRefinements
        ADTRefinement.BuildADTRefinements ADTRefinement.BuildADTSetoidMorphisms.

Generalizable All Variables.
Set Implicit Arguments.

Section ImplExamples.

  Require Import Min.

  (* Proofs of various [op] properties for [min]. *)
  Lemma min_trans : forall n m v,
                      n <= v ->
                      min n m <= v.
    intros; destruct (min_spec n m); omega.
  Qed.
  Hint Resolve min_trans.

  Lemma min_assoc
  : forall x y z : nat, min (min x y) z = min x (min y z).
  Proof.
    intros; rewrite min_assoc; eauto.
  Qed.
  Hint Resolve min_assoc.

  Lemma min_returns_arg
  : forall n0 m : nat, min n0 m = n0 \/ min n0 m = m.
  Proof.
    intros; edestruct min_dec; eauto.
  Qed.
  Hint Resolve min_returns_arg.

  Lemma min_preserves_le
  : forall n m : nat, min n m <= m.
  Proof.
    intros; destruct (min_dec n m); eauto with arith.
  Qed.
  Hint Resolve min_preserves_le.

  Hint Resolve min_comm.

  Arguments NatLower / .

  Definition MinCollectionSig : ADTSig :=
    ADTsignature {
        "Insert" : rep × nat → rep ;
        "Min" : rep × nat → nat
      }%ADTSig.

  (* The original MinCollection example folds min over a list
     implementing the multiset. This is slow, of course. *)

  Definition defaultSpec : nat -> Prop := fun _ => True.

  Definition MinCollectionSpec
  : ADT MinCollectionSig :=
    ADTRep multiset `[
             def "Insert" `[ m `: rep , n `: nat ]` : rep :=
               {m' | add_spec m n m'}%comp ;
             def "Min" `[m `: rep , n `: nat ]` : nat :=
                 {n' | bin_op_spec le defaultSpec m n n'}%comp
           ]`%ADT .

  Arguments MinCollectionSpec / .

  Definition mslAbsR (or : multiset) (nr : list nat) :=
    or = absList2Multiset nr.

  Definition MinCollection' (defaultValue : nat) :
    { Rep : ADT MinCollectionSig
    | refineADT MinCollectionSpec Rep }.
  Proof.
    hone' representation using mslAbsR.
    hone' observer "Min"%string using (bin_op_impl min defaultValue);
      intros; subst.
    unfold mslAbsR.
    rewrite refine_bin_op_spec' with (defaultValue := defaultValue).
    unfold bin_op_impl; reflexivity.
    admit.
    hone' mutator "Insert"%string using add_impl.
    admit.
    finish sharpening.
  Defined.

  Arguments NatBinOpSpec / .
  Arguments pickImpl / .

  (* Still need to clean this proof up to make it readable.
             More notation, better tactic support. *)

  Ltac autorefine :=
    unfold repInvAbsR in *|-*;
    subst; split_and; intros;
    autorewrite with refine_monad;
    eauto 50 with cache_refinements bin_op_refinements typeclass_instances;
    match goal with
        |- refine _ (ret _) => let v := fresh in
                               let CompV := fresh in
                               intros v CompV; apply computes_to_inv in CompV;
                               subst; econstructor; intros
      | _ => idtac
    end.

  (* This example derivation uses an option nat to
   represent the minimum element of the collection,
   updating the value each time an element is inserted. *)

  Definition MinCollectionCached (defaultValue : nat) :
    Sharpened MinCollectionSpec.
  Proof.
    (* Step 1: Update the representation. *)
    hone' representation using (fun or (nr : option nat) =>
                                 match nr with
                                     | Some n => nonempty_spec le or n
                                     | None => empty_spec (fun _ => True) or defaultValue
                                 end).
    (* Step 2: Refine the insert/add mutator method. *)
    hone' mutator "Insert"%string using (fun r n =>
                             ret (match r with
                               | Some n' => Some (min n' n)
                               | None => Some n
                             end)).
    repeat autorefine.
    econstructor; intros;
      unfold add_spec; eexists (add or n); destruct r_n; autorefine.
    (* Step 3: Add the Cache and replace observer. *)
    hone' observer "Min"%string using (fun (r : option nat) (n : nat) =>
                              ret (match r with
                                         | Some n => n
                                         | None => defaultValue
                                   end)).
    repeat autorefine.
    destruct r_n; unfold bin_op_spec; autorefine.
    (* Step 4: All done :). *)
    finish sharpening.
  Defined.

  (* Show the term derived above as a sanity check. *)
  Goal (forall b, MutatorMethods (proj1_sig (MinCollectionCached 0))
                                 {| bounded_s := "Insert"%string |} = b).
    simpl; unfold getMutDef; simpl.
  Abort.

  (* Slightly longer derivation which first adds a cache, then
     forgets the original list. Silly example, but it shows that
     everything works. It's also not as automated a derivation as
     I would like, but it's meant to be more of a proof of concept
     anyways. *)

  Definition MinCollectionCached' (defaultValue : nat) :
    Sharpened MinCollectionSpec.
  Proof.
    (* Step 1: Update the representation. *)
    hone' representation using (fun or nr => or = (absList2Multiset nr)).
    (* Step 2: Refine the insert/add mutator method. *)
    hone' mutator "Insert"%string using add_impl.
    intros; subst; rewrite refine_add_impl'.
    unfold add_impl; autorefine; auto.
    (* Step 3: Add the Cache and replace observer. *)
    cache observer using spec
          (fun r => bin_op_spec le (fun _ => True) (absList2Multiset r) defaultValue).
    autorefine.
    (* Step 4: Replace the [Pick] used to get [cachedVal] in the add implementation. *)
    hone mutator () using (update_cachedOp min) under invariant
         (fun r => bin_op_spec le (fun _ => True) (absList2Multiset (origRep r)) defaultValue (cachedVal r)).
    { unfold repInvBiR in *|-; intuition; subst.
      subst; unfold add_impl; simpl; autorewrite with refine_monad.
      rewrite bin_op_spec_unique with (v := match origRep r_n with
                                              | [] => n
                                              | _ => min (cachedVal r_n) n
                                            end)
                                        (n := defaultValue);
        autorewrite with refine_monad; eauto 50 with cache_refinements bin_op_refinements typeclass_instances.
      rewrite refine_pick_repInvBiR.
      unfold update_cachedOp; destruct (origRep r_n); reflexivity.
      simpl origRep; simpl cachedVal; autorefine.
    }
    destruct H4; congruence.
    unfold pointwise_relation; simpl; intros; autorefine.
    (* Step 5: Replace the list implementing the multiset with a boolean
      flag. *)
    eapply SharpenStep.
    eapply simplifyRep with
    (oldRep := cachedRep (list nat) nat)
      (newRep := option nat)
    (simplifyf := fun r => match (origRep r) with
                               | [] => None
                               | _ :: _ => Some (cachedVal r)
                           end)
    (concretize := fun r => match r with
                                | Some n => {| origRep := n :: [];
                                               cachedVal := n |}
                                | None  => {| origRep := [];
                                               cachedVal := defaultValue |}
                            end)
    (BiR := fun (r_o : cachedRep (list nat) nat)
                (r_n : option nat) =>
              (origRep r_o = [] -> cachedVal r_o = defaultValue) /\
     r_n = match (origRep r_o) with
             | [] => None
             | _ :: _ => Some (cachedVal r_o)
           end); intros; eauto; try rewrite if_unit; simpl;
     destruct r_o; destruct origRep; simpl in *; intuition; subst;
     unfold update_cachedOp; simpl; autorewrite with refine_monad;
     simpl; split; intros v CompV; inversion_by computes_to_inv;
     subst; econstructor; intuition; eauto; try discriminate.
    (* Step 6: All done with the derivation. *)
    finish sharpening.
  Defined.

  Goal (forall b, MutatorMethods (proj1_sig (MinCollectionCached' 0)) () = b).
    simpl.
    unfold simplifyMutatorMethods; simpl.
  Abort.

  Fixpoint BuildList n :=
    match n with
      | 0 => []
      | S n' => n' :: BuildList n'
    end.

  Definition MinCollectionADT :=
    ObserverMethods (proj1_sig (MinCollection 7000)) () (BuildList 2000) 11.
  Definition MinCollectionCachedADT :=
    ObserverMethods (proj1_sig (MinCollectionCached 7000)) ()
                    (Some 0) 11.

  Time Eval compute in MinCollectionCachedADT.
  Time Eval compute in MinCollectionADT.

  Require Import Max.

  (* Proofs of various [op] properties for [max]. *)
  Lemma max_trans : forall n m v,
                      n >= v ->
                      max n m >= v.
    intros; destruct (max_spec n m); omega.
  Qed.
  Hint Resolve max_trans.

  Lemma max_assoc
  : forall x y z : nat, max (max x y) z = max x (max y z).
  Proof.
    intros; rewrite max_assoc; eauto.
  Qed.
  Hint Resolve max_assoc.

  Lemma max_returns_arg
  : forall n0 m : nat, max n0 m = n0 \/ max n0 m = m.
  Proof.
    intros; edestruct max_dec; eauto.
  Qed.
  Hint Resolve max_returns_arg.

  Lemma max_preserves_lte
  : forall n m : nat, max n m >= m.
  Proof.
    intros; destruct (max_dec n m); eauto with arith.
  Qed.
  Hint Resolve max_preserves_lte.

  Hint Resolve max_comm.

  Arguments NatUpper / .

  Definition MaxCollection (defaultValue : nat) :
    { Rep : ADT
    | refineADT NatUpper Rep }.
  Proof.
    eexists; eapply refines_NatBinOp with
             (op := max)
               (defaultValue := defaultValue); eauto with typeclass_instances.
    unfold Transitive; intros; omega.
  Defined.

End ImplExamples.




(* Definition NatLower : ADT  *)
(*   := NatBinOpSpec le (fun n => n = 0).  (* Spec for collection with lower bound. *) *)

(* Definition NatUpper  *)
(* : ADT := NatBinOpSpec ge (fun n => n = 0).  (* Spec for collection with upper bound. *) *)


(* Definition NatLowerI defaultValue : ADT (NatLower defaultValue) *)
(*   := NatBinOpI _ _ _ _. *)

(* Definition NatUpperI : ADTimpl (NatUpper default_val) *)
(*   := NatBinOpI _ _ _ _. *)

(*   Program Definition NatUpper default_value : ADT *)
(*     := NatBinOpSpec max default_value. *)

(*   Program Definition NatSum default_value : ADT *)
(*     := NatBinOpSpec plus default_value. *)

(*   Program Definition NatProd default_value : ADT *)
(*     := NatBinOpSpec mult default_value. *)

(*   Hint Immediate le_min_l le_min_r le_max_l le_max_r. *)

(*   Lemma min_trans : forall n m v, *)
(*                       n <= v *)
(*                       -> min n m <= v. *)
(*     intros; destruct (min_spec n m); omega. *)
(*   Qed. *)

(*   Lemma max_trans : forall n m v, *)
(*                       n >= v *)
(*                       -> max n m >= v. *)
(*     intros; destruct (max_spec n m); omega. *)
(*   Qed. *)

(*   Hint Resolve min_trans max_trans. *)

(*   Arguments add _ _ _ / . *)


(*   Section def_NatBinOpI. *)

(*     Local Ltac induction_list_then tac := *)
(*       lazymatch goal with *)
(*   | [ l : list _ |- _ ] *)
(*     => repeat match goal with *)
(*                 | [ H : appcontext[l] |- _ ] => clear H *)
(*               end; *)
(*       induction l; tac *)
(*     end. *)

(*     Local Ltac manipulate_op op_assoc op_comm := *)
(*       match goal with *)
(*         | _ => reflexivity *)
(*         | _ => progress simpl in * *)
(*         | _ => apply op_comm *)
(*         | _ => rewrite <- ?op_assoc; revert op_assoc op_comm; rewrite_hyp'; intros *)
(*         | _ => rewrite ?op_assoc; revert op_assoc op_comm; rewrite_hyp'; intros *)
(*         | _ => rewrite <- ?op_assoc; f_equal; [] *)
(*         | _ => rewrite ?op_assoc; f_equal; [] *)
(*         | _ => apply op_comm *)
(*       end. *)

(*     Local Ltac deep_manipulate_op op op_assoc op_comm can_comm_tac := *)
(*       repeat match goal with *)
(*                | _ => progress repeat manipulate_op op_assoc op_comm *)
(*                | [ |- appcontext[op ?a ?b] ] *)
(*                  => can_comm_tac a b; *)
(*                    rewrite (op_comm a b); *)
(*                    let new_can_comm_tac := *)
(*                        fun x y => *)
(*                          can_comm_tac x y; *)
(*                          try (unify x a; *)
(*                               unify y b; *)
(*                               fail 1 "Cannot commute" a "and" b "again") *)
(*                    in deep_manipulate_op op op_assoc op_comm new_can_comm_tac *)
(*              end. *)

(*     Local Ltac solve_after_induction_list op op_assoc op_comm := *)
(*       solve [ deep_manipulate_op op op_assoc op_comm ltac:(fun a b => idtac) ]. *)

(*     Local Ltac t := *)
(*       repeat match goal with *)
(*                | _ => assumption *)
(*                | _ => intro *)
(*                | _ => progress simpl in * *)
(*                | [ |- appcontext[if string_dec ?A ?B then _ else _ ] ] *)
(*                  => destruct (string_dec A B) *)
(*                | _ => progress subst *)
(*                | [ H : ex _ |- _ ] => destruct H *)
(*                | [ H : and _ _ |- _ ] => destruct H *)
(*                | _ => split *)
(*                | [ H : option _ |- _ ] => destruct H *)
(*                | [ H : _ |- _ ] => solve [ inversion H ] *)
(*                | [ |- appcontext[match ?x with _ => _ end] ] => destruct x *)
(*                | [ H : appcontext[match ?x with _ => _ end] |- _  ] => destruct x *)
(*                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H *)
(*                | _ => progress f_equal; [] *)
(*                | _ => progress intuition *)
(*                | _ => repeat esplit; reflexivity *)
(*                | [ H : _ |- _ ] => rewrite H; try (rewrite H; fail 1) *)
(*              end. *)

(*     Local Ltac t' op op_assoc op_comm := *)
(*       repeat first [ progress t *)
(*                    | progress induction_list_then ltac:(solve_after_induction_list op op_assoc op_comm) ]. *)

(*     Definition NatBinOpImpl *)
(*                (op : nat -> nat -> nat) *)
(*                (default_value : nat) : ADT. *)
(*     Proof. *)
(*       intros. *)
(*       refine {|  *)
(*           Model := option nat; *)
(*           MutatorIndex := unit; *)
(*           ObserverIndex := unit; *)
(*           MutatorMethods u val x := ret (match val with  *)
(*                                              | None => Some x *)
(*                                              | Some x' => Some (op x x') *)
(*                                          end)%comp; *)
(*           ObserverMethods u val x := ret (match val with  *)
(*                                               | None => default_value *)
(*                                               | Some x => x *)
(*                                           end) *)
(*         |}. *)
(*     Defined. *)

(*   End def_NatBinOpI. *)

(*       Print ADT. *)
(*       intros []. *)

(*       refine {| *)
(*           Model := option (nat * nat); *)
(*           MutatorMethods u val x := (ret (match val with *)
(*                                                  | None => Some x *)
(*                                                  | Some x' => Some (op x (fst x')) *)
(*                                                end, *)
(*                                                0))%comp; *)
(*           ObserverMethods u val x := (ret (val, *)
(*                                                 match val with *)
(*                                                   | None => default_value *)
(*                                                   | Some x => x *)
(*                                                 end))%comp *)
(*         |}; *)
(*         intros []; *)
(*         solve [ (intros m [n|] [l [H0 H1] ] x ? ?); *)
(*                 inversion_by computes_to_inv; subst; simpl in *; *)
(*                 (exists (add m x)); *)
(*                 repeat split; *)
(*                 try (exists (x::l)); *)
(*                 abstract t' op op_assoc op_comm *)
(*               | intros m [n|] [l [H0 H1] ] x ? ?; *)
(*                        inversion_by computes_to_inv; subst; simpl in *; *)
(*                 repeat (split || exists m || exists l); *)
(*                 abstract t' op op_assoc op_comm *)
(*               | intros m [n|] [l [H0 H1] ] x ? ?; *)
(*                        inversion_by computes_to_inv; subst; simpl in *; *)
(*                 [ repeat split; *)
(*                   try (exists (add (fun _ => 0) n)); *)
(*                   repeat split; *)
(*                   try (exists (n::nil)); *)
(*                   abstract (repeat split) *)
(*                 | repeat split; *)
(*                   try (exists m); *)
(*                   repeat split; *)
(*                   try (exists l); *)
(*                   abstract (repeat split; assumption) ] *)
(*               ]. *)
(*     Defined. *)
(*   End def_NatBinOpI. *)

(*   Section nat_op_ex. *)
(*     Variable default_val : nat. *)

(*     Definition NatLowerI : ADTimpl (NatLower default_val) *)
(*       := NatBinOpI _ _ _ _. *)

(*     Definition NatUpperI : ADTimpl (NatUpper default_val) *)
(*       := NatBinOpI _ _ _ _. *)

(*     Definition NatSumI : ADTimpl (NatSum default_val) *)
(*       := NatBinOpI _ _ _ _. *)

(*     Definition NatProdI : ADTimpl (NatProd default_val) *)
(*       := NatBinOpI _ _ _ _. *)
(*   End nat_op_ex. *)

(*   Local Open Scope string_scope. *)

(*   Definition NatSumProd_spec : ADT *)
(*     := {| Model := multiset; *)
(*           MutatorIndex := unit; *)
(*           ObserverIndex := unit + unit; *)
(*           MutatorMethodSpecs u := add_spec; *)
(*           ObserverMethodSpecs u m x n := *)
(*             match u with *)
(*               | inl _ => bin_op_spec plus 0 m x n *)
(*               | inr _ => bin_op_spec mult 1 m x n *)
(*             end *)
(*        |}. *)
