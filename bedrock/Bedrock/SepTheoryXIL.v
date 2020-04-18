Require Import Bedrock.Heaps Bedrock.Memory.
Require Import Bedrock.PropX Bedrock.PropXTac.
Require Import Bedrock.SepTheoryX.
Require Bedrock.IL.
Require Bedrock.PropXRel.

Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (H' : Heap) <:
  SepTheoryX with Module H := H'
             with Definition settings := IL.settings.
  Module H := H'.
  Module HT := HeapTheory H.

  Section env.
    Variable pcType : Type.
    Variable stateType : Type.
    Definition settings := IL.settings.

    Definition hprop (sos : list Type) := settings -> HT.smem -> propX pcType stateType sos.

    Variable cs : codeSpec pcType stateType.

    Definition satisfies (p : hprop nil) (s : settings) (sm : HT.smem) : Prop :=
      interp cs (p s sm).

    Definition himp (gl gr : hprop nil) : Prop :=
      forall s m, interp cs (gl s m ---> gr s m).
    Definition heq (gl gr : hprop nil) : Prop :=
      himp gl gr /\ himp gr gl.

    Global Instance Refl_himp : Reflexive himp.
    Proof.
      red; unfold himp; intros.
      eapply Imply_I; eauto.
    Qed.
    Global Instance Trans_himp : Transitive himp.
    Proof.
      red; unfold himp; firstorder.
      eapply Imply_I. eapply Imply_E. eapply valid_weaken. eapply H0. firstorder.
      eapply Imply_E. eapply valid_weaken. eapply H. firstorder. eauto.
    Qed.

    Global Instance Refl_heq : Reflexive heq.
    Proof.
      red; unfold heq; auto; split; reflexivity.
    Qed.
    Global Instance Sym_heq : Symmetric heq.
    Proof.
      red; unfold heq; firstorder.
    Qed.
    Global Instance Trans_heq : Transitive heq.
    Proof.
      red; unfold heq. intuition; etransitivity; eassumption.
    Qed.

    Theorem heq_himp : forall a b, heq a b -> himp a b.
    Proof.
      unfold heq; firstorder.
    Qed.

(*
    Theorem himp_heq : forall a b, himp a b -> himp b a -> heq a b.
    Proof.
      unfold heq; firstorder.
    Qed.
*)

    Theorem heq_defn : forall a b, (himp a b /\ himp b a) <-> heq a b.
    Proof.
      unfold heq; intuition.
    Qed.

    (* Definitions *)
    Definition inj sos (p : propX pcType stateType sos) : hprop sos :=
      fun _ m => PropX.And p (PropX.Inj (HT.semp m)).

    Definition emp {sos} : hprop sos := inj (PropX.Inj True).

    Definition star sos (l r : hprop sos) : hprop sos :=
      fun s m => PropX.Exists (fun ml : HT.smem => PropX.Exists (fun mr : HT.smem =>
        PropX.And (PropX.Inj (HT.split m ml mr)) (And (l s ml) (r s mr)))).

    Definition ex sos (T : Type) (p : T -> hprop sos) : hprop sos :=
      fun s h => PropX.Exists (fun t => p t s h).

    Definition hptsto sos (p : H.addr) (v : B) : hprop sos :=
      fun s h =>
        PropX.Inj (HT.smem_get p h = Some v /\ forall p', p' <> p -> HT.smem_get p' h = None).

    (* satisfies lemmas *)
    Theorem satisfies_himp : forall P Q stn,
      himp P Q ->
      (forall m, satisfies P stn m ->
       satisfies Q stn m).
    Proof.
      unfold himp, satisfies. intros. propxFo.
      eapply Imply_E; eauto.
    Qed.

    Theorem satisfies_star : forall P Q stn m,
      satisfies (star P Q) stn m <->
      exists ml, exists mr,
        HT.split m ml mr /\
        satisfies P stn ml /\ satisfies Q stn mr.
    Proof.
      unfold satisfies. intros. propxFo. eauto 10.
      exists x; exists x0. intuition propxFo.
    Qed.

    Theorem satisfies_pure : forall p stn m,
      satisfies (inj p) stn m ->
      interp cs p /\ HT.semp m.
    Proof.
      unfold satisfies, inj; simpl; intros; propxFo.
    Qed.

    Theorem satisfies_ex : forall T p stn m,
      satisfies (@ex _ T p) stn m ->
      exists x : T, satisfies (p x) stn m.
    Proof.
      unfold satisfies, ex; simpl; intros; propxFo; eauto.
    Qed.

    (** Lemmas **)
(*
    Ltac doIt :=
      unfold himp, heq; simpl; intros;
        repeat match goal with
(*                 | [ h : HT.smem , H : forall x : HT.smem , _ |- _ ] => specialize (H h) *)
                 | [ H : _ -> _ |- _ ] => apply H; clear H
                 | [ H : forall x, _ -> _ , H' : _ |- _ ] => apply H in H'
                 | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
               end; propxFo;
        repeat match goal with
                 | [ |- exists x, _ ] => eexists
                 | [ |- _ /\ _ ] => split
                 | [ |- simplify _ _ _ ] => eassumption || apply simplify_fwd
                 | [ H : interp ?X (?Y _) |- interp ?X (?Y _) ] => eapply H
               end.


      unfold himp, heq; simpl; intros;
        repeat match goal with
(*                 | [ h : HT.smem , H : forall x : HT.smem , _ |- _ ] => specialize (H h) *)
                 | [ H : _ -> _ |- _ ] => apply H; clear H
                 | [ H : forall x, _ -> _ , H' : _ |- _ ] => apply H in H'
                 | [ H : ?X -> _ , H' : ?X |- _ ] => apply H in H'; clear H
               end; propxFo;
        repeat match goal with
                 | [ |- exists x, _ ] => eexists
                 | [ |- _ /\ _ ] => split
                 | [ |- simplify _ _ _ ] => eassumption || apply simplify_fwd
                 | [ H : interp ?X (?Y _) |- interp ?X (?Y _) ] => eapply H
               end.
*)

    Import PropXRel.

    Hint Immediate HT.split_comm : heaps.
    Hint Resolve HT.split_assoc HT.disjoint_split_join HT.split_split_disjoint : heaps.

    Lemma himp_star_comm : forall P Q, himp (star P Q) (star Q P).
    Proof.
      unfold star, himp, interp; intros; propxIntuition; eauto with heaps.
    Qed.

(*
    Theorem himp_star_comm_p : forall P Q R, himp (star P Q) R -> himp (star Q P) R.
    Proof.
      unfold star; doIt. eauto with heaps.
    Qed.
    Theorem himp_star_comm_c : forall P Q R, himp R (star P Q) -> himp R (star Q P).
    Proof.
      unfold star; doIt. eauto with heaps.
    Qed.
*)

    Theorem heq_star_comm : forall P Q, heq (star P Q) (star Q P).
    Proof.
      intros. unfold heq. generalize himp_star_comm. intuition.
    Qed.

    Theorem himp_star_assoc : forall P Q R,
      himp (star (star P Q) R) (star P (star Q R)).
    Proof.
      unfold star, himp, interp; intros; propxIntuition.
      eapply HT.split_comm. eapply HT.split_assoc. eapply HT.split_comm. eassumption. eapply HT.split_comm. eassumption.
      eapply HT.disjoint_split_join. eapply HT.disjoint_comm. eauto with heaps.
    Qed.
(*
    Theorem himp_star_assoc_c : forall P Q R S,
      himp S (star P (star Q R)) -> himp S (star (star P Q) R).
    Proof.
      doIt. eapply HT.split_assoc. eassumption. eassumption.
      eapply HT.split_comm. eapply HT.disjoint_split_join. eapply HT.disjoint_comm. eauto with heaps.
    Qed.
*)

    Theorem heq_star_assoc : forall P Q R,
      heq (star (star P Q) R) (star P (star Q R)).
    Proof.
      split. eapply himp_star_assoc.

      unfold star, himp, interp; intros; propxIntuition.

      eapply HT.split_assoc. eassumption. eassumption.
      eapply HT.split_comm. eapply HT.disjoint_split_join.
      eapply HT.disjoint_comm.
      eapply HT.split_split_disjoint. 2: eassumption. eauto with heaps.
    Qed.

    Theorem himp_star_frame : forall P Q R S,
      himp P Q -> himp R S -> himp (star P R) (star Q S).
    Proof.
      unfold himp, star, interp; intros; propxIntuition.
      Focus 2.
      eapply Imply_E. eapply valid_weaken. eapply H. firstorder. econstructor; firstorder.
      Focus 2.
      eapply Imply_E. eapply valid_weaken. eapply H0. firstorder. econstructor; firstorder.
      eauto.
    Qed.

    Theorem heq_star_frame : forall P Q R S, heq P Q -> heq R S -> heq (star P R) (star Q S).
    Proof.
      unfold heq; generalize himp_star_frame. intuition.
    Qed.

    Theorem himp_star_pure_p : forall P Q F,
      himp (star (inj F) P) Q -> (interp cs F -> himp P Q).
    Proof.
      unfold himp, star, inj; intros.
      specialize (H s m).
      unfold interp in *. propxIntuition.
      eapply Imply_E. eapply valid_weaken. eapply H. firstorder.
      eapply Exists_I. instantiate (1 := HT.smem_emp).
      eapply Exists_I. instantiate (1 := m). propxIntuition.
      eapply HT.split_a_semp_a.
      eapply valid_weaken. eassumption. firstorder. eapply HT.semp_smem_emp.
    Qed.

    Theorem himp_star_pure_c : forall P Q (F : Prop),
      (F -> himp P Q) -> himp (star (inj (PropX.Inj F)) P) Q.
    Proof.
      unfold himp, star, inj, interp; intros. propxIntuition.
      specialize (H H1). eapply PropX.Imply_E. eapply valid_weaken. eauto. firstorder.
      apply HT.split_semp in H0; auto. subst.
      constructor. firstorder.
    Qed.

    Theorem himp_star_pure_cc : forall P Q (p : Prop),
      p ->
      himp P Q ->
      himp P (star (inj (PropX.Inj p)) Q).
    Proof.
      unfold himp, star, inj, interp; intros. propxIntuition; eauto using HT.semp_smem_emp, HT.split_a_semp_a.
      eapply Imply_E. eapply valid_weaken; eauto. firstorder.
      econstructor. firstorder.
    Qed.

    Theorem himp_subst_p : forall P Q R S,
      himp P S -> himp (star S Q) R ->
      himp (star P Q) R.
    Proof.
      unfold himp, star, interp; intros; propxIntuition.
      specialize (H s x). specialize (H0 s m).
      eapply Imply_E. eapply valid_weaken. eapply H0. firstorder.
      propxIntuition. eauto. eapply Imply_E. eapply valid_weaken.
      eauto. firstorder. econstructor; firstorder.
    Qed.

    Theorem himp_subst_c : forall P Q R S,
      himp S Q -> himp P (star S R) ->
      himp P (star Q R).
    Proof.
      unfold himp, star, interp; intros.
      eapply Imply_I. eapply valid_extend.
      eapply Imply_E. eapply valid_weaken.
      specialize (H0 s m). eassumption. firstorder. eauto.
      propxIntuition; eauto.
      eapply Imply_E. eapply valid_weaken. eapply H. firstorder.
      econstructor; firstorder.
    Qed.

    Theorem heq_subst : forall P Q R S,
      heq P S -> heq (star S Q) R ->
      heq (star P Q) R.
    Proof.
      unfold heq. intros. intuition; generalize himp_subst_p; generalize himp_subst_c; eauto.
    Qed.

    Theorem himp_star_emp_p : forall P Q, himp P Q -> himp (star emp P) Q.
    Proof.
      unfold emp, inj, star, himp, interp; intuition; propxIntuition.
      eapply Imply_E. eapply valid_weaken; [ eapply H | firstorder ].
      eapply HT.split_semp in H0; eauto; subst. propxIntuition.
    Qed.

    Theorem himp_star_emp_p' : forall P Q, himp (star emp P) Q -> himp P Q.
    Proof.
      unfold emp, inj, star, himp, interp; intuition; propxIntuition.
      eapply Imply_E. eapply valid_weaken; [ eapply H | firstorder ].
      propxIntuition. eapply HT.split_a_semp_a. auto. eapply HT.semp_smem_emp.
    Qed.

    Theorem himp_star_emp_c : forall P Q, himp P Q -> himp P (star emp Q).
    Proof.
      unfold emp, inj, star, himp, interp; intuition; propxIntuition.
      eapply HT.split_a_semp_a. auto. eapply HT.semp_smem_emp.
      eapply Imply_E. eapply valid_weaken; [ eapply H | firstorder ].
      propxIntuition.
    Qed.

    Theorem himp_star_emp_c' : forall P Q, himp P (star emp Q) -> himp P Q.
    Proof.
      unfold emp, inj, star, himp, interp; intuition; propxIntuition.
      eapply valid_extend. eapply Imply_E. eapply valid_weaken. eapply (H s m). firstorder.
      econstructor; firstorder.
      propxIntuition.
      eapply HT.split_semp in H0; eauto; subst. propxIntuition.
    Qed.

    Theorem heq_star_emp_l : forall P, heq (star emp P) P.
      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p. reflexivity.
      eapply himp_star_emp_c. reflexivity.
    Qed.

    Theorem heq_star_emp_r : forall P, heq (star P emp) P.
    Proof.
      intros. unfold heq, himp, star, emp, inj, interp in *; intuition.
      propxIntuition. eapply HT.split_comm in H. eapply HT.split_semp in H; eauto; subst. propxIntuition.

      propxIntuition.
      eapply HT.split_comm. eapply HT.split_a_semp_a. auto. eapply HT.semp_smem_emp.
    Qed.

(*
    Theorem heq_star_emp' : forall P Q, heq (star emp P) Q -> heq P Q.

      intros. unfold heq in *; intuition.
      eapply himp_star_emp_p' in H0. auto.
      eapply himp_star_emp_c' in H1. auto.
    Qed.
*)

    Theorem himp_star_cancel : forall P Q R, himp Q R -> himp (star P Q) (star P R).

      intros. eapply himp_star_frame. reflexivity. auto.
    Qed.

    Theorem heq_star_cancel : forall P Q R, heq Q R -> heq (star P Q) (star P R).

      intros. eapply heq_star_frame. reflexivity. auto.
    Qed.

    Theorem himp_ex_p : forall T (P : T -> _) Q,
      (forall v, himp (P v) Q) -> himp (ex P) Q.

      intros. unfold himp, ex in *; simpl in *; intros. unfold interp in *. propxIntuition.
      eapply Imply_E. eapply valid_weaken; eauto. firstorder. econstructor; firstorder.
    Qed.

    Theorem himp_ex_c : forall T (P : T -> _) Q,
      (exists v, himp Q (P v)) -> himp Q (ex P).
    Proof.
      intros. unfold himp, ex in *; simpl in *; intros. unfold interp in *.
      destruct H. propxIntuition. instantiate (1 := x).
      eapply Imply_E. eapply valid_weaken; eauto. firstorder. eauto.
    Qed.

    Hint Resolve simplify_fwd : heaps.

    Theorem heq_ex : forall T (P Q : T -> _),
      (forall v, heq (P v) (Q v)) ->
      heq (ex P) (ex Q).
    Proof.
      unfold heq, himp, ex, interp; intros; intuition; propxIntuition;
       match goal with
         | [ H : forall v : ?T, _, x : ?T |- _ ] => specialize (H x)
       end; intuition.
      eapply Imply_E. eapply valid_weaken; eauto. firstorder. eauto.
      eapply Imply_E. eapply valid_weaken; eauto. firstorder. eauto.
    Qed.

    Theorem himp_ex : forall T (P Q : T -> _),
      (forall v, himp (P v) (Q v)) ->
      himp (ex P) (ex Q).
    Proof.
      unfold himp, ex, interp; intuition; propxIntuition;
        match goal with
          | [ H : forall v : ?T, _, x : ?T |- _ ] => specialize (H x)
        end.
      eapply Imply_E. eapply valid_weaken; eauto. firstorder. eauto.
    Qed.

    Theorem heq_ex_star : forall T (P : T -> _) Q,
      heq (star (ex P) Q) (ex (fun x => star (P x) Q)).
    Proof.
      unfold heq, himp, star, ex, interp; intuition; propxIntuition; eauto.
    Qed.

    Theorem himp_ex_star : forall T (P : T -> _) Q,
      himp (star (ex P) Q) (ex (fun x => star (P x) Q)).
    Proof.
      unfold himp, star, ex, interp; intuition; propxIntuition; eauto.
    Qed.

    Lemma himp'_ex : forall T (P : T -> _) Q,
      (forall x, himp (P x) Q) ->
      himp (ex P) Q.
    Proof.
      clear. intros. unfold himp, ex, interp in *. intuition. propxIntuition.
      eapply Imply_E. eapply valid_weaken; eauto. firstorder. eauto.
    Qed.
  End env.
End Make.
