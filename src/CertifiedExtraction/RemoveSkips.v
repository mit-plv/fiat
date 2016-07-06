Require Import Bedrock.Platform.Facade.DFacade.

Require Import
        Fiat.CertifiedExtraction.Core
        Fiat.CertifiedExtraction.FacadeUtils
        Fiat.CertifiedExtraction.FacadeNotations.

Require Import Coq.Program.Program.

Fixpoint RemoveSkips (s: Stmt) :=
  match s with
  | DFacade.Skip => Skip
  | DFacade.Seq x x0 => let x := RemoveSkips x in
                       let x0 := RemoveSkips x0 in
                       match x, x0 with
                       | DFacade.Skip, _ => x0
                       | _, DFacade.Skip => x
                       | _, _ => DFacade.Seq x x0
                       end
  | DFacade.If x x0 x1 => DFacade.If x (RemoveSkips x0) (RemoveSkips x1)
  | DFacade.While x x0 => DFacade.While x (RemoveSkips x0)
  | DFacade.Call x x0 x1 => DFacade.Call x x0 x1
  | DFacade.Assign x x0 => DFacade.Assign x x0
  end.

Hint Constructors RunsTo : runsto_safe.
Hint Constructors Safe : runsto_safe.

Ltac RemoveSkips_helper :=
  intros; simpl in *;
  try ((eauto using Equal_refl with runsto_safe) ||
       (facade_inversion; eauto using Equal_refl with runsto_safe)).

Lemma RemoveSkips_RunsTo {av} :
  forall prog pre post env,
    @RunsTo av env (RemoveSkips prog) pre post ->
    @RunsTo av env prog pre post.
Proof.
  induction prog; RemoveSkips_helper.
  + destruct (RemoveSkips prog1), (RemoveSkips prog2);
      RemoveSkips_helper.
  + remember (While e RemoveSkips prog)%facade eqn:Heq.
    induction H; try congruence; unfold loop in *;
      inversion Heq; subst; clear Heq;
        eauto using RunsToWhileTrue, RunsToWhileFalse.
Qed.

Lemma RunsTo_Equal_left_fast :
  forall {av st1 st2},
    M.Equal st1 st2 ->
    forall env prog st',
      @RunsTo av env prog st1 st' ->
      @RunsTo av env prog st2 st'.
Proof.
  intros * eq **; rewrite <- eq; assumption.
Qed.

Lemma RunsTo_Equal_right_fast :
  forall {av st1 st2},
    M.Equal st1 st2 ->
    forall env prog st',
      @RunsTo av env prog st' st1 ->
      @RunsTo av env prog st' st2.
Proof.
  intros * eq **; rewrite <- eq; assumption.
Qed.

Lemma is_true_Equal_fast :
  forall {av st1 st2},
    M.Equal st1 st2 ->
    forall e,
      @is_true av st1 e ->
      @is_true av st2 e.
Proof.
  intros * eq **; rewrite <- eq; assumption.
Qed.

Lemma is_false_Equal_fast :
  forall {av st1 st2},
    M.Equal st1 st2 ->
    forall e,
      @is_false av st1 e ->
      @is_false av st2 e.
Proof.
  intros * eq **; rewrite <- eq; assumption.
Qed.

Lemma RemoveSkips_RunsTo2 {av} :
  forall prog pre post env,
    @RunsTo av env prog pre post ->
    @RunsTo av env (RemoveSkips prog) pre post.
Proof.
  induction prog; RemoveSkips_helper.
  + destruct (RemoveSkips prog1), (RemoveSkips prog2);
    try solve [RemoveSkips_helper];
    specialize (IHprog1 _ _ _ H2);
    specialize (IHprog2 _ _ _ H5);
    repeat facade_inversion;
    try match goal with
    | [ H: M.Equal _ _ |- _ ] => rewrite H in *
    end; eauto using Equal_refl, Equal_trans with runsto_safe.
  + dependent induction H.
    eauto using RunsToWhileTrue, RunsToWhileFalse.
    eauto using RunsToWhileTrue, RunsToWhileFalse.
Qed.

Hint Extern 1 => match goal with
                | [ H: RemoveSkips _ = _ |- _ ] => rewrite H
                end : runsto_safe.

(* Lemma RemoveSkips_Safe {av} : *)
(*   forall prog pre env, *)
(*     @Safe av env prog pre -> *)
(*     @Safe av env (RemoveSkips prog) pre. *)
(* Proof. *)
(*   induction prog; RemoveSkips_helper. *)
(*   + destruct (RemoveSkips prog1) eqn:eq1, (RemoveSkips prog2); *)
(*       destruct_conjs; solve [eauto 10 using Equal_refl, Equal_trans, RemoveSkips_RunsTo with runsto_safe]. *)
(*   +                             (* Coinduction? *) *)
(* Admitted. *)

(* Lemma RemoveSkips_ProgOk {av} : *)
(*   forall prog pre post ext env, *)
(*     @ProgOk av ext env prog pre post -> *)
(*     @ProgOk av ext env (RemoveSkips prog) pre post. *)
(* Proof. *)
(*   unfold ProgOk; split; *)
(*     specialize (H _ H0); *)
(*     intuition eauto using RemoveSkips_RunsTo, RemoveSkips_Safe. *)
(* Qed. *)
