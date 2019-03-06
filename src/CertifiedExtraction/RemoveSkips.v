Require Import Bedrock.Platform.Facade.DFacade.

Require Import
        Fiat.CertifiedExtraction.Core
        Fiat.CertifiedExtraction.FacadeUtils
        Fiat.CertifiedExtraction.FacadeNotations.

Require Import Coq.Program.Program.

Definition Is_Skip : forall p, { p = Skip } + { p <> Skip }.
  destruct p;
    [ left; reflexivity | right; discriminate .. ].
Defined.

Fixpoint RemoveSkips (s: Stmt) :=
  match s with
  | DFacade.Skip => DFacade.Skip
  | DFacade.Seq a b => let a := RemoveSkips a in
                      let b := RemoveSkips b in
                      if (Is_Skip a) then b
                      else if (Is_Skip b) then a
                           else (DFacade.Seq a b)
  | DFacade.If c t f => DFacade.If c (RemoveSkips t) (RemoveSkips f)
  | DFacade.While c b => DFacade.While c (RemoveSkips b)
  | DFacade.Call r f args => DFacade.Call r f args
  | DFacade.Assign x v => DFacade.Assign x v
  end.

Hint Constructors RunsTo : runsto_safe.
Hint Constructors Safe : runsto_safe.
Hint Resolve Equal_refl : runsto_safe.

Ltac RemoveSkips_helper :=
  intros; simpl in *;
  try ((eauto using Equal_refl with runsto_safe) ||
       (facade_inversion; eauto using Equal_refl with runsto_safe)).

Ltac destruct_Is_Skip prog :=
  let eq := fresh "eq" in
  let neq := fresh "neq" in
  destruct (Is_Skip (RemoveSkips prog)) as [ eq | neq ];
  [ rewrite eq in * | ].

Lemma RemoveSkips_RunsTo {av} :
  forall prog pre post env,
    @RunsTo av env (RemoveSkips prog) pre post ->
    @RunsTo av env prog pre post.
Proof.
  induction prog; RemoveSkips_helper.
  + destruct_Is_Skip prog1;
      destruct_Is_Skip prog2;
      RemoveSkips_helper.
  + remember (While e RemoveSkips prog)%facade eqn:Heq.
    induction H; try congruence; unfold loop in *;
      inversion Heq; subst; clear Heq;
        RemoveSkips_helper.
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
  + destruct_Is_Skip prog1;
    destruct_Is_Skip prog2;
    try solve [RemoveSkips_helper];
    specialize (IHprog1 _ _ _ H2);
    specialize (IHprog2 _ _ _ H5);
    repeat facade_inversion;
    try match goal with
    | [ H: M.Equal _ _ |- _ ] => rewrite H in *
    end; eauto using Equal_trans with runsto_safe.
  + dependent induction H;
      eauto with runsto_safe.
Qed.

Lemma RemoveSkips_RunsTo_iff {av} :
  forall prog pre post env,
    @RunsTo av env (RemoveSkips prog) pre post <->
    @RunsTo av env prog pre post.
Proof.
  intuition eauto using RemoveSkips_RunsTo, RemoveSkips_RunsTo2.
Qed.

Lemma RemoveSkip_left_Safe:
  forall (av : Type) (env : Env av) (st : State av) (a b : Stmt),
    RemoveSkips a = Skip ->
    Safe env (Seq a b) st ->
    Safe env b st.
Proof.
  intros av env st a b eq safe.

  induction a; simpl in *;
    try facade_inversion;
    destruct_conjs;
    try discriminate.

  - eauto with runsto_safe.

  - destruct_Is_Skip a1.
    { apply H0;
        econstructor;
        apply RemoveSkips_RunsTo;
        rewrite ?eq, ?eq0;
        constructor;
        reflexivity. }
    { destruct_Is_Skip a2;
        (discriminate || intuition). }
Qed.

Definition RemoveSkips_Safe_CoInd_Hyp {av env} prog pre :=
  exists prog',
    (RemoveSkips prog' = prog \/ prog' = prog) /\
    @Safe av env prog' pre.

Ltac inversion' H :=
  inversion H;
  repeat match goal with
         | [ H := _ |- _ ] => progress (unfold H in *; clear H)
         end;
  subst;
  clear H.

Lemma RemoveSkips_Safe {av} :
  forall prog pre env,
    @Safe av env prog pre ->
    @Safe av env (RemoveSkips prog) pre.
Proof.
  intros.

  eapply (Safe_coind RemoveSkips_Safe_CoInd_Hyp);
    intros; unfold RemoveSkips_Safe_CoInd_Hyp;
    lazymatch goal with
    | [ H: RemoveSkips_Safe_CoInd_Hyp _ _ |- _ ] =>
      destruct H as (prog' & [ eq_rm | eq ] & safe);
        [ | subst; inversion' safe; intuition eauto ]
    | _ =>
      solve [eexists; eauto]
    end.

  - induction prog'; simpl in eq_rm;
      try discriminate.
    + destruct_Is_Skip prog'1.
      * pose proof (RemoveSkip_left_Safe eq safe).
        intuition eauto using RemoveSkip_left_Safe.
      * inversion' safe; destruct_conjs.
        destruct_Is_Skip prog'2.
        { intuition. }
        { inversion' eq_rm;
          split; eexists; eauto using RemoveSkips_RunsTo. }

  (* If case *)
  - induction prog'; simpl in eq_rm;
      try discriminate.
    + destruct_Is_Skip prog'1.
      * pose proof (RemoveSkip_left_Safe eq safe).
        intuition.
      * inversion' safe; destruct_conjs.
        destruct_Is_Skip prog'2.
        { intuition. }
        { discriminate. }
    + inversion' eq_rm; inversion' safe; intuition eauto.

  (* Loop case *)
  - induction prog'; simpl in eq_rm;
      try discriminate.
    + destruct_Is_Skip prog'1.
      * pose proof (RemoveSkip_left_Safe eq safe).
        intuition.
      * inversion' safe; destruct_conjs.
        destruct_Is_Skip prog'2.
        { intuition. }
        { discriminate. }
    + inversion' eq_rm; inversion' safe.
      * left.
        intuition eauto.
        exists (DFacade.While cond prog');
        intuition eauto using RemoveSkips_RunsTo.
      * solve [eauto].

  (* Assign case *)
  - induction prog'; simpl in eq_rm;
      try discriminate.
    + destruct_Is_Skip prog'1.
      * pose proof (RemoveSkip_left_Safe eq safe).
        intuition.
      * inversion' safe; destruct_conjs.
        destruct_Is_Skip prog'2.
        { intuition. }
        { discriminate. }
    + inversion' eq_rm; inversion' safe; intuition eauto.

  (* Call case *)
  - induction prog'; simpl in eq_rm;
      try discriminate.
    + destruct_Is_Skip prog'1.
      * pose proof (RemoveSkip_left_Safe eq safe).
        intuition.
      * inversion' safe; destruct_conjs.
        destruct_Is_Skip prog'2.
        { intuition. }
        { discriminate. }
    + inversion' eq_rm; inversion' safe.
      * intuition; eexists; eauto.
      * intuition eauto.
        eexists; split; eauto.
        right; eexists; intuition eauto.
  - eexists; eauto.
  - eexists; intuition eauto.
    right; eexists; intuition eauto.
Qed.

Lemma ProgOk_RemoveSkips {av} :
  forall (prog : Stmt) (pre post : Telescope av) ext env,
    {{ pre }} prog {{ post }} ∪ {{ ext }} // env ->
    {{ pre }} RemoveSkips prog {{ post }} ∪ {{ ext }} // env.
Proof.
  unfold ProgOk; intros * ok ** sv; specialize (ok _ sv);
    intuition eauto using RemoveSkips_Safe, RemoveSkips_RunsTo.
Qed.
