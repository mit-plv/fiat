(* An adaptation of Ni & Shao's XCAP program logic *)

Require Import Coq.Bool.Bool Coq.Strings.String.

Require Import Bedrock.Word Bedrock.IL Bedrock.LabelMap Bedrock.StringSet Bedrock.PropX Bedrock.Memory.

Set Implicit Arguments.


(* The type of basic block preconditions (assertions) *)
Definition prop := PropX W (settings * state).
Definition assert := spec W (settings * state).


(* A self-contained unit of code *)
Record module := {
  Imports : LabelMap.t assert;
  (* Which other blocks do we assume are available, and with what preconditions? *)
  Blocks : LabelMap.t (assert * block);
  (* The blocks that we provide, with precondition and code for each *)
  Exports : LabelMap.t assert;
  (* As an optimization, here is information on just the preconditions for
   * just the main function entry points. *)
  Modules : StringSet.t
  (* As another optimization, here is an exhaustive set of all module names
   * appearing in labels of blocks that we define. *)
}.

(* What must be verified for an individual block? *)
Definition blockOk (imps : LabelMap.t assert) (pre : assert) (bl : block) :=
  forall stn specs, (forall l pre, LabelMap.MapsTo l pre imps
    -> exists w, Labels stn l = Some w
      /\ specs w = Some pre)
    -> forall st, interp specs (pre (stn, st)) -> exists st', evalBlock stn st bl = Some st'
      /\ exists pre', specs (fst st') = Some pre'
        /\ interp specs (pre' (stn, snd st')).

Section moduleOk.
  Variable m : module.

  Definition noSelfImport :=
    List.Forall (fun p => ~LabelMap.In (fst p) (Imports m)) (LabelMap.elements (Blocks m)).

  (* Calculate preconditions of all labels that are legal to mention. *)
  Definition allPreconditions := LabelMap.fold (fun l x m =>
    LabelMap.add l (fst x) m) (Blocks m) (Imports m).

  (* What must be verified for a full module? *)
  Record moduleOk := {
    NoSelfImport : noSelfImport;
    BlocksOk : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> blockOk allPreconditions pre bl;
    ImportsGlobal : forall l pre,
      LabelMap.MapsTo l pre (Imports m)
      -> exists g, snd l = Global g;
    ExportsComplete : forall mn g pre bl,
      LabelMap.MapsTo (mn, Global g) (pre, bl) (Blocks m)
      -> LabelMap.MapsTo (mn, Global g) pre (Exports m);
    ExportsSound : forall mn g pre,
      LabelMap.MapsTo (mn, Global g) pre (Exports m)
      -> exists bl, LabelMap.MapsTo (mn, Global g) (pre, bl) (Blocks m);
    ModulesSound : forall mn l pre_bl,
      LabelMap.MapsTo (mn, l) pre_bl (Blocks m)
      -> StringSet.In mn (Modules m)
  }.

  (** Safety theorem that allows some unresolved imports *)

  Hint Constructors SetoidList.InA.

  Lemma allPreconditions_cases' : forall l pre mp,
    LabelMap.MapsTo l pre (LabelMap.fold (fun l x m => LabelMap.add l (fst x) m) (Blocks m) mp)
    -> LabelMap.MapsTo l pre mp
      \/ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m).
    intros.
    rewrite LabelMap.fold_1 in H.
    apply LabelMap.elements_1 in H.
    assert (SetoidList.InA (@LabelMap.eq_key_elt _) (l, pre) (LabelMap.elements mp)
      \/ exists bl, SetoidList.InA (@LabelMap.eq_key_elt _) (l, (pre, bl)) (LabelMap.elements (Blocks m))).
    generalize dependent mp.
    induction (LabelMap.elements (Blocks m)); intuition; simpl in *; eauto.

    specialize (IHl0 _ H); clear H.
    destruct IHl0 as [ | [ ] ]; intuition.
    apply LabelMap.elements_2 in H.
    apply (proj1 (LabelFacts.add_mapsto_iff _ _ _ _ _)) in H; intuition; subst.
    right; eexists.
    apply SetoidList.InA_cons_hd; hnf; simpl; eauto.
    apply LabelMap.elements_1 in H1.
    eauto.
    eauto.

    intuition; eauto.
    apply LabelMap.elements_2 in H1; eauto.
    destruct H1.
    apply LabelMap.elements_2 in H0; eauto.
  Qed.

  Lemma allPreconditions_cases : forall l pre, LabelMap.MapsTo l pre allPreconditions
    -> LabelMap.MapsTo l pre (Imports m)
    \/ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m).
    intros.
    apply allPreconditions_cases' in H; firstorder.
  Qed.

  Section safetyWithImports.
    Variable stn : settings.
    Variable prog : program.

    Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
      -> Labels stn l2 = Some w
      -> l1 = l2.

    Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
      -> exists w, Labels stn l = Some w
        /\ prog w = Some bl.

    Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (Imports m)
      -> exists w, Labels stn l = Some w
        /\ prog w = None.

    Hypothesis ok : moduleOk.

    Definition specs' : codeSpec W (settings * state) := fun w =>
      LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some p
                        else pre
                    end
        end) (Imports m) None.

    Definition specs0 : codeSpec W (settings * state) := fun w =>
      LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some (fst p)
                        else pre
                    end
        end) (Blocks m) (specs' w).

    Theorem InA_weaken : forall A (P : A -> A -> Prop) (x : A) (ls : list A),
      SetoidList.InA P x ls
      -> forall (P' : A -> A -> Prop) x',
        (forall y, P x y -> P' x' y)
        -> SetoidList.InA P' x' ls.
      induction 1; simpl; intuition.
    Qed.

    Lemma specs_nochange' : forall v w (bls : list (LabelMap.key * (assert * block))),
      List.fold_left (fun pre l_p =>
        match pre with
          | Some _ => pre
          | None => match Labels stn (fst l_p) with
                      | None => None
                      | Some w' => if weq w w'
                        then Some (fst (snd l_p))
                        else pre
                    end
        end) bls (Some v) = Some v.
      induction bls; simpl; intuition.
    Qed.

    Lemma specs_nochange : forall v w (bls : LabelMap.t (assert * block)),
      LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some (fst p)
                        else pre
                    end
        end) bls (Some v) = Some v.
      intros; rewrite LabelMap.fold_1; apply specs_nochange'.
    Qed.

    Lemma specs'_nochange : forall w v (imps : list (LabelMap.key * assert)),
      List.fold_left (fun pre l_p =>
        match pre with
          | Some _ => pre
          | None => match Labels stn (fst l_p) with
                      | None => None
                      | Some w' => if weq w w'
                        then Some (snd l_p)
                        else pre
                    end
        end) imps (Some v) = Some v.
      induction imps; simpl; intuition.
    Qed.

    Lemma specs'_gotit : forall l pre w (imps : LabelMap.t assert),
      LabelMap.MapsTo l pre imps
      -> Labels stn l = Some w
      -> LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some p
                        else pre
                    end
        end) imps None = Some pre.
      intros; apply LabelMap.elements_1 in H; rewrite LabelMap.fold_1;
        generalize (LabelMap.elements_3w imps); induction H; simpl; intuition.

      hnf in H; simpl in H; intuition subst.
      unfold LabelMap.key; rewrite H0.
      destruct (weq w w); subst; intuition.
      apply specs'_nochange.

      inversion H1; clear H1; subst.
      specialize (inj _ (fst y) H0).
      case_eq (Labels stn (fst y)); intuition.
      destruct (weq w w0); subst; intuition subst.
      rewrite specs'_nochange.
      elimtype False; apply H4.
      eapply InA_weaken; eauto.
      intros.
      hnf; hnf in H3; simpl in H3; tauto.
    Qed.

    Lemma specs'_nothere : forall l w (imps : LabelMap.t assert),
      ~LabelMap.In l imps
      -> Labels stn l = Some w
      -> LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some p
                        else pre
                    end
        end) imps None = None.
      intros.
      assert (forall pre, ~SetoidList.InA (LabelMap.eq_key_elt (elt:=assert)) (l, pre) (LabelMap.elements imps)).
      intros; intro.
      apply H.
      apply LabelFacts.elements_in_iff.
      eauto.
      clear H; rename H1 into H.
      rewrite LabelMap.fold_1; induction (LabelMap.elements imps); simpl; intuition.
      assert (forall pre, ~SetoidList.InA (LabelMap.eq_key_elt (elt := assert)) (l, pre) l0) by eauto.
      intuition.
      case_eq (Labels stn (fst a)); intuition.
      destruct (weq w w0); intuition subst.
      eapply inj in H3; [ | eauto ].
      subst.
      elimtype False; eapply H.
      constructor; hnf; simpl; eauto.
    Qed.

    Lemma specs_gotit : forall l pre w bl (bls : LabelMap.t (assert * block)),
      LabelMap.MapsTo l (pre, bl) bls
      -> Labels stn l = Some w
      -> LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some (fst p)
                        else pre
                    end
        end) bls None = Some pre.
      intros; apply LabelMap.elements_1 in H; rewrite LabelMap.fold_1;
        generalize (LabelMap.elements_3w bls); induction H; simpl; intuition.

      hnf in H; simpl in H; intuition subst.
      unfold LabelMap.key; rewrite H0.
      destruct (weq w w); subst; intuition.
      rewrite <- H3; simpl.
      apply specs_nochange'.

      inversion H1; clear H1; subst.
      specialize (inj _ (fst y) H0).
      case_eq (Labels stn (fst y)); intuition.
      destruct (weq w w0); subst; intuition subst.
      rewrite specs_nochange'.
      elimtype False; apply H4.
      eapply InA_weaken; eauto.
      intros.
      hnf; hnf in H3; simpl in H3; tauto.
    Qed.

    Lemma specsOk : forall l pre, LabelMap.MapsTo l pre allPreconditions
      -> exists w, Labels stn l = Some w
        /\ specs0 w = Some pre.
      unfold specs0; intros.
      destruct (allPreconditions_cases H) as [ | [ ] ]; clear H.

      specialize (agreeImp H0); destruct agreeImp as [ ? [ ] ]; clear agreeImp.
      do 2 esplit; eauto.
      unfold specs'; erewrite specs'_gotit.
      apply specs_nochange.
      eauto.
      auto.

      destruct (agree H0); intuition.
      do 2 esplit; eauto.
      unfold specs'; erewrite specs'_nothere; eauto.

      Focus 2.
      apply LabelMap.elements_1 in H0.
      apply SetoidList.InA_alt in H0; destruct H0; intuition.
      generalize (proj1 (List.Forall_forall _ _) (NoSelfImport ok) _ H4); intros.
      hnf in H3; simpl in H3; intuition subst.
      tauto.

      eapply specs_gotit; eauto.
    Qed.

    Lemma specs'_hit : forall w pre (imps : LabelMap.t assert),
      LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some p
                        else pre
                    end
        end) imps None = Some pre
      -> exists l, LabelMap.MapsTo l pre imps
        /\ Labels stn l = Some w.
      intros.
      assert (exists l : LabelMap.key,
        SetoidList.InA (@LabelMap.eq_key_elt _) (l, pre) (LabelMap.elements imps) /\ Labels stn l = Some w).
      rewrite LabelMap.fold_1 in *.
      induction (LabelMap.elements imps); simpl in *; intuition (try congruence).
      case_eq (Labels stn (fst a)); intros.
      rewrite H0 in *.
      destruct (weq w w0); subst.
      rewrite specs'_nochange in H.
      injection H; clear H; intros; subst.
      do 2 esplit; eauto.
      constructor; hnf; simpl; tauto.
      intuition.
      destruct H1; intuition eauto.
      rewrite H0 in H.
      intuition.
      destruct H1; intuition eauto.
      destruct H0; intuition.
      do 2 esplit; eauto.
      apply LabelMap.elements_2; auto.
    Qed.

    Lemma specs_hit : forall w preOpt pre (bls : LabelMap.t (assert * block)),
      LabelMap.fold (fun l p pre =>
        match pre with
          | Some _ => pre
          | None => match Labels stn l with
                      | None => None
                      | Some w' => if weq w w'
                        then Some (fst p)
                        else pre
                    end
        end) bls preOpt = Some pre
      -> preOpt = Some pre
      \/ exists l, exists bl, LabelMap.MapsTo l (pre, bl) bls
        /\ Labels stn l = Some w.
      intros.
      assert (preOpt = Some pre
        \/ exists l, exists bl,
        SetoidList.InA (@LabelMap.eq_key_elt _) (l, (pre, bl)) (LabelMap.elements bls) /\ Labels stn l = Some w).
      rewrite LabelMap.fold_1 in *.
      induction (LabelMap.elements bls); simpl in *; intuition (try congruence).
      destruct preOpt.
      rewrite specs_nochange' in H.
      injection H; clear H; intros; subst; tauto.
      case_eq (Labels stn (fst a)); intros.
      rewrite H0 in *.
      destruct (weq w w0); subst.
      rewrite specs_nochange' in H.
      injection H; clear H; intros; subst.
      destruct a as [ ? [ ] ]; simpl in *.
      right; do 3 esplit; eauto.
      constructor; hnf; simpl; tauto.
      intuition.
      destruct H2 as [ ? [ ] ]; intuition eauto.
      rewrite H0 in H.
      intuition.
      destruct H2 as [ ? [ ] ]; intuition eauto.
      destruct H0; intuition.
      destruct H0 as [ ? [ ] ]; intuition.
      right; do 3 esplit; eauto.
      apply LabelMap.elements_2; eauto.
    Qed.

    Lemma specsOk' : forall w pre, specs0 w = Some pre
      -> exists l, Labels stn l = Some w
        /\ (LabelMap.MapsTo l pre (Imports m)
          \/ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m)).
      unfold specs0, specs'; intros.
      apply specs_hit in H; intuition.
      apply specs'_hit in H0.
      destruct H0; intuition eauto.
      destruct H0 as [ ? [ ] ]; intuition eauto.
    Qed.

    Lemma safety' : forall st' st'', reachable stn prog st' st''
      -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
        -> forall st, interp specs0 (pre (stn, st))
          -> forall w, Labels stn l = Some w
            -> st' = (w, st)
            -> exists l', Labels stn l' = Some (fst st'')
              /\ exists pre', (LabelMap.MapsTo l' pre' (Imports m)
                \/ exists bl', LabelMap.MapsTo l' (pre', bl') (Blocks m))
              /\ interp specs0 (pre' (stn, snd st'')).
      induction 1; simpl; intuition; subst; simpl in *.
      eauto 10.

      destruct (agree H1); intuition.
      rewrite H3 in H5; injection H5; clear H5; intros; subst.
      unfold step in H; simpl in H.
      rewrite H6 in H.
      specialize (BlocksOk ok H1); intro ok'.
      red in ok'.
      specialize (@ok' stn _ specsOk _ H2).
      destruct ok'; clear ok; intuition.
      rewrite H in H5; injection H5; clear H5; intros; subst.
      destruct H7; intuition.
      destruct (specsOk' _ H5) as [? [? [ ] ] ].

      inversion H0; clear H0; subst.
      eauto 10.

      unfold step in H9.
      destruct (agreeImp H8) as [ ? [ ] ].
      rewrite H4 in H0; injection H0; clear H0; intros; subst.
      rewrite H11 in H9; discriminate.

      destruct H8.
      eapply IHreachable.
      apply H8.
      eauto.
      eauto.
      destruct x0; simpl in *.
      congruence.
    Qed.

    Theorem safety'' : forall st st', reachable stn prog st st'
      -> forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
        -> Labels stn l = Some (fst st)
        -> interp specs0 (pre (stn, snd st))
        -> (exists l', Labels stn l' = Some (fst st')
          /\ exists pre', LabelMap.MapsTo l' pre' (Imports m)
            /\ interp specs0 (pre' (stn, snd st')))
        \/ step stn prog st' <> None.
      intros.
      eapply safety' in H; eauto.
      2: destruct st; auto.
      destruct H as [ ? [ ? [ ? [ ] ] ] ]; intuition eauto.
      destruct H5.
      apply (BlocksOk ok H3) in H4; [ | apply specsOk ].
      destruct H4 as [ ? [ ? [ ? [ ] ] ] ].
      right; intro.
      unfold step in H7.
      apply agree in H3; destruct H3; intuition.
      rewrite H in H8; injection H8; clear H8; intros; subst.
      rewrite H9 in H7.
      congruence.
    Qed.
  End safetyWithImports.

  (** Main safety theorem *)

  Hypothesis closed : LabelMap.cardinal (Imports m) = 0.

  Variable stn : settings.
  Variable prog : program.

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis ok : moduleOk.

  Hint Constructors SetoidList.InA.

  Definition specs : codeSpec W (settings * state) := specs0 stn.

  Lemma it's_really_empty : forall k v,
    LabelMap.MapsTo k v (Imports m)
    -> False.
    intros; apply LabelMap.elements_1 in H.
    rewrite LabelMap.cardinal_1 in closed.
    inversion H.
    rewrite <- H0 in closed.
    discriminate.
    rewrite <- H0 in closed.
    discriminate.
  Qed.

  Theorem safety : forall mn g pre,
    LabelMap.MapsTo (mn, Global g) pre (Exports m)
    -> forall w, Labels stn (mn, Global g) = Some w
      -> forall st, interp specs (pre (stn, st))
        -> safe stn prog (w, st).
    intros; hnf; intros.
    apply (ExportsSound ok) in H; destruct H.
    eapply safety'' in H; eauto.
    intuition.
    destruct H4 as [ ? [ ? [ ? [ ] ] ] ]; intuition.
    eapply it's_really_empty; eauto.

    intros.
    elimtype False; eapply it's_really_empty; eauto.
  Qed.
End moduleOk.


(** * Safe linking of modules *)
Section link.
  Variables m1 m2 : module.

  Definition union A (mp1 mp2 : LabelMap.t A) : LabelMap.t A :=
    LabelMap.fold (@LabelMap.add _) mp1 mp2.

  Definition diff A B (mp1 : LabelMap.t A) (mp2 : LabelMap.t B) : LabelMap.t A :=
    LabelMap.fold (fun k v mp => if LabelMap.mem k mp2 then mp else LabelMap.add k v mp) mp1 (@LabelMap.empty _).

  Definition link := {|
    Imports := union (diff (Imports m1) (Exports m2)) (diff (Imports m2) (Exports m1));
    Blocks := union (Blocks m1) (Blocks m2);
    Exports := union (Exports m1) (Exports m2);
    Modules := StringSet.union (Modules m1) (Modules m2)
  |}.

  Hypothesis m1Ok : moduleOk m1.
  Hypothesis m2Ok : moduleOk m2.

  (* No label should be duplicated between the blocks of the two modules. *)
  Hypothesis NoDups : StringSet.is_empty (StringSet.inter (Modules m1) (Modules m2)) = true.

  (* Any import of one module provided by the other should have agreement on specification. *)
  Definition importsOk (Imp : LabelMap.t assert) (Exp : LabelMap.t assert) :=
    LabelMap.fold (fun l pre P =>
      match LabelMap.find l Exp with
        | None => P
        | Some pre' => pre = pre' /\ P
      end) Imp True.

  Hypothesis ImportsOk1 : importsOk (Imports m1) (Exports m2).
  Hypothesis ImportsOk2 : importsOk (Imports m2) (Exports m1).

  (* The modules must agree on shared imports. *)
  Hypothesis ImportsAgree : LabelMap.fold (fun l pre P =>
    match LabelMap.find l (Imports m2) with
      | None => P
      | Some pre' => pre = pre' /\ P
    end) (Imports m1) True.

  Theorem MapsTo_union : forall A k v (mp1 mp2 : LabelMap.t A),
    LabelMap.MapsTo k v (union mp1 mp2)
    -> LabelMap.MapsTo k v mp1 \/ LabelMap.MapsTo k v mp2.
    unfold union; intros.
    rewrite LabelMap.fold_1 in H.
    generalize (@LabelMap.elements_2 _ mp1).
    generalize dependent mp2.
    induction (LabelMap.elements mp1); simpl in *; intuition; simpl in *.
    apply IHl in H; clear IHl.
    intuition.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    left; apply H0.
    constructor.
    hnf.
    tauto.

    eauto.
  Qed.

  Lemma blockOk_impl : forall imps imps' p bl,
    (forall k v, LabelMap.MapsTo k v imps
      -> LabelMap.MapsTo k v imps')
    -> blockOk imps p bl
    -> blockOk imps' p bl.
    unfold blockOk; intuition.
  Qed.

  Lemma fold_mono1 : forall A F ls b,
    List.fold_left (fun (a : bool) (x : A) => a || F x) ls b = false
    -> b = false.
    induction ls; simpl; intuition.
    apply IHls in H.
    destruct b; simpl in *; congruence.
  Qed.

  Lemma fold_mono2 : forall A F ls b,
    List.fold_left (fun (a : bool) (x : A) => a || F x) ls b = false
    -> List.Forall (fun x => F x = false) ls.
    induction ls; simpl; intuition.
    specialize (fold_mono1 _ _ _ H).
    destruct b; try discriminate.
    eauto.
  Qed.

  Lemma link_allPreconditions : forall k v m m', LabelMap.MapsTo k v (allPreconditions m)
    -> (forall k v, LabelMap.MapsTo k v (Blocks m) -> LabelMap.MapsTo k v (Blocks m'))
    -> (forall k v, LabelMap.MapsTo k v (Imports m) -> LabelMap.MapsTo k v (Imports m')
      \/ exists bl, LabelMap.MapsTo k (v, bl) (Blocks m'))
    -> noSelfImport m'
    -> LabelMap.MapsTo k v (allPreconditions m').
    unfold allPreconditions, noSelfImport; intros.
    repeat rewrite LabelMap.fold_1 in *.
    generalize (fun k v (H : SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements (Blocks m))) => H0 k v (LabelMap.elements_2 H));
      clear H0; intro H0.

    generalize (LabelMap.elements_3w (Blocks m)).
    induction (LabelMap.elements (Blocks m)); simpl in *; intuition.

    clear H0.
    apply H1 in H; clear H1; intuition.

    generalize dependent (Imports m').
    induction (LabelMap.elements (Blocks m')); simpl; intuition; simpl in *.
    inversion H2; clear H2; intros; subst; simpl in *.
    specialize (IHl _ H5 H0).

    assert (LabelMap.MapsTo k v t -> LabelMap.MapsTo k v (LabelMap.add a0 a t)).
    intros; apply LabelMap.add_2; auto.
    intro; subst.
    apply H4.
    hnf; eauto.
    generalize dependent (LabelMap.add a0 a t).
    clear H0 H3 H4 H5; generalize dependent t.
    induction l; simpl in *; intuition; simpl in *.
    eapply IHl; eauto; intros.
    apply LabelFacts.add_mapsto_iff in H0; intuition; subst.
    apply LabelMap.add_1; auto.
    apply LabelMap.add_2; auto.


    destruct H0.
    generalize (LabelMap.elements_3w (Blocks m')).
    apply LabelMap.elements_1 in H.
    generalize dependent (Imports m').
    induction (LabelMap.elements (Blocks m')); simpl; intuition.
    inversion H.
    inversion H2; clear H2; intros; subst.
    inversion H; clear H; intros; subst.
    red in H2; intuition; subst; simpl in *; subst.
    destruct a; simpl in *; subst; simpl in *.
    inversion H0; clear H0; intros; subst.
    hnf in H2; simpl in H2; intuition; subst; simpl in *.
    assert (LabelMap.MapsTo k0 v (LabelMap.add k0 v t)).
    apply LabelMap.add_1; auto.
    generalize dependent (LabelMap.add k0 v t).
    generalize H4; clear.
    induction l; simpl; intuition.
    apply H; auto.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H4; auto.
    constructor.
    reflexivity.

    intuition.
    inversion H0; clear H0; intros; subst.
    apply H in H6; clear H; auto.
    assert (LabelMap.MapsTo k v t -> LabelMap.MapsTo k v (LabelMap.add (fst a) (fst (snd a)) t)).
    intro.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H5; hnf; eauto.
    generalize dependent (LabelMap.add (fst a) (fst (snd a)) t).
    generalize H6; clear.
    generalize t.
    induction l; simpl; intuition.
    simpl in *.
    eapply IHl in H6; eauto.
    intro.
    apply LabelFacts.add_mapsto_iff in H0; intuition; subst.
    apply LabelMap.add_1; auto.
    apply LabelMap.add_2; auto.


    inversion H3; clear H3; intros; subst.
    assert (LabelMap.MapsTo (fst a) (snd a) (Blocks m')).
    apply H0.
    constructor.
    destruct a; hnf; auto.
    assert (k = fst a /\ v = fst (snd a)
      \/ LabelMap.MapsTo k v
      (List.fold_left
        (fun (a : LabelMap.t assert) (p : label * (assert * block)) =>
          LabelMap.add (fst p) (fst (snd p)) a) l (Imports m))).

    generalize H; clear.
    assert (LabelMap.MapsTo k v (LabelMap.add (fst a) (fst (snd a)) (Imports m))
      -> (k = fst a /\ v = fst (snd a))
      \/ LabelMap.MapsTo k v (Imports m)).
    intro.
    apply LabelFacts.add_mapsto_iff in H; intuition.
    generalize dependent (LabelMap.add (fst a) (fst (snd a)) (Imports m)).
    generalize (Imports m).
    induction l; simpl; intuition.
    simpl in *.
    eapply IHl; [ | eassumption ].
    intro.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    right.
    apply LabelMap.add_1; auto.
    right.
    apply LabelMap.add_2; auto.


    intuition; subst.
    generalize (LabelMap.elements_3w (Blocks m')).
    apply LabelMap.elements_1 in H3.
    generalize H3; clear.
    destruct a; simpl.
    generalize (Imports m').
    induction (LabelMap.elements (Blocks m')); simpl; intuition.
    inversion H3.
    inversion H; clear H; intros; subst.
    inversion H3; clear H3; intros; subst.
    hnf in H0; intuition; subst; simpl in *; subst.
    simpl.
    assert (LabelMap.MapsTo a0 a (LabelMap.add a0 a t)) by (apply LabelMap.add_1; auto).
    clear IHl H4.
    generalize dependent (LabelMap.add a0 a t).
    induction l; simpl; intuition.
    apply H.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H2.
    constructor.
    red; reflexivity.

    eauto.
  Qed.

  Theorem Forall_union : forall A (P : _ * A -> Prop) bls1 bls2,
    List.Forall P (LabelMap.elements bls1)
    -> List.Forall P (LabelMap.elements bls2)
    -> List.Forall P (LabelMap.elements (union bls1 bls2)).
    intros; unfold union.
    rewrite LabelMap.fold_1.
    generalize dependent bls2.
    induction (LabelMap.elements bls1); simpl in *; intuition.

    inversion H; clear H; intros; subst.
    apply IHl; auto.
    apply List.Forall_forall; intros.
    assert (SetoidList.InA (@LabelMap.eq_key_elt _) x (LabelMap.elements (LabelMap.add (fst a) (snd a) bls2))).
    apply SetoidList.InA_alt.
    repeat esplit; auto.
    destruct x.
    apply LabelMap.elements_2 in H1.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    destruct a; assumption.
    eapply List.Forall_forall.
    apply H0.
    apply LabelMap.elements_1 in H5.
    apply SetoidList.InA_alt in H5.
    destruct H5; intuition.
    hnf in H6; simpl in H6; intuition; subst.
    destruct x; assumption.
  Qed.

  Theorem MapsTo_union1 : forall A k v (mp1 mp2 : LabelMap.t A),
    LabelMap.MapsTo k v mp1
    -> LabelMap.MapsTo k v (union mp1 mp2).
    unfold union; intros.
    rewrite LabelMap.fold_1.
    generalize (@LabelMap.elements_1 _ mp1 _ _ H); clear H.
    generalize (@LabelMap.elements_3w _ mp1).
    generalize dependent mp2.
    induction (LabelMap.elements mp1); simpl in *; intuition; simpl in *.
    inversion H0.
    inversion H; clear H; intros; subst.
    inversion H0; clear H0; intros; subst.
    hnf in H1; simpl in *; intuition; subst.
    generalize H3; clear.
    assert (LabelMap.MapsTo a0 b (LabelMap.add a0 b mp2)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add a0 b mp2).
    induction l; simpl; intuition; simpl.
    apply IHl; auto.
    apply LabelMap.add_2; auto.
    intro; subst; apply H3.
    constructor; hnf; reflexivity.

    eauto.
  Qed.

  Theorem MapsTo_union2 : forall A k v (mp1 mp2 : LabelMap.t A),
    LabelMap.MapsTo k v mp2
    -> (forall v', LabelMap.MapsTo k v' mp1 -> v' = v)
    -> LabelMap.MapsTo k v (union mp1 mp2).
    unfold union; intros.
    rewrite LabelMap.fold_1.
    generalize (@LabelMap.elements_3w _ mp1).
    generalize dependent mp2.
    generalize (fun v' (H : SetoidList.InA (@LabelMap.eq_key_elt _) (k, v') (LabelMap.elements mp1)) => H0 v' (LabelMap.elements_2 H)).
    clear.
    induction (LabelMap.elements mp1); simpl in *; intuition; simpl in *.
    inversion H1; clear H1; intros; subst; simpl in *.
    apply IHl; auto.
    destruct (LabelKey.eq_dec k (fst a)).
    hnf in e; subst.
    assert (snd a = v).
    apply H.
    destruct a; simpl.
    constructor; hnf; auto.
    subst.
    apply LabelMap.add_1; auto.
    apply LabelMap.add_2; auto.
  Qed.

  Hint Resolve MapsTo_union1 MapsTo_union2.

  Theorem NoDups_Forall : forall (bls1 bls2 : LabelMap.t (assert * block)) i,
    LabelMap.fold (fun k v b => b || LabelMap.mem k bls2) bls1 i = false
    -> List.Forall (fun p => ~LabelMap.In (fst p) bls2) (LabelMap.elements bls1).
    intros; rewrite LabelMap.fold_1 in *.
    generalize dependent bls2.
    generalize dependent i.
    induction (LabelMap.elements bls1); simpl in *; intuition; simpl in *.
    constructor; simpl.
    specialize (fold_mono1 _ _ _ H); intro Hmono.
    destruct i; try discriminate; simpl in *.
    intro.
    apply LabelMap.mem_1 in H0.
    congruence.

    eauto.
  Qed.

  Hint Resolve NoDups_Forall.

  Lemma MapsTo_diff' : forall A B k (v : A) (mp2 : LabelMap.t B) (mp1 mp' : LabelMap.t A),
    LabelMap.MapsTo k v
    (LabelMap.fold (fun k0 v0 mp => if LabelMap.mem k0 mp2 then mp else LabelMap.add k0 v0 mp)
      mp1 mp')
    -> (LabelMap.In k mp' -> ~LabelMap.In k mp2)
    -> (LabelMap.MapsTo k v mp1 \/ LabelMap.MapsTo k v mp') /\ ~LabelMap.In k mp2.
    intros; rewrite LabelMap.fold_1 in *.

    assert ((SetoidList.InA (@LabelMap.eq_key_elt _) (k, v) (LabelMap.elements mp1) \/ LabelMap.MapsTo k v mp') /\
      ~LabelMap.In k mp2); [ | generalize (@LabelMap.elements_2 _ mp1); intuition ].

    generalize dependent mp'; induction (LabelMap.elements mp1); simpl; intuition.
    unfold LabelMap.In, LabelMap.Raw.In0 in *; eauto.

    simpl in *.
    apply IHl in H; intuition.

    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; intuition.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    left; constructor; hnf; auto.

    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; intuition.
    destruct H1.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    destruct H2.
    generalize (LabelMap.mem_1 (ex_intro (fun v => LabelMap.MapsTo _ v _) _ H1)); congruence.
    unfold LabelMap.In, LabelMap.Raw.In0 in *; eauto.

    simpl in *.
    apply IHl in H; intuition.
    match goal with
      | [ _ : context[if ?E then _ else _] |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; intuition.
    destruct H2.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst.
    apply LabelMap.mem_1 in H3; congruence.
    unfold LabelMap.In, LabelMap.Raw.In0 in *; eauto.
  Qed.

  Lemma MapsTo_diff : forall A B k v (mp1 : LabelMap.t A) (mp2 : LabelMap.t B),
    LabelMap.MapsTo k v (diff mp1 mp2)
    -> LabelMap.MapsTo k v mp1 /\ ~LabelMap.In k mp2.
    intros.
    apply MapsTo_diff' in H; intuition.
    apply LabelMap.empty_1 in H; tauto.
    destruct H0.
    apply LabelMap.empty_1 in H0; tauto.
  Qed.

  Lemma linkOk' : noSelfImport link.
    destruct m1Ok; clear m1Ok.
    destruct m2Ok; clear m2Ok.
    red; simpl.
    apply Forall_union; apply List.Forall_forall; intros; intro.

    destruct H0.
    apply MapsTo_union in H0; intuition.

    apply MapsTo_diff in H1; intuition.
    hnf in NoSelfImport0.
    eapply (proj1 (List.Forall_forall _ _)) in NoSelfImport0.
    apply NoSelfImport0.
    hnf; eauto.
    auto.

    apply MapsTo_diff in H1; intuition.
    apply H2.
    destruct x; simpl in *.
    destruct k; simpl in *; subst.
    destruct p.
    eexists.
    match goal with
      | [ |- LabelMap.Raw.MapsTo ?X ?Y (LabelMap.this ?Z) ] =>
        change (LabelMap.MapsTo X Y Z)
    end.
    apply ImportsGlobal1 in H0; destruct H0; simpl in *; subst.
    eapply ExportsComplete0.
    apply LabelMap.elements_2.
    apply SetoidList.InA_alt.
    eexists.
    split.
    reflexivity.
    eauto.


    destruct H0.
    apply MapsTo_union in H0; intuition.

    apply MapsTo_diff in H1; intuition.
    destruct x; simpl in *.
    destruct k; simpl in *; subst.
    destruct p.
    destruct (ImportsGlobal0 _ _ H0).
    simpl in *; subst.
    apply H2.
    eexists.
    match goal with
      | [ |- LabelMap.Raw.MapsTo ?X ?Y (LabelMap.this ?Z) ] =>
        change (LabelMap.MapsTo X Y Z)
    end.
    eapply ExportsComplete1.
    apply LabelMap.elements_2.
    apply SetoidList.InA_alt.
    eexists.
    split.
    reflexivity.
    eauto.

    apply MapsTo_diff in H1; intuition.
    hnf in NoSelfImport1.
    eapply (proj1 (List.Forall_forall _ _)) in NoSelfImport1.
    apply NoSelfImport1.
    hnf; eauto.
    auto.
  Qed.

  Hint Resolve linkOk'.

  Lemma use_importsOk' : forall (exp : LabelMap.t assert) l P,
    List.fold_left (fun P p =>
      match LabelMap.find (fst p) exp with
        | None => P
        | Some pre' => snd p = pre' /\ P
      end) l P
    -> P.
    induction l; simpl; intuition; simpl in *.

    destruct (LabelMap.find a0 exp).
    apply IHl in H; tauto.
    apply IHl in H; tauto.
  Qed.

  Lemma use_importsOk : forall k v p imp exp,
    importsOk imp exp
    -> LabelMap.MapsTo k v imp
    -> LabelMap.find k exp = Some p
    -> v = p.
    clear ImportsAgree; unfold importsOk; intros.

    rewrite LabelMap.fold_1 in *.
    apply LabelMap.elements_1 in H0.
    generalize dependent True.
    induction (LabelMap.elements imp); simpl in *; intuition.
    inversion H0.

    inversion H0; clear H0; intuition; subst.
    hnf in H3; simpl in *; intuition; subst.
    unfold LabelMap.key in *.
    rewrite H1 in H.
    apply use_importsOk' in H; tauto.

    eauto.
  Qed.

  Lemma MapsTo_diffr : forall A B k v (mp1 : LabelMap.t A) (mp2 : LabelMap.t B),
    LabelMap.MapsTo k v mp1
    -> ~LabelMap.In k mp2
    -> SetoidList.NoDupA (@LabelMap.eq_key _) (LabelMap.elements mp1)
    -> LabelMap.MapsTo k v (diff mp1 mp2).
    intros; unfold diff.
    rewrite LabelMap.fold_1.
    apply LabelMap.elements_1 in H.
    generalize (LabelMap.empty A).
    induction (LabelMap.elements mp1); simpl in *; intuition.
    inversion H.

    inversion H1; clear H1; intros; subst.
    inversion H; clear H; intros; subst.
    hnf in H2; simpl in *; intuition; subst.
    case_eq (LabelMap.mem (fst a) mp2); intro Heq.
    apply LabelMap.mem_2 in Heq; tauto.
    generalize H4; clear.
    assert (LabelMap.MapsTo (fst a) (snd a) (LabelMap.add (fst a) (snd a) t)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add (fst a) (snd a) t).
    induction l; simpl; intuition; simpl.
    destruct (LabelMap.mem a1 mp2); auto.
    apply IHl; auto.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H4.
    constructor; hnf; auto.

    auto.
  Qed.

  Lemma use_NoDups : forall k0 v,
    LabelMap.find k0 (Blocks m2) = Some v
    -> forall v', LabelMap.MapsTo k0 v' (Blocks m1) -> v' = v.
    intros.
    elimtype False.
    apply LabelMap.find_2 in H.
    destruct k0.
    apply (ModulesSound m1Ok) in H0.
    apply (ModulesSound m2Ok) in H.
    apply StringSet.is_empty_2 in NoDups.
    eapply NoDups.
    apply StringSet.inter_3; eauto.
  Qed.

  Hint Resolve use_NoDups.

  Lemma ImportsAgree_mono : forall (imp1 : LabelMap.t assert) ls P,
    List.fold_left (fun P p =>
      match LabelMap.find (fst p) imp1 with
        | None => P
        | Some pre' => snd p = pre' /\ P
      end) ls P
    -> P.
    induction ls; simpl in *; intuition; simpl in *.
    destruct (LabelMap.find a0 imp1).
    apply IHls in H; tauto.
    apply IHls in H; tauto.
  Qed.

  Theorem linkOk : moduleOk link.
    destruct m1Ok.
    destruct m2Ok.

    constructor; auto.

    intros.
    simpl in H; apply MapsTo_union in H; destruct H.

    apply BlocksOk0 in H.
    eapply blockOk_impl; [ | eassumption ].
    intros; eapply link_allPreconditions; simpl; eauto.

    intros.
    case_eq (LabelMap.find k0 (Blocks m2)); intros.
    destruct (ImportsGlobal0 _ _ H1).
    destruct k0; simpl in *; subst.

    apply LabelMap.find_2 in H2.
    destruct p.
    apply ExportsComplete1 in H2.
    apply LabelMap.find_1 in H2.
    specialize (use_importsOk _ ImportsOk1 H1 H2); intro; subst.

    right.
    apply LabelMap.find_2 in H2.
    apply ExportsSound1 in H2.
    destruct H2.
    eexists.
    apply MapsTo_union2.
    eauto.
    apply LabelMap.find_1 in H2.
    eauto.

    left.
    apply MapsTo_union1.
    apply MapsTo_diffr; auto.
    intro.
    destruct H3.
    apply ImportsGlobal0 in H1; destruct H1.
    destruct k0; simpl in *; subst.
    apply ExportsSound1 in H3; destruct H3.
    apply LabelMap.find_1 in H1; congruence.
    apply LabelMap.elements_3w.


    apply BlocksOk1 in H.
    eapply blockOk_impl; [ | eassumption ].
    intros; eapply link_allPreconditions; simpl; eauto.

    intros.
    eapply MapsTo_union2; eauto.
    intros.
    eapply use_NoDups; eauto.
    apply LabelMap.find_1; auto.

    intros.
    case_eq (LabelMap.find k0 (Blocks m1)); intros.

    apply LabelMap.find_2 in H2.
    destruct p.
    destruct (ImportsGlobal1 _ _ H1).
    destruct k0; simpl in *; subst.
    apply ExportsComplete0 in H2.
    apply LabelMap.find_1 in H2.
    specialize (use_importsOk _ ImportsOk2 H1 H2); intro; subst.
    right.
    apply LabelMap.find_2 in H2.
    destruct (ExportsSound0 _ _ _ H2).
    eexists.
    apply MapsTo_union1.
    eauto.

    left.
    apply MapsTo_union2.


    apply MapsTo_diffr; auto.
    intro.
    destruct H3.
    apply LabelMap.find_1 in H3.
    apply ImportsGlobal1 in H1; destruct H1.
    destruct k0; simpl in *; subst.
    apply LabelMap.find_2 in H3.
    apply ExportsSound0 in H3; destruct H3.
    apply LabelMap.find_1 in H1; congruence.
    apply LabelMap.elements_3w.

    intros.
    apply MapsTo_diff in H3; intuition.
    apply LabelMap.elements_1 in H4.
    generalize ImportsAgree H1 H4; clear.
    rewrite LabelMap.fold_1.
    generalize True.
    induction (LabelMap.elements (Imports m1)); simpl; intuition.
    inversion H4.
    inversion H4; clear H4; intros; subst.
    hnf in H0; simpl in *; intuition; subst.
    apply LabelMap.find_1 in H1.
    rewrite H1 in ImportsAgree.

    apply ImportsAgree_mono in ImportsAgree; tauto.
    eauto.


    simpl; intros.
    apply MapsTo_union in H; intuition.
    apply MapsTo_diff in H0; intuition eauto.
    apply MapsTo_diff in H0; intuition eauto.


    simpl; intros.
    apply MapsTo_union in H; intuition.
    apply MapsTo_union1; eauto.
    apply MapsTo_union2; eauto.


    intros.
    apply ModulesSound1 in H0.
    apply ExportsSound0 in H; destruct H.
    apply ModulesSound0 in H.
    apply StringSet.is_empty_2 in NoDups.
    hnf in NoDups; unfold not in NoDups.
    elimtype False; eapply NoDups.
    apply StringSet.inter_3; eauto.


    simpl; intros.
    apply MapsTo_union in H; intuition.
    destruct (ExportsSound0 _ _ _ H0); eauto.
    destruct (ExportsSound1 _ _ _ H0); eauto.
    eexists; apply MapsTo_union2; eauto.


    intros.
    apply ModulesSound1 in H.
    apply ModulesSound0 in H1.
    apply StringSet.is_empty_2 in NoDups.
    hnf in NoDups; unfold not in NoDups.
    elimtype False; eapply NoDups.
    apply StringSet.inter_3; eauto.


    simpl; intros.
    apply MapsTo_union in H; intuition.
    apply StringSet.union_2; eapply ModulesSound0; eauto.
    apply StringSet.union_3; eapply ModulesSound1; eauto.
  Qed.
End link.
