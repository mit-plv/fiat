Require Import Coq.omega.Omega.
(* Structured programming (module construction) *)

Require Import Coq.Bool.Bool Coq.NArith.NArith Coq.Strings.String Coq.Lists.List.

Require Import Bedrock.Nomega Bedrock.PropX Bedrock.PropXTac Bedrock.Word Bedrock.LabelMap Bedrock.IL Bedrock.XCAP Bedrock.Structured.
Require Import Bedrock.StringSet.

Set Implicit Arguments.

Local Open Scope N_scope.

Import DefineStructured.

Section module.
  Definition import := (string * string * assert)%type.

  Variable imports : list import.
  (* Which functions from outside this module do we need? *)

  Variable modName : string.
  (* New module name *)

  Definition function := (string * assert * forall imports, importsGlobal imports -> cmd imports modName)%type.

  Variable functions : list function.
  (* All functions in this module. *)

  (* Build the full list of imports for the commands, including both external and internal functions.
   * First, we build a version for only the external functions. *)

  Definition importsMap : LabelMap.t assert :=
    List.fold_left (fun m p => let '(modl, f, pre) := p in
      LabelMap.add (modl, Global f) pre m) imports (LabelMap.empty _).

  Lemma importsMapGlobal' : forall (im : list import) m,
    importsGlobal m
    -> importsGlobal (List.fold_left (fun m p => let '(modl, f, pre) := p in
      LabelMap.add (modl, Global f) pre m) im m).
    unfold importsGlobal; induction im as [ | [ ] ]; simpl; intuition.
    apply IHim in H0; auto.
    intros.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst; simpl; eauto.
  Qed.

  Theorem importsMapGlobal : importsGlobal importsMap.
    apply importsMapGlobal'; red; intros.
    destruct (LabelMap.empty_1 H).
  Qed.

  Definition fullImports : LabelMap.t assert :=
    List.fold_left (fun m p => let '(f, pre, _) := p in
      LabelMap.add (modName, Global f) pre m) functions importsMap.

  Lemma fullImportsGlobal' : forall (fs : list function) m,
    importsGlobal m
    -> importsGlobal (List.fold_left (fun m p => let '(f, pre, _) := p in
      LabelMap.add (modName, Global f) pre m) fs m).
    induction fs as [ | [ ] ]; simpl; intuition.
    apply IHfs; red; intros.
    apply LabelFacts.add_mapsto_iff in H0; intuition; subst; simpl; eauto.
  Qed.

  Theorem fullImportsGlobal : importsGlobal fullImports.
    apply fullImportsGlobal'; apply importsMapGlobal.
  Qed.

  (* Now we are ready to generate a module out of the functions. *)

  Definition buildLocals (bls : list (assert * block)) Base := snd (List.fold_left (fun b_m p => let '(b, m) := b_m in
    (Nsucc b, LabelMap.add (modName, Local b) p m)) bls (Base, LabelMap.empty _)).

  Fixpoint blocks (fs : list function) (Base : N) : LabelMap.t (assert * block) :=
    match fs with
      | nil => LabelMap.empty _
      | (f, pre, c) :: fs' =>
        let cout := c fullImports fullImportsGlobal pre in
        let cg := Generate cout (Nsucc Base) Base in
        LabelMap.add (modName, Global f) (pre, (nil, Uncond (RvLabel (modName, Local (Nsucc Base + Entry cg)))))
          (LabelMap.add (modName, Local Base) (Postcondition cout, (nil, Uncond (RvLabel (modName, Local Base))))
            (union (buildLocals (Blocks cg) (Nsucc Base))
              (blocks fs' (Nsucc Base + N_of_nat (length (Blocks cg))))))
    end.

  Fixpoint exps (fs : list function) : LabelMap.t assert :=
    match fs with
      | nil => LabelMap.empty _
      | (f, pre, _) :: fs' => LabelMap.add (modName, Global f) pre (exps fs')
    end.

  Definition bmodule_ : module := {|
    Imports := importsMap;
    XCAP.Blocks := blocks functions 1;
    Exports := exps functions;
    Modules := StringSet.singleton modName
  |}.

  Lemma Forall_MapsTo : forall A (P : _ * A -> Prop) m,
    (forall k v, LabelMap.MapsTo k v m -> P (k, v))
    -> List.Forall P (LabelMap.elements m).
    intros.
    generalize (fun k v H' => H k v (LabelMap.elements_2 H')); clear H; intro H.
    induction (LabelMap.elements m); simpl in *; intuition.
    constructor; auto.
    destruct a.
    apply H.
    constructor; hnf; auto.
  Qed.

  Hypothesis NoSelfImport :
    List.fold_left (fun b p => let '(m, _, _) := p in
      b || if string_dec m modName then true else false) imports false = false.

  Theorem importsNotThis : forall l, LabelMap.In (elt:=assert) (modName, l) importsMap -> False.
    intros.
    assert (forall k v, LabelMap.MapsTo k v (LabelMap.empty assert) -> k <> (modName, l)).
    intros.
    apply LabelMap.empty_1 in H0; tauto.
    destruct H.
    unfold importsMap in *.
    generalize dependent (LabelMap.empty assert).
    generalize NoSelfImport; clear NoSelfImport.
    generalize false at 2.
    induction imports; simpl in *; intuition.
    apply H0 in H; auto.
    destruct a as [ [ ] ]; simpl in *.
    eapply IHl0 in NoSelfImport.
    auto.
    eauto.
    intros; subst.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst; [ | eauto ].
    destruct (string_dec s modName); subst; try congruence.
    replace (b || true) with true in NoSelfImport by (destruct b; auto).
    generalize NoSelfImport; clear.
    induction l0; simpl; intuition.
    destruct a as [ [ ] ]; intuition.
  Qed.

  Hint Immediate importsNotThis.

  Theorem importsNotThis' : forall l v, LabelMap.MapsTo (elt:=assert) (modName, l) v importsMap -> False.
    intros; eapply importsNotThis.
    hnf.
    eauto.
  Qed.

  Hint Resolve importsNotThis'.

  Lemma Forall_nth_error : forall A (P : A -> Prop) x ls,
    List.Forall P ls
    -> forall n, nth_error ls n = Some x
      -> P x.
    induction 1; destruct n; simpl; intuition; try discriminate.
    injection H1; congruence.
    eauto.
  Qed.

  Hypothesis NoDupFunc :
    match (List.fold_left (fun mOpt p => let '(modl, _, _) := p in
      match mOpt with
        | None => None
        | Some m => let k := (modl, Local 0) in
          if LabelMap.mem k m then None
          else Some (LabelMap.add k tt m)
      end) functions (Some (LabelMap.empty unit))) with
      | None => False
      | Some _ => True
    end.

  Fixpoint makeVcs (fs : list function) : list Prop :=
    match fs with
      | nil => nil
      | f :: fs' =>
        let '(_, pre, c) := f in
          let cout := c fullImports fullImportsGlobal pre in
            (forall stn_st specs, ~interp specs (Postcondition cout stn_st))
            :: VerifCond cout
            ++ makeVcs fs'
    end.

  Hypothesis BlocksGood : vcs (makeVcs functions).

  Lemma BlocksGood' : List.Forall (fun f : function => let '(_, pre, c) := f in
    let cout := c fullImports fullImportsGlobal pre in
    (forall stn_st specs, ~interp specs (Postcondition cout stn_st))
    /\ vcs (VerifCond cout)) functions.
    generalize BlocksGood; clear.
    induction functions; simpl; intuition.
    destruct a as [ [ ] ].
    inversion BlocksGood; subst; intuition.
    constructor; intuition.
    eapply vcs_app_bwd1; eauto.
    apply IHl; eapply vcs_app_bwd2; eauto.
  Qed.

  Theorem buildLocals_notImport' : forall k v Base bls Base',
    LabelMap.MapsTo k v (buildLocals bls Base')
    -> Base' >= Base
    -> exists l, k = (modName, Local l) /\ l >= Base /\ l < Base' + N_of_nat (length bls).
    unfold buildLocals; intros.
    assert (LabelMap.MapsTo k v (LabelMap.empty (assert * block)) -> exists l, k = (modName, Local l) /\ l >= Base /\ l < Base' + N_of_nat (length bls))
      by (intro uhoh; destruct (LabelMap.empty_1 uhoh)).
    generalize dependent (LabelMap.empty (assert * block)).
    generalize dependent Base'; clear; induction bls; simpl; intuition.
    assert (Nsucc Base' >= Base) by nomega.
    destruct (IHbls _ H2 _ H); clear IHbls; intuition.
    apply LabelFacts.add_mapsto_iff in H3; intuition; subst; eauto.
    repeat esplit.
    auto.
    nomega.
    destruct H4; intuition.
    repeat esplit; eauto.
    nomega.
    repeat esplit; eauto.
    nomega.
  Qed.

  Theorem buildLocals_notImport : forall k v Base bls,
    LabelMap.MapsTo k v (buildLocals bls Base)
    -> exists l, k = (modName, Local l) /\ l >= Base /\ l < Base + N_of_nat (length bls).
    intros; eapply buildLocals_notImport'; eauto; nomega.
  Qed.

  Lemma getLocal : forall v bls Base Entry,
    nth_error bls (nat_of_N Entry) = Some v
    -> LabelMap.MapsTo (modName, Local (Base + Entry)) v (buildLocals bls Base).
    unfold buildLocals; intros.
    generalize (LabelMap.empty (assert * block)).
    generalize dependent Base.
    generalize dependent Entry.
    induction bls; simpl; intuition.
    elimtype False.
    destruct (nat_of_N Entry); discriminate.
    destruct (N_eq_dec Entry 0); subst; simpl in *.
    injection H; clear H; intros; subst.
    replace (Base + 0) with Base by nomega.
    assert (LabelMap.MapsTo (modName, Local Base) (a0, b) (LabelMap.add (modName, Local Base) (a0, b) t))
      by (apply LabelMap.add_1; auto).
    generalize H; clear.
    generalize (LabelMap.add (modName, Local Base) (a0, b) t).
    assert (Base < Nsucc Base) by nomega.
    generalize dependent (Nsucc Base).
    induction bls; simpl; intuition; eauto.
    apply IHbls.
    nomega.
    apply LabelMap.add_2; eauto.

    replace (Base + Entry) with (Nsucc Base + (Entry - 1)) by nomega.
    apply IHbls.
    autorewrite with N; simpl.
    assert (nat_of_N Entry <> O).
    nomega.
    destruct (nat_of_N Entry); simpl in *.
    tauto.
    replace (n0 - 0)%nat with n0 by omega; auto.
  Qed.

  Lemma ungetLocal' : forall A k v bls Base (m : LabelMap.t A),
    LabelMap.MapsTo k v (snd (List.fold_left (fun b_m p => let '(b, m) := b_m in
      (Nsucc b, LabelMap.add (modName, Local b) p m)) bls (Base, m)))
    -> LabelMap.MapsTo k v m
    \/ exists n, nth_error bls n = Some v /\ k = (modName, Local (Base + N_of_nat n)).
    clear; induction bls; simpl; intuition.
    apply IHbls in H; clear IHbls; intuition.
    apply LabelFacts.add_mapsto_iff in H0; intuition; subst.
    right; exists O; intuition.
    do 2 f_equal; nomega.
    destruct H0; intuition; subst.
    right; exists (S x); intuition.
    do 2 f_equal; nomega.
  Qed.

  Lemma ungetLocal : forall k v bls Base,
    LabelMap.MapsTo k v (buildLocals bls Base)
    -> exists n, nth_error bls n = Some v /\ k = (modName, Local (Base + N_of_nat n)).
    unfold buildLocals; intros.
    apply ungetLocal' in H; intuition.
    destruct (LabelMap.empty_1 H0).
  Qed.

  Hint Extern 1 (_ >= _) => nomega.

  Lemma MapsTo_blocks : forall k v fs Base,
    LabelMap.MapsTo k v (blocks fs Base)
    -> exists f, exists pre, exists c, In (f, pre, c) fs
      /\ exists Base', Base' >= Base /\
        let cout := c fullImports fullImportsGlobal pre in
        let cg := Generate (c fullImports fullImportsGlobal pre) (Nsucc Base') Base' in
          (forall n v', nth_error (Blocks cg) n = Some v'
            -> LabelMap.MapsTo (modName, Local (Nsucc Base' + N_of_nat n)) v' (blocks fs Base))
          /\ (exists bl, LabelMap.MapsTo (modName, Local Base') (Postcondition cout, bl) (blocks fs Base))
          /\ ((k = (modName, Global f)
            /\ v = (pre, (nil, Uncond (RvLabel (modName, Local (Nsucc Base' + Entry cg))))))
          \/ (k = (modName, Local Base') /\ v = (Postcondition cout, (nil, Uncond (RvLabel (modName, Local Base')))))
          \/ exists n, k = (modName, Local (Nsucc Base' + N_of_nat n)) /\ nth_error (Blocks cg) n = Some v).
    clear; induction fs as [ | [ [ ] ] ]; simpl; intuition.
    destruct (LabelMap.empty_1 H).
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.

    do 4 esplit.
    eauto.
    exists Base; intuition.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union1.
    apply getLocal; autorewrite with N; auto.
    eexists.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_1; auto.

    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.

    do 4 esplit.
    eauto.
    exists Base; intuition.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union1.
    apply getLocal; autorewrite with N; auto.
    eexists.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_1; auto.

    apply MapsTo_union in H2; intuition.

    apply ungetLocal in H0; destruct H0; intuition; subst.
    do 4 esplit.
    eauto.
    exists Base; intuition.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union1.
    apply getLocal; autorewrite with N; auto.
    eexists.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_1; auto.
    eauto 10.

    apply IHfs in H0; clear IHfs; intuition.
    destruct H0 as [? [? [? [ ] ] ] ].
    destruct H2; intuition; subst.

    do 4 esplit.
    right; eauto.
    exists x2; intuition.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union2; intuition.
    apply ungetLocal in H6; destruct H6; intuition.
    elimtype False; injection H8; intros.
    apply nth_error_bound in H7.
    nomega.
    destruct H4.
    eexists.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union2; eauto.
    intros.
    apply ungetLocal in H5; destruct H5; intuition.
    elimtype False; injection H7; intros.
    apply nth_error_bound in H6.
    nomega.

    do 4 esplit.
    right; eauto.
    exists x2; intuition.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union2; intuition.
    apply ungetLocal in H6; destruct H6; intuition.
    elimtype False; injection H8; intros.
    apply nth_error_bound in H7.
    nomega.
    destruct H4.
    eexists.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union2; eauto.
    intros.
    apply ungetLocal in H5; destruct H5; intuition.
    elimtype False; injection H7; intros.
    apply nth_error_bound in H6.
    nomega.


    destruct H6; intuition; subst.
    do 4 esplit.
    right; eauto.
    exists x2; intuition eauto.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union2; intuition.
    apply ungetLocal in H6; destruct H6; intuition.
    elimtype False; injection H9; intros.
    apply nth_error_bound in H8.
    nomega.
    destruct H4.
    eexists.
    apply LabelMap.add_2; [ congruence | ].
    apply LabelMap.add_2; [ intro Ho; injection Ho; nomega | ].
    apply MapsTo_union2; eauto.
    intros.
    apply ungetLocal in H5; destruct H5; intuition.
    apply nth_error_bound in H6.
    elimtype False; injection H8; intros.
    nomega.
  Qed.

  Lemma skipImports : forall m l p bls,
    LabelMap.MapsTo (modName, Local l) (p, bls) m
    -> LabelMap.MapsTo (modName, Local l) p
    (LabelMap.fold
      (fun (l : LabelMap.key) (x : assert * block) (m : LabelMap.t assert) =>
        LabelMap.add l (fst x) m) m importsMap).
    clear NoDupFunc BlocksGood.
    unfold importsMap.
    generalize NoSelfImport; clear NoSelfImport.
    generalize false at 2.
    intros; assert (forall v, ~LabelMap.MapsTo (modName, Local l) v (LabelMap.empty assert)).
    do 2 intro.
    apply LabelMap.empty_1 in H0; tauto.
    apply LabelMap.elements_1 in H.
    generalize (LabelMap.elements_3w m).
    generalize dependent (LabelMap.empty assert).
    induction imports; simpl in *; intuition.
    rewrite LabelMap.fold_1.
    generalize dependent t.
    induction (LabelMap.elements m); simpl; intuition.

    inversion H.
    inversion H1; clear H1; subst.
    inversion H; clear H; subst.
    hnf in H2; simpl in H2; intuition.
    destruct a; simpl in *; subst; simpl in *.
    generalize H4; clear.
    assert (LabelMap.MapsTo (modName, Local l) p (LabelMap.add (modName, Local l) p t)).
    apply LabelMap.add_1; auto.
    generalize dependent (LabelMap.add (modName, Local l) p t).
    induction l0; simpl; intuition; simpl.
    apply IHl0; auto.
    apply LabelMap.add_2.
    intro; subst.
    apply H4.
    constructor; hnf; auto.
    auto.

    intuition.
    apply H1; clear H1.
    intros.
    apply LabelFacts.add_mapsto_iff in H; intuition.
    destruct a as [ [ ] ]; simpl in *; subst; simpl in *.
    injection H; clear H; intros; subst.
    generalize H2 H4; clear.
    induction 1; simpl; intuition.
    apply H4.
    constructor.
    hnf in H; hnf; simpl in *; tauto.
    eauto.

    destruct a as [ [ ] ]; simpl in *.
    apply IHl0; auto.

    generalize NoSelfImport; clear.
    match goal with
      | [ |- context[?E || ?F] ] =>
        assert (E || F = false -> E = false) by (destruct b; auto);
          generalize dependent (E || F); generalize dependent E
    end.
    induction l0; simpl; intuition.
    destruct a as [ [ ] ]; simpl in *.
    eapply IHl0; [ | eassumption ].
    destruct b0; destruct b; simpl in *; intuition congruence.

    intros.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst.
    congruence.
    eauto.
  Qed.

  Lemma imps_cases : forall k v ims exit post bls base,
    LabelMap.MapsTo k v (imps ims modName bls base exit post)
    -> (k = (modName, Local exit) /\ v = post)
    \/ LabelMap.MapsTo k v ims
    \/ exists n, exists bl, nth_error bls n = Some (v, bl) /\ k = (modName, Local (base + N_of_nat n)).
    induction bls; simpl; intuition.

    apply LabelFacts.add_mapsto_iff in H; intuition.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.

    do 2 right; exists O; exists b; intuition.
    do 2 f_equal; nomega.

    apply IHbls in H1; intuition.
    destruct H1 as [ ? [ ] ]; intuition.
    do 2 right; exists (S x); exists x0; intuition.
    rewrite H2; do 2 f_equal; nomega.
  Qed.

  Lemma MapsTo_fullImports : forall k v,
    LabelMap.MapsTo k v fullImports
    -> LabelMap.MapsTo k v importsMap
    \/ (exists f, k = (modName, Global f) /\ exists c, In (f, v, c) functions).
    clear; unfold fullImports; do 2 intro; generalize importsMap.
    induction functions as [ | [ [ ] ] ]; simpl; intuition.
    apply IHl in H; clear IHl; intuition.
    apply LabelFacts.add_mapsto_iff in H0; intuition; subst.
    eauto 10.
    destruct H0; intuition; subst.
    destruct H1; eauto 10.
  Qed.

  Lemma importsMap_global' : forall l pre imps (acc : LabelMap.t assert),
    (forall l' pre', LabelMap.MapsTo l' pre' acc
      -> exists g, snd l' = Global g)
    -> LabelMap.MapsTo l pre (fold_left (fun m p => let '(modl, f, pre) := p in
      LabelMap.add (modl, Global f) pre m) imps acc)
    -> exists g, snd l = Global g.
    clear; induction imps; simpl; intuition eauto.
    eapply IHimps; [ | eauto ].
    intros.
    destruct (LabelKey.eq_dec l' (a, Global b0)).
    hnf in e; subst; simpl; eauto.
    eapply LabelMap.add_3 in H1.
    eauto.
    auto.
  Qed.

  Lemma importsMap_global : forall l pre,
    LabelMap.MapsTo l pre importsMap -> exists g, snd l = Global g.
    intros; apply importsMap_global' with pre imports (LabelMap.empty _).
    intros.
    apply LabelMap.empty_1 in H0; tauto.
    assumption.
  Qed.

  Lemma MapsTo_func : forall A (m : LabelMap.t A) k v v',
    LabelMap.MapsTo k v m
    -> LabelMap.MapsTo k v' m
    -> v = v'.
    intros.
    apply LabelMap.find_1 in H.
    apply LabelMap.find_1 in H0.
    congruence.
  Qed.

  Lemma blocks_exps : forall (mn g : string) (pre : assert) (bl : block)
    funcs start,
    LabelMap.MapsTo (mn, Global g) (pre, bl) (blocks funcs start) ->
    LabelMap.MapsTo (mn, Global g) pre (exps funcs).
    clear; induction funcs; simpl; intuition.
    apply LabelMap.empty_1 in H; tauto.
    destruct a as [ [ ] ].
    destruct (LabelKey.eq_dec (modName, Global s) (mn, Global g)).
    generalize e; intro e'.
    eapply LabelMap.add_1 in e'.


    hnf in e.
    rewrite <- e in *.
    eapply MapsTo_func in e'.
    2: apply H.
    injection e'; clear e'; intros; subst.
    eauto.

    apply LabelMap.add_3 in H; [ | assumption ].
    apply LabelMap.add_3 in H; [ | lomega ].
    apply MapsTo_union in H; intuition.
    apply buildLocals_notImport in H0; destruct H0; intuition congruence.

    eauto.
  Qed.

  Lemma exps_blocks : forall (mn g : string) (pre : assert)
    funcs start,
    LabelMap.MapsTo (mn, Global g) pre (exps funcs)
    -> exists bl, LabelMap.MapsTo (mn, Global g) (pre, bl) (blocks funcs start).
    induction funcs; simpl; intuition.
    apply LabelMap.empty_1 in H; tauto.
    destruct a as [ [ ] ].
    destruct (LabelKey.eq_dec (modName, Global s) (mn, Global g)).
    generalize e; intro e'.
    eapply LabelMap.add_1 in e'.
    hnf in e.
    rewrite <- e in *.
    eapply MapsTo_func in e'.
    2: apply H.
    subst.
    eauto.

    apply LabelMap.add_3 in H; [ | assumption ].
    eapply IHfuncs in H; destruct H.
    exists x.
    apply LabelMap.add_2; auto.
    apply LabelMap.add_2; auto.
    apply MapsTo_union2.
    eauto.
    intros.
    apply buildLocals_notImport in H0; destruct H0; intuition congruence.
  Qed.

  Lemma blocks_modName : forall mn l pre_bl funcs start,
    LabelMap.MapsTo (mn, l) pre_bl (blocks funcs start)
    -> modName = mn.
    clear; induction funcs; simpl; intuition.
    apply LabelMap.empty_1 in H; tauto.
    destruct a as [ [ ] ].
    destruct (LabelKey.eq_dec (modName, Global s) (mn, l)).
    congruence.
    apply LabelMap.add_3 in H; [ | assumption ].
    destruct (LabelKey.eq_dec (modName, Local start) (mn, l)).
    congruence.
    apply LabelMap.add_3 in H; [ | assumption ].
    apply MapsTo_union in H; intuition.
    apply buildLocals_notImport in H0; destruct H0; intuition congruence.
    eauto.
  Qed.

  Theorem bmoduleOk : moduleOk bmodule_.
    constructor.

    clear NoDupFunc BlocksGood.
    red; simpl.
    apply Forall_MapsTo.
    intros.
    simpl.
    generalize dependent 1.
    induction functions; simpl; intuition.
    apply LabelMap.empty_1 in H; tauto.
    destruct a as [ [ ] ]; simpl in *.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst; eauto.
    apply LabelFacts.add_mapsto_iff in H2; intuition; subst; eauto.
    apply MapsTo_union in H3; intuition.

    destruct (buildLocals_notImport _ _ H1); intuition; subst; eauto.
    eauto.


    red; simpl; unfold allPreconditions; simpl; intros.

    generalize (MapsTo_blocks _ _ H); intros.
    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H; intuition; subst
           end.

    injection H8; clear H8; intros; subst; simpl.
    destruct (PreconditionOk (Generate (x1 fullImports fullImportsGlobal x0) (Nsucc x2) x2)).
    apply H2 in H6.
    autorewrite with N in H6.

    match type of H6 with
      | LabelMap.MapsTo ?k (?v, _) _ => destruct (H0 k v)
    end.
    eapply skipImports; eauto.
    intuition.
    rewrite H8.
    eauto.


    injection H8; clear H8; intros; subst; simpl.
    match type of H5 with
      | LabelMap.MapsTo ?k (?v, _) _ => destruct (H0 k v)
    end.
    eapply skipImports; eauto.
    intuition.
    rewrite H7.
    eauto.


    generalize (BlocksOk (Generate (x1 fullImports fullImportsGlobal x0) (Nsucc x2) x2)); intuition.
    match type of H6 with
      | ?P -> _ => assert P
    end.
    generalize BlocksGood' H3; clear.
    induction functions; simpl; intuition; subst.
    inversion H; clear H; subst.
    tauto.
    inversion H; clear H; subst.
    auto.

    intuition.
    match type of H9 with
      | ?P -> _ => assert P by nomega
    end; intuition.
    apply (Forall_nth_error H10) in H8; simpl in *.
    apply H8; intuition.
    apply H0.

    apply imps_cases in H9; intuition; subst.

    eapply skipImports; eauto.

    apply MapsTo_fullImports in H9; intuition.
    assert (~LabelMap.In l (blocks functions 1)).
    pose proof importsNotThis' as importsNotThis'.
    generalize NoSelfImport H11; clear -importsNotThis'.
    generalize false at 2.
    generalize 1.
    induction functions as [ | [ [ ] ] ]; simpl; intuition.
    destruct H.
    destruct (LabelMap.empty_1 H).
    destruct H.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    eapply importsNotThis'; eauto.
    apply LabelFacts.add_mapsto_iff in H1; intuition; subst.
    eapply importsNotThis'; eauto.
    apply MapsTo_union in H2; intuition.
    apply ungetLocal in H0; destruct H0; intuition; subst.
    eapply importsNotThis'; eauto.
    eapply IHl0 in NoSelfImport; eauto.
    eexists; eauto.

    assert (forall v, ~SetoidList.InA (@LabelMap.eq_key_elt _) (l, v) (LabelMap.elements (blocks functions 1))).
    generalize H9; clear.
    intros; intro.
    apply H9.
    eexists.
    apply LabelMap.elements_2; eauto.

    generalize H11 H12; clear.
    rewrite LabelMap.fold_1.
    generalize importsMap.
    induction (LabelMap.elements (blocks functions 1)) as [ | [ [ ] ] ]; simpl; intuition; simpl.
    apply IHl0.
    apply LabelMap.add_2; auto.
    intro; subst.
    eapply H12.
    constructor; hnf; eauto.
    eauto.


    destruct H11; intuition; subst.
    destruct H12.

    assert (SetoidList.NoDupA (fun p1 p2 => fst (fst p1) = fst (fst p2)) functions).
    generalize NoDupFunc; clear.
    generalize dependent (LabelMap.empty unit).
    induction functions as [ | [ [ ] ] ]; simpl; intuition.
    case_eq (LabelMap.mem (s, Local 0) t); intro Heq; rewrite Heq in *.
    elimtype False.
    generalize NoDupFunc; clear.
    induction l as [ | [ [ ] ] ]; simpl; intuition.
    specialize (IHl _ NoDupFunc).
    constructor; auto.
    generalize NoDupFunc; clear.
    assert (LabelMap.MapsTo (s, Local 0) tt (LabelMap.add (s, Local 0) tt t)) by (apply LabelMap.add_1; auto).
    generalize dependent (LabelMap.add (s, Local 0) tt t).
    induction l as [ | [ [ ] ] ]; simpl; intuition.
    inversion H0.
    inversion H0; clear H0; simpl in *; subst.
    assert (LabelMap.In (s0, Local 0) t0) by (hnf; eauto).
    apply LabelMap.mem_1 in H0.
    rewrite H0 in NoDupFunc.
    elimtype False.
    generalize NoDupFunc; clear.
    induction l as [ | [ [ ] ] ]; simpl; intuition.
    case_eq (LabelMap.mem (s0, Local 0) t0); intro Heq; rewrite Heq in *.
    elimtype False.
    generalize NoDupFunc; clear.
    induction l as [ | [ [ ] ] ]; simpl; intuition.
    specialize (fun H => IHl _ H NoDupFunc).
    apply IHl; auto.

    assert (exists bl, LabelMap.MapsTo (modName, Global x5) (pre0, bl) (blocks functions 1)).
    generalize H11 H9; clear.
    generalize 1.
    induction functions; simpl; intuition; subst.
    eexists; apply LabelMap.add_1; eauto.
    destruct a as [ [ ] ].
    inversion H11; clear H11; subst.
    match goal with
      | [ |- context[blocks _ ?n] ] => destruct (IHl n H3)
    end; auto.
    eexists.
    apply LabelMap.add_2.
    intro Ho; injection Ho; clear Ho; intros; subst.
    apply H2.
    generalize H; clear.
    induction l; simpl; intuition; subst; auto.
    apply LabelMap.add_2; [ congruence | ].
    apply MapsTo_union2; eauto.
    intros.
    destruct (ungetLocal _ _ H1); intuition congruence.

    rewrite LabelMap.fold_1.
    destruct H12.
    assert (SetoidList.InA (@LabelMap.eq_key_elt _) ((modName, Global x5), (pre0, x7)) (LabelMap.elements (blocks functions 1))).
    apply LabelMap.elements_1; auto.
    generalize H13; clear.
    generalize (LabelMap.elements_3w (blocks functions 1)).
    generalize importsMap.
    induction (LabelMap.elements (blocks functions 1)); simpl; intuition.
    inversion H13.
    inversion H; clear H; subst.
    inversion H13; clear H13; subst; simpl.
    hnf in H0; simpl in H0; intuition; subst.
    injection H1; clear H1; intros; subst.
    assert (LabelMap.MapsTo (modName, Global x5) a (LabelMap.add (modName, Global x5) a t)) by (apply LabelMap.add_1; auto).
    generalize H2 H; clear.
    generalize (LabelMap.add (modName, Global x5) a t).
    induction l; simpl; intuition; simpl.
    apply IHl; auto.
    apply LabelMap.add_2; auto.
    intro; subst.
    apply H2; constructor; hnf; auto.
    auto.

    destruct H9 as [ ? [ ] ]; intuition; subst.
    eapply skipImports; eauto.


    simpl.

    intros; eapply importsMap_global; eauto.


    simpl.

    intros; eapply blocks_exps; eauto.


    simpl.

    intros; eapply exps_blocks; eauto.


    simpl.
    intros.
    apply StringSet.singleton_2.

    eapply blocks_modName; eauto.
  Qed.

End module.
