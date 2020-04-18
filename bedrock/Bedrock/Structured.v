(* Structured programming (basic command constructs) *)

Require Import Coq.NArith.NArith Coq.Strings.String Coq.Lists.List.

Require Import Bedrock.Nomega Bedrock.PropX Bedrock.PropXTac Bedrock.Word Bedrock.LabelMap Bedrock.IL Bedrock.XCAP.

Set Implicit Arguments.

Local Open Scope N_scope.


Lemma nth_error_bound : forall A x (ls : list A) n,
  nth_error ls n = Some x
  -> (n < length ls)%nat.
  induction ls; destruct n; simpl; intuition; discriminate.
Qed.

Lemma nth_error_bound' : forall A x (ls : list A) n,
  nth_error ls (nat_of_N n) = Some x
  -> n < N_of_nat (length ls).
  intros; apply nth_error_bound in H; nomega.
Qed.

Section imports.
  (* Which external code labels must be available? *)
  Variable imports : LabelMap.t assert.

  Definition importsGlobal := forall k v, LabelMap.MapsTo k v imports
    -> exists s, snd k = Global s.

  Hypothesis imports_global : importsGlobal.

  (* Which code module are we defining here? *)
  Variable modName : string.

  (* Full set of code labels that may be mentioned in generated code *)
  Fixpoint imps (bls : list (assert * block)) (base exit : N) (post : assert) : LabelMap.t assert :=
    match bls with
      | nil => LabelMap.add (modName, Local exit) post imports
      | (pre, _) :: bls' => LabelMap.add (modName, Local base) pre (imps bls' (Nsucc base) exit post)
    end.

  (** The data type of structured program pieces *)

  Inductive vcs : list Prop -> Prop :=
  | VcsNil : vcs nil
  | VcsCons : forall (P : Prop) Ps, P -> vcs Ps -> vcs (P :: Ps).

  Implicit Arguments VcsCons [P Ps].

  Hint Constructors vcs.

  Theorem vcs_app_fwd : forall Ps1 Ps2,
    vcs Ps1
    -> vcs Ps2
    -> vcs (Ps1 ++ Ps2).
    induction 1; simpl; auto.
  Qed.

  Theorem vcs_app_bwd1 : forall Ps1 Ps2,
    vcs (Ps1 ++ Ps2)
    -> vcs Ps1.
    induction Ps1; inversion 1; subst; eauto.
  Qed.

  Theorem vcs_app_bwd2 : forall Ps1 Ps2,
    vcs (Ps1 ++ Ps2)
    -> vcs Ps2.
    induction Ps1; inversion 1; subst; eauto.
  Qed.

  Record codeGen (Precondition : assert) (Base Exit : N) (Postcondition : assert) (VerifCond : list Prop) := {
    Entry : N;                      (* Jump here to start *)
    Blocks : list (assert * block); (* Code blocks *)

    PreconditionOk : exists bl, nth_error Blocks (nat_of_N Entry) = Some (Precondition, bl);

    BlocksOk : vcs VerifCond
      -> Exit < Base
      -> List.Forall (fun p => blockOk (imps Blocks Base Exit Postcondition) (fst p) (snd p)) Blocks
  }.

  Record codeOut (Precondition : assert) := {
    Postcondition : assert;     (* Guarantee this on exit. *)
    VerifCond : list Prop;      (* User must prove all of these conditions. *)
    Generate : forall Base Exit : N, (* Start generating code labels at this address *)
      codeGen Precondition Base Exit Postcondition VerifCond
  }.

  Definition cmd := forall cin, codeOut cin.


  (** Sequencing *)

  Definition notStuck (pre : assert) (is : list instr) :=
    forall stn st specs, interp specs (pre (stn, st))
      -> evalInstrs stn st is <> None.

  Ltac lomega := (let H := fresh in intro H; discriminate
    || injection H; clear H; intro; try subst; simpl in *; congruence || nomega)
  || (repeat match goal with
                 | [ |- eq (A := ?A) _ _ ] =>
                   match A with
                     | N => fail 1
                     | _ => f_equal
                   end
               end; nomega).

  Hint Extern 1 (_ < _) => nomega.
  Hint Extern 1 (~(eq (A := N) _ _)) => nomega.

  Lemma ge_refl : forall n, n >= n.
    intros; nomega.
  Qed.

  Hint Resolve ge_refl.

  Hint Extern 1 (eq (A := label) _ _) => lomega.
  Hint Extern 1 (~(eq (A := label) _ _)) => lomega.
  Hint Extern 1 (eq (A := LabelKey.t) _ _) => lomega.
  Hint Extern 1 (~(eq (A := LabelKey.t) _ _)) => lomega.

  Hint Resolve LabelMap.add_1 LabelMap.add_2.

  Lemma lookup_imps : forall p bl exit post bls n base,
    nth_error bls (nat_of_N n) = Some (p, bl)
    -> LabelMap.MapsTo (modName, Local (base + n)) p
    (imps bls base exit post).
    induction bls; simpl in *; intuition.

    destruct (nat_of_N n); discriminate.

    induction n using Nind; simpl in *.

    injection H; clear H; intros; subst.
    autorewrite with N.
    auto.

    autorewrite with N in *; simpl in *.
    replace (base + Nsucc n) with (Nsucc base + n) by nomega.
    auto.
  Qed.

  Hint Resolve lookup_imps.

  Hint Immediate simplify_fwd.

  Hint Extern 2 (blockOk _ _ _) => simpl in *; eapply blockOk_impl; [ | eassumption ].

  Lemma imps_exit : forall exit post bls base,
    exit < base
    -> LabelMap.MapsTo (modName, Local exit) post (imps bls base exit post).
    induction bls; simpl; intuition.
  Qed.

  Hint Resolve imps_exit.

  Lemma specialize_imps : forall {exit post} {P : _ -> _ -> Prop} {bls base},
    (forall k v, LabelMap.MapsTo k v (imps bls base exit post) -> P k v)
    -> (exit < base -> P (modName, Local exit) post)
    /\ (forall base', base = Nsucc base'
      -> forall n p bl, nth_error bls (nat_of_N n) = Some (p, bl)
        -> P (modName, Local (base + n)) p).
    intuition.

    apply H.
    rewrite H0.
    eapply lookup_imps; eauto.
  Qed.

  Lemma lt_succ : forall n, n < Nsucc n.
    intros; nomega.
  Qed.

  Lemma lt_succ' : forall n m, n < m -> n < Nsucc m.
    intros; nomega.
  Qed.

  Hint Immediate lt_succ lt_succ'.

  Hint Extern 1 (List.Forall _ _) => eapply Forall_impl; [ | eassumption ]; cbv zeta.

  Theorem split_add : forall A k (v : A) m {P : _ -> _ -> Prop},
    (forall k' v', LabelMap.MapsTo k' v' (LabelMap.add k v m) -> P k' v')
    -> P k v
    /\ (forall k' v', LabelMap.MapsTo k' v' m -> k' <> k -> P k' v').
    intuition.
  Qed.

  Hint Extern 1 (interp _ _) => cbv zeta; simpl;
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end; apply simplify_bwd; simpl.

  Hint Extern 1 (_ = _) => congruence.

  Hint Rewrite nat_of_N_of_nat Nplus_assoc : N.

  Lemma nth_error_app2 : forall n A (ls2 ls1 : list A),
    nth_error (ls1 ++ ls2) (length ls1 + n) = nth_error ls2 n.
    induction ls1; simpl; intuition.
  Qed.

  Hint Rewrite nth_error_app2 : N.

  Lemma nth_error_app2' : forall n A (ls2 ls1 : list A) x,
    nth_error ls2 n = x
    -> nth_error (ls1 ++ ls2) (nat_of_N (N_of_nat (length ls1) + N_of_nat n)) = x.
    intros; subst; autorewrite with N; reflexivity.
  Qed.

  Lemma Forall_app : forall A (P : A -> Prop) ls1 ls2,
    List.Forall P ls1
    -> List.Forall P ls2
    -> List.Forall P (ls1 ++ ls2).
    induction 1; simpl; intuition.
  Qed.

  Hint Resolve Forall_app.

  Hint Extern 1 (LabelMap.MapsTo ?k _ _) =>
    match goal with
      | [ H : snd k = _ |- _ ] => destruct k; simpl in *; subst
    end.

  Lemma imps_imports : forall exit post k v bls base,
    LabelMap.MapsTo k v imports
    -> LabelMap.MapsTo k v (imps bls base exit post).
    induction bls; simpl; intuition.
    destruct (imports_global H).
    auto.
    destruct (imports_global H).
    destruct k; simpl in *; subst.
    auto.
  Qed.

  Hint Resolve imps_imports.

  Lemma imps_app1 : forall exit post bls2 k v bls1 base,
    exit < base
    -> LabelMap.MapsTo k v (imps bls1 base exit post)
    -> LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit post).
    induction bls1; simpl; intuition.

    apply LabelFacts.add_mapsto_iff in H0; intuition; subst; auto.

    apply LabelFacts.add_mapsto_iff in H0; intuition; subst; auto.
  Qed.

  Lemma imps_app2'' : forall k v exit exit' post post' bls base,
    LabelMap.MapsTo k v (imps bls base exit' post')
    -> (k = (modName, Local exit') /\ v = post') \/ LabelMap.MapsTo k v (imps bls base exit post).
    induction bls; simpl; intuition.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    right.
    apply LabelMap.add_2.
    apply imports_global in H1.
    destruct H1.
    destruct k; simpl in *; congruence.
    auto.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    eauto.
    apply IHbls in H1.
    intuition.
  Qed.

  Lemma imps_neq : forall k v exit post l bls base,
    LabelMap.MapsTo k v (imps bls base exit post)
    -> l < base
    -> l <> exit
    -> (modName, Local l) <> k.
    induction bls; simpl; intuition.

    apply LabelFacts.add_mapsto_iff in H; intuition; subst.
    destruct (imports_global H4).
    discriminate.

    subst.
    apply LabelFacts.add_mapsto_iff in H; intuition; subst.

    injection H; intros; nomega.
    eauto.
  Qed.

  Hint Extern 2 (_ <> _) => eapply imps_neq; [ eassumption | nomega | nomega ].

  Lemma imps_app2' : forall exit post bls2 k v exit' post' bls1 base,
    LabelMap.MapsTo k v (imps bls2 (base + N_of_nat (length bls1)) exit' post')
    -> exit < base
    -> (k = (modName, Local exit') /\ v = post') \/ LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit post).
    induction bls1; simpl; intuition.

    replace (base + 0) with base in H by nomega.
    apply imps_app2''; auto.

    replace (base + Npos (P_of_succ_nat (length bls1)))
      with (Nsucc base + N_of_nat (length bls1)) in H by nomega.

    apply IHbls1 in H; clear IHbls1; intuition eauto.
  Qed.

  Lemma nth_error_app1 : forall A x (ls2 ls1 : list A) n,
    nth_error ls1 n = Some x
    -> nth_error (ls1 ++ ls2) n = Some x.
    induction ls1; destruct n; simpl; intuition; discriminate.
  Qed.

  Hint Resolve nth_error_app1.

  Lemma imps_app2 : forall exit post bls2 k v post' bl bls1 base offset,
    LabelMap.MapsTo k v (imps bls2 (base + N_of_nat (length bls1)) (base + offset) post')
    -> nth_error bls1 (nat_of_N offset) = Some (post', bl)
    -> exit < base
    -> LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit post).
    intros.
    eapply imps_app2' in H.
    intuition; subst; eauto.
    auto.
  Qed.

  Hint Resolve imps_app1 imps_app2.

  Hint Rewrite app_length : N.

  Lemma nth_app_hyp : forall {A B} {P : N -> A -> B -> Prop} {ls1 ls2},
    (forall n (x : A) (y : B),
      nth_error (ls1 ++ ls2) (nat_of_N n) = Some (x, y) -> P n x y)
    -> (forall n (x : A) (y : B),
      nth_error ls1 (nat_of_N n) = Some (x, y) -> P n x y)
    /\ (forall n (x : A) (y : B),
      nth_error ls2 (nat_of_N n) = Some (x, y) -> P (N_of_nat (length ls1) + n) x y).
    intuition.
    eapply nth_error_app2' in H0.
    apply H in H0.
    autorewrite with N in *; assumption.
  Qed.

  Hint Resolve nth_error_bound'.

  Ltac preSimp := simpl in *; intuition eauto; repeat (apply Forall_nil || apply Forall_cons); simpl; unfold importsGlobal in *.

  Ltac destrOpt E := let Heq := fresh "Heq" in case_eq E; (intros ? Heq || intro Heq); rewrite Heq in *.

  Definition evalCond (rv1 : rvalue) (t : test) (rv2 : rvalue) (stn : settings) (st : state) :=
    match evalRvalue stn st rv1, evalRvalue stn st rv2 with
      | Some w1, Some w2 => Some (evalTest t w1 w2)
      | _, _ => None
    end.

  Implicit Arguments vcs_app_bwd1 [Ps1 Ps2].
  Implicit Arguments vcs_app_bwd2 [Ps1 Ps2].

  Ltac simp := repeat (match goal with
                         | [ x : codeGen _ _ _ _ _ |- _ ] => destruct x; simpl in *
                         | [ H : _ /\ _ |- _ ] => destruct H
                         | [ H : ex _ |- _ ] => destruct H

                         | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
                         | [ H : vcs (_ ++ _) |- _ ] => generalize (vcs_app_bwd1 H);
                           generalize (vcs_app_bwd2 H); clear H; intros

                         | [ |- vcs nil ] => constructor
                         | [ |- vcs (_ :: _) ] => constructor
                         | [ |- vcs (_ ++ _) ] => apply vcs_app_fwd

                         | [ H1 : notStuck _ _, H2 : _ |- _ ] => specialize (H1 _ _ _ H2)
                         | [ H : LabelMap.find _ _ = Some _ |- _ ] => apply LabelMap.find_2 in H
                         | [ H : forall k v, _ |- _ ] => destruct (split_add H); clear H
                         | [ H : forall n x y, _ |- _ ] => destruct (nth_app_hyp H); clear H
                         | [ H : _ |- _ ] => destruct (specialize_imps H); clear H
                         | [ H : forall x, _ -> _ |- _ ] => specialize (H _ (refl_equal _))
                         | [ H : forall x y z, _ -> _ , H' : _ |- _ ] => specialize (H _ _ _ H')
                         | [ H : forall x y, _ -> _ , H' : LabelMap.MapsTo _ _ _ |- _ ] => destruct (H _ _ H'); clear H; auto
                         | [ |- blockOk _ _ _ ] => red
                         | [ _ : match ?E with Some _ => _ | None => _ end = Some _ |- _ ] => destrOpt E; [ | discriminate ]
                         | [ _ : match ?E with Some _ => _ | None => _ end = None -> False |- _ ] => destrOpt E; [ | tauto ]
                         | [ _ : match ?E with Some _ => _ | None => _ end |- _ ] => destrOpt E; [ | tauto ]
                         | [ |- context[if ?E then _ else _] ] => destrOpt E
                         | [ H : ?E = None -> False |- _ ] =>
                           match E with
                             | Some _ => clear H
                             | _ => case_eq E; intros; tauto || clear H
                           end
                         | [ H : _ |- _ ] => rewrite H
                         | [ H : ?P -> _ |- _ ] =>
                           match type of P with
                             | Prop => let H' := fresh in assert (H' : P) by (lomega || auto); specialize (H H'); clear H'
                           end
                         | [ x : N |- _ ] => unfold x in *; clear x
                         | [ H : nth_error ?ls (nat_of_N ?n) = _ |- _ ] =>
                           match goal with
                             | [ _ : n < N_of_nat (length ls) |- _ ] => fail 1
                             | _ => specialize (nth_error_bound' _ _ H)
                           end
                         | [ H : snd ?x = _ |- _ ] => destruct x; simpl in H; congruence
                         | [ H : forall rp, _ rp = Some _ -> _, H' : _ _ = Some _ |- _ ] => specialize (H _ H')
                       end; intros; unfold evalBlock, evalCond in *; simpl; autorewrite with N in *).

  Ltac struct := preSimp; simp; eauto 15.


  (** * Lemmas: [MapsTo] and [imps] *)

  Lemma MapsTo_or : forall A k (v : A) k' v' m,
    (k = k' -> v = v')
    -> (k <> k' -> LabelMap.MapsTo k v m)
    -> LabelMap.MapsTo k v (LabelMap.add k' v' m).
    intros; destruct (LabelKey.eq_dec k k'); unfold LabelKey.eq in *; intuition; subst; eauto.
  Qed.

  Ltac use_add := match goal with
                    | [ H : LabelMap.MapsTo _ _ (LabelMap.add _ _ _) |- _ ] =>
                      apply LabelFacts.add_mapsto_iff in H; intuition; subst
                  end; try match goal with
                             | [ H : _ |- _ ] => destruct (imports_global H)
                           end; simpl in *; intuition eauto.

  Lemma imps_contra : forall k v exit post bls base,
    LabelMap.MapsTo (modName, Local k) v (imps bls base exit post)
    -> k < base
    -> k <> exit
    -> False.
    induction bls; simpl; intuition; use_add;
      match goal with
        | [ H : _ |- _ ] => injection H; intros; subst; nomega
      end.
  Qed.

  Lemma imps_exit' : forall exit post post' bls base,
    LabelMap.MapsTo (modName, Local exit) post' (imps bls base exit post)
    -> exit < base
    -> post' = post.
    intros.
    eapply imps_exit in H0.
    eauto using LabelFacts.MapsTo_fun.
  Qed.

  Lemma imps_app_1 : forall k v exit post bls2 exit' post' bls1 base,
    LabelMap.MapsTo k v (imps bls1 base exit post)
    -> k <> (modName, Local exit)
    -> exit' < base + N_of_nat (length bls1)
    -> LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit' post').
    induction bls1; simpl; intuition; use_add.
  Qed.

  Lemma imps_app_2 : forall k v exit post bls2 exit' post' bls1 base,
    LabelMap.MapsTo k v (imps bls2 (base + N_of_nat (length bls1)) exit post)
    -> k <> (modName, Local exit)
    -> exit' < base
    -> LabelMap.MapsTo k v (imps (bls1 ++ bls2) base exit' post').
    induction bls1; simpl; intuition.

    replace (base + 0) with base in * by nomega.
    generalize dependent base; induction bls2; simpl; intuition; use_add.

    replace (base + N.pos (Pos.of_succ_nat (Datatypes.length bls1)))
      with (N.succ base + N_of_nat (Datatypes.length bls1)) in H by nomega.
    apply IHbls1 in H; clear IHbls1; auto.
  Qed.

  Lemma imps_not_exit : forall k v exit post exit' post' bls base,
    LabelMap.MapsTo k v (imps bls base exit post)
    -> exit < base
    -> k <> (modName, Local exit)
    -> LabelMap.MapsTo k v (imps bls base exit' post').
    induction bls; simpl; intuition; use_add.
  Qed.

  Hint Extern 2 (LabelMap.MapsTo _ _ _) => apply MapsTo_or; intro; subst.
  Hint Extern 1 (@eq assert _ _) => elimtype False; eapply imps_contra; [ eassumption | nomega | nomega ].
  Hint Extern 1 (@eq assert _ _) => eapply imps_exit'; [ eassumption | nomega ].
  Hint Resolve imps_app_1 imps_app_2 imps_not_exit.


  (** *  Literal sequences of non-jump instructions *)

  Definition Straightline_ (is : list instr) : cmd.
    red; refine (fun pre => {|
      Postcondition := (fun stn_st => Ex st', pre (fst stn_st, st') /\ [|evalInstrs (fst stn_st) st' is = Some (snd stn_st)|])%PropX;
      VerifCond := (forall stn st specs, interp specs (pre (stn, st)) -> evalInstrs stn st is <> None) :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (is, Uncond (RvLabel (modName, Local Exit)))) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** *  Sequential composition *)

  Definition Seq_ (c1 c2 : cmd) : cmd.
    red; refine (fun pre =>
      let cout1 := c1 pre in
      let cout2 := c2 (Postcondition cout1) in
        {|
          Postcondition := Postcondition cout2;
          VerifCond := VerifCond cout1 ++ VerifCond cout2;
          Generate := fun Base Exit =>
            let cg2 := Generate cout2 Base Exit in
              let numBlocks := N_of_nat (length (Blocks cg2)) in
                let cg1 := Generate cout1 (Base + numBlocks) (Base + Entry cg2) in
                  {|
                    Entry := numBlocks + Entry cg1;
                    Blocks := Blocks cg2 ++ Blocks cg1
                  |}
        |}); abstract struct.
  Defined.

  (** * Cop-out infinite loops *)

  Definition Diverge_ : cmd.
    red; refine (fun pre => {|
      Postcondition := (fun _ => [|False|])%PropX;
      VerifCond := nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel (modName, Local Base)))) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** * Points we want to prove are unreachable *)

  Definition Fail_ : cmd.
    red; refine (fun pre => {|
      Postcondition := (fun _ => [|False|])%PropX;
      VerifCond := (forall x specs, ~interp specs (pre x)) :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel (modName, Local Exit)))) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** * No-op *)

  Definition Skip_ : cmd.
    red; refine (fun pre => {|
      Postcondition := pre;
      VerifCond := nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel (modName, Local Exit)))) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** * Assertions *)

  Definition Assert_ (post : assert) : cmd.
    red; refine (fun pre => {|
      Postcondition := post;
      VerifCond := (forall stn_st specs, interp specs (pre stn_st) -> interp specs (post stn_st)) :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel (modName, Local Exit)))) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** * Standard conditional *)

  Definition If_ (rv1 : rvalue) (t : test) (rv2 : rvalue) (Then Else : cmd) : cmd.
    red; refine (fun pre =>
      let cout1 := Then (fun stn_st => pre stn_st /\ [|evalCond rv1 t rv2 (fst stn_st) (snd stn_st) = Some true|])%PropX in
      let cout2 := Else (fun stn_st => pre stn_st /\ [|evalCond rv1 t rv2 (fst stn_st) (snd stn_st) = Some false|])%PropX in
      {|
        Postcondition := (fun stn_st => Postcondition cout1 stn_st \/ Postcondition cout2 stn_st)%PropX;
        VerifCond := (forall stn st specs, interp specs (pre (stn, st)) -> evalCond rv1 t rv2 stn st <> None)
          :: VerifCond cout1 ++ VerifCond cout2;
        Generate := fun Base Exit =>
          let Base' := Nsucc (Nsucc (Nsucc Base)) in
          let cg1 := Generate cout1 Base' (Nsucc Base) in
          let Base'' := Base' + N_of_nat (length (Blocks cg1)) in
          let cg2 := Generate cout2 Base'' (Nsucc (Nsucc Base)) in
          {|
            Entry := 0;
            Blocks := (pre, (nil, Cond rv1 t rv2
              (modName, Local (Base' + Entry cg1))
              (modName, Local (Base'' + Entry cg2))))
              :: (Postcondition cout1, (nil, Uncond (RvLabel (modName, Local Exit))))
              :: (Postcondition cout2, (nil, Uncond (RvLabel (modName, Local Exit))))
              :: Blocks cg1 ++ Blocks cg2
          |}
      |}); abstract struct.
  Defined.

  (** * Standard loop *)

  Definition While_ (inv : assert) (rv1 : rvalue) (t : test) (rv2 : rvalue) (Body : cmd) : cmd.
    red; refine (fun pre =>
      let cout := Body (fun stn_st => inv stn_st /\ [|evalCond rv1 t rv2 (fst stn_st) (snd stn_st) = Some true|])%PropX in
      {|
        Postcondition := (fun stn_st => inv stn_st /\ [|evalCond rv1 t rv2 (fst stn_st) (snd stn_st) = Some false|])%PropX;
        VerifCond := (forall stn_st specs, interp specs (pre stn_st) -> interp specs (inv stn_st))
          :: (forall stn st specs, interp specs (inv (stn, st)) -> evalCond rv1 t rv2 stn st <> None)
          :: (forall stn_st specs, interp specs (Postcondition cout stn_st) -> interp specs (inv stn_st))
          :: VerifCond cout;
        Generate := fun Base Exit =>
          let Base' := Nsucc (Nsucc (Nsucc Base)) in
          let cg := Generate cout Base' (Nsucc (Nsucc Base)) in
          {|
            Entry := 0;
            Blocks := (pre, (nil, Uncond (RvLabel (modName, Local (Nsucc Base)))))
              :: (inv, (nil, Cond rv1 t rv2
                (modName, Local (Base' + Entry cg))
                (modName, Local Exit)))
              :: (Postcondition cout, (nil, Uncond (RvLabel (modName, Local (Nsucc Base)))))
              :: Blocks cg
          |}
      |}); abstract struct.
  Defined.

  Hint Extern 1 (interp _ _) => progress simpl.

  (** * Direct jump *)

  Inductive jumpToUnknownLabel (f : label) : Prop := .

  Definition Goto_ (f : label) : cmd.
    red; refine (fun pre => {|
      Postcondition := (fun _ => [|False|])%PropX;
      VerifCond := match LabelMap.find f imports with
                     | None => jumpToUnknownLabel f
                     | Some pre' => forall stn_st specs, interp specs (pre stn_st)
                       -> interp specs (pre' stn_st)
                   end :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel f))) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** * Direct function call *)

  Definition Call_ (f : label) (afterCall : assert) : cmd.
    red; refine (fun pre => {|
      Postcondition := afterCall;
      VerifCond := match LabelMap.find f imports with
                     | None => jumpToUnknownLabel f
                     | Some pre' => forall stn st specs,
                       interp specs (pre (stn, st))
                       -> forall rp, specs rp = Some afterCall
                         -> interp specs (pre' (stn, {| Regs := rupd (Regs st) Rp rp; Mem := Mem st |}))
                   end :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (Assign Rp (RvLabel (modName, Local Exit)) :: nil, Uncond (RvLabel f))) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** * Indirect jump *)

  Inductive rvalueCrashes (rv : rvalue) : Prop := .

  Definition IGoto (rv : rvalue) : cmd.
    red; refine (fun pre => {|
      Postcondition := (fun _ => [|False|])%PropX;
      VerifCond := (forall specs stn st, interp specs (pre (stn, st))
        -> match evalRvalue stn st rv with
             | None => rvalueCrashes rv
             | Some w => exists pre', specs w = Some pre'
               /\ interp specs (pre' (stn, st))
           end) :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond rv)) :: nil
      |}
    |}); abstract struct.
  Defined.

  (** * Indirect function call *)

  Definition ICall_ (rv : rvalue) (afterCall : assert) : cmd.
    red; refine (fun pre => {|
      Postcondition := afterCall;
      VerifCond := (forall stn st specs,
        interp specs (pre (stn, st))
        -> forall rp, specs rp = Some afterCall
          -> match evalRvalue stn {| Regs := rupd (Regs st) Rp rp; Mem := Mem st |} rv with
               | None => rvalueCrashes rv
               | Some w => exists pre', specs w = Some pre'
                 /\ interp specs (pre' (stn, {| Regs := rupd (Regs st) Rp rp; Mem := Mem st |}))
             end) :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (Assign Rp (RvLabel (modName, Local Exit)) :: nil, Uncond rv)) :: nil
      |}
    |}); abstract struct.
  Defined.
End imports.


(** Redefine tactics for use in other files *)

Module DefineStructured.
  Hint Constructors vcs.

  Hint Resolve ge_refl.

  Ltac lomega := (let H := fresh in intro H; discriminate
    || injection H; clear H; intro; try subst; simpl in *; congruence || nomega)
  || (repeat match goal with
               | [ |- eq (A := ?A) _ _ ] =>
                 match A with
                   | N => fail 1
                   | _ => f_equal
                 end
             end; nomega).

  Hint Extern 1 (eq (A := label) _ _) => lomega.
  Hint Extern 1 (~(eq (A := label) _ _)) => lomega.
  Hint Extern 1 (eq (A := LabelKey.t) _ _) => lomega.
  Hint Extern 1 (~(eq (A := LabelKey.t) _ _)) => lomega.

  Hint Resolve LabelMap.add_1 LabelMap.add_2.

  Hint Resolve lookup_imps.

  Hint Immediate simplify_fwd.

  Hint Extern 1 (List.Forall _ _) => eapply Forall_impl; [ | eassumption ]; cbv zeta.
  Hint Extern 2 (blockOk _ _ _) => simpl in *; eapply blockOk_impl; [ | eassumption ].

  Hint Resolve imps_exit.

  Hint Extern 2 (LabelMap.MapsTo _ _ _) => apply MapsTo_or; intro; subst.
  Hint Extern 1 (@eq assert _ _) => elimtype False; eapply imps_contra; [ eassumption | eassumption | nomega | nomega ].
  Hint Extern 1 (@eq assert _ _) => eapply imps_exit'; [ eassumption | nomega ].
  Hint Resolve imps_app_1 imps_app_2 imps_not_exit.

  Ltac preSimp := simpl in *; intuition eauto; repeat (apply Forall_nil || apply Forall_cons); simpl; unfold importsGlobal in *.

  Ltac destrOpt E := let Heq := fresh "Heq" in case_eq E; (intros ? Heq || intro Heq); rewrite Heq in *.

  Ltac simp := repeat (match goal with
                         | [ x : codeGen _ _ _ _ _ _ _ |- _ ] => destruct x; simpl in *
                         | [ H : _ /\ _ |- _ ] => destruct H
                         | [ H : ex _ |- _ ] => destruct H

                         | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
                         | [ H : vcs (_ ++ _) |- _ ] => generalize (vcs_app_bwd1 _ _ H);
                           generalize (vcs_app_bwd2 _ _ H); clear H; intros

                         | [ |- vcs nil ] => constructor
                         | [ |- vcs (_ :: _) ] => constructor
                         | [ |- vcs (_ ++ _) ] => apply vcs_app_fwd

                         | [ H1 : notStuck _ _, H2 : _ |- _ ] => specialize (H1 _ _ _ H2)
                         | [ H : LabelMap.find _ _ = Some _ |- _ ] => apply LabelMap.find_2 in H
                         | [ H : forall k v, _ |- _ ] => destruct (split_add H); clear H
                         | [ H : forall n x y, _ |- _ ] => destruct (nth_app_hyp H); clear H
                         | [ H : _ |- _ ] => destruct (specialize_imps H); clear H
                         | [ H : forall x, _ -> _ |- _ ] => specialize (H _ (refl_equal _))
                         | [ H : forall x y z, _ -> _ , H' : _ |- _ ] => specialize (H _ _ _ H')
                         | [ H : forall x y, _ -> _ , H' : LabelMap.MapsTo _ _ _ |- _ ] => destruct (H _ _ H'); clear H; auto
                         | [ |- blockOk _ _ _ ] => red
                         | [ _ : match ?E with Some _ => _ | None => _ end = Some _ |- _ ] => destrOpt E; [ | discriminate ]
                         | [ _ : match ?E with Some _ => _ | None => _ end = None -> False |- _ ] => destrOpt E; [ | tauto ]
                         | [ _ : match ?E with Some _ => _ | None => _ end |- _ ] => destrOpt E; [ | tauto ]
                         | [ |- context[if ?E then _ else _] ] => destrOpt E
                         | [ H : ?E = None -> False |- _ ] =>
                           match E with
                             | Some _ => clear H
                             | _ => case_eq E; intros; tauto || clear H
                           end
                         | [ H : _ |- _ ] => rewrite H
                         | [ H : ?P -> _ |- _ ] =>
                           match type of P with
                             | Prop => let H' := fresh in assert (H' : P) by (lomega || auto); specialize (H H'); clear H'
                           end
                         | [ x : N |- _ ] => unfold x in *; clear x
                         | [ H : nth_error ?ls (nat_of_N ?n) = _ |- _ ] =>
                           match goal with
                             | [ _ : n < N_of_nat (length ls) |- _ ] => fail 1
                             | _ => specialize (nth_error_bound' _ _ H)
                           end
                         | [ H : snd ?x = _ |- _ ] => destruct x; simpl in H; congruence
                         | [ H : forall rp, _ rp = Some _ -> _, H' : _ _ = Some _ |- _ ] => specialize (H _ H')
                       end; intros; unfold evalBlock, evalCond in *; simpl; autorewrite with N in *).

  Ltac struct := preSimp; simp; eauto 15.
End DefineStructured.
