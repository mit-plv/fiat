Require Import Coq.omega.Omega.
Require Import Bedrock.Bedrock Coq.Bool.Bool.

Open Scope list_scope.


Inductive bexp :=
| Test : rvalue -> test -> rvalue -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp.

Fixpoint bexpD (b : bexp) (stn : settings) (st : state) : option bool :=
  match b with
    | Test rv1 t rv2 =>
      match evalRvalue stn st rv1, evalRvalue stn st rv2 with
        | Some v1, Some v2 => Some (evalTest t v1 v2)
        | _, _ => None
      end
    | Not b => match bexpD b stn st with
                 | Some b => Some (negb b)
                 | None => None
               end
    | And b1 b2 => match bexpD b1 stn st, bexpD b2 stn st with
                     | Some v1, Some v2 => Some (v1 && v2)
                     | Some false, None => Some false
                     | _, _ => None
                   end
    | Or b1 b2 => match bexpD b1 stn st, bexpD b2 stn st with
                    | Some v1, Some v2 => Some (v1 || v2)
                    | Some true, None => Some true
                    | _, _ => None
                  end
  end.

Fixpoint bexpTrue (b : bexp) (stn : settings) (st : state) : Prop :=
  match b with
    | Test rv1 t rv2 => evalCond rv1 t rv2 stn st = Some true
    | Not b => bexpFalse b stn st
    | And b1 b2 => bexpTrue b1 stn st /\ bexpTrue b2 stn st
    | Or b1 b2 => bexpTrue b1 stn st \/ (bexpFalse b1 stn st /\ bexpTrue b2 stn st)
  end

with bexpFalse (b : bexp) (stn : settings) (st : state) : Prop :=
  match b with
    | Test rv1 t rv2 => evalCond rv1 t rv2 stn st = Some false
    | Not b => bexpTrue b stn st
    | And b1 b2 => bexpFalse b1 stn st \/ (bexpTrue b1 stn st /\ bexpFalse b2 stn st)
    | Or b1 b2 => bexpFalse b1 stn st /\ bexpFalse b2 stn st
  end.

Theorem bexpD_truth : forall stn st b,
  match bexpD b stn st with
    | None => True
    | Some true => bexpTrue b stn st
    | Some false => bexpFalse b stn st
  end.
  induction b; simpl; unfold evalCond; intuition;
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H in *
             | [ |- context[match ?E with None => _ | _ => _ end] ] =>
               match E with
                 | context[match _ with None => _ | _ => _ end] => fail 1
                 | _ => case_eq E; intros
               end
             | [ b : bool |- _ ] => destruct b; simpl in *
             | [ |- context[if ?E then _ else _] ] => destruct E
           end; intuition; try discriminate.
Qed.

Fixpoint bexpSafe (b : bexp) (stn : settings) (st : state) : Prop :=
  match b with
    | Test rv1 t rv2 => ~(evalCond rv1 t rv2 stn st = None)
    | Not b => bexpSafe b stn st
    | And b1 b2 => bexpSafe b1 stn st /\ (bexpTrue b1 stn st -> bexpSafe b2 stn st)
    | Or b1 b2 => bexpSafe b1 stn st /\ (bexpFalse b1 stn st -> bexpSafe b2 stn st)
  end.

Theorem bexpSafe_really : forall stn st b,
  bexpSafe b stn st
  -> bexpD b stn st = None -> False.
  induction b; simpl; intuition;
    repeat match goal with
             | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
               match E with
                 | bexpD ?b ?stn ?st => specialize (bexpD_truth stn st b)
               end; destruct E
             | [ b : bool |- _ ] => destruct b
           end; intuition; try discriminate.
Qed.

Fixpoint size (b : bexp) : nat :=
  match b with
    | Test _ _ _ => 1
    | Not b => size b
    | And b1 b2 => size b1 + size b2
    | Or b1 b2 => size b1 + size b2
  end.

Import DefineStructured.

Section Cond.
  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Fixpoint blocks (Base : N) (pre : assert) (b : bexp) (Tru Fals : N) : list (assert * block) :=
    match b with
      | Test rv1 t rv2 => (pre, (nil, Cond rv1 t rv2
        (modName, Local Tru)
        (modName, Local Fals))) :: nil
      | Not b => blocks Base pre b Fals Tru
      | And b1 b2 =>
        let Base' := (Base + N_of_nat (size b1))%N in
        blocks Base pre b1 Base' Fals
        ++ blocks Base' (fun stn_st =>
          [| bexpD b1 (fst stn_st) (snd stn_st) = Some true |] /\ pre stn_st)%PropX b2 Tru Fals
      | Or b1 b2 =>
        let Base' := (Base + N_of_nat (size b1))%N in
        blocks Base pre b1 Tru Base'
        ++ blocks Base' (fun stn_st =>
          [| bexpD b1 (fst stn_st) (snd stn_st) = Some false |] /\ pre stn_st)%PropX b2 Tru Fals
    end.

  Lemma blocks_first : forall b Base pre Tru Fals,
    exists bl, exists rest, blocks Base pre b Tru Fals = (pre, bl) :: rest.
    induction b; simpl; intuition eauto;
      match goal with
        | [ H : context[blocks _ _ ?B _ _] |- context[blocks ?Base ?pre ?B ?Tru ?False] ] =>
          specialize (H Base pre Tru False); destruct H as [ ? [ ? H ] ]; rewrite H
      end; simpl; eauto.
  Qed.

  Lemma length_size : forall b Base pre Tru Fals,
    length (blocks Base pre b Tru Fals) = size b.
    induction b; simpl; intuition; rewrite app_length; struct.
  Qed.

  Transparent evalInstrs.

  Hint Extern 1 => match goal with
                     | [ H : ?E = _ |- match ?E with None => _ | _ => _ end = _ ] =>
                       rewrite H; reflexivity
                   end.

  Ltac t := repeat match goal with
                     | [ |- blockOk _ _ _ ] => hnf; simpl; intros
                     | [ H1 : _, H2 : interp _ _ |- _ ] => destruct (H1 _ _ H2); clear H1; simpl in *
                     | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
                     | [ H : _ = _ |- _ ] => rewrite H in *
                     | [ H : match ?E with Some _ => _ | _ => _ end = Some _ |- _ ] => case_eq E; intros
                     | [ |- context[if ?E then _ else _] ] => case_eq E; intros
                     | [ H : LabelMap.MapsTo ?Which _ _ |- context[Labels _ ?Which] ] =>
                         match goal with
                           | [ H' : LabelMap.MapsTo _ _ _ |- _ ] =>
                             match H' with
                               | H => fail 1
                               | _ => clear H'
                             end
                         end
                     end; discriminate || intuition; struct;
    repeat match goal with
             | [ |- Logic.ex _ ] => eexists
             | [ |- _ /\ _ ] => split
           end; (simpl; simpl; eauto);
    try match goal with
          | [ |- interp _ _ ] =>
            propxFo;
            try match goal with
                  | [ H : _ |- _ ] => apply H; auto
                end; simpl;
            repeat match goal with
                     | [ H : _ = _ |- _ ] => rewrite H in *
                   end; trivial
        end.

  Lemma blocks_ok : forall imps b Base pre Tru Fals Tru_spec Fals_spec,
    (forall specs st, interp specs (pre st)
      -> exists v, bexpD b (fst st) (snd st) = Some v)
    -> LabelMap.MapsTo (modName, Local Tru) Tru_spec imps
    -> LabelMap.MapsTo (modName, Local Fals) Fals_spec imps
    -> (forall specs stn_st, bexpD b (fst stn_st) (snd stn_st) = Some true
      -> interp specs (pre stn_st)
      -> interp specs (Tru_spec stn_st))
    -> (forall specs stn_st, bexpD b (fst stn_st) (snd stn_st) = Some false
      -> interp specs (pre stn_st)
      -> interp specs (Fals_spec stn_st))
    -> (forall n pre' bl, nth_error (blocks Base pre b Tru Fals) n = Some (pre', bl)
      -> LabelMap.MapsTo (modName, Local (Base + N_of_nat n)) pre' imps)
    -> List.Forall (fun p => blockOk imps (fst p) (snd p))
    (blocks Base pre b Tru Fals).
    induction b; simpl; intuition; repeat match goal with
                                            | [ |- List.Forall _ _ ] => (constructor || apply Forall_app); simpl
                                          end.

    t.
    eapply IHb; intuition eauto; t.

    edestruct (blocks_first b2) as [ ? [ ] ].
    eapply IHb1; intros.
    t.
    eapply H4.
    rewrite Expr.nth_error_app_R.
    rewrite length_size.
    replace (size b1 - size b1) with 0 by omega.
    rewrite H5.
    reflexivity.
    rewrite length_size; auto.
    eauto.
    propxFo.
    t.
    t.
    eapply H4.
    rewrite Expr.nth_error_app_L.
    eauto.
    eapply nth_error_bound; eauto.

    eapply IHb2; intros.
    propxFo.
    t.
    eauto.
    eauto.
    t.
    t.
    replace (Base + N.of_nat (size b1) + N.of_nat n)%N
      with (Base + N.of_nat (size b1 + n))%N by nomega.
    eapply H4.
    rewrite Expr.nth_error_app_R.
    rewrite length_size.
    replace (size b1 + n - size b1) with n by omega.
    eauto.
    rewrite length_size; omega.

    edestruct (blocks_first b2) as [ ? [ ] ].
    eapply IHb1; intros.
    t.
    eauto.
    eapply H4.
    rewrite Expr.nth_error_app_R.
    rewrite length_size.
    replace (size b1 - size b1) with 0 by omega.
    rewrite H5.
    reflexivity.
    rewrite length_size; auto.
    t.
    propxFo.
    eapply H4.
    rewrite Expr.nth_error_app_L.
    eauto.
    eapply nth_error_bound; eauto.

    eapply IHb2; intros.
    propxFo.
    t.
    eauto.
    eauto.
    t.
    t.
    replace (Base + N.of_nat (size b1) + N.of_nat n)%N
      with (Base + N.of_nat (size b1 + n))%N by nomega.
    eapply H4.
    rewrite Expr.nth_error_app_R.
    rewrite length_size.
    replace (size b1 + n - size b1) with n by omega.
    eauto.
    rewrite length_size; omega.
  Qed.

  Ltac choosePost :=
    match goal with
      | [ _ : LabelMap.MapsTo _ _ (imps _ _ _ _ _ ?post) |- LabelMap.MapsTo _ _ (imps _ _ _ _ _ ?post') ] =>
        equate post' post
    end.

  Hint Extern 2 (LabelMap.MapsTo _ _ _) =>
    eapply imps_app_2; [ assumption | | eassumption | nomega ];
      rewrite length_size; choosePost.

  Hint Extern 1 (_ < _)%N => nomega.
  Hint Extern 1 (~(eq (A := LabelMap.key) _ _)) => lomega.

  Lemma imps_app_1 : forall k v exit post bls2 bls1 base,
    LabelMap.MapsTo k v (imps imports modName bls1 base exit post)
    -> k <> (modName, Local exit)
    -> (exit < base + N_of_nat (length bls1))%N
    -> LabelMap.MapsTo k v (imps imports modName (bls1 ++ bls2) base exit post).
    intros; eapply imps_app_1; eauto.
  Qed.

  Lemma imps_app_2 : forall k v exit post bls2 bls1 base,
    LabelMap.MapsTo k v (imps imports modName bls2 (base + N_of_nat (length bls1)) exit post)
    -> k <> (modName, Local exit)
    -> (exit < base)%N
    -> LabelMap.MapsTo k v (imps imports modName (bls1 ++ bls2) base exit post).
    intros; eapply imps_app_2; eauto.
  Qed.

  Lemma interp_eta : forall specs (pre : assert) st,
    interp specs (pre st)
    -> interp specs (pre (fst st, snd st)).
    destruct st; auto.
  Qed.

  Lemma ex_up : forall A (e : option A),
    (e = None -> False)
    -> exists v, e = Some v.
    destruct e; intuition eauto.
  Qed.

  Hint Resolve interp_eta ex_up bexpSafe_really.

  Definition Cond_ (b : bexp) (Then Else : cmd imports modName) : cmd imports modName.
    red; refine (fun pre =>
      let cout1 := Then (fun stn_st => pre stn_st /\ [|bexpTrue b (fst stn_st) (snd stn_st)|])%PropX in
      let cout2 := Else (fun stn_st => pre stn_st /\ [|bexpFalse b (fst stn_st) (snd stn_st)|])%PropX in
      {|
        Postcondition := (fun stn_st => Postcondition cout1 stn_st \/ Postcondition cout2 stn_st)%PropX;
        VerifCond := (forall stn st specs, interp specs (pre (stn, st)) -> bexpSafe b stn st)
          :: VerifCond cout1 ++ VerifCond cout2;
        Generate := fun Base Exit =>
          let Base' := (Nsucc (Nsucc Base) + N_of_nat (size b))%N in
          let cg1 := Generate cout1 Base' Base in
          let Base'' := (Base' + N_of_nat (length (Blocks cg1)))%N in
          let cg2 := Generate cout2 Base'' (Nsucc Base) in
          {|
            Entry := 2;
            Blocks := (Postcondition cout1, (nil, Uncond (RvLabel (modName, Local Exit))))
              :: (Postcondition cout2, (nil, Uncond (RvLabel (modName, Local Exit))))
              :: blocks (Nsucc (Nsucc Base)) pre b (Base' + Entry cg1) (Base'' + Entry cg2)
              ++ Blocks cg1 ++ Blocks cg2
          |}
      |}); abstract (struct;
        try match goal with
              | [ |- context[blocks ?Base ?pre ?b ?Tru ?Fals] ] =>
                solve [ let H := fresh in destruct (blocks_first b Base pre Tru Fals) as [ ? [ ? H ] ];
                  rewrite H; struct ]
              | [ H : context[imps _ ?modName _ _ ?Exit ?post] |- context[Labels _ (?modName, Local ?Exit)] ] =>
                let H' := fresh in destruct (H (modName, Local Exit) post) as [ ? [ H' ] ]; eauto; rewrite H';
                  repeat esplit; eauto; propxFo
            end;
        repeat apply Forall_app;
          (eapply blocks_ok; (intros; eauto; propxFo;
            try match goal with
                  | [ H : bexpD ?b ?stn ?st = _ |- _ ] => specialize (bexpD_truth stn st b); rewrite H; tauto
                end;
            repeat (apply LabelMap.add_2; [ lomega | ]);
            match goal with
              | [ H : nth_error ?Blocks (N.to_nat ?Entry) = Some _
                  |- LabelMap.MapsTo (_, Local (_ + ?Entry)) _ ?m ] =>
                apply imps_app_2; auto;
                  match m with
                    | context[Blocks ++ _] => apply imps_app_1
                    | _ => apply imps_app_2
                  end; auto; eapply lookup_imps in H; rewrite length_size; eauto
              | [ H : nth_error ?Blocks ?n = Some _ |- LabelMap.MapsTo (_, Local (_ + N.of_nat ?n)) _ ?m ] =>
                apply imps_app_1; auto; eapply lookup_imps; rewrite Nat2N.id; eauto
            end)) || eauto 15).
  Defined.

End Cond.


(** * Notation *)

Inductive bexp' :=
| Test' : condition -> bexp'
| Not' : bexp' -> bexp'
| And' : bexp' -> bexp' -> bexp'
| Or' : bexp' -> bexp' -> bexp'.

Coercion Test' : condition >-> bexp'.
Notation "!" := Not' : Condition_scope.
Infix "&&" := And' : Condition_scope.
Infix "||" := Or' : Condition_scope.

Delimit Scope Condition_scope with Condition.

Fixpoint makeBexp (b : bexp') (ns : list string) : bexp :=
  match b with
    | Test' c => Test (c.(COperand1) ns) c.(CTest) (c.(COperand2) ns)
    | Not' b => Not (makeBexp b ns)
    | And' b1 b2 => And (makeBexp b1 ns) (makeBexp b2 ns)
    | Or' b1 b2 => Or (makeBexp b1 ns) (makeBexp b2 ns)
  end.

Definition Cond (b : bexp') (Then Else : chunk) : chunk := fun ns res =>
  Structured nil (fun im mn H => Cond_ im H mn (makeBexp b ns)
    (toCmd Then mn H ns res) (toCmd Else mn H ns res)).

Notation "'If*' c { b1 } 'else' { b2 }" := (Cond c%Condition b1 b2)
  (no associativity, at level 95, c at level 0) : SP_scope.
