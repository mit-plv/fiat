Require Import Coq.omega.Omega.
Require Import Bedrock.Examples.PreAutoSep Bedrock.Examples.Wrap Bedrock.Examples.Conditional.

Import DefineStructured.

Set Implicit Arguments.


(** Test expressions over arrays *)

Inductive exp :=
| Const (w : W)
(* Literal word value *)
| Index
(* Position in the array *)
| Value
(* Content of array cell *)
| Var (x : string)
(* Injected value of Bedrock local variable *).

Inductive condition :=
| Test (e1 : exp) (t : test) (e2 : exp)
(* Basic comparison *)
| Not (c1 : condition)
| And (c1 c2 : condition)
| Or (c1 c2 : condition)
(* Boolean operators *).

Coercion Const : W >-> exp.
Coercion Var : string >-> exp.

Notation "x = y" := (Test x IL.Eq y) : ArrayQuery_scope.
Notation "x <> y" := (Test x IL.Ne y) : ArrayQuery_scope.
Notation "x < y" := (Test x IL.Lt y) : ArrayQuery_scope.
Notation "x <= y" := (Test x IL.Le y) : ArrayQuery_scope.
Notation "x > y" := (Test y IL.Lt x) : ArrayQuery_scope.
Notation "x >= y" := (Test y IL.Le x) : ArrayQuery_scope.

Notation "!" := Not : ArrayQuery_scope.
Infix "&&" := And : ArrayQuery_scope.
Infix "||" := Or : ArrayQuery_scope.

Delimit Scope ArrayQuery_scope with ArrayQuery.

Definition eval (vs : vals) (index value : W) (e : exp) : W :=
  match e with
    | Const w => w
    | Index => index
    | Value => value
    | Var x => sel vs x
  end.

Fixpoint satisfies (vs : vals) (index value : W) (c : condition) : Prop :=
  match c with
    | Test e1 t e2 => (evalTest t) (eval vs index value e1) (eval vs index value e2) = true
    | Not c1 => ~satisfies vs index value c1
    | And c1 c2 => satisfies vs index value c1 /\ satisfies vs index value c2
    | Or c1 c2 => satisfies vs index value c1 \/ satisfies vs index value c2
  end.

Section Query.
  Hint Extern 1 (Mem _ = Mem _) =>
    eapply scratchOnlyMem; [ | eassumption ];
      simpl; intuition congruence.
  Hint Extern 1 (Mem _ = Mem _) =>
    symmetry; eapply scratchOnlyMem; [ | eassumption ];
      simpl; intuition congruence.

  Hint Resolve evalInstrs_app sepFormula_Mem.

  Hint Extern 2 (interp ?specs2 (![ _ ] (?stn2, ?st2))) =>
    match goal with
      | [ _ : interp ?specs1 (![ _ ] (?stn1, ?st1)) |- _ ] =>
        solve [ equate specs1 specs2; equate stn1 stn2; equate st1 st2; step auto_ext ]
    end.

  Variable arr : string.
  (* Name of local variable containing an array to query *)
  Variable size : string.
  (* Name of local variable containing the array length in words *)
  Variable index : string.
  (* Name of local variable that, inside the loop, is assigned the current array index *)
  Variable value : string.
  (* Name of local variable that, inside the loop, is assigned the current array cell value *)

  Variable c : condition.
  (* We will loop over only those indices satisfying this condition. *)

  Variable imports : LabelMap.t assert.
  Hypothesis H : importsGlobal imports.
  Variable modName : string.

  Variable quants : Type.
  (* Quantified variables, in scope for both precondition and postcondition *)

  Variable invPre : quants -> list W -> list W -> vals -> qspec.
  (* Precondition part of loop invariant, parameterized over part of array visited already and then whole array *)

  Variable invPost : quants -> list W -> vals -> W -> qspec.
  (* Postcondition part of loop invariant, parameterized over whole array *)

  Variables Body : cmd imports modName.
  (* Code to run on each matching array index *)

  Variable ns : list string.
  (* Local variable names *)
  Variable res : nat.
  (* Reserved stack slots *)

  Definition loopInvariant : assert :=
    st ~> Ex qs, ExX, Ex wsPre, Ex ws, Ex vs, qspecOut (invPre qs wsPre ws (sel vs)) (fun PR =>
      ![ ^[locals ("rp" :: ns) vs res st#Sp * array ws (sel vs arr) * PR] * #0 ] st
      /\ [| sel vs size = length ws /\ sel vs index = length wsPre |]
      /\ Ex wsPost, [| ws = wsPre ++ wsPost |]
      /\ (sel vs "rp", fst st) @@@ (st' ~>
        [| st'#Sp = st#Sp |]
        /\ Ex vs', qspecOut (invPost qs ws (sel vs) st'#Rv) (fun PO =>
          ![ ^[locals ("rp" :: ns) vs' res st#Sp * array ws (sel vs arr) * PO] * #1 ] st'))).

  Definition bodyPre : assert :=
    st ~> Ex qs, Ex wsPre, Ex ws, ExX, Ex vs, qspecOut (invPre qs wsPre ws (sel vs)) (fun PR =>
      ![ ^[locals ("rp" :: ns) vs res st#Sp * array ws (sel vs arr) * PR] * #0 ] st
      /\ [| sel vs size = length ws /\ sel vs index = length wsPre
        /\ satisfies vs (sel vs index) (sel vs value) c |]
      /\ Ex wsPost, [| ws = wsPre ++ sel vs value :: wsPost |]
      /\ (sel vs "rp", fst st) @@@ (st' ~>
        [| st'#Sp = st#Sp |]
        /\ Ex vs', qspecOut (invPost qs ws (sel vs) st'#Rv) (fun PO =>
          ![ ^[locals ("rp" :: ns) vs' res st#Sp * array ws (sel vs arr) * PO] * #1 ] st'))).

  Definition expBound (e : exp) : Prop :=
    match e with
      | Const _ => True
      | Index => True
      | Value => True
      | Var x => In x ns /\ x <> value /\ x <> index
    end.

  Fixpoint conditionBound (c : condition) : Prop :=
    match c with
      | Test e1 _ e2 => expBound e1 /\ expBound e2
      | Not c1 => conditionBound c1
      | And c1 c2 => conditionBound c1 /\ conditionBound c2
      | Or c1 c2 => conditionBound c1 /\ conditionBound c2
    end.

  Definition expOut (e : exp) : rvalue :=
    match e with
      | Const w => w
      | Index => variableSlot index ns
      | Value => variableSlot value ns
      | Var x => variableSlot x ns
    end.

  Fixpoint conditionOut (c : condition) : bexp :=
    match c with
      | Test e1 t e2 => Conditional.Test (expOut e1) t (expOut e2)
      | Not c1 => Conditional.Not (conditionOut c1)
      | And c1 c2 => Conditional.And (conditionOut c1) (conditionOut c2)
      | Or c1 c2 => Conditional.Or (conditionOut c1) (conditionOut c2)
    end.

  Fixpoint indexEquals (c : condition) : option string :=
    match c with
      | Test Index IL.Eq (Var s) => Some s
      | Test _ _ _ => None
      | Not _ => None
      | And c1 c2 => match indexEquals c1 with
                       | None => indexEquals c2
                       | v => v
                     end
      | Or _ _ => None
    end.

  Fixpoint indexGe (c : condition) : option string :=
    match c with
      | Test (Var s) IL.Le Index => Some s
      | Test _ _ _ => None
      | Not _ => None
      | And c1 c2 => match indexGe c1 with
                       | None => indexGe c2
                       | v => v
                     end
      | Or _ _ => None
    end.

  (* Here's the raw command, which we will later wrap with nicer VCs. *)
  Definition Query_ : cmd imports modName :=
    match indexEquals c with
      | None =>
        match indexGe c with
          | None =>
            Seq_ H
            (Straightline_ _ _ (Assign (variableSlot index ns) 0 :: nil))
            (Structured.While_ H loopInvariant (variableSlot index ns) IL.Lt (variableSlot size ns)
              (Seq_ H
                (Straightline_ _ _ (
                  Binop Rv 4 Times (variableSlot index ns)
                  :: Binop Rv (variableSlot arr ns) Plus Rv
                  :: Assign (variableSlot value ns) (LvMem (Reg Rv))
                  :: nil))
                (Seq_ H
                  (Cond_ _ H _ (conditionOut c)
                    (Seq_ H
                      (Structured.Assert_ _ _ bodyPre)
                      Body)
                    (Skip_ _ _))
                  (Straightline_ _ _ (Binop (variableSlot index ns) (variableSlot index ns) Plus 1 :: nil)))))
          | Some b =>
            Structured.If_ H (variableSlot size ns) IL.Le (variableSlot b ns)
            (Skip_ _ _)
            (Seq_ H
              (Straightline_ _ _ (Assign (variableSlot index ns) (variableSlot b ns) :: nil))
              (Structured.While_ H loopInvariant (variableSlot index ns) IL.Lt (variableSlot size ns)
                (Seq_ H
                  (Straightline_ _ _ (
                    Binop Rv 4 Times (variableSlot index ns)
                    :: Binop Rv (variableSlot arr ns) Plus Rv
                    :: Assign (variableSlot value ns) (LvMem (Reg Rv))
                    :: nil))
                  (Seq_ H
                    (Cond_ _ H _ (conditionOut c)
                      (Seq_ H
                        (Structured.Assert_ _ _ bodyPre)
                        Body)
                      (Skip_ _ _))
                    (Straightline_ _ _ (Binop (variableSlot index ns) (variableSlot index ns) Plus 1 :: nil))))))
        end
      | Some b =>
        Structured.If_ H (variableSlot b ns) IL.Lt (variableSlot size ns)
        (Seq_ H
          (Straightline_ _ _ (
            Binop Rv 4 Times (variableSlot b ns)
            :: Binop Rv (variableSlot arr ns) Plus Rv
            :: Assign (variableSlot value ns) (LvMem (Reg Rv))
            :: Assign (variableSlot index ns) (variableSlot b ns)
            :: nil))
          (Cond_ _ H _ (conditionOut c)
            (Seq_ H
              (Structured.Assert_ _ _ bodyPre)
              Body)
            (Skip_ _ _)))
        (Skip_ _ _)
    end.

  Ltac wrap := wrap0; post; wrap1.

  Hint Resolve simplify_fwd.

  Lemma subst_qspecOut_fwd : forall pc state (specs : codeSpec pc state) A v qs (k : _ -> propX _ _ (A :: nil)),
    interp specs (subst (qspecOut qs k) v)
    -> interp specs (qspecOut qs (fun x => subst (k x) v)).
    induction qs; propxFo; eauto.
  Qed.

  Lemma subst_qspecOut_bwd : forall pc state (specs : codeSpec pc state) A v qs (k : _ -> propX _ _ (A :: nil)),
    interp specs (qspecOut qs (fun x => subst (k x) v))
    -> interp specs (subst (qspecOut qs k) v).
    induction qs; propxFo; eauto.
  Qed.

  Fixpoint domain (qs : qspec) : Type :=
    match qs with
      | Programming.Body _ => unit
      | Quant _ f => sigT (fun x => domain (f x))
    end.

  Fixpoint qspecOut' (qs : qspec) : domain qs -> HProp :=
    match qs with
      | Programming.Body P => fun _ => P
      | Quant _ f => fun d => qspecOut' (f (projT1 d)) (projT2 d)
    end.

  Lemma qspecOut_fwd : forall (specs : codeSpec W (settings * state)) qs k,
    interp specs (qspecOut qs k)
    -> exists v : domain qs, interp specs (k (qspecOut' qs v)).
    induction qs; simpl; propxFo.
    exists tt; auto.
    match goal with
      | [ H0 : forall a k, interp _ _ -> _, H1 : interp _ _ |- _ ]
        => apply H0 in H1; destruct H1 as [x0 ?]
    end.
    exists (existT _ x x0); eauto.
  Qed.

  Lemma qspecOut_bwd : forall (specs : codeSpec W (settings * state)) qs k v,
    interp specs (k (qspecOut' qs v))
    -> interp specs (qspecOut qs k).
    induction qs; simpl; propxFo; eauto.
  Qed.

  Lemma must_be_nil : forall (ind sz : W) (ws1 ws2 : list W),
    sz <= ind
    -> ind = length ws1
    -> sz = length (ws1 ++ ws2)
    -> goodSize (length (ws1 ++ ws2))
    -> ws2 = nil.
    intros; subst; rewrite app_length in *;
      match goal with
        | [ H : _ |- _ ] => eapply wle_goodSize in H; eauto
      end; destruct ws2; simpl in *; auto; omega.
  Qed.

  Hint Extern 1 (_ = _) => eapply must_be_nil; solve [ eauto ].

  Lemma length_app_nil : forall (w : W) A (ls : list A),
    w = length (ls ++ nil)
    -> w = length ls.
    intros; rewrite app_length in *; simpl in *; subst; auto.
  Qed.

  Hint Immediate length_app_nil.

  Hint Extern 1 (interp _ (_ ---> _)%PropX) => apply Imply_refl.

  Theorem double_sel : forall V x,
    sel (sel V) x = sel V x.
    reflexivity.
  Qed.

  Hint Rewrite double_sel sel_upd_eq sel_upd_ne using congruence : Locals.

  Ltac locals := intros; autorewrite with Locals; reflexivity.

  Hint Rewrite app_length natToW_plus DepList.pf_list_simpl : sepFormula.

  Lemma goodSize_middle : forall (pre : list W) mid post,
    goodSize (length (pre ++ mid :: post))
    -> goodSize (length pre).
    intros; autorewrite with sepFormula in *; simpl in *; eauto.
  Qed.

  Lemma goodSize_middleS : forall (pre : list W) mid post,
    goodSize (length (pre ++ mid :: post))
    -> goodSize (S (length pre)).
    intros; autorewrite with sepFormula in *; simpl in *; eauto.
    eapply goodSize_weaken; eauto.
  Qed.

  Hint Extern 1 (goodSize (length _)) => (eapply goodSize_middle || eapply goodSize_middleS);
    eapply containsArray_goodSize; [ eassumption | eauto ].

  Hint Rewrite sel_middle using solve [ eauto ] : sepFormula.

  Lemma condition_safe : forall specs V fr stn st,
    interp specs (![locals ("rp" :: ns) V res (Regs st Sp) * fr] (stn, st))
    -> In index ns
    -> In value ns
    -> ~In "rp" ns
    -> forall c', conditionBound c'
      -> bexpSafe (conditionOut c') stn st.
    clear_fancy; induction c'; simpl; intuition;
      match goal with
        | [ _ : evalCond (expOut ?e1) _ (expOut ?e2) _ _ = None |- _ ] =>
          destruct e1; destruct e2; (simpl in *; intuition idtac; prep_locals; evaluate auto_ext)
      end.
  Qed.

  Hint Resolve condition_safe.

  Hint Extern 1 (weqb _ _ = true) => apply weqb_true_iff.

  Lemma wneb_true : forall w1 w2,
    w1 <> w2
    -> wneb w1 w2 = true.
    unfold wneb; intros; destruct (weq w1 w2); auto.
  Qed.

  Lemma wltb_true : forall w1 w2,
    w1 < w2
    -> wltb w1 w2 = true.
    unfold wltb; intros; destruct (wlt_dec w1 w2); auto.
  Qed.

  Lemma wleb_true : forall w1 w2,
    w1 <= w2
    -> wleb w1 w2 = true.
    unfold wleb; intros; destruct (weq w1 w2); destruct (wlt_dec w1 w2); auto.
    elimtype False; apply n.
    assert (H1 : wordToNat w1 = wordToNat w2) by nomega.
    apply (f_equal (fun w => natToWord 32 w)) in H1.
    repeat rewrite natToWord_wordToNat in H1.
    assumption.
  Qed.

  Hint Resolve wneb_true wltb_true wleb_true.

  Lemma bool_one : forall b,
    b = true
    -> b = false
    -> False.
    intros; congruence.
  Qed.

  Lemma weqb_false : forall w1 w2,
    w1 <> w2
    -> weqb w1 w2 = false.
    unfold weqb; intros; generalize (weqb_true_iff w1 w2); destruct (Word.weqb w1 w2); intuition.
  Qed.

  Lemma wneb_false : forall w1 w2,
    w1 = w2
    -> wneb w1 w2 = false.
    unfold wneb; intros; destruct (weq w1 w2); intuition.
  Qed.

  Lemma wltb_false : forall w1 w2,
    w2 <= w1
    -> wltb w1 w2 = false.
    unfold wltb; intros; destruct (wlt_dec w1 w2); intuition.
  Qed.

  Lemma wleb_false : forall w1 w2,
    w2 < w1
    -> wleb w1 w2 = false.
    unfold wleb; intros; destruct (weq w1 w2); destruct (wlt_dec w1 w2); intuition; nomega.
  Qed.

  Hint Resolve weqb_false wneb_false wltb_false wleb_false.

  Lemma condition_satisfies' : forall specs V fr stn st,
    interp specs (![locals ("rp" :: ns) V res (Regs st Sp) * fr] (stn, st))
    -> In index ns
    -> In value ns
    -> ~In "rp" ns
    -> forall c', conditionBound c'
      -> (bexpTrue (conditionOut c') stn st -> satisfies V (sel V index) (sel V value) c')
      /\ (bexpFalse (conditionOut c') stn st -> ~satisfies V (sel V index) (sel V value) c').
    clear_fancy; induction c'; simpl; intuition;
      try (eapply bool_one; [ eassumption | ]);
        match goal with
          | [ _ : evalCond (expOut ?e1) ?t (expOut ?e2) _ _ = _ |- _ ] =>
            destruct e1; destruct t; destruct e2;
              (simpl in *; intuition idtac; prep_locals; evaluate auto_ext; auto)
        end.
  Qed.

  Lemma condition_satisfies : forall specs V fr stn st ind val,
    interp specs (![locals ("rp" :: ns) V res (Regs st Sp) * fr] (stn, st))
    -> In index ns
    -> In value ns
    -> ~In "rp" ns
    -> sel V index = ind
    -> sel V value = val
    -> forall c', conditionBound c'
      -> bexpTrue (conditionOut c') stn st
      -> satisfies V ind val c'.
    intros; subst; edestruct condition_satisfies'; eauto.
  Qed.

  Lemma condition_not_satisfies : forall specs V fr stn st ind val,
    interp specs (![locals ("rp" :: ns) V res (Regs st Sp) * fr] (stn, st))
    -> In index ns
    -> In value ns
    -> ~In "rp" ns
    -> sel V index = ind
    -> sel V value = val
    -> forall c', conditionBound c'
      -> bexpFalse (conditionOut c') stn st
      -> ~satisfies V ind val c'.
    intros; subst; edestruct condition_satisfies'; eauto.
  Qed.

  Fixpoint noMatches (V : vals) (ws : list W) (index : nat) : Prop :=
    match ws with
      | nil => True
      | w :: ws' => ~satisfies V index w c /\ noMatches V ws' (index + 1)
    end.

  Hint Rewrite app_nil_r : sepFormula.

  Lemma invPre_skip : (forall specs stn st V qs ws wsAll this v fr,
    ~satisfies V (length ws) this c
    -> interp specs (![qspecOut' (invPre qs ws wsAll (sel V)) v * fr] (stn, st))
    -> goodSize (S (length ws))
    -> exists v', interp specs (![qspecOut' (invPre qs (ws ++ this :: nil) wsAll (sel V)) v' * fr] (stn, st)))
  -> forall specs V fr stn st ws' qs ws wsAll v,
    interp specs (![qspecOut' (invPre qs ws wsAll V) v * fr] (stn, st))
    -> noMatches V ws' (length ws)
    -> goodSize (length (ws ++ ws'))
    -> exists v', interp specs (![qspecOut' (invPre qs (ws ++ ws') wsAll V) v' * fr] (stn, st)).
    induction ws'; simpl; intuition; autorewrite with sepFormula; eauto.

    match goal with
      | [ H0 : forall specs stn st V qs ws wsAll this v fr, (satisfies _ _ _ _ -> False) -> _,
            H4 : satisfies _ _ _ _ -> False |- _ ]
        => eapply H0 in H4
    end.
    post.
    match goal with
      | [ H2 : interp _ _ |- _ ]
        => apply IHws' in H2; [ | post; auto | auto ]
    end.
    autorewrite with sepFormula in *; eauto.
    autorewrite with sepFormula in *; auto.
    eauto.
    eapply goodSize_middleS; eauto.
  Qed.

  Hint Resolve natToW_inj.

  Lemma wleb_true_fwd : forall u v, wleb u v = true -> u <= v.
    unfold wleb; intros;
      destruct (weq u v); destruct (wlt_dec u v); subst; auto; discriminate || nomega.
  Qed.

  Ltac indexEquals :=
    repeat match goal with
             | [ _ : match ?E with None => _ | _ => _ end = _ |- _ ] => destruct E; try discriminate
             | [ _ : match ?E with Const _ => _ | _ => _ end = _ |- _ ] => destruct E; try discriminate
             | [ _ : match ?E with IL.Eq => _ | _ => _ end = _ |- _ ] => destruct E; try discriminate
             | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst; simpl in *
             | [ H : weqb _ _ = true |- _ ] => apply weqb_true_iff in H
             | [ H : wleb _ _ = true |- _ ] => apply wleb_true_fwd in H
           end.

  Lemma indexEquals_correct : forall k V (len : nat) val c',
    indexEquals c' = Some k
    -> satisfies V len val c'
    -> goodSize len
    -> (forall len' val', goodSize len' -> len <> len' -> ~satisfies V len' val' c').
    induction c'; simpl; intuition; indexEquals; intuition (subst; eauto);
      match goal with
        | [ H : _ -> False |- _ ] => apply H; apply natToW_inj; auto; congruence
      end.
  Qed.
  Require Import Coq.Arith.Arith.

  Lemma notSatisfies_noMatches' : forall V ws index,
    (forall (index' : nat) val, goodSize index' -> satisfies V index' val c
      -> (index <= index' < index + length ws)%nat -> False)
    -> goodSize (index + length ws)
    -> noMatches V ws index.
    induction ws; simpl; intuition eauto.
    eapply IHws; intros.
    eauto.
    rewrite <- plus_assoc.
    auto.
  Qed.

  Lemma notSatisfies_noMatches : forall V ws index,
    (forall (index' : nat) val, goodSize index' -> (index <= index' < index + length ws)%nat
      -> ~satisfies V index' val c)
    -> goodSize (index + length ws)
    -> noMatches V ws index.
    intuition; eapply notSatisfies_noMatches'; eauto.
  Qed.

  Lemma goodSize_middle' : forall (ls1 : list W) x ls2,
    goodSize (length (ls1 ++ x :: ls2))
    -> goodSize (length (ls1 ++ x :: nil) + length ls2).
    intros; autorewrite with sepFormula in *; simpl in *; rewrite <- plus_assoc; auto.
  Qed.

  Hint Resolve goodSize_middle'.

  Hint Extern 1 (~(@eq nat _ _)) => omega.

  Lemma indexEquals_bound : forall x c',
    indexEquals c' = Some x
    -> conditionBound c'
    -> In x ns.
    induction c'; simpl; intuition; indexEquals; tauto.
  Qed.

  Lemma indexGe_bound : forall x c',
    indexGe c' = Some x
    -> conditionBound c'
    -> In x ns.
    induction c'; simpl; intuition; indexEquals; tauto.
  Qed.

  Lemma indexEquals_correct' : forall k V c',
    indexEquals c' = Some k
    -> (forall len' val', goodSize len' -> sel V k <> len' -> ~satisfies V len' val' c').
    induction c'; simpl; intuition; indexEquals; intuition (subst; eauto).
  Qed.

  Lemma indexGe_correct : forall k V c',
    indexGe c' = Some k
    -> (forall len' val', goodSize len' -> natToW len' < sel V k -> ~satisfies V len' val' c').
    induction c'; simpl; intuition; indexEquals; intuition (subst; eauto).
  Qed.

  Lemma noMatches_app : forall V ws' ws index,
    noMatches V ws index
    -> noMatches V ws' (length ws + index)
    -> noMatches V (ws ++ ws') index.
    induction ws; simpl; intuition.
    match goal with
      | [ H1 : noMatches _ _ (S (length ?ws + ?index0)) |- _ ]
        => replace (S (length ws + index0)) with (length ws + (index0 + 1)) in H1 by omega
    end.
    auto.
  Qed.

  Lemma indexEquals_index : forall x c',
    indexEquals c' = Some x
    -> conditionBound c'
    -> x <> index.
    induction c'; simpl; intuition; indexEquals; tauto.
  Qed.

  Lemma indexEquals_value : forall x c',
    indexEquals c' = Some x
    -> conditionBound c'
    -> x <> value.
    induction c'; simpl; intuition; indexEquals; tauto.
  Qed.

  Lemma indexGe_index : forall x c',
    indexGe c' = Some x
    -> conditionBound c'
    -> x <> index.
    induction c'; simpl; intuition; indexEquals; tauto.
  Qed.

  Lemma indexGe_value : forall x c',
    indexGe c' = Some x
    -> conditionBound c'
    -> x <> value.
    induction c'; simpl; intuition; indexEquals; tauto.
  Qed.

  Hint Rewrite roundTrip_0 : N.

  Lemma skipn_breakout : forall ws n,
    (n < length ws)%nat
    -> skipn n ws = Array.selN ws n :: tl (skipn n ws).
    induction ws; destruct n; simpl; intuition.
  Qed.

  Lemma satisfies_incidentals : forall ind val c',
    conditionBound c'
    -> forall V V', (forall x, x <> index -> x <> value -> sel V x = sel V' x)
      -> satisfies V ind val c'
      -> satisfies V' ind val c'.
    induction c'; simpl; intuition eauto.
    destruct e1; destruct e2; simpl in *; intuition idtac;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite <- H by tauto
             end; tauto.
    eauto using eq_sym.
  Qed.

  Lemma not_satisfies_incidentals : forall ind val c',
    conditionBound c'
    -> forall V V', (forall x, x <> index -> x <> value -> sel V x = sel V' x)
      -> ~satisfies V ind val c'
      -> ~satisfies V' ind val c'.
    intuition.
    eauto using satisfies_incidentals, eq_sym.
  Qed.

  Lemma length_tl : forall A (ls : list A),
    length (tl ls) = length ls - 1.
    destruct ls; simpl; omega.
  Qed.

  Theorem wordToNat_natToW_goodSize : forall n,
    goodSize n
    -> wordToNat (natToW n) = n.
    intros; unfold natToW; rewrite wordToNat_natToWord_idempotent; auto.
  Qed.

  Hint Rewrite wordToNat_natToW_goodSize using solve [ eauto ] : N.

  Opaque goodSize.

  Lemma length_prefix : forall mid (ws : list W),
    (exists sz, mid < sz /\ sz = natToW (length ws))
    -> goodSize (length ws)
    -> length (firstn (wordToNat mid) ws) = wordToNat mid.
    destruct 1; intuition idtac; subst; rewrite firstn_length; rewrite min_l; intuition nomega.
  Qed.

  Hint Rewrite length_prefix using solve [ eauto ] : sepFormula.

  Lemma goodSize_middle'' : forall (ls1 ls2 : list W) x,
    goodSize (length (ls1 ++ x :: ls2))
    -> goodSize (length ls1 + 1 + length ls2).
    intros; autorewrite with sepFormula in *; simpl in *.
    rewrite <- plus_assoc; auto.
  Qed.

  Hint Resolve goodSize_middle''.

  Hint Rewrite plus_0_r length_tl CancelIL.skipn_length : sepFormula.

  Lemma roundTrip' : forall w : W,
    w = natToW (wordToNat w).
    intros; unfold natToW; rewrite natToWord_wordToNat; auto.
  Qed.

  Hint Resolve roundTrip'.

  Ltac my_nomega := repeat match goal with
                             | [ H : sel _ size = _ |- _ ] => rewrite H in *
                             | [ |- (_ <> _)%type ] =>
                               let H := fresh in intro H; rewrite H in *
                             | [ _ : goodSize ?X, H : context[wordToNat (natToW ?X)] |- _ ] =>
                               rewrite wordToNat_natToW_goodSize in H by assumption
                           end; nomega.

  Lemma goodSize_funky : forall mid sz n,
    mid < sz
    -> sz = natToW n
    -> goodSize n
    -> goodSize (wordToNat mid + 1 + (n - wordToNat mid - 1)).
    intros; subst; apply goodSize_weaken with n; eauto; my_nomega.
  Qed.

  Hint Resolve goodSize_funky.

  Lemma breakout : forall (ws : list W) mid,
    (wordToNat mid < length ws)%nat
    -> ws = firstn (wordToNat mid) ws ++ Array.sel ws mid :: tl (skipn (wordToNat mid) ws).
    intros; etransitivity; [ symmetry; apply (firstn_skipn (wordToNat mid)) | ];
      cbv beta; f_equal; apply skipn_breakout; auto.
  Qed.

  Hint Extern 1 (_ = _ ++ _ :: _) => apply breakout; my_nomega.


  Ltac depropx H := apply simplify_fwd in H; simpl in H;
    repeat match goal with
             | [ H : Logic.ex ?P |- _ ] => destruct H;
               try match goal with
                     | [ H : Logic.ex P |- _ ] => clear H
                   end
             | [ H : ?P /\ ?Q |- _ ] => destruct H;
               try match goal with
                     | [ H : P /\ Q |- _ ] => clear H
                   end
           end.

  Ltac begin0 :=
    match goal with
      | [ x : (settings * state)%type |- _ ] => destruct x; unfold fst, snd in *
      | [ H : forall x y z, _, H' : interp _ _ |- _ ] =>
        specialize (H _ _ _ H')
      | [ H : interp _ _ |- _ ] =>
        (apply subst_qspecOut_fwd in H; simpl in H)
        || (apply qspecOut_fwd in H; simpl in H; autorewrite with sepFormula in H; simpl in H; destruct H)
      | [ H : interp _ (Ex x, _) |- _ ] => depropx H
      | [ H : interp _ (ExX, _) |- _ ] => depropx H
      | [ H : interp _ (_ /\ _) |- _ ] => depropx H
      | [ H : simplify _ _ _ |- _ ] =>
        (apply simplify_bwd in H || (apply simplify_bwd' in H; unfold Substs in H);
          simpl in H; autorewrite with sepFormula in H; simpl in H)
    end.

  Ltac locals_rewrite :=
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
             | [ |- context[sel (upd ?V ?x ?v) ?y] ] =>
               rewrite (@sel_upd_ne V x v y) by congruence
             | [ |- context[sel (upd ?V ?x ?v) ?y] ] =>
               rewrite (@sel_upd_eq V x v y) by congruence
           end.

  Ltac finish0 :=
    try match goal with
          | [ |- ?L = firstn _ ?L ++ _ ] => symmetry; apply firstn_skipn
        end; eauto; progress (try rewrite app_nil_r in *; descend; autorewrite with sepFormula;
          repeat match goal with
                   | [ H : _ = _ |- _ ] => rewrite H
                   | [ |- specs (sel (upd _ ?x _) ?y) = Some _ ] => assert (y <> x) by congruence
                   | [ |- appcontext[invPost _ _ ?V] ] => (has_evar V; fail 2) ||
                     match goal with
                       | [ |- appcontext[invPost _ _ ?V'] ] =>
                         match V' with
                           | V => fail 1
                           | _ => match goal with
                                    | [ H : forall (_ : quants) (_ : list W) (V : vals), _ |- _ ] =>
                                      rewrite (H _ _ V V') by locals
                                  end
                         end
                     end
                 end;
          try match goal with
                | [ |- satisfies _ _ _ _ ] => eapply condition_satisfies; solve [ finish0 ]
                | [ |- interp _ (subst _ _) ] =>
                  try match goal with
                        | [ _ : context[locals _ ?X _ _] |- context[locals _ ?Y _ _] ] => equate X Y
                      end;
                  apply subst_qspecOut_bwd; eapply qspecOut_bwd; propxFo
                | _ => try match goal with
                             | [ _ : context[qspecOut' _ ?X] |- context[qspecOut' _ ?Y] ] => equate X Y
                           end; step auto_ext
        end).

  Ltac enrich := match goal with
                   | [ H : indexEquals _ = Some _, H' : conditionBound _ |- _ ] =>
                     specialize (indexEquals_bound _ H H');
                       specialize (indexEquals_index _ H H');
                         specialize (indexEquals_value _ H H');
                           intros; prep_locals
                   | [ H : indexGe _ = Some _, H' : conditionBound _ |- _ ] =>
                     specialize (indexGe_bound _ H H');
                       specialize (indexGe_index _ H H');
                         specialize (indexGe_value _ H H');
                           intros; prep_locals
                 end.

  Ltac invPre_skip :=
    edestruct invPre_skip; try match goal with
                                 | [ _ : context[qspecOut' _ ?X] |- context[qspecOut' _ ?Y] ] => equate X Y
                               end; eauto; simpl.

  Ltac notSatisfies_noMatches :=
    eapply notSatisfies_noMatches; autorewrite with sepFormula; simpl; intros; eauto 6.
  Ltac indexEquals_correct :=
    eapply indexEquals_correct; (cbv beta; eauto).
  Ltac indexEquals_correct' := eapply indexEquals_correct'; autorewrite with Locals; eauto;
    (autorewrite with Locals; my_nomega).
  Ltac indexGe_correct := eapply indexGe_correct; autorewrite with Locals; eauto;
    (autorewrite with Locals; my_nomega).

  Ltac evolve :=
    match goal with
      | [ v : domain (invPre _ ((_ ++ _ :: nil) ++ _) _ _) |- _ ] =>
        generalize dependent v; autorewrite with sepFormula; intros
      | [ v : domain (invPre _ _ (_ ++ nil) _) |- _ ] =>
        generalize dependent v; autorewrite with sepFormula in *; intros
      | [ v : domain (invPre _ _ _ _) |- _ ] =>
        generalize dependent v; simpl; autorewrite with sepFormula;
          match goal with
            | [ H : forall qs : quants, _ |- context[locals _ ?V _ _] ] =>
              rewrite (H _ _ _ _ (sel V)) by locals
          end; intros
    end.

  Ltac finish := repeat finish0.

  Ltac nonempty L := destruct L; [ elimtype False; rewrite app_nil_r in *;
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H in *
           end;
    match goal with
      | [ H : ?X < ?X |- _ ] => generalize H; clear; intros
    end; nomega
    | ].

  Lemma app_length_le : forall A (ls1 ls2 : list A),
    (length ls1 <= length (ls1 ++ ls2))%nat.
    intros; rewrite app_length; auto.
  Qed.

  Hint Resolve app_length_le.

  Lemma goodSize_S' : forall (ls1 ls2 : list W) ind siz,
    ind = natToW (length ls1)
    -> siz = natToW (length (ls1 ++ ls2))
    -> ind < siz
    -> goodSize (length (ls1 ++ ls2))
    -> (S (length ls1) <= length ls1 + length ls2)%nat.
    intros; subst; autorewrite with sepFormula in *.
    match goal with
      | [ H : _ |- _ ] => solve [ apply lt_goodSize' in H; eauto ]
    end.
  Qed.

  Hint Extern 1 (S _ <= _)%nat => eapply goodSize_S'; [ eassumption | eassumption | eassumption
    | eapply containsArray_goodSize; eauto ].

  Ltac goodSize := eapply goodSize_weaken; [
    eapply containsArray_goodSize; eauto
    | cbv beta; autorewrite with sepFormula; simpl; eauto; my_nomega ].

  Ltac begin := repeat begin0;
    try match goal with
          | [ _ : bexpFalse _ _ _, H : evalInstrs _ _ (Binop _ _ Plus _ :: nil) = Some _ |- _ ] =>
            generalize dependent H
        end;
    evaluate auto_ext; intros; subst;
      try match goal with
            | [ _ : sel _ size = natToW (length (_ ++ ?ws)) |- _ ] => assert (ws = nil) by auto; subst;
              try evolve

            | [ _ : indexEquals _ = Some _,_ : satisfies _ _ _ _ |- _ ] =>
              invPre_skip; [ match goal with
                               | [ _ : context[array (_ ++ _ :: ?wsPost) _] |- _ ] => instantiate (1 := wsPost)
                             end; notSatisfies_noMatches; indexEquals_correct
                | goodSize
                | evolve ]

            | [ _ : indexEquals _ = Some _, _ : evalCond _ _ _ _ _ = Some false |- _ ] =>
              invPre_skip; [ match goal with
                               | [ _ : context[array ?ws _] |- _ ] => instantiate (1 := ws)
                             end; notSatisfies_noMatches; indexEquals_correct'
                | goodSize
                | finish ]

            | [ _ : indexEquals _ = Some _, _ : evalCond _ _ _ _ _ = Some true, _ : bexpFalse _ _ _ |- _ ] =>
              invPre_skip; [ match goal with
                               | [ _ : ?mid < sel _ size, _ : context[array ?ws _] |- _ ] => instantiate (1 := ws);
                                 rewrite <- (firstn_skipn (wordToNat mid) ws)
                             end; apply noMatches_app; [ notSatisfies_noMatches; indexEquals_correct'
                               | rewrite skipn_breakout by my_nomega; split; autorewrite with sepFormula ]; [
                                 evolve; invPre_skip; [
                                   match goal with
                                     | [ _ : ?mid < sel _ size, _ : context[array ?ws _] |- _ ] =>
                                       instantiate (1 := firstn (wordToNat mid) ws)
                                   end; notSatisfies_noMatches; indexEquals_correct'
                                   | goodSize
                                   | match goal with
                                       | [ _ : context[locals _ ?V _ _] |- ~satisfies _ _ _ _ ] =>
                                         apply not_satisfies_incidentals with V; intros; autorewrite with Locals; auto
                                     end; eapply condition_not_satisfies; finish0; auto ]
                                 | notSatisfies_noMatches; indexEquals_correct' ]
                | goodSize
                | evolve ]

            | [ _ : indexEquals _ = Some _, _ : evalCond _ _ _ _ _ = Some true, _ : bexpTrue _ _ _ |- _ ] =>
              invPre_skip; [ match goal with
                               | [ _ : ?mid < sel _ size, _ : context[array ?ws _] |- _ ] =>
                                 instantiate (1 := firstn (wordToNat mid) ws)
                             end; notSatisfies_noMatches; indexEquals_correct'
                | goodSize
                | evolve ]

            | [ _ : indexGe _ = Some _, _ : evalCond _ _ _ _ _ = Some true |- _ ] =>
              invPre_skip; [ notSatisfies_noMatches; indexGe_correct
                | goodSize
                | match goal with
                    | [ v : domain (invPre _ (nil ++ _) _ _) |- _ ] =>
                      generalize dependent v; simpl; intros
                  end ]

            | [ _ : indexGe _ = Some _, _ : evalCond _ _ _ _ _ = Some false |- _ ] =>
              invPre_skip; [ match goal with
                               | [ _ : ?mid < sel _ size, _ : context[array ?ws _] |- _ ] =>
                                 instantiate (1 := firstn (wordToNat mid) ws)
                             end; notSatisfies_noMatches; indexGe_correct
                | goodSize
                | evolve ]

            | [ v : domain (invPre ?qs nil _ (sel ?V)), H : forall x : quants, _ |- _ ] =>
              generalize dependent v; rewrite (H qs nil _ (sel V) (sel (upd V index 0))) by locals;
                intros; do 2 eexists; exists nil

            | [ v : domain (invPre ?qs (?x ++ ?l :: nil) _ (sel ?V)), H : forall x : quants, _ |- _ ] =>
              generalize dependent v; rewrite (H qs (x ++ l :: nil) _ (sel V) (sel (upd V index (sel V index ^+ $1))))
                by locals; intros; do 2 eexists; exists (x ++ l :: nil)

            | [ _ : bexpTrue _ _ _, v : domain (invPre _ ?l _ (sel ?V)), H : forall x : quants, _,
                _ : _ = natToW (length (?wPre ++ ?wPost)) |- _ ] =>
              generalize dependent v; rewrite (H _ _ _ _ (upd V value (Array.sel (wPre ++ wPost)
                (sel V index)))) by locals; intros;
              nonempty wPost;
              match goal with
                | [ H : context[v] |- _ ] => generalize v H
              end; locals_rewrite; rewrite sel_middle by eauto; intro v'; intros; repeat eexists;
              apply simplify_fwd'; unfold Substs; apply subst_qspecOut_bwd; apply qspecOut_bwd with v'

            | [ Hf : bexpFalse (conditionOut c) _ _, _ : evalInstrs _ _ (Binop _ _ Plus _ :: nil) = Some _,
                v : domain (invPre _ ?l ?all (sel ?V)), H : forall x : quants, _,
                _ : context[Array.sel (?wPre ++ ?wPost) ?u], _ : _ = natToW (length ?L) |- _ ] =>
              let Hf' := fresh in
              match goal with
                | [ _ : context[locals _ ?V' _ _] |- _ ] =>
                  assert (Hf' : ~satisfies V' (length L) (sel V' value) c)
                    by (eapply condition_not_satisfies; finish0)
              end; clear Hf; rename Hf' into Hf;
              generalize dependent v; rewrite (H _ _ _ _ (upd V value (Array.sel (wPre ++ wPost) u))) by locals;
                intros;
                  match goal with
                    | [ H' : forall specs : codeSpec _ _, _ |- _ ] =>
                      change (forall specs stn st V qs ws wsAll this v fr,
                        ~satisfies V (Datatypes.length ws) this c
                        -> interp specs (![qspecOut' (invPre qs ws wsAll V) v * fr] (stn, st))
                        -> goodSize (S (length ws))
                        -> exists v', interp specs (![qspecOut' (invPre qs (ws ++ this :: nil) wsAll V) v' * fr] (stn, st))) in H';
                      eapply H' in Hf; [ |
                        match goal with
                          | [ |- context[qspecOut' _ ?v'] ] => equate v v'
                        end; eauto | goodSize ]
                  end; rewrite (H _ _ _ _ (upd
                    (upd V value (Array.sel (wPre ++ wPost) u)) index
                    (sel (upd V value (Array.sel (wPre ++ wPost) u)) index ^+ $1)))
                  in Hf by locals;
                  intros; do 2 eexists;
                    exists (wPre ++ Array.sel (wPre ++ wPost) u :: nil); exists all;
                      exists (upd (upd V value (Array.sel (wPre ++ wPost) u)) index
                        (sel (upd V value (Array.sel (wPre ++ wPost) u))
                          index ^+ $1));
                      nonempty wPost;
                      repeat match goal with
                               | [ H : interp _ _ |- _ ] => clear H
                             end; destruct Hf as [v']; evaluate auto_ext;
                      apply simplify_fwd'; unfold Substs; apply subst_qspecOut_bwd;
                        generalize dependent v'; locals_rewrite; intros; apply qspecOut_bwd with v'
          end.

  Ltac t := begin; finish.

  Definition Query : cmd imports modName.
    refine (Wrap _ H _ Query_
      (fun _ st => Ex qs, Ex ws, ExX, Ex V, qspecOut (invPre qs ws ws (sel V)) (fun PR =>
        ![ ^[locals ("rp" :: ns) V res st#Sp * array ws (sel V arr) * PR] * #0 ] st
        /\ [| sel V size = length ws |]
        /\ (sel V "rp", fst st) @@@ (st' ~>
          [| st'#Sp = st#Sp |]
          /\ Ex V', qspecOut (invPost qs ws (sel V) st'#Rv) (fun PO =>
            ![ ^[locals ("rp" :: ns) V' res st#Sp * array ws (sel V arr) * PO] * #1 ] st'))))%PropX
      (fun pre =>
        (* Basic hygiene requirements *)
        In arr ns
        :: In size ns
        :: In index ns
        :: In value ns
        :: (~In "rp" ns)
        :: (~(index = arr))
        :: (~(size = index))
        :: (~(value = index))
        :: (~(value = size))
        :: (~(value = arr))
        :: conditionBound c

        (* Invariants are independent of values of some variables. *)
        :: (forall qs ws all V V',
          (forall x, x <> index -> x <> value -> sel V x = sel V' x)
          -> invPre qs ws all V = invPre qs ws all V')
        :: (forall qs ws V V',
          (forall x, x <> index -> x <> value -> sel V x = sel V' x)
          -> invPost qs ws V = invPost qs ws V')

        (* Precondition implies loop invariant. *)
        :: (forall specs stn st, interp specs (pre (stn, st))
          -> interp specs (Ex qs, ExX, Ex V, Ex ws, qspecOut (invPre qs nil ws (sel V)) (fun PR =>
            ![ ^[locals ("rp" :: ns) V res (Regs st Sp) * array ws (sel V arr) * PR] * #0 ] (stn, st)
            /\ [| sel V size = length ws |]
            /\ (sel V "rp", stn) @@@ (st' ~>
              [| st'#Sp = Regs st Sp |]
              /\ Ex V', qspecOut (invPost qs ws (sel V) st'#Rv) (fun PO =>
                ![ ^[locals ("rp" :: ns) V' res (Regs st Sp) * array ws (sel V arr) * PO] * #1 ] st'))))%PropX)

        (* Loop invariant is preserved on no-op, when the current cell isn't a match. *)
        :: (forall specs stn st V qs ws all this v fr,
          ~satisfies V (length ws) this c
          -> interp specs (![qspecOut' (invPre qs ws all (sel V)) v * fr] (stn, st))
          -> goodSize (S (length ws))
          -> exists v', interp specs (![qspecOut' (invPre qs (ws ++ this :: nil) all (sel V)) v' * fr] (stn, st)))

        (* Postcondition implies loop invariant. *)
        :: (forall specs stn st, interp specs (Postcondition (Body bodyPre) (stn, st))
          -> interp specs (Ex qs, ExX, Ex wsPre, Ex ws, Ex this, Ex V,
            qspecOut (invPre qs (wsPre ++ this :: nil) ws (sel V)) (fun PR =>
              ![ ^[locals ("rp" :: ns) V res (Regs st Sp) * array ws (sel V arr) * PR] * #0 ] (stn, st)
              /\ [| sel V size = length ws /\ sel V index = length wsPre /\ satisfies V (length wsPre) this c |]
              /\ Ex wsPost, [| ws = wsPre ++ this :: wsPost |]
              /\ (sel V "rp", stn) @@@ (st' ~>
                [| st'#Sp = Regs st Sp |]
                /\ Ex V', qspecOut (invPost qs ws (sel V) st'#Rv) (fun PO =>
                  ![ ^[locals ("rp" :: ns) V' res (Regs st Sp) * array ws (sel V arr) * PO] * #1 ] st'))))%PropX)

        (* Conditions of body are satisfied. *)
        :: VerifCond (Body bodyPre))
      _ _); abstract (unfold Query_; case_eq (indexEquals c); [ | case_eq (indexGe c) ]; intros;
        wrap; try enrich; t).
  Defined.

End Query.

Definition ForArray (arr size index value : string) (c : condition) quants invPre invPost (Body : chunk) : chunk :=
  fun ns res => Structured nil (fun _ _ H => Query arr size index value c H (quants := quants) invPre invPost
    (toCmd Body _ H ns res) ns res).

Record aspec := {
  Quants : Type;
  InvPre : Quants -> list W -> list W -> vals -> qspec;
  InvPost : Quants -> list W -> vals -> W -> qspec
}.

Definition aspecBase (invPre : list W -> list W -> vals -> qspec)
  (invPost : list W -> vals -> W -> qspec) : aspec :=
  {| Quants := unit;
    InvPre := (fun _ => invPre);
    InvPost := (fun _ => invPost) |}.

Definition aspecForall A (asp : A -> aspec) : aspec :=
  {| Quants := { x : A & Quants (asp x) };
    InvPre := (fun v => InvPre (asp (projT1 v)) (projT2 v));
    InvPost := (fun v => InvPost (asp (projT1 v)) (projT2 v)) |}.


Notation "'After' ws 'Approaching' full 'PRE' [ V ] pre 'POST' [ R ] post" :=
  (aspecBase (fun ws full V => pre%qspec%Sep) (fun full V R => post%qspec%Sep))
  (at level 89) : aspec_scope.

Notation "'Al' x , asp" := (aspecForall (fun x => asp)) : aspec_scope.

Delimit Scope aspec_scope with aspec.

Notation "[ asp ] 'For' index 'Holding' value 'in' arr 'Size' size 'Where' c { Body }" :=
  (let asp' := asp%aspec in ForArray arr size index value c%ArrayQuery (InvPre asp') (InvPost asp') Body)
  (no associativity, at level 95, index at level 0, value at level 0, arr at level 0, size at level 0,
    c at level 0) : SP_scope.

Ltac for0 := try solve [ intuition (try congruence);
  repeat match goal with
           | [ H : forall x : string, _ |- _ ] => rewrite H by congruence
         end; reflexivity ].

Ltac eta_evar T k :=
  match eval cbv beta in T with
    | unit => k tt
    | @sigT ?A ?F =>
      let x' := fresh in evar (x' : A); let x := eval unfold x' in x' in clear x';
        eta_evar (F x) ltac:(fun v => k (existT F x v))
    | _ =>
      idtac "BYE";
        let x' := fresh in evar (x' : T); let x := eval unfold x' in x' in clear x';
          k x
  end.

Ltac multi_ex :=
  try match goal with
        | [ _ : sigT _ |- _ ] =>
          repeat match goal with
                   | [ x : sigT _ |- _ ] => destruct x
                 end; simpl in *
      end;
  try match goal with
        | [ |- @Logic.ex ?T _ ] =>
          match T with
            | sigT _ => eta_evar T ltac:(fun v => exists v; simpl)
          end
      end.
