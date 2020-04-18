Require Import Bedrock.Bedrock Bedrock.Platform.PreAutoSep.


Import DefineStructured.

Section Wrap.
  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Variable body : cmd imports modName.
  Variable postcondition : assert -> assert.
  Variable verifCond : assert -> list Prop.

  Hypothesis postcondition_ok : forall pre specs x,
    vcs (verifCond pre)
    -> interp specs ((body pre).(Postcondition) x)
    -> interp specs (postcondition pre x).

  Hypothesis verifCond_ok : forall pre,
    vcs (verifCond pre)
    -> vcs (body pre).(VerifCond).

  Hint Extern 1 (_ < _)%N => nomega.
  Hint Extern 1 (not (@eq LabelMap.key _ _)) => lomega.
  Hint Extern 1 (@eq LabelMap.key _ _ -> False) => lomega.
  Hint Extern 1 (LabelMap.MapsTo _ _ _) => apply imps_exit.

  Transparent evalInstrs.

  Definition Wrap : cmd imports modName.
    red; refine (fun pre =>
      let cout := body pre in
      {|
        Postcondition := postcondition pre;
        VerifCond := verifCond pre;
        Generate := fun Base Exit =>
        let cg := cout.(Generate) (Nsucc Base) Base in
          {|
            Entry := Nsucc cg.(Entry);
            Blocks := (cout.(Postcondition),
              (nil, Uncond (RvLabel (modName, Local Exit))))
            :: cg.(Blocks)
          |}
      |}); abstract (struct;
        match goal with
          | [ H : forall k' : LabelMap.key, _
              |- context[Labels _ ?k]  ] =>
            edestruct (H k) as [ ? [ ] ]; eauto;
              match goal with
                | [ H : _ = _ |- _ ] => solve [ rewrite H; eauto 6 ]
              end
          | [ |- context[LabelMap.add (_, Local ?Base) _ _] ] =>
            assert (Base < N.succ Base)%N by nomega;
              match goal with
                | [ H : vcs _ |- _ ] => apply verifCond_ok in H
              end; intuition struct
        end).
  Defined.

End Wrap.


(** * A simpler combinator, for [chunk]-level programs with explicit invariants ahoy *)

Section WrapC.
  Variable body : chunk.

  Definition assertC := bool
    -> (W -> W)
    -> list string
    -> nat
    -> assert.

  Variables precondition postcondition : assertC.
  Variable verifCond : LabelMap.t assert -> list string -> nat -> list Prop.

  Hypothesis postcondition_covered : forall im mn H ns res pre specs st,
    (forall specs st, interp specs (pre st)
      -> interp specs (precondition true (fun x => x) ns res st))
    -> vcs (verifCond im ns res)
    -> interp specs ((toCmd body (im := im) mn H ns res pre).(Postcondition) st)
    -> interp specs (postcondition true (fun x => x) ns res st).

  Hypothesis verifCond_covered : forall im mn H ns res pre,
    (forall specs st, interp specs (pre st) -> interp specs (precondition true (fun x => x) ns res st))
    -> vcs (verifCond im ns res)
    -> vcs ((toCmd body (im := im) mn H ns res pre).(VerifCond)).

  Definition WrapC : chunk.
    red; refine (fun ns res => Structured nil
      (fun im mn H => Wrap im H mn (toCmd body mn H ns res)
        (fun _ => postcondition true (fun x => x) ns res)
        (fun pre => (forall specs st, interp specs (pre st) -> interp specs (precondition true (fun x => x) ns res st)) :: verifCond im ns res)
        _ _)); abstract struct.
  Defined.
End WrapC.


(** * Some tactics useful in clients of [Wrap] *)

Require Import Bedrock.sep.Locals.

Lemma four_plus_variablePosition : forall x ns',
  ~In "rp" ns'
  -> In x ns'
  -> 4 + variablePosition ns' x = variablePosition ("rp" :: ns') x.
  unfold variablePosition at 2; intros.
  destruct (string_dec "rp" x); auto; subst; tauto.
Qed.

Ltac prep_locals :=
  unfold variableSlot in *; repeat rewrite four_plus_variablePosition in * by assumption;
    repeat match goal with
             | [ H : In ?X ?ls |- _ ] =>
               match ls with
                 | "rp" :: _ => fail 1
                 | _ =>
                   match goal with
                     | [ _ : In X ("rp" :: ls) |- _ ] => fail 1
                     | _ => assert (In X ("rp" :: ls)) by (simpl; tauto)
                   end
               end
           end.

Ltac clear_fancy := repeat match goal with
                             | [ H : importsGlobal _ |- _ ] => clear H
                             | [ H : vcs _ |- _ ] => clear H
                           end.

Ltac wrap0 :=
  intros;
    repeat match goal with
             | [ H : vcs nil |- _ ] => clear H
             | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; intros; subst
             | [ H : vcs (_ ++ _) |- _ ] => specialize (vcs_app_bwd1 _ _ H);
               specialize (vcs_app_bwd2 _ _ H); clear H; intros
           end; simpl;
    repeat match goal with
             | [ |- vcs nil ] => constructor
             | [ |- vcs (_ :: _) ] => constructor
             | [ |- vcs (_ ++ _) ] => apply vcs_app_fwd
           end; propxFo;
    try match goal with
          | [ H : forall stn : settings, _, H' : interp _ _ |- _ ] =>
            specialize (H _ _ _ H')
        end.

Ltac wrap1 := prep_locals; auto; clear_fancy.

Ltac app := match goal with
              | [ H : _, H' : ?P |- _ ] => apply H in H';
                try match goal with
                      | [ H' : P |- _ ] => clear H'
                    end
            end.

Ltac handle_IH :=
  try match goal with
        | [ H : importsGlobal _ |- _ ] =>
          match goal with
            | [ IH : context[H] |- _ ] => clear H IH
            | _ => clear H
          end
      end.

Ltac simp := post; unfold lvalIn, regInL, immInR in *; clear_fancy; prep_locals.

Ltac finish := descend; repeat (step auto_ext; descend); descend; step auto_ext.


(** * Useful facts about instruction sequences not changing parts of machine state *)

Fixpoint scratchOnly (is : list instr) : Prop :=
  match is with
    | nil => True
    | Assign (LvReg r) _ :: is' => r <> Sp /\ scratchOnly is'
    | Binop (LvReg r) _ _ _ :: is' => r <> Sp /\ scratchOnly is'
    | _ => False
  end.

Ltac matcher := repeat match goal with
                         | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
                           match E with
                             | context[match _ with None => _ | _ => _ end] => fail 1
                             | _ => destruct E; try discriminate
                           end
                         | [ |- context[match ?E with None => _ | _ => _ end] ] =>
                           match E with
                             | context[match _ with None => _ | _ => _ end] => fail 1
                             | _ => destruct E; try discriminate
                           end
                       end.

Transparent evalInstrs.

Theorem scratchOnlySp : forall stn st' is st,
  scratchOnly is
  -> evalInstrs stn st is = Some st'
  -> Regs st' Sp = Regs st Sp.
  induction is as [ | [ [ ] | [ ] ] ]; simpl; intuition; matcher; try congruence;
    erewrite IHis by eassumption; apply rupd_ne; auto.
Qed.

Theorem scratchOnlyMem : forall stn st' is st,
  scratchOnly is
  -> evalInstrs stn st is = Some st'
  -> Mem st' = Mem st.
  induction is as [ | [ [ ] | [ ] ] ]; simpl; intuition; matcher; try congruence;
    erewrite IHis by eassumption; reflexivity.
Qed.

Theorem sepFormula_Mem : forall specs stn st st' P,
  interp specs (![P] (stn, st))
  -> Mem st' = Mem st
  -> interp specs (![P] (stn, st')).
  rewrite sepFormula_eq; unfold sepFormula_def; simpl; intros; congruence.
Qed.

Fixpoint spless (is : list instr) : Prop :=
  match is with
    | nil => True
    | Assign (LvReg r) _ :: is' => r <> Sp /\ spless is'
    | Binop (LvReg r) _ _ _ :: is' => r <> Sp /\ spless is'
    | _ :: is' => spless is'
  end.

Theorem splessSp : forall stn st' is st,
  spless is
  -> evalInstrs stn st is = Some st'
  -> Regs st' Sp = Regs st Sp.
  induction is as [ | [ [ ] | [ ] ] ]; simpl; intuition; matcher; try congruence;
    erewrite IHis by eassumption; simpl; try rewrite rupd_ne by auto; auto.
Qed.

Theorem spless_app : forall is1 is2,
  spless is1
  -> spless is2
  -> spless (is1 ++ is2).
  induction is1 as [ | [ ] ]; simpl; intuition;
    destruct l; intuition.
Qed.

Lemma evalInstrs_app_fwd_None : forall stn is2 is1 st,
  evalInstrs stn st (is1 ++ is2) = None
  -> evalInstrs stn st is1 = None
  \/ (exists st', evalInstrs stn st is1 = Some st' /\ evalInstrs stn st' is2 = None).
  induction is1; simpl; intuition eauto.
  destruct (evalInstr stn st a); eauto.
Qed.

Lemma evalInstrs_app_fwd : forall stn is2 st' is1 st,
  evalInstrs stn st (is1 ++ is2) = Some st'
  -> exists st'', evalInstrs stn st is1 = Some st''
    /\ evalInstrs stn st'' is2 = Some st'.
  induction is1; simpl; intuition eauto.
  destruct (evalInstr stn st a); eauto; discriminate.
Qed.

Lemma evalInstr_evalInstrs : forall stn st i,
  evalInstr stn st i = evalInstrs stn st (i :: nil).
  simpl; intros; destruct (evalInstr stn st i); auto.
Qed.

Lemma evalAssign_rhs : forall stn st lv rv rv',
  evalRvalue stn st rv = evalRvalue stn st rv'
  -> evalInstr stn st (Assign lv rv) = evalInstr stn st (Assign lv rv').
  simpl; intros.
  rewrite H; reflexivity.
Qed.
