Require Import Coq.omega.Omega.
Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT Bedrock.Platform.Cito.RepInv.
Require Import Bedrock.Platform.AutoSep.


Module Make (Import E : ADT) (Import M : RepInv E).
  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Make E.
  Require Import Coq.Lists.List.

  Require Import Bedrock.Platform.Cito.Link.
  Module Import LinkMake := Make E M.

  Import StubsMake StubMake ConvertLabelMap GoodModule GoodOptimizer.
  Import LinkSpecMake LinkSpecMake2.
  Require Import Bedrock.Platform.Cito.SemanticsUtil.

  Definition wrapper_module mname impls (fs : list (string * ForeignFuncSpec * nat * label)) :=
    StructuredModule.bmodule_ impls
    (map (fun (p : string * ForeignFuncSpec * nat * label) => let '(name, ffs, n, delegate) := p in
      (name, foreign_func_spec (mname, name) ffs,
        fun im im_g =>
          Structured.If_ im_g (LvMem (Sp + 4)%loc) IL.Lt n
          (Structured.Goto_ im_g mname ("sys"!"abort")%SP)
          (Structured.Goto_ im_g mname delegate))) fs).

  Notation "'ffunction' name 'reserving' n [ ffs ] := lab" :=
    (name, ffs, n, lab%SP) (no associativity, at level 95) : ffuncs_scope.
  Delimit Scope ffuncs_scope with ffuncs.

  Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : ffuncs_scope.

  Notation "'bimport' is 'fmodule' name fs" := (wrapper_module name is%SPimps fs%ffuncs)
    (no associativity, at level 95, name at level 0, only parsing).

  Lemma pure_split : forall P Q R,
    (forall specs sm m, interp specs (P sm m ---> [|Q|]))%PropX
    -> P ===> R
    -> P ===> [|Q|] * R.
    intros; do 3 intro.
    apply existsR with smem_emp.
    apply existsR with m0.
    apply andR.
    apply injR.
    apply split_a_semp_a.
    apply andR.
    eapply Imply_trans; [ apply H | ].
    apply injL; propxFo.
    reflexivity.
    apply H0.
  Qed.

  Lemma pure_extend : forall P Q R,
    P ===> [|Q|] * any
    -> [|Q|] * P ===> R
    -> P ===> R.
    intros; do 3 intro.
    eapply Imply_trans; [ | apply H0 ].
    apply pure_split; try apply Himp_refl; intros.
    unfold Himp, himp, injB, inj in H.
    eapply Imply_trans; [ apply H | ].
    do 2 (apply existsL; intro).
    repeat (apply andL || (apply injL; intro)).
    apply Inj_I; auto.
  Qed.

  Import CompileFuncSpecMake.InvMake2 Inv Malloc CompileFuncSpecMake.InvMake SemanticsMake.

  Fixpoint zip_vals (args : list string) (pairs : list (W * ArgIn)) : vals :=
    match args, pairs with
      | arg :: args, (w, _) :: pairs => upd (zip_vals args pairs) arg w
      | _, _ => empty_vs
    end.

  Ltac selify :=
    repeat match goal with
             | [ |- context[upd ?a ?b ?c ?d] ] => change (upd a b c d) with (sel (upd a b c) d)
           end; autorewrite with sepFormula.

  Lemma toArray_dontcare : forall x v vs args,
    ~In x args
    -> toArray args (upd vs x v) = toArray args vs.
    induction args; simpl; intuition idtac.
    f_equal; auto.
    selify; auto.
  Qed.

  Hint Rewrite toArray_dontcare using assumption : sepFormula.

  Lemma unzip : forall args,
    NoDup args
    -> forall pairs, length args = length pairs
      -> toArray args (zip_vals args pairs) = map fst pairs.
    induction 1; destruct pairs; simpl; intuition.
    f_equal; auto; selify; auto.
  Qed.

  Hint Rewrite unzip using assumption : sepFormula.

  Opaque mult.

  Fixpoint saved_vars vs args (pairs : list (W * ArgIn)) :=
    match args, pairs with
      | arg :: args, (w, _) :: pairs => sel vs arg = w /\ saved_vars vs args pairs
      | _, _ => True
    end.

  Lemma zig : forall P Q R,
    P ===> R * any
    -> P * Q ===> R * any.
    intros.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply H | apply Himp_refl ] | ].
    eapply Himp_trans; [ apply Himp_star_assoc | ].
    apply Himp_star_frame; try apply Himp_refl.
    apply any_easy.
  Qed.

  Lemma zag : forall P Q R,
    Q ===> R * any
    -> P * Q ===> R * any.
    intros.
    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_refl | apply H ] | ].
    eapply Himp_trans; [ apply Himp_star_assoc' | ].
    eapply Himp_trans; [ apply Himp_star_frame; [ apply Himp_star_comm | apply Himp_refl ] | ].
    eapply Himp_trans; [ apply Himp_star_assoc | ].
    apply Himp_star_frame; try apply Himp_refl.
    apply any_easy.
  Qed.

  Lemma saved_vars_irrel : forall x v args pairs vs,
    saved_vars vs args pairs
    -> ~In x args
    -> saved_vars (upd vs x v) args pairs.
    induction args; destruct pairs; simpl; intuition.
    rewrite sel_upd_ne; auto.
  Qed.

  Lemma saved_vars_zip_vars : forall args,
    NoDup args
    -> forall pairs, saved_vars (zip_vals args pairs) args pairs.
    induction 1; destruct pairs; simpl; intuition.
    apply sel_upd_eq; auto.
    apply saved_vars_irrel; auto.
  Qed.

  Theorem is_state_out : forall sp rp e_stack args pairs,
    NoDup args
    -> ~In "rp" args
    -> ~In "extra_stack" args
    -> length args = length pairs
    -> is_state sp rp e_stack e_stack nil (empty_vs, make_heap pairs) (map fst pairs)
    ===> Ex vs, locals ("rp" :: "extra_stack" :: args) vs (wordToNat (sel vs "extra_stack")) sp
    * is_heap (make_heap pairs) * [| e_stack = wordToNat (sel vs "extra_stack") |]
    * [| saved_vars vs args pairs |].
    unfold is_state, locals, has_extra_stack; simpl.
    intros.
    apply Himp_ex_c.
    exists (upd (upd (zip_vals args pairs) "extra_stack" e_stack) "rp" rp).
    selify.
    replace (S (S (length args)) * 4) with (8 + 4 * length args) by omega.
    rewrite map_length.
    rewrite <- H2.
    rewrite natToWord_plus.
    eapply Himp_trans; [ | do 4 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply ptsto32m'_out ] ].
    simpl.
    unfold ArgIn.
    generalize (map fst pairs); intro.
    unfold array at 1; simpl.
    apply pure_extend with (goodSize e_stack).

    do 2 apply zag.
    do 3 intro.
    eapply existsR with smem_emp; apply existsR with m.
    apply andR.
    apply injR.
    apply split_a_semp_a.
    apply andR.
    apply andR.
    eapply Imply_trans; [ apply SepHints.behold_the_array_ls | ].
    do 3 (apply existsL; intro).
    repeat (apply andL || (apply injL; intro)).
    rewrite <- H4.
    apply containsArray_goodSizex'; eauto.
    apply injR; reflexivity.
    apply any_easy.
    apply Himp_star_pure_c; intro; subst.

    sepLemma.
    repeat constructor; simpl; intuition.
    symmetry; apply wordToNat_natToWord_idempotent; auto.

    do 2 (apply saved_vars_irrel; auto).

    eauto using saved_vars_zip_vars.

    etransitivity; [ apply himp_star_comm | ].
    apply himp_star_frame.
    etransitivity; [ | apply Arrays.ptsto32m'_in ].
    etransitivity; [ | apply ptsto32m_shift_base ].
    unfold array.
    instantiate (1 := 8).
    simpl.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    reflexivity.
    auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    rewrite wordToNat_natToWord_idempotent by auto.
    sepLemma.
  Qed.

  Lemma locals_for_abort : forall res (k : nat) vars vs sp,
    res < natToW k
    -> locals ("rp" :: vars) vs (wordToNat res) sp
    ===> locals ("rp" :: nil) vs 0 sp * any.
    unfold locals; simpl.
    intros.

    apply Himp_trans with ([|NoDup ("rp" :: vars)|] * ptsto32m' _ sp 0 (vs "rp" :: toArray vars vs) *
      (sp ^+ $ (S (Datatypes.length vars) * 4)) =?> wordToNat res)%Sep.
    repeat (apply Himp_star_frame; try apply Himp_refl).
    apply Arrays.ptsto32m'_in.
    unfold array; simpl.
    change (vs "rp") with (sel vs "rp").
    sepLemma.
    apply any_easy.
  Qed.

  Lemma locals_for_method : forall res (k : nat) vars vs sp,
    natToW k <= res
    -> goodSize k
    -> locals vars vs (wordToNat res) sp
    ===> locals vars vs k sp * (sp ^+ $ ((length vars + k) * 4)) =?> (wordToNat res - k).
    unfold locals; simpl.
    sepLemma.
    etransitivity; [ eapply allocated_split | sepLemma ].
    nomega.
    eapply allocated_shift_base; auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    replace (length vars * 4 + 4 * k) with ((length vars + k) * 4) by omega.
    unfold natToW.
    words.
  Qed.

  Theorem is_state_in : forall vs sp args e_stack h,
    locals ("rp" :: "extra_stack" :: args) vs e_stack sp
    * is_heap h
    ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack nil
    (vs, h) (toArray args vs).
    unfold is_state, locals, has_extra_stack; simpl.
    intros.
    change (vs "rp") with (sel vs "rp").
    change (vs "extra_stack") with (sel vs "extra_stack").
    replace (S (S (length args)) * 4) with (8 + 4 * length args) by omega.
    rewrite natToWord_plus.
    rewrite length_toArray.
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply Arrays.ptsto32m'_in ] | ].
    simpl.
    unfold array at 1; simpl.
    sepLemma.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    unfold natToW; rewrite natToWord_wordToNat.
    sepLemma.
    etransitivity; [ apply ptsto32m'_out | ].
    unfold array; etransitivity; [ apply ptsto32m_shift_base' | ].
    instantiate (1 := 8); auto.
    simpl.
    change (4 * 0) with 0.
    sepLemma.
  Qed.

  Module Hints := InvFacts.Make(E).
  Module Export Inner := Hints.Make(M).

  Lemma extra_back_in : forall k vars sp res vs,
    natToW k <= res
    -> goodSize k
    -> (sp ^+ natToW ((k + length vars) * 4)) =?> (wordToNat res - k) * locals vars vs k sp
    ===> locals vars vs (wordToNat res) sp.
    unfold locals; sepLemma.
    etransitivity; [ | eapply allocated_join ]; sepLemma.
    eapply allocated_shift_base; auto.
    repeat rewrite <- wplus_assoc.
    repeat rewrite <- natToWord_plus.
    do 2 f_equal.
    omega.
    nomega.
  Qed.

  Lemma store_pair_inl_fwd : forall h w v,
    is_heap (store_pair h (w, SCA _ v)) ===> is_heap h.
    intros; apply Himp_refl.
  Qed.

  Lemma store_pair_inl_bwd : forall h w v,
    is_heap h ===> is_heap (store_pair h (w, SCA _ v)).
    intros; apply Himp_refl.
  Qed.

  Import WordMap LayoutHintsUtil.
  Require Import Coq.FSets.FMapFacts.
  Module Properties := Properties WordMap.
  Module Facts := Facts WordMap.
  Require Import Bedrock.Platform.Cito.SemanticsFacts5.

  Lemma store_pair_inr_fwd : forall h w v,
    ~WordMap.In w h
    -> is_heap (store_pair h (w, ADT v)) ===> rep_inv w v * is_heap h.
    unfold store_pair; simpl.
    intros.
    unfold is_heap at 1.
    assert (In (w, v) (heap_elements (heap_upd h w v))).
    apply InA_In.
    apply WordMap.elements_1.
    apply Properties.F.add_mapsto_iff; auto.
    eapply starL_out in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
    destruct H0; intuition idtac.
    eapply Himp_trans; [ apply H1 | ]; clear H1.
    simpl.
    apply Himp_star_frame; try apply Himp_refl.
    apply starL_permute; auto.
    apply NoDupA_NoDup; apply WordMap.elements_3w.
    intuition.
    apply H3 in H1; intuition idtac.
    apply In_InA' in H4.
    apply WordMap.elements_2 in H4.
    apply Properties.F.add_mapsto_iff in H4; intuition subst.
    tauto.
    apply InA_In; apply WordMap.elements_1; auto.
    apply H3.
    intuition.
    injection H2; clear H2; intros; subst.
    apply In_InA' in H1.
    apply WordMap.elements_2 in H1.
    apply H.
    eexists; eauto.
    apply InA_In.
    apply WordMap.elements_1.
    apply WordMap.add_2; auto.
    intro; subst.
    apply In_InA' in H1.
    apply WordMap.elements_2 in H1.
    apply H; eexists; eauto.
    apply In_InA' in H1.
    apply WordMap.elements_2 in H1.
    auto.
  Qed.

  Lemma store_pair_inr_bwd : forall h w v,
    ~WordMap.In w h
    -> rep_inv w v * is_heap h ===> is_heap (store_pair h (w, ADT v)).
    unfold store_pair; simpl.
    intros.
    unfold is_heap at 2.
    assert (In (w, v) (heap_elements (heap_upd h w v))).
    apply InA_In.
    apply WordMap.elements_1.
    apply Properties.F.add_mapsto_iff; auto.
    eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
    destruct H0; intuition idtac.
    eapply Himp_trans; [ | apply H1 ]; clear H1.
    simpl.
    apply Himp_star_frame; try apply Himp_refl.
    apply starL_permute; auto.
    apply NoDupA_NoDup; apply WordMap.elements_3w.
    intuition.
    apply H3; intuition.
    injection H2; clear H2; intros; subst.
    apply In_InA' in H1.
    apply WordMap.elements_2 in H1.
    apply H; eexists; eauto.
    apply InA_In.
    apply WordMap.elements_1.
    apply WordMap.add_2; auto.
    intro; subst.
    apply In_InA' in H1.
    apply WordMap.elements_2 in H1.
    apply H; eexists; eauto.
    apply In_InA' in H1.
    apply WordMap.elements_2 in H1.
    auto.
    apply H3 in H1; intuition.
    apply In_InA' in H4.
    apply WordMap.elements_2 in H4.
    apply Properties.F.add_mapsto_iff in H4; intuition subst.
    tauto.
    apply InA_In; apply WordMap.elements_1; auto.
  Qed.

  Lemma not_in_empty : forall w,
    ~WordMap.In w heap_empty.
    do 2 intro.
    apply Facts.empty_in_iff in H; tauto.
  Qed.

  Lemma not_in_heap_upd : forall w h w' v,
    w' <> w
    -> ~WordMap.In w h
    -> ~WordMap.In w (heap_upd h w' v).
    intros; intro.
    apply Facts.add_in_iff in H1; intuition idtac.
  Qed.

  Ltac prove_not_in := repeat (simpl; congruence || apply not_in_empty || apply not_in_heap_upd).

  Hint Extern 1 (~In _ _) => simpl; intuition congruence.

  Ltac do_abort argNames :=
    post; repeat match goal with
                   | [ H : nil = nil |- _ ] => clear H
                   | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
                   | [ H : snd ?E = _ |- _ ] => destruct E; simpl in *; subst
                   | [ H : map snd ?X = _ |- _ ] => destruct X; simpl in *; try discriminate
                 end;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 2 (eapply Himp_star_frame; [ | apply Himp_refl ]);
          apply is_state_out; [ instantiate (1 := argNames); auto | .. ]; solve [ auto ] ]
    end;
    evaluate auto_ext;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 3 (apply Himp_star_frame; [ apply Himp_refl | ]);
          apply Himp_star_frame; [ eapply locals_for_abort; eassumption | apply Himp_refl ] ]
    end; descend; step auto_ext.

  Lemma Regs_back : forall s : state, (let (Regs, _) := s in Regs) = Regs s.
    auto.
  Qed.

  Ltac add_side_conditions' E :=
    match E with
      | store_pair ?h (?k, ?v) =>
        match v with
        | ADT _ =>
          assert (~WordMap.In k h) by prove_not_in
        | _ => idtac
        end; add_side_conditions' h
      | _ => idtac
    end.

  Ltac add_side_conditions :=
    match goal with
      | [ |- himp _ ?lhs ?rhs ] =>
        try match lhs with
              | context[is_heap ?h] => add_side_conditions' h
            end;
        try match rhs with
              | context[is_heap ?h] => add_side_conditions' h
            end
    end.

  Ltac use_arg_facts :=
    unfold disjoint_ptrs, Semantics.disjoint_ptrs, good_scalars, word_scalar_match in *;
      simpl in *;
        repeat (match goal with
                  | [ H : NoDup _ |- _ ] => inversion_clear H
                  | [ H : List.Forall _ _ |- _ ] => inversion_clear H
                end; simpl in *; intuition subst);
        repeat match goal with
                 | [ H : True |- _ ] => clear H
                 | [ H : False -> False |- _ ] => clear H
                 | [ H : ?x = ?x |- _ ] => clear H
               end.

  Ltac do_delegate1 argNames hints :=
    post; repeat match goal with
                   | [ H : nil = nil |- _ ] => clear H
                   | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
                   | [ H : snd ?E = _ |- _ ] => destruct E; simpl in *; subst
                   | [ H : map snd ?X = _ |- _ ] => destruct X; simpl in *; try discriminate
                 end;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 2 (eapply Himp_star_frame; [ | apply Himp_refl ]);
          apply is_state_out; [ instantiate (1 := argNames); auto | .. ]; solve [ auto ] ]
    end;
    evaluate auto_ext;
    match goal with
      | [ H : interp _ _ |- _ ] => eapply CompileExprs.change_hyp in H; [ |
        do 3 (apply Himp_star_frame; [ apply Himp_refl | ]);
          apply Himp_star_frame; [ eapply locals_for_method; eassumption || reflexivity | apply Himp_refl ] ]
    end; simpl in *; intuition subst;
    descend; [ step auto_ext; try solve [ use_arg_facts; eauto ]; unfold make_heap; simpl; add_side_conditions; step hints | .. ];
    (simpl; step auto_ext); use_arg_facts.

  Ltac make_toArray argNames :=
    match goal with
      | [ |- context[locals _ ?vs _ _] ] =>
        match goal with
          | [ |- context[is_state _ _ _ _ _ _ ?ls ] ] =>
            replace ls with (toArray argNames vs) by reflexivity
        end
    end.

  Ltac do_delegate2 argNames := use_arg_facts;
    simpl; try rewrite Regs_back; step auto_ext;
      match goal with
        | [ _ : natToW ?k <= _ |- _ ] => apply (@extra_back_in k ("rp" :: "extra_stack" :: argNames)); auto
      end.

  Ltac unfolder := unfold store_out, Semantics.store_out, make_heap, store_pair; simpl.

  Ltac do_delegate argNames tac :=
    do_delegate1 argNames; [ | tac ]; cbv beta; do_delegate2 argNames.

  Ltac wrapper1 argNames tac :=
    do_abort argNames || do_delegate argNames tac.

  Ltac wrapper argNames tac := vcgen; wrapper1 argNames tac.

  Ltac returnScalar1 :=
    match goal with
      | [ |- Regs ?a ?b = fst (decide_ret ?X ?Y) ] =>
        let w := fresh "w" in evar (w : W); let w' := eval unfold w in w in clear w;
          equate X (Regs a b); equate Y (@SCA ADTValue w'); reflexivity
    end.

  Ltac returnAdt1 :=
    match goal with
      | [ |- Regs ?a ?b = fst (decide_ret ?X ?Y) ] =>
        let a := fresh "a" in evar (a : ADTValue); let a' := eval unfold a in a in clear a;
          equate X (Regs a b); equate Y (ADT a'); reflexivity
    end.

  Ltac returnSomething := intuition; (cbv beta; simpl;
    repeat match goal with
             | [ |- @length ?A ?ls = O ] => equate ls (@nil A); reflexivity
             | [ |- @length ?A ?ls = S _ ] =>
               let x := fresh in let y := fresh in evar (x : A); evar (y : list A);
                 equate ls (x :: y); subst x y; simpl; f_equal
           end).

  Ltac returnScalar := returnSomething; (cbv beta; returnScalar1 || eauto).
  Ltac returnAdt := returnSomething; (cbv beta; returnAdt1 || eauto).
End Make.
