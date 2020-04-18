Require Import Coq.omega.Omega.
Require Import Coq.Strings.Ascii Coq.Bool.Bool Coq.Strings.String Coq.Lists.List.
Require Import Bedrock.Word Bedrock.Memory Bedrock.Expr Bedrock.SepExpr Bedrock.SymEval Bedrock.SepIL Bedrock.Env Bedrock.Prover Bedrock.SymEval Bedrock.IL Bedrock.SymIL.
Require Import Bedrock.sep.Array.
Require Import Bedrock.Allocated.
Require Import Bedrock.ListFacts.

Set Implicit Arguments.

Definition vals := string -> W.

Definition toArray (ns : list string) (vs : vals) : list W := map vs ns.

Definition locals (ns : list string) (vs : vals) (avail : nat) (p : W) : HProp :=
  ([| NoDup ns |] * array (toArray ns vs) p * ((p ^+ $ (length ns * 4)) =?> avail))%Sep.

Definition ascii_eq (a1 a2 : ascii) : bool :=
  let (b1, c1, d1, e1, f1, g1, h1, i1) := a1 in
  let (b2, c2, d2, e2, f2, g2, h2, i2) := a2 in
    eqb b1 b2 && eqb c1 c2 && eqb d1 d2 && eqb e1 e2
    && eqb f1 f2 && eqb g1 g2 && eqb h1 h2 && eqb i1 i2.

Lemma ascii_eq_true : forall a,
  ascii_eq a a = true.
Proof.
  destruct a; simpl; intuition.
  repeat rewrite eqb_reflx; reflexivity.
Qed.

Lemma ascii_eq_false : forall a b,
  a <> b -> ascii_eq a b = false.
  destruct b, a; simpl; intuition.
  match goal with
    | [ |- ?E = _ ] => case_eq E
  end; intuition.
    repeat match goal with
             | [ H : _ |- _ ] => apply andb_prop in H; destruct H
             | [ H : _ |- _ ] => apply eqb_prop in H
           end; congruence.
Qed.

Fixpoint string_eq (s1 s2 : string) : bool :=
  match s1, s2 with
    | EmptyString, EmptyString => true
    | String a1 s1', String a2 s2' => ascii_eq a1 a2 && string_eq s1' s2'
    | _, _ => false
  end.

Theorem string_eq_true : forall s,  string_eq s s = true.
Proof.
  induction s; simpl; intuition; rewrite ascii_eq_true; assumption.
Qed.

Theorem string_eq_false : forall s1 s2,
  s1 <> s2 -> string_eq s1 s2 = false.
  induction s1; destruct s2; simpl; intuition.
  match goal with
    | [ |- ?E = _ ] => case_eq E
  end; intuition.
  repeat match goal with
           | [ H : _ |- _ ] => apply andb_prop in H; destruct H
           | [ H : _ |- _ ] => apply eqb_prop in H
         end.
  destruct (ascii_dec a a0); subst.
  destruct (string_dec s1 s2); subst.
  tauto.
  apply IHs1 in n; congruence.
  apply ascii_eq_false in n; congruence.
Qed.

Theorem string_eq_correct : forall s1 s2,
  string_eq s1 s2 = true -> s1 = s2.
Proof.
  intros; destruct (string_dec s1 s2); subst; auto.
  apply string_eq_false in n; congruence.
Qed.

Definition sel (vs : vals) (nm : string) : W := vs nm.
Definition upd (vs : vals) (nm : string) (v : W) : vals := fun nm' =>
  if string_eq nm' nm then v else vs nm'.

Definition bedrock_type_string : type :=
  {| Impl := string
   ; Eqb := string_eq
   ; Eqb_correct := string_eq_correct |}.

Definition bedrock_type_listString : type :=
  {| Impl := list string
   ; Eqb := (fun _ _ => false)
   ; Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition bedrock_type_vals : type :=
  {| Impl := vals
   ; Eqb := (fun _ _ => false)
   ; Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition types_r : Env.Repr type :=
  Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
    let lst :=
      (@Some type ILEnv.bedrock_type_W) ::
      (@Some type ILEnv.bedrock_type_setting_X_state) ::
      None ::
      None ::
      (@Some type ILEnv.bedrock_type_nat) ::
      None ::
      (@Some type bedrock_type_string) ::
      (@Some type bedrock_type_listString) ::
      (@Some type bedrock_type_vals) ::
      nil
    in Env.listOptToRepr lst EmptySet_type.

Local Notation "'pcT'" := (tvType 0).
Local Notation "'stT'" := (tvType 1).
Local Notation "'wordT'" := (tvType 0).
Local Notation "'natT'" := (tvType 4).
Local Notation "'stringT'" := (tvType 6).
Local Notation "'listStringT'" := (tvType 7).
Local Notation "'valsT'" := (tvType 8).

Definition badLocalVariable := O.
Global Opaque badLocalVariable.

Fixpoint variablePosition (ns : list string) (nm : string) : nat :=
  match ns with
    | nil => badLocalVariable
    | nm' :: ns' => if string_dec nm' nm then O
      else 4 + variablePosition ns' nm
  end.

Local Notation "'wplusF'" := 0.
Local Notation "'wmultF'" := 2.
Local Notation "'natToWF'" := 5.
Local Notation "'nilF'" := 9.
Local Notation "'consF'" := 10.
Local Notation "'selF'" := 11.
Local Notation "'updF'" := 12.
Local Notation "'InF'" := 13.
Local Notation "'variablePositionF'" := 14.

Section parametric.
  Variable types' : list type.
  Definition types := repr types_r types'.
  Variable Prover : ProverT types.

  Definition nil_r : signature types.
    refine {| Domain := nil; Range := listStringT |}.
    exact (@nil _).
  Defined.

  Definition cons_r : signature types.
    refine {| Domain := stringT :: listStringT :: nil; Range := listStringT |}.
    exact (@cons _).
  Defined.

  Definition sel_r : signature types.
    refine {| Domain := valsT :: stringT :: nil; Range := wordT |}.
    exact sel.
  Defined.

  Definition upd_r : signature types.
    refine {| Domain := valsT :: stringT :: wordT :: nil; Range := valsT |}.
    exact upd.
  Defined.

  Definition In_r : signature types.
    refine {| Domain := stringT :: listStringT :: nil; Range := tvProp |}.
    exact (@In _).
  Defined.

  Definition variablePosition_r : signature types.
    refine {| Domain := listStringT :: stringT :: nil; Range := natT |}.
    exact variablePosition.
  Defined.

  Definition funcs_r : Env.Repr (signature types) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
      let lst :=
        Some (ILEnv.wplus_r types) ::
        None ::
        Some (ILEnv.wmult_r types) ::
        None ::
        None ::
        Some (ILEnv.natToW_r types) ::
        None ::
        None ::
        None ::
        Some nil_r ::
        Some cons_r ::
        Some sel_r ::
        Some upd_r ::
        Some In_r ::
        Some variablePosition_r ::
        nil
      in Env.listOptToRepr lst (Default_signature _).

  Inductive deref_res :=
  | Nothing : deref_res
  | Constant : expr types -> nat -> deref_res
  | Symbolic : expr types -> expr types -> expr types -> deref_res.
  (* Last one's args: base, variable list, and specific variable name *)

  Definition deref (e : expr types) : deref_res :=
    match e with
      | Func wplusF (base :: offset :: nil) =>
        match offset with
          | Func natToWF (Const t k :: nil) =>
            match t return tvarD types t -> _ with
              | natT => fun k => match div4 k with
                                   | None => Nothing
                                   | Some k' => Constant base k'
                                 end
              | _ => fun _ => Nothing
            end k

          | Func natToWF (Func variablePositionF (xs :: x :: nil) :: nil) => Symbolic base xs x

          | _ => Nothing
        end

      | _ => Nothing
    end.

  Fixpoint listIn (e : expr types) : option (list string) :=
    match e with
      | Func nilF nil => Some nil
      | Func consF (Const tp s :: t :: nil) =>
        match tp return tvarD types tp -> option (list string) with
          | stringT => fun s => match listIn t with
                                  | None => None
                                  | Some t => Some (s :: t)
                                end
          | _ => fun _ => None
        end s
      | _ => None
    end.

  Fixpoint sym_sel (vs : expr types) (nm : string) : expr types :=
    match vs with
      | Func updF (vs' :: Const tp nm' :: v :: nil) =>
        match tp return tvarD types tp -> expr types with
          | stringT => fun nm' =>
            if string_eq nm' nm
              then v
              else sym_sel vs' nm
          | _ => fun _ => Func selF (vs :: Const (types := types) (t := stringT) nm :: nil)
        end nm'
      | _ => Func selF (vs :: Const (types := types) (t := stringT) nm :: nil)
    end.

  Definition sym_read (summ : Prover.(Facts)) (args : list (expr types)) (p : expr types)
    : option (expr types) :=
    match args with
      | ns :: vs :: _ :: p' :: nil =>
        match deref p with
          | Nothing => None
          | Constant base offset =>
            match listIn ns with
              | None => None
              | Some ns' =>
                if Prover.(Prove) summ (Equal wordT p' base)
                  then match nth_error ns' offset with
                         | None => None
                         | Some nm => Some (sym_sel vs nm)
                       end
                  else None
            end
          | Symbolic base nms nm =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Equal listStringT nms ns)
              && Prover.(Prove) summ (Func InF (nm :: nms :: nil))
              then Some (match nm with
                           | Const tp nm' =>
                             match tp return tvarD types tp -> expr types with
                               | stringT => fun nm' => sym_sel vs nm'
                               | _ => fun _ => Func selF (vs :: nm :: nil)
                             end nm'
                           | _ => Func selF (vs :: nm :: nil)
                         end)
              else None
        end
      | _ => None
    end.

  Definition sym_read_easier (summ : Prover.(Facts)) (args : list (expr types)) (p : expr types)
    : option (expr types) :=
    match args with
      | ns :: vs :: _ :: p' :: nil =>
        match deref p with
          | Nothing => None
          | Constant base offset =>
            match listIn ns with
              | None => None
              | Some ns' =>
                if Prover.(Prove) summ (Equal wordT p' base)
                  then match nth_error ns' offset with
                         | None => None
                         | Some nm => Some (sym_sel vs nm)
                       end
                  else None
            end
          | Symbolic base nms nm =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Equal listStringT nms ns)
              && Prover.(Prove) summ (Func InF (nm :: nms :: nil))
              then Some (Func selF (vs :: nm :: nil))
              else None
        end
      | _ => None
    end.

  Definition sym_write (summ : Prover.(Facts)) (args : list (expr types)) (p v : expr types)
    : option (list (expr types)) :=
    match args with
      | ns :: vs :: avail :: p' :: nil =>
        match deref p with
          | Nothing => None
          | Constant base offset =>
            match listIn ns with
              | None => None
              | Some ns' =>
                if Prover.(Prove) summ (Equal wordT p' base)
                  then match nth_error ns' offset with
                         | None => None
                         | Some nm => Some (ns
                           :: Func updF (vs :: Const (types := types) (t := stringT) nm :: v :: nil)
                           :: avail :: p' :: nil)
                       end
                  else None
            end
          | Symbolic base nms nm =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Equal listStringT nms ns)
              && Prover.(Prove) summ (Func InF (nm :: nms :: nil))
              then Some (ns
                :: Func updF (vs :: nm :: v :: nil)
                :: avail :: p' :: nil)
              else None
        end
      | _ => None
    end.
End parametric.

Definition MemEval types' : @MEVAL.PredEval.MemEvalPred (types types') :=
  MEVAL.PredEval.Build_MemEvalPred (@sym_read _) (@sym_write _) (fun _ _ _ _ => None) (fun _ _ _ _ _ => None).

Section correctness.
  Variable types' : list type.
  Definition types0 := types types'.

  Definition ssig : SEP.predicate types0 pcT stT.
    refine (SEP.PSig _ _ _ (listStringT :: valsT :: natT :: wordT :: nil) _).
    exact locals.
  Defined.

  Definition ssig_r : Env.Repr (SEP.predicate types0 pcT stT) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in
      let lst :=
        None :: None :: Some ssig :: nil
      in Env.listOptToRepr lst (SEP.Default_predicate _ _ _).

  Variable funcs' : functions types0.
  Definition funcs := Env.repr (funcs_r _) funcs'.

  Variable Prover : ProverT types0.
  Variable Prover_correct : ProverT_correct Prover funcs.

  Ltac doMatch P :=
    match P with
      | match ?E with 0 => _ | _ => _ end => destr2 idtac E
      | match ?E with nil => _ | _ => _ end => destr idtac E
      | match ?E with Const _ _ => _ | _ => _ end => destr2 idtac E
      | match ?E with tvProp => _ | _ => _ end => destr idtac E
      | match ?E with None => _ | _ => _ end => destr idtac E
      | match ?E with left _ => _ | _ => _ end => destr2 idtac E
      | match ?E with Nothing => _ | _ => _ end => destr2 idtac E
    end.

  Ltac deconstruct' :=
    match goal with
      | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
      | [ H : ?P |- _ ] =>
        let P := stripSuffix P in doMatch P
      | [ H : match ?P with None => _ | _ => _ end |- _ ] =>
        let P := stripSuffix P in doMatch P
      | [ |- match ?P with Nothing => _ | _ => _ end ] =>
        let P := stripSuffix P in doMatch P
    end.

  Ltac deconstruct := repeat deconstruct'.

  Lemma deref_correct : forall uvars vars e w,
    exprD funcs uvars vars e wordT = Some w
    -> match deref e with
         | Nothing => True
         | Constant base offset =>
           exists wb,
             exprD funcs uvars vars base wordT = Some wb
             /\ w = wb ^+ $ (offset * 4)
         | Symbolic base nms nm =>
           exists wb nmsV nmV,
             exprD funcs uvars vars base wordT = Some wb
             /\ exprD funcs uvars vars nms listStringT = Some nmsV
             /\ exprD funcs uvars vars nm stringT = Some nmV
             /\ w = wb ^+ $ (variablePosition nmsV nmV)
       end.
  Proof.
    destruct e; simpl deref; intuition; try discriminate.
    deconstruct.

    match goal with
      | [ |- context[div4 ?N] ] => specialize (div4_correct N);
        destruct (div4 N)
    end; intuition.
    specialize (H0 _ (refl_equal _)); subst.
    simpl in H.
    deconstruct.
    repeat (esplit || eassumption).
    repeat f_equal.
    unfold natToW.
    f_equal.
    omega.

    simpl in H.
    deconstruct.
    destruct (exprD funcs uvars vars e0 listStringT); try discriminate.
    destruct (exprD funcs uvars vars e1 stringT); try discriminate.
    deconstruct; eauto 10.
  Qed.

  Lemma listIn_correct : forall uvars vars e ns, listIn e = Some ns
    -> exprD funcs uvars vars e listStringT = Some ns.
  Proof.
    induction e; simpl; intuition; try discriminate.
    repeat match type of H with
             | Forall _ (_ :: _ :: nil) => inversion H; clear H; subst
             | _ => deconstruct'
           end.
    inversion H4; clear H4; subst.
    clear H5.
    deconstruct.
    simpl in *.
    erewrite H2; reflexivity.
  Qed.

  Ltac t := simpl in *; try discriminate; try (deconstruct;
    match goal with
      | [ _ : Range (match ?E with nil => _ | _ => _ end) === _ |- _ ] =>
        destruct E; simpl in *; try discriminate;
          match goal with
            | [ H : Range ?X === _ |- _ ] => destruct X; simpl in *; hnf in H; subst
          end;
          match goal with
              | [ H : _ = _ |- _ ] => rewrite H; reflexivity
            end
      end).

  Lemma sym_sel_correct : forall uvars vars nm (vs : expr types0) vsv,
    exprD funcs uvars vars vs valsT = Some vsv
    -> exprD funcs uvars vars (sym_sel vs nm) wordT = Some (sel vsv nm).
  Proof.
    induction vs; simpl; intros; try discriminate.

    destruct (equiv_dec t valsT); congruence.

    rewrite H; reflexivity.

    rewrite H; reflexivity.
    simpl in *.

    do 13 (destruct f; t).

    Focus 2.
    deconstruct.
    hnf in e; subst.
    rewrite H0; reflexivity.

    destruct l; simpl in *; try discriminate.
    destruct l; simpl in *; try discriminate.
    rewrite H0; reflexivity.
    destruct e0; simpl in *; try (rewrite H0; reflexivity).
    do 2 (destruct l; simpl in *; try (rewrite H0; reflexivity)).
    destruct t; simpl in *; try (rewrite H0; reflexivity).
    do 7 (destruct n; simpl in *; try (rewrite H0; reflexivity)).
    inversion H; clear H; subst.
    inversion H4; clear H4; subst.
    inversion H5; clear H5; subst.
    clear H6.
    destruct (string_dec t0 nm); subst.
    rewrite string_eq_true.
    deconstruct.
    unfold sel, upd.
    rewrite string_eq_true; reflexivity.

    rewrite string_eq_false by assumption.
    deconstruct.
    erewrite H3 by reflexivity.
    f_equal; unfold sel, upd.
    rewrite string_eq_false; auto.
  Qed.
  Require Import Bedrock.PropXTac.

  Lemma array_selN : forall nm vs ns n,
    nth_error ns n = Some nm
    -> Array.selN (toArray ns vs) n = sel vs nm.
  Proof.
    induction ns; destruct n; simpl; intuition; try discriminate.
    injection H; clear H; intros; subst; reflexivity.
  Qed.

  Require Import Coq.NArith.NArith Bedrock.Nomega.

  Lemma length_toArray : forall ns vs,
    length (toArray ns vs) = length ns.
  Proof.
    induction ns; simpl; intuition.
  Qed.

  Fixpoint variablePosition' (ns : list string) (nm : string) : nat :=
    match ns with
      | nil => O
      | nm' :: ns' => if string_dec nm' nm then O
        else S (variablePosition' ns' nm)
    end.

  Lemma variablePosition'_4 : forall nm ns,
    variablePosition' ns nm * 4 = variablePosition ns nm.
    induction ns; simpl; intuition.
    destruct (string_dec a nm); intuition.
  Qed.

  Lemma nth_error_variablePosition' : forall nm ns,
    In nm ns
    -> nth_error ns (variablePosition' ns nm) = Some nm.
    induction ns; simpl; intuition; subst.
    destruct (string_dec nm nm); tauto.
    destruct (string_dec a nm); intuition; subst; auto.
  Qed.

  Lemma variablePosition'_length : forall nm ns,
    In nm ns
    -> (variablePosition' ns nm < length ns)%nat.
    induction ns; simpl; intuition; subst.
    destruct (string_dec nm nm); intuition.
    destruct (string_dec a nm); omega.
  Qed.

  Theorem sym_read_easier_correct : forall args uvars vars cs summ pe p ve m stn,
    sym_read_easier Prover summ args pe = Some ve ->
    Valid Prover_correct uvars vars summ ->
    exprD funcs uvars vars pe wordT = Some p ->
    match
      applyD (exprD funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars ve wordT with
      | Some v =>
        ST.HT.smem_get_word (IL.implode stn) p m = Some v
      | _ => False
    end.
  Proof.
    simpl; intuition.
    do 5 (destruct args; simpl in *; intuition; try discriminate).
    generalize (deref_correct uvars vars pe); destruct (deref pe); intro Hderef; try discriminate.

    generalize (listIn_correct uvars vars e); destr idtac (listIn e); intro HlistIn.
    specialize (HlistIn _ (refl_equal _)).
    rewrite HlistIn in *.
    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove Prover ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct Prover_correct summ H (goal := goal)); intro
               end
           end; unfold ValidProp in *.
    unfold types0 in *.
    match type of H with
      | (if ?E then _ else _) = _ => destruct E
    end; intuition; try discriminate.
    simpl in H4.
    case_eq (nth_error l n); [ intros ? Heq | intro Heq ]; rewrite Heq in *; try discriminate.
    injection H; clear H; intros; subst.
    generalize (sym_sel_correct uvars vars s e0); intro Hsym_sel.
    destruct (exprD funcs uvars vars e0 valsT); try tauto.
    specialize (Hsym_sel _ (refl_equal _)).
    rewrite Hsym_sel.
    specialize (Hderef _ H1).
    destruct Hderef as [ ? [ ] ].
    subst.
    unfold types0 in H2.
    unfold types0 in H1.
    case_eq (exprD funcs uvars vars e1 natT); [ intros ? Heq' | intro Heq' ]; rewrite Heq' in *; try tauto.
    case_eq (exprD funcs uvars vars e2 wordT); [ intros ? Heq'' | intro Heq'' ]; rewrite Heq'' in *; try tauto.
    rewrite H in H4.
    specialize (H4 (ex_intro _ _ (refl_equal _))).
    hnf in H4; simpl in H4.
    rewrite Heq'' in H4.
    rewrite H in H4.
    subst.
    apply simplify_fwd in H2.
    destruct H2 as [ ? [ ? [ ? [ ] ] ] ].
    destruct H3 as [ ? [ ? [ ? [ ] ] ] ].
    simpl simplify in H2, H3, H5.
    destruct H5.
    apply simplify_bwd in H6.
    generalize (split_semp _ _ _ H3 H7); intro; subst.
    specialize (smem_read_correct' _ _ _ _ (i := natToW n) H6); intro Hsmem.
    rewrite natToW_times4.
    rewrite wmult_comm.
    unfold natToW in *.
    erewrite split_smem_get_word; eauto.
    left.
    rewrite Hsmem.
    f_equal.

    unfold Array.sel.
    apply array_selN.
    apply array_bound in H6.
    rewrite wordToNat_natToWord_idempotent; auto.

    apply nth_error_Some_length in Heq.

    rewrite length_toArray in *.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    omega.

    rewrite length_toArray.
    apply Nlt_in.
    repeat rewrite wordToN_nat.
    repeat rewrite Nat2N.id.
    apply array_bound in H6.
    rewrite length_toArray in *.
    repeat rewrite wordToNat_natToWord_idempotent.
    eapply nth_error_Some_length; eauto.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    omega.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    apply nth_error_Some_length in Heq.
    omega.

    (* Now the [Symbolic] case... *)
    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove Prover ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct Prover_correct summ H (goal := goal)); intro
               end
           end; unfold ValidProp in *.
    unfold types0 in *.
    match type of H with
      | (if ?E then _ else _) = _ => case_eq E
    end; intuition; match goal with
                      | [ H : _ = _ |- _ ] => rewrite H in *
                    end; try discriminate.
    simpl in H3, H4, H5.
    apply andb_prop in H6; destruct H6.
    apply andb_prop in H6; destruct H6.
    intuition.
    destruct (Hderef _ H1) as [ ? [ ? [ ] ] ]; clear Hderef; intuition; subst.
    rewrite H10 in *.
    rewrite H5 in *.
    rewrite H11 in *.
    specialize (H4 (ex_intro _ _ (refl_equal _))).
    unfold Provable in H4.
    injection H; clear H; intros; subst.
    simpl exprD in *.
    unfold types0 in *.
    unfold Provable in *.
    simpl exprD in *.
    deconstruct.
    rewrite H10 in *.
    specialize (H3 (ex_intro _ _ (refl_equal _))).
    specialize (H9 (ex_intro _ _ (refl_equal _))).
    subst.
    apply simplify_fwd in H2.
    destruct H2.
    destruct H.
    destruct H.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H5.
    simpl in H.
    simpl in H2.
    simpl in H5.
    destruct H5.
    generalize (split_semp _ _ _ H2 H11); intro; subst.
    apply simplify_bwd in H9.

    specialize (smem_read_correct' _ _ _ _ (i := natToW (variablePosition' t x1)) H9); intro Hsmem.
    rewrite wmult_comm in Hsmem.
    rewrite <- natToW_times4 in Hsmem.

    rewrite variablePosition'_4 in Hsmem.
    erewrite split_smem_get_word; eauto.
    left.
    unfold natToW in *.
    rewrite Hsmem.
    f_equal.
    unfold Array.sel.
    apply array_selN.
    apply array_bound in H9.
    rewrite wordToNat_natToWord_idempotent; auto.

    apply nth_error_variablePosition'; auto.
    rewrite length_toArray in *.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.

    specialize (variablePosition'_length _ _ H4).
    omega.

    red.
    apply array_bound in H9.
    repeat rewrite wordToN_nat.
    rewrite wordToNat_natToWord_idempotent.
    rewrite wordToNat_natToWord_idempotent.
    apply Nlt_in.
    repeat rewrite Nat2N.id.
    rewrite length_toArray.
    apply variablePosition'_length; auto.
    apply Nlt_in.
    rewrite Npow2_nat.
    repeat rewrite Nat2N.id.
    assumption.
    apply Nlt_in.
    rewrite Npow2_nat.
    repeat rewrite Nat2N.id.
    specialize (variablePosition'_length _ _ H4).
    rewrite length_toArray in H9.
    omega.
  Qed.

  Theorem easy_bridge : forall args uvars vars summ pe ve P,
    sym_read Prover summ args pe = Some ve
    -> match
         applyD (exprD funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
         with
         | None => False
         | Some p => P p
       end
    -> exists ve', sym_read_easier Prover summ args pe = Some ve'
      /\ exprD funcs uvars vars ve wordT = exprD funcs uvars vars ve' wordT.
    intros.
    simpl in H0.
    repeat (destruct args; simpl in *; try discriminate).
    case_eq (exprD funcs uvars vars e0 valsT); [ intros ? Heq | intro Heq ]; rewrite Heq in *.
    Focus 2.
    deconstruct.
    deconstruct.
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; try discriminate.
    deconstruct; eauto.
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; try discriminate.
    deconstruct.
    do 2 esplit; [ reflexivity | ].
    simpl exprD.
    destruct e5; try reflexivity.
    destruct t3; try reflexivity.
    do 7 (destruct n; try reflexivity).
    rewrite Heq.
    erewrite sym_sel_correct by eassumption; reflexivity.
  Qed.

  Theorem sym_read_correct : forall args uvars vars cs summ pe p ve m stn,
    sym_read Prover summ args pe = Some ve ->
    Valid Prover_correct uvars vars summ ->
    exprD funcs uvars vars pe wordT = Some p ->
    match
      applyD (exprD funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars ve wordT with
      | Some v =>
        ST.HT.smem_get_word (IL.implode stn) p m = Some v
      | _ => False
    end.
  Proof.
    intros.
    eapply easy_bridge in H; eauto.
    2: instantiate (1 := fun p => ST.satisfies cs p stn m); eauto.
    destruct H as [ ? [ ] ].
    rewrite H3.
    eapply sym_read_easier_correct; eauto.
  Qed.

  Lemma toArray_irrel : forall vs v nm ns,
    ~In nm ns
    -> toArray ns (upd vs nm v) = toArray ns vs.
    induction ns; simpl; intuition.
    f_equal; auto.
    unfold upd.
    rewrite string_eq_false; auto.
  Qed.

  Lemma nth_error_In : forall A (x : A) ls n,
    nth_error ls n = Some x
    -> In x ls.
    induction ls; destruct n; simpl; intuition; try discriminate; eauto.
    injection H; intros; subst; auto.
  Qed.

  Lemma array_updN : forall vs nm v ns,
    NoDup ns
    -> forall n, nth_error ns n = Some nm
      -> Array.updN (toArray ns vs) n v
      = toArray ns (upd vs nm v).
    induction 1; destruct n; simpl; intuition.
    injection H1; clear H1; intros; subst.
    rewrite toArray_irrel by assumption.
    unfold upd; rewrite string_eq_true; reflexivity.
    rewrite IHNoDup; f_equal; auto.
    unfold upd; rewrite string_eq_false; auto.
    intro; subst.
    apply H.
    eapply nth_error_In; eauto.
  Qed.
  Require Import Bedrock.Arrays.

  Lemma array_updN_variablePosition' : forall vs nm v ns,
    NoDup ns
    -> In nm ns
    -> toArray ns (upd vs nm v) = updN (toArray ns vs) (variablePosition' ns nm) v.
    induction 1; simpl; intuition; subst.
    destruct (string_dec nm nm); try tauto.
    rewrite toArray_irrel; auto.
    unfold upd.
    rewrite string_eq_true.
    auto.

    destruct (string_dec x nm); subst.
    rewrite toArray_irrel; auto.
    unfold upd.
    rewrite string_eq_true.
    auto.

    unfold upd at 1.
    rewrite string_eq_false by auto.
    rewrite H1; auto.
  Qed.

  Theorem sym_write_correct : forall args uvars vars cs summ pe p ve v m stn args',
    sym_write Prover summ args pe ve = Some args' ->
    Valid Prover_correct uvars vars summ ->
    exprD funcs uvars vars pe wordT = Some p ->
    exprD funcs uvars vars ve wordT = Some v ->
    match
      applyD (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match
      applyD (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args' _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some pr =>
        match ST.HT.smem_set_word (IL.explode stn) p v m with
          | None => False
          | Some sm' => ST.satisfies cs pr stn sm'
        end
    end.
  Proof.
    simpl; intuition.
    do 5 (destruct args; simpl in *; intuition; try discriminate).
    generalize (deref_correct uvars vars pe); destruct (deref pe); intro Hderef; try discriminate.

    generalize (listIn_correct uvars vars e); destr idtac (listIn e); intro HlistIn;
      specialize (HlistIn _ (refl_equal _)); rewrite HlistIn in *.
    destruct (Hderef _ H1); clear Hderef; intuition; subst.
    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove Prover ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct Prover_correct summ H (goal := goal)); intro
               end
           end; unfold ValidProp in *.
    unfold types0 in *.
    match type of H with
      | (if ?E then _ else _) = _ => destruct E
    end; intuition; try discriminate.
    simpl in H5.
    case_eq (nth_error l n); [ intros ? Heq | intro Heq ]; rewrite Heq in *; try discriminate.
    injection H; clear H; intros; subst.
    unfold applyD.
    rewrite HlistIn.
    simpl exprD.
    destruct (exprD funcs uvars vars e0 valsT); try tauto.
    unfold Provable in H6.
    simpl in H6.
    rewrite H5 in H6.
    destruct (exprD funcs uvars vars e1 natT); try tauto.
    destruct (exprD funcs uvars vars e2 wordT); try tauto.
    rewrite H2.
    specialize (H6 (ex_intro _ _ (refl_equal _))); subst.
    apply simplify_fwd in H3.
    destruct H3 as [ ? [ ? [ ? [ ] ] ] ].
    destruct H3 as [ ? [ ? [ ? [ ] ] ] ].
    simpl in H, H3, H6, H7.
    destruct H6.
    apply simplify_bwd in H7.
    eapply smem_write_correct' in H7.
    destruct H7 as [ ? [ ] ].
    rewrite natToW_times4.
    rewrite wmult_comm.
    generalize (split_semp _ _ _ H3 H8); intro; subst.
    eapply split_set_word in H7.
    destruct H7.
    destruct H; subst.
    rewrite H10.
    unfold locals.
    apply simplify_bwd.
    exists x4; exists x1.
    repeat split; auto.
    exists smem_emp.
    exists x4.
    simpl; intuition.
    apply split_a_semp_a.
    reflexivity.
    apply simplify_fwd.

    unfold Array.upd in H9.
    rewrite wordToNat_natToWord_idempotent in H9.
    erewrite array_updN in H9; eauto.
    apply nth_error_Some_length in Heq.
    apply array_bound in H9.
    rewrite updN_length in H9.
    rewrite length_toArray in H9.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    omega.

    destruct H; auto.

    rewrite length_toArray.
    apply Nlt_in.
    repeat rewrite wordToN_nat.
    repeat rewrite Nat2N.id.
    apply array_bound in H7.
    rewrite length_toArray in *.
    repeat rewrite wordToNat_natToWord_idempotent.
    eapply nth_error_Some_length; eauto.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    omega.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    apply nth_error_Some_length in Heq.
    omega.


    (* Now the [Symbolic] case... *)

    destruct (Hderef _ H1) as [ ? [ ? [ ? [ ] ] ] ]; clear Hderef; intuition; subst.
    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove Prover ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct Prover_correct summ H (goal := goal)); intro
               end
           end; unfold ValidProp in *.
    unfold types0 in *.
    match type of H with
      | (if ?E then _ else _) = _ => case_eq E
    end; intuition; match goal with
                      | [ H : _ = _ |- _ ] => rewrite H in *
                    end; try discriminate.
    simpl in H7, H8, H9.
    apply andb_prop in H10; destruct H10.
    apply andb_prop in H10; destruct H10.
    intuition.
    injection H; clear H; intros; subst.
    simpl applyD.
    unfold Provable in *.
    simpl exprD in *.
    deconstruct.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H in *
             | [ H : _ |- _ ] => specialize (H (ex_intro _ _ (refl_equal _))); subst
           end.
    apply simplify_fwd in H3.
    destruct H3.
    destruct H.
    destruct H.
    simpl in H.
    destruct H3.
    destruct H3.
    destruct H3.
    destruct H3.
    simpl in H3.
    destruct H9.
    simpl in H9.
    destruct H9.
    apply simplify_bwd in H13.
    generalize (split_semp _ _ _ H3 H14); intro; subst.
    eapply smem_write_correct' in H13.
    destruct H13 as [ ? [ ] ].
    rewrite <- variablePosition'_4.
    rewrite natToW_times4.
    rewrite wmult_comm.
    eapply split_set_word in H13.
    destruct H13.
    generalize (proj2 H); intro; subst.
    rewrite H16.
    apply simplify_bwd.
    esplit.
    esplit.
    esplit.
    simpl.
    apply disjoint_split_join; auto.
    esplit.
    esplit.
    esplit.
    esplit.
    simpl.
    apply split_a_semp_a.
    esplit.
    simpl; intuition.
    apply semp_smem_emp.
    apply simplify_fwd.
    unfold Array.upd in H15.
    rewrite wordToNat_natToWord_idempotent in H15.

    rewrite array_updN_variablePosition'; auto.

    apply array_bound in H15.
    rewrite updN_length in H15.
    apply Nlt_in.
    rewrite Npow2_nat.
    repeat rewrite Nat2N.id.
    apply variablePosition'_length in H8.
    rewrite length_toArray in H15.
    omega.

    assumption.
    apply H.
    rewrite length_toArray.
    apply Nlt_in.
    repeat rewrite wordToN_nat.
    repeat rewrite Nat2N.id.
    rewrite wordToNat_natToWord_idempotent.
    rewrite wordToNat_natToWord_idempotent.
    apply variablePosition'_length; auto.
    apply array_bound in H13.
    apply Nlt_in.
    rewrite Npow2_nat.
    repeat rewrite Nat2N.id.
    rewrite length_toArray in H13.
    assumption.

    apply Nlt_in.
    rewrite Npow2_nat.
    repeat rewrite wordToN_nat.
    repeat rewrite Nat2N.id.
    apply array_bound in H13.
    generalize (variablePosition'_length _ _ H8).
    rewrite length_toArray in H13.
    omega.
  Qed.

End correctness.

Definition MemEvaluator types' : MEVAL.MemEvaluator (types types') (tvType 0) (tvType 1) :=
  Eval cbv beta iota zeta delta [ MEVAL.PredEval.MemEvalPred_to_MemEvaluator ] in
    @MEVAL.PredEval.MemEvalPred_to_MemEvaluator _ (tvType 0) (tvType 1) (MemEval types') 2.

Theorem MemEvaluator_correct types' funcs' preds'
  : @MEVAL.MemEvaluator_correct (Env.repr types_r types') (tvType 0) (tvType 1)
  (MemEvaluator (Env.repr types_r types')) (funcs funcs') (Env.repr (ssig_r _) preds')
  (IL.settings * IL.state) (tvType 0) (tvType 0)
  (@IL_mem_satisfies (types types')) (@IL_ReadWord (types types')) (@IL_WriteWord (types types'))
  (@IL_ReadByte (types types')) (@IL_WriteByte (types types')).
Proof.
  intros. eapply (@MemPredEval_To_MemEvaluator_correct (types types')); simpl; intros; try discriminate.
  eapply (@sym_read_correct (types types')); eauto.
  eapply (@sym_write_correct (types types')); eauto.
  reflexivity.
Qed.

Definition pack : MEVAL.MemEvaluatorPackage types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
  IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte :=

  @MEVAL.Build_MemEvaluatorPackage types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
  IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte
  types_r
  funcs_r
  (fun ts => Env.listOptToRepr (None :: None :: Some (ssig ts) :: nil)
    (SEP.Default_predicate (Env.repr types_r ts)
      (tvType 0) (tvType 1)))
  (fun ts => MemEvaluator (types ts))
  (fun ts fs ps => @MemEvaluator_correct (types ts) _ _).


(** * Some additional helpful theorems *)

Theorem sel_upd_eq : forall vs nm v nm',
  nm = nm'
  -> sel (upd vs nm v) nm' = v.
Proof.
  unfold sel, upd; intros; subst; rewrite string_eq_true; reflexivity.
Qed.

Theorem sel_upd_ne : forall vs nm v nm',
  nm <> nm'
  -> sel (upd vs nm v) nm' = sel vs nm'.
Proof.
  unfold sel, upd; intros; subst; rewrite string_eq_false; auto.
Qed.

(*
Require Import PropX.
*)

Ltac simp := cbv beta; unfold In.

(** ** Point-of-view switch at function call sites *)

Lemma behold_the_array' : forall p ns,
  NoDup ns
  -> forall offset, allocated p offset (length ns)
    ===> Ex vs, ptsto32m' nil p offset (toArray ns vs).
  induction 1; simpl length; unfold allocated; fold allocated; intros.

  simpl.
  apply Himp_ex_c.
  exists (fun _ => wzero _).
  apply Himp_refl.

  eapply Himp_trans; [ apply Himp_ex_star | ].
  apply Himp'_ex; intro.
  eapply Himp_trans; [ eapply Himp_star_frame | ]; [ apply Himp_refl | apply IHNoDup | ].
  eapply Himp_trans; [ apply Himp_star_comm | ].
  eapply Himp_trans; [ apply Himp_ex_star | ].
  eapply Himp'_ex; intro.
  simpl toArray.
  unfold ptsto32m'; fold ptsto32m'.

  replace (match offset with
             | 0 => p
             | S _ => p ^+ $ (offset)
           end) with (p ^+ $ (offset)) by (destruct offset; W_eq).

  apply Himp_ex_c; exists (upd x1 x x0).
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_frame.
  change (upd x1 x x0 x) with (sel (upd x1 x x0) x).
  rewrite sel_upd_eq by reflexivity.
  apply Himp_refl.

  rewrite toArray_irrel by assumption.
  apply Himp_refl.
Qed.

Theorem Himp_star_Emp : forall P,
  Emp * P ===> P.
  intros; intro cs.
  destruct (heq_star_emp_l cs P); auto.
Qed.

Theorem ptsto32m'_out : forall a vs offset,
  ptsto32m' _ a offset vs ===> ptsto32m _ a offset vs.
  induction vs; intros.

  apply Himp_refl.

  unfold ptsto32m', ptsto32m; fold ptsto32m; fold ptsto32m'.
  replace (match offset with
             | 0 => a
             | S _ => a ^+ $ (offset)
           end) with (a ^+ $ (offset)) by (destruct offset; W_eq).
  destruct vs.
  simpl ptsto32m'.
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_Emp.
  apply Himp_star_frame.
  apply Himp_refl.
  auto.
Qed.

Theorem Himp_ex : forall T (P Q : T -> _),
  (forall v, P v ===> Q v) ->
  ex P ===> ex Q.
  intros; intro cs; apply himp_ex; firstorder.
Qed.

Lemma behold_the_array : forall p ns,
  NoDup ns
  -> forall offset, allocated p offset (length ns)
    ===> Ex vs, ptsto32m nil p offset (toArray ns vs).
  intros.
  eapply Himp_trans; [ apply behold_the_array' | ]; auto.
  apply Himp_ex; intro.
  apply ptsto32m'_out.
Qed.

Lemma do_call' : forall ns ns' vs avail avail' p p',
  (length ns' <= avail)%nat
  -> avail' = avail - length ns'
  -> p' = p ^+ natToW (4 * length ns)
  -> NoDup ns'
  -> locals ns vs avail p ===> locals ns vs 0 p * Ex vs', locals ns' vs' avail' p'.
Proof.
  intros.
  unfold locals.
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_frame.
  apply Himp_refl.

  subst.
  eapply Himp_trans; [ | apply Himp_star_Emp' ].
  eapply Himp_trans; [ apply allocated_split | ]; eauto.
  replace (0 + 4 * length ns') with (length ns' * 4) by omega.
  replace (4 * length ns) with (length ns * 4) by omega.
  eapply Himp_trans.
  eapply Himp_star_frame.
  apply behold_the_array; auto.
  apply Himp_refl.
  eapply Himp_trans; [ apply Himp_ex_star | ].
  apply Himp'_ex; intro vs'.
  apply Himp_ex_c; exists vs'.
  unfold array.
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_pure_cc; auto.
  apply Himp_star_frame.
  apply Himp_refl.
  apply allocated_shift_base; auto.
  unfold natToW; W_eq.
Qed.

Definition reserved (p : W) (len : nat) := (p =?> len)%Sep.

Ltac words' := repeat (rewrite (Mult.mult_comm 4)
  || rewrite natToW_times4 || rewrite natToW_plus); unfold natToW.
Ltac words := words'; W_eq.

Lemma expose_avail : forall ns vs avail p expose avail',
  (expose <= avail)%nat
  -> avail' = avail - expose
  -> locals ns vs avail p ===> locals ns vs avail' p
  * reserved (p ^+ natToW (4 * (length ns + avail'))) expose.
Proof.
  unfold locals; intros.
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_frame.
  apply Himp_refl.
  subst.
  eapply Himp_trans; [ apply allocated_split | ].
  instantiate (1 := avail - expose); omega.
  apply Himp_star_frame.
  apply Himp_refl.
  apply allocated_shift_base; try omega.
  words.
Qed.

Theorem Himp_refl' : forall P Q,
  P = Q
  -> P ===> Q.
  intros; subst; apply Himp_refl.
Qed.

Theorem do_call : forall ns ns' vs avail avail' p p',
  (length ns' <= avail)%nat
  -> (avail' <= avail - length ns')%nat
  -> p' = p ^+ natToW (4 * length ns)
  -> NoDup ns'
  -> locals ns vs avail p ===>
  locals ns vs 0 p
  * Ex vs', locals ns' vs' avail' p'
  * reserved (p ^+ natToW (4 * (length ns + length ns' + avail')))
  (avail - length ns' - avail').
Proof.
  intros; subst.
  eapply Himp_trans; [ apply do_call' | ]; eauto.
  apply Himp_star_frame; [ apply Himp_refl | ].
  apply Himp_ex; intro.
  eapply Himp_trans; [ apply expose_avail | ].
  instantiate (1 := avail - length ns' - avail'); omega.
  eauto.
  apply Himp_star_frame.
  apply Himp_refl'.
  f_equal; omega.
  apply Himp_refl'.
  f_equal.
  words'.
  replace (avail - Datatypes.length ns' -
    (avail - Datatypes.length ns' - avail'))
    with avail' by omega.
  W_eq.
Qed.

Lemma ptsto32m'_allocated : forall (p : W) (ls : list W) (offset : nat),
  ptsto32m' nil p offset ls ===> allocated p offset (length ls).
  induction ls.

  intros; apply Himp_refl.

  simpl length.
  unfold ptsto32m', allocated; fold ptsto32m'; fold allocated.
  intros.
  replace (match offset with
             | 0 => p
             | S _ => p ^+ $ (offset)
           end) with (p ^+ $ (offset)) by (destruct offset; W_eq).
  apply Himp_star_frame.
  apply Himp_ex_c; eexists; apply Himp_refl.
  auto.
Qed.

Lemma ptsto32m_allocated : forall (p : W) (ls : list W) (offset : nat),
  ptsto32m nil p offset ls ===> allocated p offset (length ls).
  intros; eapply Himp_trans.
  apply ptsto32m'_in.
  apply ptsto32m'_allocated.
Qed.

Lemma do_return' : forall ns ns' vs avail avail' p p',
  avail = avail' + length ns'
  -> p' = p ^+ natToW (4 * length ns)
  -> (locals ns vs 0 p * Ex vs', locals ns' vs' avail' p') ===> locals ns vs avail p.
  unfold locals; intros.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_frame; [ apply Himp_refl | ].
  unfold allocated; fold allocated.
  eapply Himp_trans; [ apply Himp_star_Emp | ].
  apply Himp'_ex; intro vs'.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_pure_c; intro.
  subst.
  eapply Himp_trans; [ | apply allocated_join ].
  2: instantiate (1 := length ns'); omega.
  apply Himp_star_frame.
  unfold array.
  words'.
  replace (length ns') with (length (toArray ns' vs')) by apply length_toArray.
  apply ptsto32m_allocated.
  apply allocated_shift_base; try omega.
  words.
Qed.

Lemma unexpose_avail : forall ns vs avail p expose avail',
  (expose <= avail)%nat
  -> avail' = avail - expose
  -> locals ns vs avail' p
  * reserved (p ^+ natToW (4 * (length ns + avail'))) expose
  ===> locals ns vs avail p.
  unfold locals; intros.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_frame; [ apply Himp_refl | ].
  eapply Himp_trans; [ | apply allocated_join ].
  2: instantiate (1 := avail'); omega.
  apply Himp_star_frame; [ apply Himp_refl | ].
  apply allocated_shift_base; try omega.
  subst.
  words.
Qed.

Lemma do_return : forall ns ns' vs avail avail' p p',
  (avail >= avail' + length ns')%nat
  -> p' = p ^+ natToW (4 * length ns)
  -> (locals ns vs 0 p * Ex vs', locals ns' vs' avail' p'
    * reserved (p ^+ natToW (4 * (length ns + length ns' + avail')))
    (avail - length ns' - avail'))
    ===> locals ns vs avail p.
  intros.
  eapply Himp_trans; [ | apply do_return' ].
  3: eassumption.
  Focus 2.
  instantiate (1 := ns').
  instantiate (1 := (avail - avail' - length ns') + avail').
  omega.
  apply Himp_star_frame; [ apply Himp_refl | ].
  apply Himp_ex; intro vs'.
  unfold locals.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_frame; [ apply Himp_refl | ].
  eapply Himp_trans; [ | apply allocated_join ].
  2: instantiate (1 := avail'); omega.
  apply Himp_star_frame; [ apply Himp_refl | ].
  apply allocated_shift_base; try omega.
  subst.
  words.
Qed.


(** ** Point-of-view switch in function preludes *)

Definition agree_on (vs vs' : vals) (ns : list string) :=
  List.Forall (fun nm => sel vs nm = sel vs' nm) ns.

Fixpoint merge (vs vs' : vals) (ns : list string) :=
  match ns with
    | nil => vs'
    | nm :: ns' => upd (merge vs vs' ns') nm (sel vs nm)
  end.

Lemma Forall_weaken : forall A (P P' : A -> Prop),
  (forall x, P x -> P' x)
  -> forall ls, List.Forall P ls
    -> List.Forall P' ls.
Proof.
  induction 2; simpl; intuition.
Qed.

Theorem merge_agree : forall vs vs' ns,
  agree_on (merge vs vs' ns) vs ns.
Proof.
  induction ns; simpl; intuition; constructor.
  unfold sel, upd.
  rewrite string_eq_true; reflexivity.
  eapply Forall_weaken; [ | eassumption ].
  simpl; intros.
  destruct (string_dec a x); subst.
  apply sel_upd_eq; reflexivity.
  rewrite sel_upd_ne; assumption.
Qed.

Lemma NoDup_unapp2 : forall A (ls1 ls2 : list A),
  NoDup (ls1 ++ ls2)
  -> NoDup ls2.
Proof.
  induction ls1; inversion 1; simpl in *; intuition.
Qed.

Lemma toArray_vals_eq : forall vs vs' ns, agree_on vs vs' ns
  -> toArray ns vs = toArray ns vs'.
Proof.
  induction ns; simpl; intuition.
  inversion H; clear H; subst.
  f_equal; auto.
Qed.

Lemma agree_on_symm : forall vs vs' nm, agree_on vs vs' nm
  -> agree_on vs' vs nm.
Proof.
  intros; eapply Forall_weaken; [ | eauto ].
  intuition.
Qed.

Lemma Forall_weaken' : forall A (P P' : A -> Prop) ls,
  List.Forall P ls
  -> (forall x, In x ls -> P x -> P' x)
  -> List.Forall P' ls.
Proof.
  induction 1; simpl; intuition.
Qed.

Lemma ptsto32m'_merge : forall p vs' ns' ns offset vs vs'',
  NoDup (ns ++ ns')
  -> agree_on vs'' (merge vs vs' ns) (ns ++ ns')
  -> ptsto32m' nil p offset (toArray ns vs)
  * ptsto32m' nil p (offset + 4 * length ns) (toArray ns' vs')
  ===> ptsto32m' nil p offset (toArray (ns ++ ns') vs'').
  induction ns; simpl app; intros.

  simpl.
  eapply Himp_trans; [ apply Himp_star_Emp | ].
  apply Himp_refl'.
  f_equal.
  omega.
  simpl in *.
  apply toArray_vals_eq; auto.
  apply agree_on_symm; auto.

  inversion H; clear H; subst.
  simpl in H0.
  simpl toArray; simpl length.
  unfold ptsto32m'; fold ptsto32m'.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_frame.
  apply Himp_refl'.
  f_equal.
  assert (Hin : In a (a :: ns ++ ns')) by (simpl; tauto).
  apply (proj1 (Forall_forall _ _) H0) in Hin.
  rewrite sel_upd_eq in Hin by reflexivity.
  symmetry; assumption.

  eapply Himp_trans; [ | apply IHns ]; auto.
  apply Himp_star_frame.
  apply Himp_refl.
  apply Himp_refl'; f_equal; omega.

  inversion H0; clear H0; subst.
  eapply Forall_weaken'.
  eassumption.
  simpl; intros.
  rewrite H0.
  destruct (string_dec a x); subst.
  tauto.
  rewrite sel_upd_ne by assumption; reflexivity.
Qed.

Lemma ptsto32m_merge : forall p vs' ns' ns offset vs vs'',
  NoDup (ns ++ ns')
  -> agree_on vs'' (merge vs vs' ns) (ns ++ ns')
  -> ptsto32m nil p offset (toArray ns vs)
  * ptsto32m nil p (offset + 4 * length ns) (toArray ns' vs')
  ===> ptsto32m nil p offset (toArray (ns ++ ns') vs'').
Proof.
  intros.
  eapply Himp_trans.
  apply Himp_star_frame; apply ptsto32m'_in.
  eapply Himp_trans; [ | apply ptsto32m'_out ].
  apply ptsto32m'_merge; auto.
Qed.

Lemma agree_on_refl : forall vs ns,
  agree_on vs vs ns.
Proof.
  unfold agree_on; induction ns; simpl; intuition.
Qed.

Lemma ptsto32m'_shift_base : forall p n ls offset,
  (n <= offset)%nat
  -> ptsto32m' nil (p ^+ $ (n)) (offset - n) ls
  ===> ptsto32m' nil p offset ls.
  induction ls.

  intros; apply Himp_refl.

  unfold ptsto32m'; fold ptsto32m'.
  intros.
  intro; apply Himp_star_frame.
  apply Himp_refl'; f_equal.
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  unfold natToW.
  repeat f_equal.
  omega.
  replace (4 + (offset - n)) with ((4 + offset) - n) by omega.
  apply IHls; omega.
Qed.

Lemma ptsto32m_shift_base : forall p n ls offset,
  (n <= offset)%nat
  -> ptsto32m nil (p ^+ $ (n)) (offset - n) ls
  ===> ptsto32m nil p offset ls.
  intros; eapply Himp_trans.
  apply ptsto32m'_in.
  eapply Himp_trans.
  apply ptsto32m'_shift_base; auto.
  apply ptsto32m'_out.
Qed.

Theorem prelude_in : forall ns ns' vs avail p,
  (length ns' <= avail)%nat
  -> NoDup (ns ++ ns')
  -> locals ns vs avail p ===>
  Ex vs', locals (ns ++ ns') (merge vs vs' ns) (avail - length ns') p.
  unfold locals; intros.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_pure_c; intro Hns.
  eapply Himp_trans.
  eapply Himp_star_frame; [ apply Himp_refl | ].
  eapply allocated_split.
  eassumption.
  eapply Himp_trans; [ apply Himp_star_assoc' | ].
  eapply Himp_trans.
  eapply Himp_star_frame.
  apply Himp_star_comm.
  apply Himp_refl.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  eapply Himp_trans.
  eapply Himp_star_frame.
  apply behold_the_array.
  eapply NoDup_unapp2; eauto.
  apply Himp_refl.
  eapply Himp_trans; [ apply Himp_ex_star | ].
  apply Himp_ex; intro vs'.
  unfold array.
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_pure_cc; auto.
  eapply Himp_trans; [ apply Himp_star_assoc' | ].
  apply Himp_star_frame.
  eapply Himp_trans; [ | apply ptsto32m_merge ]; eauto.
  eapply Himp_trans; [ apply Himp_star_comm | ].
  apply Himp_star_frame.
  apply Himp_refl.
  match goal with
    | [ |- ?P ===> _ ] =>
      replace P
    with (ptsto32m nil (p ^+ $ (Datatypes.length ns * 4)) (0 + 4 * length ns - length ns * 4) (toArray ns' vs'))
      by (f_equal; omega)
  end.
  apply ptsto32m_shift_base.
  omega.
  apply agree_on_refl.

  apply allocated_shift_base; try omega.
  rewrite app_length.
  words.
Qed.

Lemma ptsto32m'_split : forall p ns' ns offset vs,
  ptsto32m' nil p offset (toArray (ns ++ ns') vs)
  ===> ptsto32m' nil p offset (toArray ns vs)
  * ptsto32m' nil p (offset + 4 * length ns) (toArray ns' vs).
Proof.
  induction ns.

  simpl.
  intros.
  eapply Himp_trans; [ | apply Himp_star_Emp' ].
  apply Himp_refl'; f_equal; omega.

  simpl toArray; simpl length.
  unfold ptsto32m'; fold ptsto32m'.
  intros.

  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_frame; [ apply Himp_refl | ].
  eapply Himp_trans; [ apply IHns | ].
  apply Himp_star_frame; [ apply Himp_refl | ].
  apply Himp_refl'; f_equal; omega.
Qed.

Lemma ptsto32m_split : forall p ns' ns offset vs,
  ptsto32m nil p offset (toArray (ns ++ ns') vs)
  ===> ptsto32m nil p offset (toArray ns vs)
  * ptsto32m nil p (offset + 4 * length ns) (toArray ns' vs).
  intros; eapply Himp_trans.
  apply ptsto32m'_in.
  eapply Himp_trans.
  apply ptsto32m'_split.
  apply Himp_star_frame; apply ptsto32m'_out.
Qed.

Lemma NoDup_unapp1 : forall A (ls1 ls2 : list A),
  NoDup (ls1 ++ ls2)
  -> NoDup ls1.
  induction ls1; inversion 1; simpl in *; intuition; subst; constructor.
  intro; apply H2.
  apply in_or_app; auto.
  eauto.
Qed.

Lemma ptsto32m'_shift_base' : forall p n ls offset,
  (n <= offset)%nat
  -> ptsto32m' nil p offset ls
  ===> ptsto32m' nil (p ^+ $ (n)) (offset - n) ls.
  induction ls.

  intros; apply Himp_refl.

  unfold ptsto32m'; fold ptsto32m'.
  intros.
  intro; apply Himp_star_frame.
  apply Himp_refl'; f_equal.
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  unfold natToW.
  repeat f_equal.
  omega.
  replace (4 + (offset - n)) with ((4 + offset) - n) by omega.
  apply IHls; omega.
Qed.

Lemma ptsto32m_shift_base' : forall p n ls offset,
  (n <= offset)%nat
  -> ptsto32m nil p offset ls
  ===> ptsto32m nil (p ^+ $ (n)) (offset - n) ls.
  intros; eapply Himp_trans.
  apply ptsto32m'_in.
  eapply Himp_trans.
  apply ptsto32m'_shift_base'.
  2: apply ptsto32m'_out.
  auto.
Qed.

Theorem prelude_out : forall ns ns' vs avail p,
  (length ns' <= avail)%nat
  -> locals (ns ++ ns') vs (avail - length ns') p
  ===> locals ns vs avail p.
  unfold locals; intros.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_pure_c; intro Hboth.
  eapply Himp_trans; [ | apply Himp_star_assoc' ].
  apply Himp_star_pure_cc.
  eapply NoDup_unapp1; eauto.
  unfold array.
  eapply Himp_trans.
  eapply Himp_star_frame.
  apply ptsto32m_split.
  apply Himp_refl.
  eapply Himp_trans; [ apply Himp_star_assoc | ].
  apply Himp_star_frame; [ apply Himp_refl | ].
  eapply Himp_trans; [ | apply allocated_join ].
  2: eassumption.
  apply Himp_star_frame.
  eapply Himp_trans; [ apply ptsto32m_allocated | ].
  apply allocated_shift_base.
  words.
  apply length_toArray.
  apply allocated_shift_base.
  rewrite app_length; words.
  auto.
Qed.

Lemma toArray_sel : forall x V V' ns',
  In x ns'
  -> toArray ns' V' = toArray ns' V
  -> sel V' x = sel V x.
  unfold toArray; induction ns'; simpl; intuition.
  subst.
  injection H0; intros.
  assumption.
  injection H0.
  auto.
Qed.
