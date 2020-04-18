Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Bedrock.Expr Bedrock.Env.
Require Import Coq.Classes.EquivDec Bedrock.EqdepClass.
Require Import Bedrock.DepList.
Require Import Bedrock.Word Bedrock.Prover.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** * The Transitivity Prover **)

(* Algorithm for grouping expressions by equalities. Terribly inefficient... *)
Section Grouper.
  Variable A : Type.
  Variable A_seq : A -> A -> bool.

  Fixpoint in_seq (ls : list A) (a : A) : bool :=
    match ls with
      | nil => false
      | x :: ls' => A_seq x a || in_seq ls' a
    end.

  Fixpoint groupWith (grps : list (list A)) (g : list A) (a : A) :=
    match grps with
      | nil => [a :: g]
      | g' :: grps' => if in_seq g' a
                       then (g' ++ a :: g) :: grps'
                       else g' :: groupWith grps' g a
    end.

  Fixpoint addEquality (ls : list (list A)) (a : A) (b : A) : list (list A) :=
    match ls with
      | nil => [[a, b]] (* matched nothing *)
      | grp :: ls' => if in_seq grp a
                        then groupWith ls' grp b
                        else if in_seq grp b
                               then groupWith ls' grp a
                               else grp :: addEquality ls' a b
    end.

  Fixpoint inSameGroup (grps : list (list A)) (a : A) (b : A) :=
    match grps with
      | nil => false
      | g :: grps' =>
        if in_seq g a then
          if in_seq g b
            then true
            else inSameGroup grps' a b
        else inSameGroup grps' a b
    end.

  Variable R : A -> A -> Prop.
  (* An arbitrary partial equivalence relation *)

  Hypothesis Rsym : forall x y, R x y -> R y x.
  Hypothesis Rtrans : forall x y z, R x y -> R y z -> R x z.
  Hypothesis A_seq_correct : forall x y, A_seq x y = true -> R x y.

  Fixpoint InR (x : A) (ls : list A) : Prop :=
    match ls with
      | nil => False
      | y :: ls' => R y x \/ InR x ls'
    end.

  Definition groupEqualTo (a : A) := Forall (R a).

  Definition groupEqual (g : list A) :=
    match g with
      | nil => True
      | a' :: g' => groupEqualTo a' g'
    end.

  Definition groupsEqual := Forall groupEqual.

  Hint Extern 1 (groupEqual _) => hnf.

  Hint Resolve Rsym Rtrans.

  Lemma Rweaken : forall x y l,
    Forall (R x) l
    -> R x y
    -> Forall (R y) l.
    induction 1; t.
  Qed.

  Hint Resolve Rweaken.

  Lemma groupEqualTo_groupEqual : forall x xs,
    Forall (R x) xs
    -> groupEqual xs.
    induction 1; t.
  Qed.

  Hint Resolve groupEqualTo_groupEqual.

  Hint Resolve Folds.Forall_app.

  Lemma groupEqualTo_In : forall x y g,
    InR y g
    -> Forall (R x) g
    -> R x y.
    induction 2; t.
  Qed.

  Hint Immediate groupEqualTo_In.

  Hint Extern 1 (Forall _ _) => progress hnf.

  Lemma in_seq_correct : forall (a : A) (ls : list A),
    in_seq ls a = true -> InR a ls.
  Proof.
    induction ls; t.
  Qed.

  Hint Resolve in_seq_correct A_seq_correct.

  Lemma groupWith_sound : forall x xs grps,
    Forall groupEqual grps
    -> Forall (R x) xs
    -> Forall groupEqual (groupWith grps xs x).
    induction 1; t. eauto 10.
      apply in_seq_correct in H3. eauto 7.
  Qed.

  Hint Resolve groupWith_sound.

  Theorem addEquality_sound : forall x y grps,
    groupsEqual grps
    -> R x y
    -> groupsEqual (addEquality grps x y).
    induction 1; t;
      match goal with
        | [ H : _ |- _ ] => apply A_seq_correct in H || apply in_seq_correct in H
      end; eauto 7.
  Qed.

  Theorem inSameGroup_sound : forall grps, groupsEqual grps
    -> forall x y, inSameGroup grps x y = true
      -> R x y.
    induction 1; t;
      repeat match goal with
        | [ H : _ |- _ ] => apply A_seq_correct in H || apply in_seq_correct in H
      end; eauto 7.
  Qed.
End Grouper.

Section TransitivityProver.
  Variable types : list type.
  Variable fs : functions types.
  Section with_vars.
  Variables uvars vars : env types.

  Definition transitivity_summary : Type := list (list (expr types)).

  Coercion typeof_env : env >-> tenv.

  Definition eqD (e1 e2 : expr types) : Prop :=
    match typeof (typeof_funcs fs) uvars vars e1 with
      | None => False
      | Some t =>
        match exprD fs uvars vars e1 t, exprD fs uvars vars e2 t with
          | Some v1, Some v2 => v1 = v2
          | _, _ => False
        end
    end.

  Theorem eqD_refl : forall e1 e2, e1 = e2
    -> forall t, typeof (typeof_funcs fs) uvars vars e1 = Some t
      -> forall v, exprD fs uvars vars e1 t = Some v
        -> eqD e1 e2.
    t.
  Qed.

  Lemma nth_error_nil : forall T n,
    nth_error (@nil T) n = None.
  Proof.
    destruct n; simpl; auto.
  Qed.

(*
  Theorem eqD_refl_wt : forall e1 e2, e1 = e2 ->
    match is_well_typed (typeof_funcs fs) uvars vars e1 (typeof (typeof_funcs fs) uvars vars e1) return Prop with
      | None => True
      | Some t => eqD e1 e2
    end.
  Proof.
    intros; subst.
    case_eq (well_typed fs uvars vars e2); intros; auto.
    generalize is_well_typed_typeof.
    generalize well_typed_is_well_typed. intros.
    generalize H. apply H0 in H.
    generalize H.
    apply is_well_typed_correct in H.
    intros.
    apply H1 in H2. destruct H.
    eapply eqD_refl; eauto.
  Qed.
*)

  Fixpoint transitivityLearn (sum : transitivity_summary) (hyps : list (expr types)) : transitivity_summary :=
    match hyps with
      | nil => sum
      | h :: hyps' =>
        let grps := transitivityLearn sum hyps' in
          match h with
            | Equal t x y => addEquality (@expr_seq_dec  _) grps x y
            | _ => grps
          end
    end.
  Definition groupsOf := transitivityLearn nil.

  Definition transitivityEqProver (groups : transitivity_summary)
    (x y : expr types) := inSameGroup (@expr_seq_dec _) groups x y.

  Fixpoint proveEqual (groups : transitivity_summary) (e1 e2 : expr types) {struct e1} :=
    expr_seq_dec e1 e2 ||
      (inSameGroup (@expr_seq_dec _) groups e1 e2
        || match e1, e2 with
             | Func f1 args1, Func f2 args2 =>
               if eq_nat_dec f1 f2
                 then (fix proveEquals (es1 es2 : list (expr types)) :=
                   match es1, es2 with
                     | nil, nil => true
                     | e1 :: es1', e2 :: es2' => proveEqual groups e1 e2 && proveEquals es1' es2'
                     | _, _ => false
                   end) args1 args2
                 else false
             | _, _ => false
           end
    ).

  Definition transitivityProve (groups : transitivity_summary)
    (goal : expr types) :=
    match goal with
      | Equal _ x y => proveEqual groups x y
      | _ => false
    end.

  Hint Resolve addEquality_sound.
  Hint Immediate lookupAs_det.

  Ltac foundTypeof E := generalize (@exprD_principal _ fs uvars vars (typeof_funcs fs) uvars vars
    (typeof_env_WellTyped_env _) (typeof_env_WellTyped_env _) (typeof_funcs_WellTyped_funcs _) E);
  destruct (typeof (typeof_funcs fs) uvars vars E); intuition.

  Ltac foundDup E T1 T2 := match T1 with
                             | T2 => fail 1
                             | _ =>
                               assert (T1 = T2) by (apply (exprD_det fs uvars vars E);
                                 try match goal with
                                       | [ H : _ |- _ ] => solve [ intro; apply H with T1; t ]
                                     end); subst
                           end.

  Ltac eqD1 :=
    match goal with
      | [ _ : context[typeof _ _ _ ?E] |- _ ] => foundTypeof E
      | [ |- context[typeof _ _ _ ?E] ] => foundTypeof E
      | [ _ : context[exprD fs uvars vars ?E ?T1] |- context[exprD fs uvars vars ?E ?T2] ] => foundDup E T1 T2
      | [ _ : context[exprD fs uvars vars ?E ?T1], _ : context[exprD fs uvars vars ?E ?T2] |- _ ] => foundDup E T1 T2
      | [ x : tvar, H1 : forall y : tvar, _ |- False ] => apply H1 with x; t
    end.

  Ltac eqD := unfold eqD; intros; repeat eqD1; t.

  Theorem eqD_sym : forall x y : expr types, eqD x y -> eqD y x.
    unfold eqD; intros.
    eqD.
  Qed.

  Theorem eqD_trans : forall x y z : expr types, eqD x y -> eqD y z -> eqD x z.
    eqD.
  Qed.

  Hint Immediate eqD_sym eqD_trans.

  Theorem groupsOf_sound : forall hyps,
    AllProvable fs uvars vars hyps
    -> groupsEqual eqD (groupsOf hyps).
    induction hyps. intuition. simpl in *. constructor.

    intro. simpl in H. destruct H.
    specialize (IHhyps H0).

    t1.
    destruct a; auto.
    revert H; case_eq (exprD fs uvars vars (Equal t a1 a2) tvProp); intros; try contradiction.
    simpl in *. apply addEquality_sound; eauto.

    Focus 2.

    revert H.
    unfold eqD.
    case_eq (exprD fs uvars vars a1 t); try congruence; intros.
(*
    rewrite (exprD_typeof _ _ _ _ _ H). rewrite H. destruct (exprD fs uvars vars a2 t); try congruence.
    inversion H2. subst; auto.
*)
    admit. (** TODO : this isn't true in general, but the fact that everything is provable makes it true **)
    admit.
  Qed.
  End with_vars.

  Definition transitivityValid (uvars vars : env types) (sum : transitivity_summary) : Prop :=
    (forall ls, In ls sum -> forall e, In e ls -> ValidExp fs uvars vars e) ->
    groupsEqual (eqD uvars vars) sum.

  Definition transitivitySummarize := groupsOf.

  Theorem transitivitySummarizeCorrect : forall uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    transitivityValid uvars vars (transitivitySummarize hyps).
  Proof.
  Admitted.

  Theorem transitivityLearnCorrect : forall uvars vars sum,
    transitivityValid uvars vars sum -> forall hyps,
    AllProvable fs uvars vars hyps ->
    transitivityValid uvars vars (transitivityLearn sum hyps).
  Proof.
  Admitted.

  Theorem transitivityProverCorrect : ProverCorrect fs transitivityValid transitivityProve.
    admit.
(*
    unfold transitivityProver; hnf; intros;
      destruct goal; try discriminate;
        match goal with
          | [ H1 : _, H2 : _ |- _ ] =>
            apply (inSameGroup_sound eqD_sym eqD_trans expr_seq_dec
              (groupsOf_sound _ H1)) in H2
        end; hnf in *; simpl in *; eqD.
*)
  Qed.

  Theorem transitivityValid_extensible : forall (u g : env types) (f : transitivity_summary)
     (ue ge : list (sigT (tvarD types))),
   transitivityValid u g f -> transitivityValid (u ++ ue) (g ++ ge) f.
  Proof.
  Admitted.


  Definition transitivityProver : ProverT types :=
  {| Facts := transitivity_summary
   ; Summarize := transitivitySummarize
   ; Learn := transitivityLearn
   ; Prove := transitivityProve
   |}.

  Definition transitivityProver_correct : ProverT_correct transitivityProver fs.
  eapply Build_ProverT_correct with (Valid := transitivityValid);
    eauto using transitivityValid_extensible, transitivitySummarizeCorrect, transitivityLearnCorrect, transitivityProverCorrect.
  Qed.

End TransitivityProver.

Definition TransitivityProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => transitivityProver_correct fs
|}.

Ltac unfold_transitivityProver H :=
  match H with
    | tt =>
      cbv delta [
        transitivityProver proveEqual
        transitivitySummarize transitivityLearn transitivityProve

        groupsOf addEquality
        transitivityLearn
        inSameGroup
        expr_seq_dec
        in_seq
        groupWith
      ]
    | _ =>
      cbv delta [
        transitivityProver proveEqual
        transitivitySummarize transitivityLearn transitivityProve

        groupsOf addEquality
        transitivityLearn
        inSameGroup
        expr_seq_dec
        in_seq
        groupWith
      ] in H
  end.
