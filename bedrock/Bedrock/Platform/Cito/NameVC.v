Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep.

Definition NameNotInImports name imports :=
  fold_left
    (fun (b : bool) (p : string * string * assert) =>
       let '(m, _, _) := p in
       (b || (if string_dec m name then true else false))%bool)
    imports false = false.

Definition fst_2 A B C (x : A * B * C) := fst (fst x).
Notation fst2 := (@fst_2 _ _ _).

Lemma NotIn_NameNotInImports : forall imps mn, ~ In mn (map fst2 imps) -> NameNotInImports mn imps.
  clear.
  unfold NameNotInImports.
  induction imps; simpl; intros.
  eauto.
  destruct a; destruct p; simpl in *.
  destruct (string_dec s mn).
  contradict H.
  eauto.
  eapply IHimps.
  intuition.
Qed.

Definition f mod_name (mOpt : option (LabelMap.t unit))
           (p : string * assert *
                (forall imports : LabelMap.t assert,
                   importsGlobal imports -> cmd imports mod_name)) :=
  let '(modl, _, _) := p in
  match mOpt with
    | Some m =>
      let k := (modl, Local 0) in
      if LabelMap.mem (elt:=unit) k m
      then None
      else Some (LabelMap.add k tt m)
    | None => None
  end.

Definition NoDupFuncNames' init mod_name funcs :=
  match fold_left (@f mod_name) funcs (Some init)
  with
    | Some _ => True
    | None => False
  end.

Definition NoDupFuncNames := NoDupFuncNames' (LabelMap.empty unit).

Lemma NoDup_NoDupFuncNames' :
  forall mod_name funcs init,
    let names := map (fun f => fst (fst f)) funcs in
    NoDup names ->
    (forall x, List.In x names -> LabelMap.mem (elt := unit) (x, Local 0) init = false) ->
    @NoDupFuncNames' init mod_name funcs.
Proof.
  induction funcs; simpl; intuition.
  compute; eauto.
  unfold NoDupFuncNames' in *; simpl in *.
  erewrite H0 by eauto.
  eapply IHfuncs.
  inversion H; subst; eauto.
  intros.
  erewrite LabelFacts.add_neq_b.
  eapply H0.
  eauto.
  intuition.
  injection H2; intros.
  subst.
  inversion H; subst.
  contradiction.
Qed.

Lemma NoDup_NoDupFuncNames : forall mod_name funcs, NoDup (map (fun f => fst (fst f)) funcs) -> @NoDupFuncNames mod_name funcs.
  intros.
  eapply NoDup_NoDupFuncNames'.
  eauto.
  intros.
  eauto.
Qed.
