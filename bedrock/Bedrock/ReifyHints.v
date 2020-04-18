Require Import Coq.Lists.List.
Require Bedrock.Reflect Bedrock.ReifySepExpr.
Require Import Bedrock.Expr.
Require Import Bedrock.SepExpr Bedrock.SepLemma.
Require Import Bedrock.Env.

Module Make (SL : SepLemma).
  Module SE := SL.SE.
  Module SEP_REIFY := ReifySepExpr.ReifySepExpr SE.

  (* This tactic processes the part of a lemma statement after the quantifiers. *)
  Ltac collectTypes_hint' isConst P types k :=
    match P with
      | fun x => @?H x -> @?P x =>
         ReifyExpr.collectTypes_expr ltac:(isConst) H types ltac:(fun types =>
          collectTypes_hint' ltac:(isConst) P types k)
      | fun x => forall cs, @SE.ST.himp ?pcT ?stT cs (@?L x) (@?R x) =>
        SEP_REIFY.collectTypes_sexpr ltac:(isConst) L types ltac:(fun types =>
          SEP_REIFY.collectTypes_sexpr ltac:(isConst) R types k)
      | fun x => _ (@?L x) (@?R x) =>
        SEP_REIFY.collectTypes_sexpr ltac:(isConst) L types ltac:(fun types =>
          SEP_REIFY.collectTypes_sexpr ltac:(isConst) R types k)
    end.

  (* This tactic adds quantifier processing. *)
  Ltac collectTypes_hint isConst P types k :=
    match P with
      | fun xs : ?T => forall x : ?T', @?f xs x =>
        match T' with
          | PropX.codeSpec _ _ => fail 1
          | _ => match type of T' with
                   | Prop => fail 1
                   | _ => let P := eval simpl in (fun x : ReifyExpr.VarType (T * T') =>
                     f (@ReifyExpr.openUp _ T (@fst _ _) x) (@ReifyExpr.openUp _ T' (@snd _ _) x)) in
                   let types := Reflect.cons_uniq T' types in
                     collectTypes_hint ltac:(isConst) P types k
                 end
        end
      | _ => collectTypes_hint' ltac:(isConst) P types k
    end.

  (* Finally, this tactic adds a loop over all hints. *)
  Ltac collectTypes_hints unfoldTac isConst Ps types k :=
    match Ps with
      | tt => k types
      | (?P1, ?P2) =>
        collectTypes_hints unfoldTac ltac:(isConst) P1 types ltac:(fun types =>
          collectTypes_hints unfoldTac ltac:(isConst) P2 types k)
      | _ =>
        let T := type of Ps in
        let T := eval simpl in T in
        let T := unfoldTac T in
          collectTypes_hint ltac:(isConst) (fun _ : ReifyExpr.VarType unit => T) types k
    end.

  (* Now we repeat this sequence of tactics for reflection itself. *)

  Ltac reify_hint' pcType stateType isConst P types funcs preds vars k :=
    match P with
      | fun x => @?H x -> @?P x =>
        ReifyExpr.reify_expr isConst H types funcs (@nil tvar) vars ltac:(fun _ funcs H =>
          reify_hint' pcType stateType isConst P types funcs preds vars ltac:(fun funcs preds P =>
            let lem := eval simpl in (SL.Build_lemma (types := types) (pcType := pcType) (stateType := stateType)
              vars (H :: SL.Hyps P) (SL.Lhs P) (SL.Rhs P)) in
            k funcs preds lem))
      | fun x => forall cs, @SE.ST.himp _ _ cs (@?L x) (@?R x) =>
        SEP_REIFY.reify_sexpr isConst L types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _uvars funcs preds L =>
          SEP_REIFY.reify_sexpr isConst R types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _uvars funcs preds R =>
            let lem := constr:(SL.Build_lemma (types := types) (pcType := pcType) (stateType := stateType)
              vars nil L R) in
            k funcs preds lem))
      | fun x => _ (@?L x) (@?R x) =>
        SEP_REIFY.reify_sexpr isConst L types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _ funcs preds L =>
          SEP_REIFY.reify_sexpr isConst R types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _ funcs preds R =>
            let lem := constr:(SL.Build_lemma (types := types) (pcType := pcType) (stateType := stateType)
              vars nil L R) in
            k funcs preds lem))
    end.

  Ltac reify_hint pcType stateType isConst P types funcs preds vars k :=
    match P with
      | fun xs : ?T => forall x : ?T', @?f xs x =>
        match T' with
          | PropX.codeSpec _ _ => fail 1
          | _ => match type of T' with
                   | Prop => fail 1
                   | _ =>
                     let P := eval simpl in (fun x : ReifyExpr.VarType (T' * T) =>
                       f (@ReifyExpr.openUp _ T (@snd _ _) x) (@ReifyExpr.openUp _ T' (@fst _ _) x)) in
                     let T' := ReifyExpr.reflectType types T' in
                     reify_hint pcType stateType isConst P types funcs preds (T' :: vars) k
                   | _ => fail 3
                 end
          | _ => fail 2
        end
      | _ => reify_hint' pcType stateType isConst P types funcs preds vars k
    end.

  Ltac reify_hints unfoldTac pcType stateType isConst Ps types funcs preds k :=
    match Ps with
      | tt => k funcs preds (@nil (SL.lemma types pcType stateType)) || fail 2
      | (?P1, ?P2) =>
        reify_hints unfoldTac pcType stateType isConst P1 types funcs preds ltac:(fun funcs preds P1 =>
          reify_hints unfoldTac pcType stateType isConst P2 types funcs preds ltac:(fun funcs preds P2 =>
            k funcs preds (P1 ++ P2)))
        || fail 2
      | _ =>
        let T := type of Ps in
        let T := eval simpl in T in
        let T := unfoldTac T in
          reify_hint pcType stateType isConst (fun _ : ReifyExpr.VarType unit => T) types funcs preds (@nil tvar) ltac:(fun funcs preds P =>
            k funcs preds (P :: nil))
    end.

  (* Build proofs of combined lemma statements *)
  Ltac prove Ps :=
    match Ps with
      | tt => constructor
      | (?P1, ?P2) =>
           (apply Folds.Forall_app; [ prove P1 | prove P2 ])
        || (constructor; [ split; [ reflexivity | exact P1 ] | prove P2 ])
      | _ => constructor; [ split; [ reflexivity | exact Ps ] | constructor ]
    end.


  (* Unfold definitions in a list of types *)
  Ltac unfoldTypes types :=
    match eval hnf in types with
      | nil => types
      | ?T :: ?types =>
        let T := eval hnf in T in
          let types := unfoldTypes types in
            constr:(T :: types)
    end.

  (* Main entry point tactic, to generate a hint database *)
Ltac lift_signature_over_repr s rp :=
  let d := eval simpl Domain in (Domain s) in
  let r := eval simpl Range in (Range s) in
  let den := eval simpl Denotation in (Denotation s) in
  constr:(fun ts' => @Sig (Env.repr rp ts') d r den).

Ltac lift_signatures_over_repr fs rp :=
  match eval hnf in fs with
    | nil => constr:(fun ts' => @nil (signature (repr rp ts')))
    | ?f :: ?fs =>
      let f := lift_signature_over_repr f rp in
      let fs := lift_signatures_over_repr fs rp in
      constr:(fun ts' => (f ts') :: (fs ts'))
  end.

Ltac lift_ssignature_over_repr s rp pc st :=
  let d := eval simpl SE.SDomain in (SE.SDomain s) in
  let den := eval simpl SE.SDenotation in (SE.SDenotation s) in
  constr:(fun ts' => @SE.PSig (repr rp ts') pc st d den).

Ltac lift_ssignatures_over_repr fs rp pc st :=
  match eval hnf in fs with
    | nil => constr:(fun ts' => @nil (SE.predicate (repr rp ts') pc st))
    | ?f :: ?fs =>
      let f := lift_ssignature_over_repr f rp pc st in
      let fs := lift_ssignatures_over_repr fs rp pc st in
      constr:(fun ts' => (f ts') :: (fs ts'))
  end.

Ltac lift_expr_over_repr e rp :=
  match eval hnf in e with
    | @Expr.Const _ ?t ?v => constr:(fun ts => @Expr.Const (repr rp ts) t v)
    | Expr.Var ?v => constr:(fun ts => @Expr.Var (repr rp ts) v)
    | Expr.UVar ?v => constr:(fun ts => @Expr.UVar (repr rp ts) v)
    | Expr.Func ?f ?args =>
      let args := lift_exprs_over_repr args rp in
      constr:(fun ts => @Expr.Func (repr rp ts) f (args ts))
    | Expr.Equal ?t ?l ?r =>
      let l := lift_expr_over_repr l rp in
      let r := lift_expr_over_repr r rp in
      constr:(fun ts => @Expr.Equal (repr rp ts) t (l ts) (r ts))
    | Expr.Not ?e1 =>
      let e1 := lift_expr_over_repr e1 rp in
      constr:(fun ts => @Expr.Not (repr rp ts) (e1 ts))
  end
with lift_exprs_over_repr es rp :=
  match eval hnf in es with
    | nil => constr:(fun ts => @nil (expr (repr rp ts)))
    | ?e :: ?es =>
      let e := lift_expr_over_repr e rp in
      let es := lift_exprs_over_repr es rp in
      constr:(fun ts => e ts :: es ts)
  end.

Ltac lift_sexpr_over_repr e rp pc st :=
  match eval hnf in e with
    | @SE.Emp _ _ _ => constr:(fun ts => @SE.Emp (repr rp ts) pc st)
    | @SE.Inj _ _ _ ?e =>
      let e := lift_expr_over_repr e rp in
      constr:(fun ts => @SE.Inj (repr rp ts) pc st (e ts))
    | @SE.Star _ _ _ ?l ?r =>
      let l := lift_sexpr_over_repr l rp pc st in
      let r := lift_sexpr_over_repr r rp pc st in
      constr:(fun ts => @SE.Star (repr rp ts) pc st (l ts) (r ts))
    | @SE.Exists _ _ _ ?t ?e =>
      let e := lift_sexpr_over_repr e rp pc st in
      constr:(fun ts => @SE.Exists (repr rp ts) pc st t (e ts))
    | @SE.Func _ _ _ ?f ?args =>
      let args := lift_exprs_over_repr args rp in
      constr:(fun ts => @SE.Func (repr rp ts) pc st f (args ts))
    | @SE.Const _ _ _ ?b => constr:(fun ts => @SE.Const (repr rp ts) pc st b)
  end.

Ltac lift_lemma_over_repr lm rp pc st :=
  match eval hnf in lm with
    | {| SL.Foralls := ?f
       ; SL.Hyps := ?h
       ; SL.Lhs := ?l
       ; SL.Rhs := ?r
       |} =>
    let h := lift_exprs_over_repr h rp in
    let l := lift_sexpr_over_repr l rp pc st in
    let r := lift_sexpr_over_repr r rp pc st in
    constr:(fun ts => {| SL.Foralls := f
                       ; SL.Hyps := h ts
                       ; SL.Lhs := l ts
                       ; SL.Rhs := r ts
                       |})
  end.
Ltac lift_lemmas_over_repr lms rp pc st :=
  match lms with
    | nil => constr:(fun ts => @nil (SL.lemma (repr rp ts) pc st))
    | ?lml ++ ?lmr =>
      let lml := lift_lemmas_over_repr lml rp pc st in
      let lmr := lift_lemmas_over_repr lmr rp pc st in
      constr:(fun ts => lml ts ++ lmr ts)
    | ?lm :: ?lms =>
      let lm := lift_lemma_over_repr lm rp pc st in
      let lms := lift_lemmas_over_repr lms rp pc st in
      constr:(fun ts => lm ts :: lms ts)
  end.

(*
Require TypedPackage.
Module Packaged (CE : TypedPackage.CoreEnv).

(*
  (** Package hints together with their environment/parameters. *)
  Record hints := {
    Types : Repr type;
    Functions : forall ts, Repr (signature (repr Types ts));
    PcType : tvar;
    StateType : tvar;
    Predicates : forall ts, Repr (SE.predicate (Env.repr Types ts) PcType StateType);
    Hints : forall ts, hintsPayload (repr Types ts) PcType StateType;
    HintsOk : forall ts fs ps, hintsSoundness (repr (Functions ts) fs) (repr (Predicates ts) ps) (Hints ts)
  }.
*)

  Module PACK := TypedPackage.Make SE CE.

  Ltac prepareHints unfoldTac pcType stateType isConst env fwd bwd ret :=
    let types :=
      match type of env with
        | PACK.TypeEnv =>
          let ts := eval cbv beta iota zeta delta [ env PACK.applyTypes PACK.Types ] in (PACK.applyTypes env nil) in
          eval simpl in ts
        | PACK.TypeEnv =>
          let ts := eval cbv beta iota zeta delta [ PACK.applyTypes PACK.Types ] in (PACK.applyTypes env nil) in
          eval simpl in ts
      end
    in
    collectTypes_hints unfoldTac isConst fwd (@nil Type) ltac:(fun rt =>
      collectTypes_hints unfoldTac isConst bwd rt ltac:(fun rt =>
        let rt := constr:((pcType : Type) :: (stateType : Type) :: rt) in
        let types := ReifyExpr.extend_all_types rt types in
        let pcT := ReifyExpr.reflectType types pcType in
        let stateT := ReifyExpr.reflectType types stateType in
        let funcs := eval simpl in (PACK.applyFuncs_red env types nil) in
        let preds := eval simpl in (PACK.applyPreds_red env types nil) in
        (reify_hints unfoldTac pcT stateT isConst fwd types funcs preds ltac:(fun funcs preds fwd' =>
          reify_hints unfoldTac pcT stateT isConst bwd types funcs preds ltac:(fun funcs preds bwd' =>
            let types_r := eval cbv beta iota zeta delta [ listToRepr ] in (listToRepr types EmptySet_type) in
            let types_rV := fresh "types" in
            (pose (types_rV := types_r) || fail 1000);
            let funcs_r := lift_signatures_over_repr funcs types_rV in
            let funcs_r := eval cbv beta iota zeta delta [ listToRepr ] in (fun ts => listToRepr (funcs_r ts) (Default_signature (repr types_rV ts))) in
            let funcs_rV := fresh "funcs" in
            pose (funcs_rV := funcs_r) ;
            let preds_r := lift_ssignatures_over_repr preds types_rV pcT stateT in
            let preds_rV := fresh "preds" in
            let preds_r := eval cbv beta iota zeta delta [ listToRepr ] in (fun ts => listToRepr (preds_r ts) (SE.Default_predicate (repr types_rV ts) pcT stateT)) in
            pose (preds_rV := preds_r) ;
            let fwd' := lift_lemmas_over_repr fwd' types_rV pcT stateT in
            let bwd' := lift_lemmas_over_repr bwd' types_rV pcT stateT in
            let pf := fresh "fwd_pf" in
            assert (pf : forall ts fs ps, hintsSoundness (repr (funcs_rV ts) fs) (repr (preds_rV ts) ps) ({| Forward := fwd' ts ; Backward := bwd' ts |})) by
              (abstract (constructor; [ prove fwd | prove bwd ])) ;
            let res := constr:(
              {| Types      := types_rV
               ; PcType     := pcT
               ; StateType  := stateT
               ; Functions  := funcs_rV
               ; Predicates := preds_rV
               ; Hints      := fun ts => {| Forward := fwd' ts ; Backward := bwd' ts |}
               ; HintsOk    := pf
               |}) in ret res))))).

  (* Main entry point to simplify a goal *)
(*
  Ltac unfolder isConst hs bound :=
    intros;
      let types := eval simpl in (repr (Types hs) nil) in
      match goal with
        | [ |- ST.himp _ ?P ?Q ] =>
          SEP_REIFY.collectTypes_sexpr isConst P (@nil Type) ltac:(fun rt =>
          SEP_REIFY.collectTypes_sexpr isConst Q rt ltac:(fun rt =>
            let types := extend_all_types rt types in
            let funcs := eval simpl in (repr (Functions hs types) nil) in
            let preds := eval simpl in (repr (Predicates hs types) nil) in
            let pc := eval simpl in (PcType hs) in
            let state := eval simpl in (StateType hs) in
            SEP_REIFY.reify_sexpr isConst P types funcs pc state preds (@nil type) (@nil type) ltac:(fun uvars funcs preds P =>
            SEP_REIFY.reify_sexpr isConst Q types funcs pc state preds (@nil type) (@nil type) ltac:(fun uvars funcs preds Q =>
            let proverC := constr:(@Provers.reflexivityProver_correct types funcs) in
            apply (@unfolderOk types funcs pc state preds (Hints hs types) _ (HintsOk hs types funcs preds) proverC bound P Q)))))
      end.
*)

(*
  Module TESTS.
    Section Tests.
    Variables pc state : Type.

    Variable f : nat -> ST.hprop pc state nil.
    Variable h : bool -> unit -> ST.hprop pc state nil.
    Variable g : bool -> nat -> nat -> nat.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Definition nat_type := {|
      Impl := nat;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None
                       end
      |}.

    Definition bool_type := {|
      Impl := bool;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None
                       end
      |}.

    Definition unit_type := {|
      Impl := unit;
      Eq := fun x y => match equiv_dec x y with
                         | left pf => Some pf
                         | _ => None
                       end
      |}.

    Definition types0 := nat_type :: bool_type :: unit_type :: nil.

    Definition env0 : PACK.TypeEnv  :=
      {| PACK.Types := listToRepr
           ({| Impl := pc ; Eq := fun _ _ => None |} ::
            {| Impl := state ; Eq := fun _ _ => None |} :: nil) EmptySet_type
       ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
       ; PACK.Preds := fun ts => nil_Repr (SE.Default_predicate _ _ _)
      |}.

    Fixpoint assumptionProver (types : list type) (Hs : list (expr types)) (P : expr types) :=
      match Hs with
        | nil => false
        | H :: Hs' => match expr_seq_dec H P with
                        | Some _ => true
                        | None => assumptionProver Hs' P
                      end
      end.

    Hypothesis Hemp : forall cs, ST.himp cs (ST.emp pc state) (ST.emp pc state).
    Hypothesis Hf : forall cs, ST.himp cs (f 0) (ST.emp _ _).
    Hypothesis Hh : forall cs, ST.himp cs (h true tt) (ST.star (h true tt) (f 13)).

    Hypothesis Hf0 : forall n cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh0 : forall b u cs, ST.himp cs (h b u) (ST.star (h (negb b) tt) (f 13)).

    Hypothesis Hf1 : forall n, n <> 0 -> forall cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh1 : forall b u, b = false -> u <> tt -> forall cs, ST.himp cs (h b u) (ST.star (h b tt) (f 13)).


    (** * Creating hint databases *)

    Ltac prepare := prepareHints ltac:(fun x => x) pc state isConst env0.

    Definition hints_emp : hints.
      prepare (Hemp, Hf) (Hemp, Hf, Hh) ltac:(fun x => refine x).
    Defined.

    Definition hints_tt : hints.
      prepare tt tt ltac:(fun x => refine x).
    Defined.
    End Tests.
  End TESTS.
*)
End Packaged.
*)

End Make.
