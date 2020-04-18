(** This file contains record definitions for
 ** type, function and predicate environments.
 **)
Require Import Bedrock.Expr Bedrock.SepExpr.
Require Import Bedrock.Env.

Set Implicit Arguments.
Set Strict Implicit.

Module Type CoreEnv.
  Parameter core : Repr type.
  Parameter pc : tvar.
  Parameter st : tvar.
End CoreEnv.

Module Type Package.
  Declare Module SEP : SepExpr.
  Declare Module CE : CoreEnv.

  Record TypeEnv : Type :=
  { Types : Repr type
  ; Funcs : forall ts, Repr (signature (repr CE.core (repr Types ts)))
  ; Preds : forall ts,
    Repr (SEP.predicate (repr CE.core (repr Types ts)) CE.pc CE.st)
  }.

  Section Apps.
    Variable TE : TypeEnv.

    Definition applyTypes (ls : list type) : list type :=
      repr CE.core (repr (Types TE) ls).
    Definition applyFuncs ts (ls : functions (applyTypes ts)) : functions (applyTypes ts) :=
      repr (Funcs TE ts) ls.
    Definition applyPreds ts (ls : SEP.predicates (applyTypes ts) CE.pc CE.st) : SEP.predicates (applyTypes ts) CE.pc CE.st :=
      repr (Preds TE ts) ls.
  End Apps.


  (** These are reducible by [simpl] **)
  Definition applyTypes_red TE (ls : list type) : list type :=
    match TE with
      | {| Types := ts |} =>
        repr CE.core (repr ts ls)
    end.
  Definition applyFuncs_red TE ts : functions (applyTypes TE ts) -> functions (applyTypes TE ts) :=
    match TE with
      | {| Types := ts' ; Funcs := fs |} => fun ls =>
        repr (fs ts) ls
    end.
  Definition applyPreds_red TE ts : SEP.predicates (applyTypes TE ts) CE.pc CE.st -> SEP.predicates (applyTypes TE ts) CE.pc CE.st :=
    match TE with
      | {| Types := ts' ; Preds := ps |} => fun ls =>
        repr (ps ts) ls
    end.

  Ltac glue_env l r ret :=
    let res := constr:(
      let types := Env.repr_combine (Types l) (Types r) in
      {| Types := types
       ; Funcs := fun ts => Env.repr_combine (Funcs l (Env.repr types ts)) (Funcs r (Env.repr types ts))
       ; Preds := fun ts => Env.repr_combine (Preds l (Env.repr types ts)) (Preds r (Env.repr types ts))
       |})
    in
    ret res.

End Package.

Module Type AlgoTypes (SEP : SepExpr) (CE : CoreEnv).
  Parameter AlgoImpl  : list type -> Type.
  Parameter AlgoProof : forall ts : list type,
    functions (repr CE.core ts) ->
    SEP.predicates (repr CE.core ts) CE.pc CE.st ->
    AlgoImpl ts -> Type.
End AlgoTypes.

Module Make (SEP' : SepExpr) (CE' : CoreEnv) <: Package with Module SEP := SEP' with Module CE := CE'.
  Module SEP := SEP'.
  Module CE := CE'.

  Section TypeEnv.
    Record TypeEnv : Type :=
    { Types : Repr type
    ; Funcs : forall ts, Repr (signature (repr CE.core (repr Types ts)))
    ; Preds : forall ts, Repr (SEP.predicate (repr CE.core (repr Types ts)) CE.pc CE.st)
    }.

    Variable TE : TypeEnv.

    Definition applyTypes (ls : list type) : list type :=
      repr CE.core (repr (Types TE) ls).
    Definition applyFuncs ts (ls : functions (applyTypes ts)) : functions (applyTypes ts) :=
      repr (Funcs TE ts) ls.
    Definition applyPreds ts (ls : SEP.predicates (applyTypes ts) CE.pc CE.st) : SEP.predicates (applyTypes ts) CE.pc CE.st :=
      repr (Preds TE ts) ls.

  End TypeEnv.

  Definition applyTypes_red TE (ls : list type) : list type :=
    match TE with
      | {| Types := ts |} =>
        repr CE.core (repr ts ls)
    end.
  Definition applyFuncs_red TE ts : functions (applyTypes TE ts) -> functions (applyTypes TE ts) :=
    match TE with
      | {| Types := ts' ; Funcs := fs |} => fun ls =>
        repr (fs ts) ls
    end.
  Definition applyPreds_red TE ts : SEP.predicates (applyTypes TE ts) CE.pc CE.st -> SEP.predicates (applyTypes TE ts) CE.pc CE.st :=
    match TE with
      | {| Types := ts' ; Preds := ps |} => fun ls =>
        repr (ps ts) ls
    end.

End Make.

Module AlgoPack (P : Package) (A : AlgoTypes P.SEP P.CE).

  Record TypedPackage : Type :=
  { Env   : P.TypeEnv
  ; Algos : forall ts, A.AlgoImpl ts
  ; Algos_correct : forall ts (fs : functions (P.applyTypes Env ts)) ps,
    @A.AlgoProof (repr (P.Types Env) ts) (P.applyFuncs Env ts fs) (P.applyPreds Env ts ps) (Algos _)
  }.

  (** given to [TypedPackage]s, combines them and passes the combined [TypedPackage]
   ** to [k].
   ** This tactic will fail if any of the environments are not compatible.
   **)
  Ltac glue_pack composite composite_correct l r ret :=
    P.glue_env (Env l) (Env r) ltac:(fun nenv' =>
      let res := constr:(
        let nenv := nenv' in
        let types := P.Types nenv in
        {| Env   := nenv
         ; Algos := fun ts => composite (Algos l (P.applyTypes nenv ts)) (Algos r (Env.repr types ts))
         ; Algos_correct := fun ts fs ps =>
           composite_correct
             (Algos_correct l (P.applyTypes nenv ts) (P.applyFuncs nenv fs) (P.applyPreds nenv ps))
             (Algos_correct r (P.applyTypes nenv ts) (P.applyFuncs nenv fs) (P.applyPreds nenv ps))
         |})
      in
      ret res).
(*
(**
      let algosL := constr:(fun ts => Algos l (applyTypes nenvEnv.repr ntypesV ts)) in
      let algosR := constr:(fun ts => Algos r (Env.repr ntypesV ts)) in
      let algosCL :=
        constr:(fun ts fs ps =>
          Algos_correct l (Env.repr ntypesV ts)
          (Env.repr (nfuncsV ts) fs)
          (Env.repr (npredsV ts) ps)) in
      let algosCR :=
        constr:(fun ts fs ps =>
          Algos_correct r (Env.repr ntypesV ts)
          (Env.repr (nfuncsV ts) fs)
          (Env.repr (npredsV ts) ps)) in
      let pf := constr:(fun ts fs ps => AllAlgos_correct_composite (algosCL ts fs ps) (algosCR ts fs ps)) in
      opaque pf ltac:(fun pf =>
      let res :=
        constr:{|
          Types := ntypesV;
          Funcs := nfuncsV;
          Preds := npredsV;
          Algos := fun ts => AllAlgos_composite (algosL ts) (algosR ts);
          Algos_correct := pf
        |} in
        ret res)).
**)

  Ltac refine_glue_pack l r :=
    let reduce_repr e := e in
    let opaque v k := k v in
    match eval hnf in l with
      | @Build_TypedPackage ?CT ?PC ?ST ?SAT ?READ ?WRITE ?tl ?fl ?pl ?al ?acl =>
        match eval hnf in r with
        | @Build_TypedPackage _ _ _ _ _ _ ?tr ?fr ?pr ?ar ?acr =>
          refine (
              let types := repr_combine tl tr in
              let funcs := fun ts => repr_combine (fl (repr types ts)) (fr (repr types ts)) in
              let preds := fun ts => repr_combine (pl (repr types ts)) (pr (repr types ts)) in
              @Build_TypedPackage CT PC ST SAT READ WRITE
                types funcs preds
                (fun ts => AllAlgos_composite (al (repr types ts)) (ar (repr types ts)))
                _
               );
          (subst; abstract exact (fun ts fs ps => AllAlgos_correct_composite
                  (acl (repr (repr_combine tl tr) ts)
                       (repr (repr_combine (fl (repr (repr_combine tl tr) ts)) (fr (repr (repr_combine tl tr) ts))) fs)
                       (repr (repr_combine (pl (repr (repr_combine tl tr) ts)) (pr (repr (repr_combine tl tr) ts))) ps))
                  (acr (repr (repr_combine tl tr) ts)
                       (repr (repr_combine (fl (repr (repr_combine tl tr) ts)) (fr (repr (repr_combine tl tr) ts))) fs)
                       (repr (repr_combine (pl (repr (repr_combine tl tr) ts)) (pr (repr (repr_combine tl tr) ts))) ps))))
      end
  end.

(*
Ltac hlist_from_tuple tpl acc :=
  match tpl with
    | tt => acc
    | (?L, ?R) =>
      let acc := hlist_from_tuple R acc in
      hlist_from_tuple L acc
    | _ => constr:(@HCons _ _ _ _ tpl acc)
  end.
*)

(** given a tuple or list of [TypedPackage]s, this tactic combines them all and calls [k] with
 ** the result.
 **)
Ltac glue_packs packs k :=
  match type of packs with
    | TypedPackage _ _ _ _ _ _ => k packs
    | _ =>
      match packs with
        | tt => k BedrockPackage.bedrock_package
        | nil => k BedrockPackage.bedrock_package
        | ?L :: ?R =>
          glue_packs R ltac:(fun R => glue_pack L)
        | (?L, ?R) =>
          glue_packs L ltac:(fun L =>
          glue_packs R ltac:(fun R =>
            glue_pack L R k))
      end
  end.

(** TODO: is there a way to make this more efficient? **)
Ltac opaque_pack pack :=
  match eval hnf in pack with
    | @Build_TypedPackage ?CT ?PC ?ST ?SAT ?READ ?WRITE ?tl ?fl ?pl ?al ?acl =>
      refine ({|
        Types := tl ;
        Funcs := fl ;
        Preds := pl ;
        Algos := al ;
        Algos_correct := _
      |});
      abstract (exact acl)
  end.
*)

End AlgoPack.
