Set Implicit Arguments.

Require Import Bedrock.IL Bedrock.Memory Coq.Strings.String Bedrock.sep.Locals Coq.Lists.List.

Definition upd_option vs x value :=
  match x with
    | None => vs
    | Some s => Locals.upd vs s value
  end.

Require Import Bedrock.Platform.Cito.FuncCore.
Export FuncCore.
Require Import ListFacts3.
Record InternalFuncSpec :=
  {
    Fun : FuncCore;
    NoDupArgVars : is_no_dup (ArgVars Fun) = true
  }.

Coercion Fun : InternalFuncSpec >-> FuncCore.

Require Import Bedrock.Platform.Cito.Syntax Bedrock.Platform.Cito.SemanticsExpr.
Require Import Bedrock.Platform.Cito.GLabel.
Require Import Bedrock.Platform.Cito.WordMap.
Require Import Bedrock.Platform.Cito.AxSpec.
Export AxSpec.

Section ADTValue.

  Variable ADTValue : Type.

  Definition Heap := WordMap.t ADTValue.

  Definition State := (vals * Heap)%type.

  Notation Value := (@Value ADTValue).
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Arguments SCA {ADTValue} _.
  Arguments ADT {ADTValue} _.

  Inductive Callee :=
  | Foreign : AxiomaticSpec -> Callee
  | Internal : InternalFuncSpec -> Callee.

  Definition word_adt_match (heap : Heap) (p : W * Value) :=
    let word := fst p in
    let in_ := snd p in
    match in_ with
      | SCA w => word = w
      | ADT a => WordMap.find word heap = Some a
    end.

  Definition disjoint_ptrs (pairs : list (W * Value)) :=
    let pairs := filter (fun p => is_adt (snd p)) pairs in
    NoDup (List.map fst pairs).

  Definition good_inputs heap pairs :=
    Forall (word_adt_match heap) pairs /\
    disjoint_ptrs pairs.

  Record ArgTriple :=
    {
      Word : W;
      ADTIn : Value;
      ADTOut : option ADTValue
    }.

  Definition store_out (heap : Heap) t :=
    match ADTIn t, ADTOut t with
      | SCA _, _ => heap
      | ADT _, None => WordMap.remove (Word t) heap
      | ADT _, Some a => WordMap.add (Word t) a heap
    end.

  Definition decide_ret addr (ret : Value) :=
    match ret with
      | SCA w => (w, None)
      | ADT a => (addr, Some a)
    end.

  Definition separated heap ret_w (ret_a : option ADTValue) :=
    ret_a = None \/ ~ @WordMap.In ADTValue ret_w heap.

  Definition heap_upd_option m k (v : option ADTValue) :=
    match v with
      | Some x => WordMap.add k x m
      | None => m
    end.

  (* Semantics *)

  Section Env.

    Variable env : (glabel -> option W) * (W -> option Callee).

    Inductive RunsTo : Stmt -> State -> State -> Prop :=
    | RunsToSkip : forall v, RunsTo Syntax.Skip v v
    | RunsToSeq :
        forall a b v v' v'',
          RunsTo a v v' ->
          RunsTo b v' v'' ->
          RunsTo (Syntax.Seq a b) v v''
    | RunsToIfTrue :
        forall cond t f v v',
          wneb (eval (fst v) cond) $0 = true ->
          RunsTo t v v' ->
          RunsTo (Syntax.If cond t f) v v'
    | RunsToIfFalse :
        forall cond t f v v',
          wneb (eval (fst v) cond) $0 = false ->
          RunsTo f v v' ->
          RunsTo (Syntax.If cond t f) v v'
    | RunsToWhileTrue :
        forall cond body v v' v'',
          let loop := While cond body in
          wneb (eval (fst v) cond) $0 = true ->
          RunsTo body v v' ->
          RunsTo loop v' v'' ->
          RunsTo loop v v''
    | RunsToWhileFalse :
        forall cond body v,
          let loop := While cond body in
          wneb (eval (fst v) cond) $0 = false ->
          RunsTo loop v v
    | RunsToCallInternal :
        forall var f args v spec vs_callee vs_callee' heap',
          let vs := fst v in
          let heap := snd v in
          let fs := snd env in
          fs (eval vs f) = Some (Internal spec) ->
          map (Locals.sel vs_callee) (ArgVars spec) = map (eval vs) args ->
          RunsTo (Body spec) (vs_callee, heap) (vs_callee', heap') ->
          let vs := upd_option vs var (Locals.sel vs_callee' (RetVar spec)) in
          let heap := heap' in
          RunsTo (Syntax.Call var f args) v (vs, heap)
    | RunsToCallForeign :
        forall var f args v spec triples addr ret heap',
          let vs := fst v in
          let heap := snd v in
          let fs := snd env in
          fs (eval vs f) = Some (Foreign spec) ->
          map (eval vs) args = map Word triples ->
          good_inputs heap (map (fun x => (Word x, ADTIn x)) triples) ->
          PreCond spec (map ADTIn triples) ->
          PostCond spec (map (fun x => (ADTIn x, ADTOut x)) triples) ret ->
          let heap := fold_left store_out triples heap in
          let t := decide_ret addr ret in
          let ret_w := fst t in
          let ret_a := snd t in
          separated heap ret_w ret_a ->
          let heap := heap_upd_option heap ret_w ret_a in
          let vs := upd_option vs var ret_w in
          WordMap.Equal heap' heap ->
          RunsTo (Syntax.Call var f args) v (vs, heap')
    | RunsToLabel :
        forall x lbl v w,
          fst env lbl = Some w ->
          RunsTo (Syntax.Label x lbl) v (Locals.upd (fst v) x w, snd v)
    | RunsToAssign :
        forall x e v,
          let vs := fst v in
          RunsTo (Syntax.Assign x e) v (Locals.upd vs x (eval vs e), snd v).

    CoInductive Safe : Stmt -> State -> Prop :=
    | SafeSkip :
        forall v, Safe Syntax.Skip v
    | SafeSeq :
        forall a b v,
          Safe a v ->
          (forall v', RunsTo a v v' -> Safe b v') ->
          Safe (Syntax.Seq a b) v
    | SafeIf :
        forall cond t f v,
          let b := wneb (eval (fst v) cond) $0 in
          b = true /\ Safe t v \/ b = false /\ Safe f v ->
          Safe (Syntax.If cond t f) v
    | SafeWhileTrue :
        forall cond body v,
          let loop := While cond body in
          wneb (eval (fst v) cond) $0 = true ->
          Safe body v ->
          (forall v', RunsTo body v v' -> Safe loop v') ->
          Safe loop v
    | SafeWhileFalse :
        forall cond body v,
          let loop := While cond body in
          wneb (eval (fst v) cond) $0 = false ->
          Safe loop v
    | SafeCallInternal :
        forall var f args v spec,
          let vs := fst v in
          let heap := snd v in
          let fs := snd env in
          fs (eval vs f) = Some (Internal spec) ->
          length (ArgVars spec) = length args ->
          (forall vs_arg,
             map (Locals.sel vs_arg) (ArgVars spec) = map (eval vs) args
             -> Safe (Body spec) (vs_arg, heap)) ->
          Safe (Syntax.Call var f args) v
    | SafeCallForeign :
        forall var f args v spec pairs,
          let vs := fst v in
          let heap := snd v in
          let fs := snd env in
          fs (eval vs f) = Some (Foreign spec) ->
          map (eval vs) args = map fst pairs ->
          good_inputs heap pairs ->
          PreCond spec (map snd pairs) ->
          Safe (Syntax.Call var f args) v
    | SafeLabel :
        forall x lbl v,
          fst env lbl <> None ->
          Safe (Syntax.Label x lbl) v
    | SafeAssign :
        forall x e v,
          Safe (Syntax.Assign x e) v.

    Section Safe_coind.
      Variable R : Stmt -> State -> Prop.

      Hypothesis SeqCase : forall a b v, R (Syntax.Seq a b) v -> R a v /\ forall v', RunsTo a v v' -> R b v'.

      Hypothesis IfCase : forall cond t f v, R (Syntax.If cond t f) v -> (wneb (eval (fst v) cond) $0 = true /\ R t v) \/ (wneb (eval (fst v) cond) $0 = false /\ R f v).

      Hypothesis WhileCase :
        forall cond body v,
          let loop := Syntax.While cond body in
          R loop v ->
          (wneb (eval (fst v) cond) $0 = true /\ R body v /\ (forall v', RunsTo body v v' -> R loop v')) \/
          (wneb (eval (fst v) cond) $0 = false).

      Hypothesis CallCase : forall var f args v,
        R (Syntax.Call var f args) v
        -> (exists spec, let vs := fst v in
          let heap := snd v in
            let fs := snd env in
              fs (eval vs f) = Some (Internal spec) /\
              length (ArgVars spec) = length args /\
              (forall vs_arg,
                map (Locals.sel vs_arg) (ArgVars spec) = map (eval vs) args
                -> R (Body spec) (vs_arg, heap)))
        \/ (exists spec, exists pairs, let vs := fst v in
          let heap := snd v in
            let fs := snd env in
              fs (eval vs f) = Some (Foreign spec) /\
              map (eval vs) args = map fst pairs /\
              good_inputs heap pairs /\
              PreCond spec (map snd pairs)).

      Hypothesis LabelCase : forall x lbl v,
        R (Syntax.Label x lbl) v
        -> fst env lbl <> None.

      Hint Constructors Safe.

      Ltac openhyp :=
        repeat match goal with
                 | H : _ /\ _ |- _  => destruct H
                 | H : _ \/ _ |- _ => destruct H
                 | H : exists x, _ |- _ => destruct H
               end.

      Ltac break_pair :=
        match goal with
          V : (_ * _)%type |- _ => destruct V
        end.

      Theorem Safe_coind : forall c v, R c v -> Safe c v.
        cofix; unfold State; intros; break_pair; destruct c.

        eauto.

        eapply SeqCase in H; openhyp; eauto.

        eapply IfCase in H; openhyp; eauto.

        eapply WhileCase in H; openhyp; eauto.

        eapply CallCase in H; openhyp; simpl in *; intuition eauto.

        eapply LabelCase in H; openhyp; eauto.

        eauto.
      Qed.

    End Safe_coind.

  End Env.

End ADTValue.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Definition RunsTo := @RunsTo ADTValue.

  Definition Safe := @Safe ADTValue.

  Definition Heap := @Heap ADTValue.

  Definition State := @State ADTValue.

  Definition ArgIn := @Value ADTValue.

  Definition ArgOut := option ADTValue.

  Definition Ret := @Value ADTValue.

  Definition ForeignFuncSpec := @AxiomaticSpec ADTValue.

  Definition Callee := @Callee ADTValue.

  Definition ArgTriple := @ArgTriple ADTValue.

  Definition word_adt_match := @word_adt_match ADTValue.

  Definition is_adt := @is_adt ADTValue.

  Definition disjoint_ptrs := @disjoint_ptrs ADTValue.

  Definition good_inputs := @good_inputs ADTValue.

  Definition store_out := @store_out ADTValue.

  Definition decide_ret := @decide_ret ADTValue.

  Definition separated := @separated ADTValue.

  Definition heap_upd_option := @heap_upd_option ADTValue.

  Definition Foreign := @Foreign ADTValue.

  Definition Internal := @Internal ADTValue.

  (* some shorthands for heap operations *)
  Require Import Coq.FSets.FMapFacts.
  Module Import P := Properties WordMap.
  Import F WordMap.

  Definition elt := ADTValue.

  Implicit Types m h : Heap.
  Implicit Types x y z k p w : key.
  Implicit Types e v a : elt.
  Implicit Types ls : list (key * elt).

  Definition heap_sel h p := find p h.

  Definition heap_mem := @In elt.

  Definition heap_upd h p v := add p v h.

  Definition heap_remove h p := remove p h.

  Definition heap_empty := @empty elt.

  Definition heap_merge := @update elt.

  Definition heap_elements := @elements elt.

  Definition heap_diff := @diff elt.

End Make.
