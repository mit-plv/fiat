Require Import CompileDFacade.
Require Import FiatToFacade.Compiler.
Require Import List.

Notation argvar1 := "arg1".
Notation argvar2 := "arg2".
Notation argvars := (argvar1 :: argvar2 :: nil).
Notation retvar := "ret".

Unset Implicit Arguments.

Definition PairOfConditionsForCompileUnit av prog (pre_cond: _ -> _ -> Prop) post_cond imports :=
  (forall st value1 value2, 
     StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) -> 
     pre_cond value1 value2 -> DFacade.Safe (GLabelMap.map (@Axiomatic av) imports) prog st) /\
  (forall st st' value1 value2, 
     StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) -> 
     pre_cond value1 value2 -> DFacade.RunsTo (GLabelMap.map (@Axiomatic av) imports) prog st st' -> 
     exists ret, StringMapFacts.Submap (StringMapFacts.make_map (retvar :: nil) (ret :: nil)) st' /\
                 (forall x, x <> retvar -> not_mapsto_adt x st' = true) /\
                 post_cond value1 value2 ret).

Lemma two_conds_as_one :
  forall av prog (pre_cond: _ -> _ -> Prop) post_cond imports,
  (forall st value1 value2, 
           StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) -> 
           pre_cond value1 value2 -> 
           DFacade.Safe (GLabelMap.map (@Axiomatic av) imports) prog st /\
           forall st',
             DFacade.RunsTo (GLabelMap.map (@Axiomatic av) imports) prog st st' -> 
             exists ret, StringMapFacts.Submap (StringMapFacts.make_map (retvar :: nil) (ret :: nil)) st' /\
                         (forall x, x <> retvar -> not_mapsto_adt x st' = true) /\
                         post_cond value1 value2 ret)  <-> 
  PairOfConditionsForCompileUnit av prog pre_cond post_cond imports.
Proof.
  split; intros.
  
  { split; intros st; [ | intros st']; intros v1 v2 eqm precond; [ | intros runsto]; specialize (H st v1 v2 eqm precond).
    - intuition.
    - destruct H as (_ & H);
      specialize (H st' runsto);
      destruct H; eexists; eauto. }
  { destruct H as (safe & runsto).
    split;
      [ specialize (safe st value1 value2 H0 H1); intuition
      | intros; specialize (runsto st st' value1 value2 H0 H1 H); destruct_ex; eexists; eauto ].
  }
Defined.

Lemma pick_compile_helper :
    forall (TR TP : Type) (R : Comp TR) (P : TP -> TR -> Prop) 
           (retval : TR) (prog : TP),
      refine (r <- R;
              p <- {p : TP | P p r};
              ret (r, p)) (ret (retval, prog)) -> R ↝ retval /\ P prog retval.
Proof.
  unfold refine; intros * h; subst.
  specialize (h _ (AdditionalRefinementLemmas.eq_ret_compute _ _ _ eq_refl)).
  inversion_by computes_to_inv; autoinj; subst; intuition.
Qed.