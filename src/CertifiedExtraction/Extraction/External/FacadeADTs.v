Require Import CertifiedExtraction.Extraction.External.Core.

Unset Implicit Arguments.

Definition List_pop {av} A `{FacadeWrapper (Value av) A} `{FacadeWrapper av (list A)} : AxiomaticSpec av.
  refine {|
      PreCond := fun args =>
                   exists (h: A) t,
                     args = (wrap (cons h t)) :: nil;
      PostCond := fun args ret =>
                    exists (h: A) t,
                      args = (wrap (cons h t), Some (wrap t)) :: nil /\
                      ret = wrap h
    |}; spec_t.
Defined.

Definition List_empty {av} A `{FacadeWrapper (Value av) A} `{FacadeWrapper av (list A)} : AxiomaticSpec av.
  refine {|
      PreCond := fun args =>
                   exists l: list A,
                     args = (wrap l) :: nil;
      PostCond := fun args ret =>
                    exists l: list A,
                      args = (wrap l, Some (wrap l)) :: nil /\
                      exists w, ret = wrap w /\ w = bool2w (match l with
                                                       | nil => true
                                                       | _ => false
                                                       end)
    |}; spec_t.
Defined.

Set Implicit Arguments.

Lemma CompileCallEmpty:
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper av (list A)} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec av)) (tenv: Telescope av) ext
    (fempty : GLabelMap.key) (lst : list A),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap lst) ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty _)) env ->
    {{ tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[`vtest ->> (bool2w match lst with
                         | nil => true
                         | _ :: _ => false
                         end) as _]]::(DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  [ facade_eauto.. | ].
  rewrite <- remove_add_comm by congruence.
  apply DropName_remove.
  eauto.
  rewrite <- add_redundant_cancel; eauto.
Qed.

Lemma CompileCallEmpty_spec:
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper av (list A)} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec av)) (tenv: Telescope av) ext
    (fempty : GLabelMap.key) (lst : Comp (list A)),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    {{ [[`vlst ~~> lst as _]] :: tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[`vlst ~~> lst as ls]] :: [[`vtest ->> (bool2w match ls with
                                                | nil => true
                                                | _ :: _ => false
                                                end) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileCallPop:
  forall `{FacadeWrapper (Value av) A} `{FacadeWrapper av (list A)} (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec av)) tenv ext
    (fpop : GLabelMap.key) head (tail : list A),
    vlst <> vhead ->
    vhead ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (head :: tail)) ->
    Lifted_not_mapsto_adt ext tenv vhead ->
    GLabelMap.MapsTo fpop (Axiomatic (List_pop _)) env ->
    {{ tenv }}
      Call vhead fpop (vlst :: nil)
    {{ [[`vhead ->> head as _]]::[[`vlst ->> tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.
