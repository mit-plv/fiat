Require Import CertifiedExtraction.Extraction.External.Core.

Definition List_pop : AxiomaticSpec (list W).
  refine {|
      PreCond := fun args =>
                   exists h t,
                     args = (ADT (cons h t)) :: nil;
      PostCond := fun args ret =>
                    exists h t,
                      args = (ADT (cons h t), Some t) :: nil /\
                      ret = SCA (list W) h
    |}; spec_t.
Defined.

Definition List_empty : AxiomaticSpec (list W).
  refine {|
      PreCond := fun args =>
                   exists l,
                     args = (ADT l) :: nil;
      PostCond := fun args ret =>
                    exists l,
                      args = (ADT l, Some l) :: nil /\
                      exists w, ret = SCA _ w /\ w = bool2w (match l with
                                                       | nil => true
                                                       | _ => false
                                                       end)
    |}; spec_t.
Defined.

Lemma CompileCallEmpty:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec (list W))) tenv ext
    (fempty : GLabelMap.key) (lst : list W),
    vlst <> vtest ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    {{ [[vlst <-- ADT lst as _]]::tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[vtest <-- SCA (list W) (bool2w match lst with
                                      | nil => true
                                      | _ :: _ => false
                                      end) as _]]::[[vlst <-- ADT lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call).

  facade_eauto.
  facade_eauto.
  facade_eauto.
  facade_eauto.
  info_eauto 3 with SameValues_db call_helpers_db.
  facade_eauto.
  facade_eauto.
  facade_eauto.
  facade_eauto.
  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileCallEmpty':
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec (list W))) tenv ext
    (fempty : GLabelMap.key) (lst : list W),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_MapsTo ext tenv vlst (ADT lst) ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    {{ tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[vtest <-- SCA (list W) (bool2w match lst with
                                      | nil => true
                                      | _ :: _ => false
                                      end) as _]]::(DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ =>  SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t
         end.
  facade_eauto.
  facade_eauto.
  rewrite <- remove_add_comm by congruence.
  apply DropName_remove.
  eauto.
  rewrite <- add_redundant_cancel; eauto.
Qed.

Lemma CompileCallPop':
  forall (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec (list W))) tenv ext
    (fpop : GLabelMap.key) head (tail : list W),
    vlst <> vhead ->
    vhead ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (ADT (head :: tail)) ->
    Lifted_not_mapsto_adt ext tenv vhead ->
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    {{ tenv }}
      Call vhead fpop (vlst :: nil)
    {{ [[vhead <-- SCA (list W) head as _]]::[[vlst <-- ADT tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ =>  SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t
         end;
  facade_eauto.
Qed.
