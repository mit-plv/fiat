Require Import CertifiedExtraction.Extraction.External.Core.

Definition List_pop `{FacadeWrapper av (list W)} : AxiomaticSpec av.
  refine {|
      PreCond := fun args =>
                   exists h t,
                     args = (wrap (cons h t)) :: nil;
      PostCond := fun args ret =>
                    exists h t,
                      args = (wrap (cons h t), Some (wrap t)) :: nil /\
                      ret = wrap h
    |}; spec_t.
Defined.

Definition List_empty `{FacadeWrapper av (list W)} : AxiomaticSpec av.
  refine {|
      PreCond := fun args =>
                   exists l: list W,
                     args = (wrap l) :: nil;
      PostCond := fun args ret =>
                    exists l: list W,
                      args = (wrap l, Some (wrap l)) :: nil /\
                      exists w, ret = wrap w /\ w = bool2w (match l with
                                                       | nil => true
                                                       | _ => false
                                                       end)
    |}; spec_t.
Defined.

Lemma CompileCallEmpty:
  forall `{FacadeWrapper av (list W)} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec av)) (tenv: Telescope av) ext
    (fempty : GLabelMap.key) (lst : list W),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap lst) ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    {{ tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[`vtest <-- (bool2w match lst with
                         | nil => true
                         | _ :: _ => false
                         end) as _]]::(DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  facade_eauto.
  rewrite <- remove_add_comm by congruence. (* FIXME *)
  apply DropName_remove.
  eauto.
  rewrite <- add_redundant_cancel; eauto.
Qed.

(* Lemma CompileCallEmpty: *)
(*   forall `{FacadeWrapper av (list W)} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec av)) (tenv: Telescope av) ext *)
(*     (fempty : GLabelMap.key) (lst : list W), *)
(*     vlst <> vtest -> *)
(*     vtest ∉ ext -> *)
(*     NotInTelescope vtest tenv -> *)
(*     vlst ∉ ext -> *)
(*     NotInTelescope vlst tenv -> *)
(*     GLabelMap.MapsTo fempty (Axiomatic List_empty) env -> *)
(*     {{ [[`vlst <-- lst as _]]::tenv }} *)
(*       Call vtest fempty (vlst :: nil) *)
(*     {{ [[`vtest <-- (bool2w match lst with *)
(*                          | nil => true *)
(*                          | _ :: _ => false *)
(*                          end) as _]]::[[`vlst <-- lst as _]]::tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   repeat match goal with *)
(*          | _ => SameValues_Facade_t_step *)
(*          | _ => facade_cleanup_call *)
(*          (* | [ H: ADT _ = ADT _ |- _ ] => inversion' H *) *)
(*          (* | [  |- context[wrap (FacadeWrapper := WrapInstance) ?x]     ] => rewrite WrapInstance_wrap *) *)
(*          (* | [ H: context[wrap (FacadeWrapper := WrapInstance) _] |- _ ] => rewrite WrapInstance_wrap in H *) *)
(*          (* | _ => rewrite WrapInstance_unwrap_wrap *) *)
(*          end. *)

(*   facade_eauto. *)
(*   facade_eauto. *)
(*   facade_eauto. *)
(*   facade_eauto. *)

(*   eapply (SameValues_PopExt' (H := WrapInstance (H := H))). (* FIXME *) *)
(*   facade_eauto. *)
(*   facade_eauto. *)
(* Qed. *)

Lemma CompileCallEmpty_spec:
  forall `{FacadeWrapper av (list W)} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec av)) (tenv: Telescope av) ext
    (fempty : GLabelMap.key) (lst : Comp (list W)),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic List_empty) env ->
    {{ [[`vlst <~~ lst as _]] :: tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[`vlst <~~ lst as ls]] :: [[`vtest <-- (bool2w match ls with
                                                | nil => true
                                                | _ :: _ => false
                                                end) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileCallPop:
  forall `{FacadeWrapper av (list W)} (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec av)) tenv ext
    (fpop : GLabelMap.key) head (tail : list W),
    vlst <> vhead ->
    vhead ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (head :: tail)) ->
    Lifted_not_mapsto_adt ext tenv vhead ->
    GLabelMap.MapsTo fpop (Axiomatic List_pop) env ->
    {{ tenv }}
      Call vhead fpop (vlst :: nil)
    {{ [[`vhead <-- head as _]]::[[`vlst <-- tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.
