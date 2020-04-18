Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.Basics.

(* Lemma CompileBinop: *)
(*   forall {av} name var1 var2 (val1 val2: W) ext op tenv, *)
(*     name ∉ ext -> *)
(*     NotInTelescope name tenv -> *)
(*     StringMap.MapsTo var1 (SCA av val1) ext -> *)
(*     StringMap.MapsTo var2 (SCA av val2) ext -> *)
(*     forall env, *)
(*     {{ tenv }} *)
(*       Assign name (Binop op (Var var1) (Var var2)) *)
(*     {{ [[name ->> (SCA _ (eval_binop (inl op) val1 val2)) as _]]::tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   SameValues_Facade_t. *)
(* Qed. *)

Definition WrapOpInExpr op :=
  match op with
  | inl o => Binop o
  | inr t => TestE t
  end.

Lemma CompileBinopOrTest:
  forall {av} name var1 var2 (val1 val2: W) ext op (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var1 (wrap val1) ext ->
    StringMap.MapsTo var2 (wrap val2) ext ->
    forall env,
    {{ tenv }}
      Assign name (WrapOpInExpr op (Var var1) (Var var2))
    {{ [[`name ->> (eval_binop op val1 val2) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  destruct op;
  SameValues_Facade_t.
Qed.

(* Lemma CompileBinopB_util: *)
(*   forall {T} k1 k2 k3 {v1 v2 v3} (fmap: StringMap.t T), *)
(*     k1 <> k2 -> k2 <> k3 -> k1 <> k3 -> *)
(*     StringMap.Equal ([`k3 |> v3] ::[`k2 |> v2]::[`k1 |> v1]::fmap) *)
(*                     ([`k1 |> v1] ::[`k2 |> v2]::[`k3 |> v3]::fmap). *)
(* Proof. *)
(*   unfold StringMap.Equal; intros; *)
(*   destruct (StringMap.E.eq_dec y k1); *)
(*   destruct (StringMap.E.eq_dec y k2); *)
(*   destruct (StringMap.E.eq_dec y k3); *)
(*   SameValues_Facade_t. *)
(* Qed. *)

(* Lemma CompileBinopB_util2: *)
(*   forall {av : Type} (var1 var2 var3 : StringMap.key) *)
(*     (val1 val2 val3 : _) (ext : StringMap.t (Value av)), *)
(*     var1 <> var2 -> *)
(*     var2 <> var3 -> *)
(*     var1 <> var3 -> *)
(*     var1 ∉ ext -> *)
(*     var2 ∉ ext -> *)
(*     var3 ∉ ext -> *)
(*     [`var1 |> val1] *)
(*       ::[`var2 |> val2] *)
(*       ::[`var3 |> val3]::ext *)
(*       ≲ [[`var1 ->> val1 as _]] *)
(*       ::[[`var2 ->> val2 as _]] *)
(*       ::[[`var3 ->> val3 as _]]::Nil ∪ ext. *)
(* Proof. *)
(*   intros. *)
(*   repeat apply Cons_PopExt; try decide_not_in. *)
(*   rewrite CompileBinopB_util by assumption. *)
(*   apply SameValues_Nil_always. *)
(* Qed. *)

(* Lemma CompileBinop_with_dealloc_USELESS: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2 p3, *)
(*     name ∉ ext -> *)
(*     var1 ∉ ext -> *)
(*     var2 ∉ ext -> *)
(*     var1 <> var2 -> *)
(*     var1 <> name -> *)
(*     var2 <> name -> *)
(*     {{ Nil }} *)
(*       p1 *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::Nil }} *)
(*       p2 *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::[[`var2 ->> SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::[[`var2 ->> SCA _ val2 as _]]::[[`name ->> (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} *)
(*       p3 *)
(*     {{ [[ret (SCA _ val1) as _]]::[[ret (SCA _ val2) as _]]::[[`name ->> (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p1 (Seq p2 (Seq (Assign name (Binop op (Var var1) (Var var2))) p3))) *)
(*     {{ [[`name ->> (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t; *)
(*  *)
(*   assert ([`name |> SCA av (IL.evalBinop op val1 val2)]::st'0 *)
(*         ≲ [[`var1 ->> SCA av val1 as _]] *)
(*           ::[[`var2 ->> SCA av val2 as _]] *)
(*             ::[[`name ->> SCA av (eval_binop (inl op) val1 val2) as _]]::Nil *)
(*             ∪ ext) by (repeat apply Cons_PopExt; *)
(*                         try decide_not_in; *)
(*                         simpl; *)
(*                         SameValues_Facade_t); *)
(*  *)
(*   SameValues_Facade_t. *)
(* Qed. *)

(* Lemma CompileBinop_left: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p2, *)
(*     name ∉ ext -> *)
(*     StringMap.MapsTo var1 (SCA av val1) ext -> *)
(*     var2 ∉ ext -> *)
(*     var1 <> var2 -> *)
(*     var2 <> name -> *)
(*     {{ Nil }} *)
(*       p2 *)
(*     {{ [[`var2 ->> SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p2 (Assign name (Binop op (Var var1) (Var var2)))) *)
(*     {{ [[`name ->> (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t. *)
(*  *)
(*   rewrite (add_redundant_cancel H0) in H19; SameValues_Facade_t. *)
(*   apply Cons_PopExt; [ SameValues_Facade_t | ]. *)
(*  *)
(*   cut (st' ≲ Nil ∪ ext); *)
(*   repeat match goal with *)
(*          | _ => reflexivity *)
(*          | _ => solve [simpl; SameValues_Facade_t] *)
(*          | _ => apply WeakEq_pop_SCA; [decide_not_in|] *)
(*          | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H *)
(*          | _ => progress simpl *)
(*          end. *)
(* Qed. *)

Lemma CompileBinopOrTest_left:
  forall {av} name var1 var2 (val1 val2: W) env ext op p2 (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var1 (wrap val1) ext ->
    var2 ∉ ext ->
    var1 <> var2 ->
    var2 <> name ->
    {{ tenv }}
      p2
    {{ [[`var2 ->> val2 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p2 (Assign name (WrapOpInExpr op (Var var1) (Var var2))))
    {{ [[`name ->> (eval_binop op val1 val2) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  destruct op; SameValues_Facade_t.
Qed.

(* Lemma CompileBinop_right: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p2, *)
(*     name ∉ ext -> *)
(*     var1 ∉ ext -> *)
(*     StringMap.MapsTo var2 (SCA av val2) ext -> *)
(*     var1 <> var2 -> *)
(*     var1 <> name -> *)
(*     {{ Nil }} *)
(*       p2 *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p2 (Assign name (Binop op (Var var1) (Var var2)))) *)
(*     {{ [[`name ->> (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t. *)
(*  *)
(*   rewrite (add_redundant_cancel H1) in H19; SameValues_Facade_t. *)
(*   apply Cons_PopExt; [ SameValues_Facade_t | ]. *)
(*  *)
(*   cut (st' ≲ Nil ∪ ext); *)
(*   repeat match goal with *)
(*          | _ => reflexivity *)
(*          | _ => solve [simpl; SameValues_Facade_t] *)
(*          | _ => apply WeakEq_pop_SCA; [decide_not_in|] *)
(*          | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H *)
(*          | _ => progress simpl *)
(*          end. *)
(* Qed. *)

Lemma CompileBinopOrTest_right:
  forall {av} name var1 var2 (val1 val2: W) env ext op p2 (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var2 (wrap val2) ext ->
    var1 ∉ ext ->
    var1 <> var2 ->
    var1 <> name ->
    {{ tenv }}
      p2
    {{ [[`var1 ->> val1 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p2 (Assign name (WrapOpInExpr op (Var var1) (Var var2))))
    {{ [[`name ->> (eval_binop op val1 val2) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  destruct op; SameValues_Facade_t.
Qed.

(* Lemma CompileBinop_full: *)
(*   forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2, *)
(*     name ∉ ext -> *)
(*     var1 ∉ ext -> *)
(*     var2 ∉ ext -> *)
(*     var1 <> var2 -> *)
(*     var1 <> name -> *)
(*     var2 <> name -> *)
(*     {{ Nil }} *)
(*       p1 *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::Nil }} *)
(*       p2 *)
(*     {{ [[`var1 ->> SCA _ val1 as _]]::[[`var2 ->> SCA _ val2 as _]]::Nil }} ∪ {{ ext }} // env -> *)
(*     {{ Nil }} *)
(*       (Seq p1 (Seq p2 (Assign name (Binop op (Var var1) (Var var2))))) *)
(*     {{ [[`name ->> (SCA av (eval_binop (inl op) val1 val2)) as _]]::Nil }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   Time SameValues_Facade_t. *)
(*   apply Cons_PopExt; [ SameValues_Facade_t | ]. *)
(*  *)
(*   cut (st'0 ≲ Nil ∪ ext); *)
(*   repeat match goal with *)
(*          | _ => reflexivity *)
(*          | _ => solve [simpl; SameValues_Facade_t] *)
(*          | _ => apply WeakEq_pop_SCA; [decide_not_in|] *)
(*          | [ H: WeakEq ?a ?st |- ?st ≲ _ ∪ _ ] => rewrite <- H *)
(*          | _ => progress simpl *)
(*          end. *)
(* Qed. *)

Opaque Word.natToWord.

Lemma CompileBinopOrTest_full:
  forall {av} name var1 var2 (val1 val2: W) env ext op p1 p2 (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    var1 ∉ ext ->
    var2 ∉ ext ->
    var1 <> var2 ->
    var1 <> name ->
    var2 <> name ->
    {{ tenv }}
      p1
    {{ [[`var1 ->> val1 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[`var1 ->> val1 as _]]::tenv }}
      p2
    {{ [[`var1 ->> val1 as _]]::[[`var2 ->> val2 as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 (Seq p2 (Assign name ((match op with inl o => Binop o | inr o => TestE o end) (Var var1) (Var var2)))))
    {{ [[`name ->> (eval_binop op val1 val2) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  destruct op; SameValues_Facade_t.

  apply (SameValues_Pop_Both (H := FacadeWrapper_SCA)); eauto 2.
  apply SameValues_not_In_Telescope_not_in_Ext_remove; eauto 2.
  eapply SameValues_forget_Ext.
  2:eapply SameValues_forget_Ext; try eassumption.
  eauto with SameValues_db.
  eauto with SameValues_db.

  apply (SameValues_Pop_Both (H := FacadeWrapper_SCA)); eauto 2.
  apply SameValues_not_In_Telescope_not_in_Ext_remove; eauto 2.
  eapply SameValues_forget_Ext.
  2:eapply SameValues_forget_Ext; try eassumption.
  eauto with SameValues_db.
  eauto with SameValues_db.
Qed.                               (* NOTE why doesn't eauto suffice here? *)

Lemma CompileBinopOrTest_right_inPlace:
  forall {av} op name var2 (val1 val2: W) env ext (tenv: Telescope av),
    name ∉ ext ->
    NotInTelescope name tenv ->
    StringMap.MapsTo var2 (wrap val2) ext ->
    {{ [[`name ->> val1 as _]]::tenv }}
      (Assign name (WrapOpInExpr op (Var name) (Var var2)))
    {{ [[`name ->> (eval_binop op val1 val2) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  destruct op; SameValues_Facade_t.
Qed.

Lemma CompileBinopOrTest_right_inPlace_tel:
  forall {av} op vret varg (val1 val2: W) env ext (tenv: Telescope av),
    PreconditionSet tenv ext [[[vret; varg]]] ->
    {{ [[`vret ->> val1 as _]]::[[`varg ->> val2 as _]]::tenv }}
      Assign vret (WrapOpInExpr op (Var vret) (Var varg))
    {{ [[`vret ->> (eval_binop op val1 val2) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  move_to_front varg.
  apply CompileDeallocW_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions.
  intros; apply CompileBinopOrTest_right_inPlace; try compile_do_side_conditions.
Qed.

Lemma CompileBinopOrTest_right_inPlace_tel_generalized:
  forall {av} op vret varg (val1 val2: W) env ext (tenv tenv': Telescope av) pCoda,
    PreconditionSet tenv ext [[[vret; varg]]] ->
    {{ [[`vret ->> (eval_binop op val1 val2) as _]]::[[`varg ->> val2 as _]]::tenv }}
      pCoda
    {{ [[`vret ->> (eval_binop op val1 val2) as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vret ->> val1 as _]]::[[`varg ->> val2 as _]]::tenv }}
      (Seq (Assign vret (WrapOpInExpr op (Var vret) (Var varg))) pCoda)
    {{ [[`vret ->> (eval_binop op val1 val2) as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  repeat hoare.
  move_to_front varg.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions.
  intros; apply CompileBinopOrTest_right_inPlace; try compile_do_side_conditions.
Qed.

