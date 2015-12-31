(** * Extensionality of boolean recognizer *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.ListMorphisms.
(*Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common Fiat.Common.Wf.*)

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Ltac subst_le_proof :=
  idtac;
  match goal with
    | [ H : ?x <= ?y, H' : ?x <= ?y |- _ ]
      => assert (H = H') by apply Le.le_proof_irrelevance; subst
  end.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {rdata : @parser_removal_dataT' _ G _}.

  Create HintDb boolr_ext_db discriminated.
  Hint Unfold Proper respectful respectful_hetero pointwise_relation forall_relation pointwise2_relation sumbool_rect : boolr_ext_db.

  Local Ltac expand' :=
    idtac;
    (lazymatch goal with
    | [ |- ?R = ?L ]
      => (let rh := head R in
          let lh := head L in
          constr_eq rh lh;
          progress unfold rh)
     end).

  Local Ltac t_ext' :=
    idtac;
    match goal with
      | _ => reflexivity
      | _ => solve [ eauto with nocore ]
      | _ => progress intros
      | _ => progress subst
      | _ => progress subst_le_proof
      | [ |- @list_rect ?A ?P ?Pn ?Pc ?ls = @list_rect ?A ?P ?Pn' ?Pc' ?ls ]
        => apply (@list_rect_ext A P Pn Pn' Pc Pc' ls)
      | [ |- @option_rect ?A ?P ?Ps ?Pn ?x = @option_rect ?A ?P ?Ps' ?Pn' ?x ]
        => apply (@option_rect_ext A P Ps Ps' Pn Pn' x)
      | [ |- @List.fold_left ?A ?B _ _ _ = @List.fold_left ?A ?B _ _ _ ]
        => let lem := constr:(_ : Proper (_ ==> _ ==> _ ==> eq) (@List.fold_left A B)) in
           apply lem
      | [ |- @List.fold_right ?A ?B _ _ _ = @List.fold_right ?A ?B _ _ _ ]
        => let lem := constr:(_ : Proper (_ ==> _ ==> _ ==> eq) (@List.fold_right A B)) in
           apply lem
      | [ |- @List.map ?A ?B _ _ = @List.map ?A ?B _ _ ]
        => let lem := constr:(_ : Proper (_ ==> _ ==> eq) (@List.map A B)) in
           apply lem
      | [ |- andb ?x _ = andb ?x _ ] => apply f_equal
      | [ |- andb _ ?x = andb _ ?x ] => apply f_equal2
      | _ => progress autounfold with boolr_ext_db
      | [ |- appcontext[match ?e with _ => _ end] ] => is_var e; destruct e
      | [ |- appcontext[match ?e with _ => _ end] ] => destruct e eqn:?
      | [ H : _ |- _ ] => rewrite H
      | _ => progress autorewrite with boolr_ext_db
      | _ => progress simpl option_rect
      | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
    end.

  Local Ltac t_ext tac := repeat (t_ext' || tac).

  Global Instance parse_item'_Proper
  : Proper (pointwise_relation _ eq ==> eq ==> eq ==> eq) (parse_item').
  Proof. t_ext expand'. Qed.

  Lemma parse_item'_ext
        (str_matches_nonterminal str_matches_nonterminal' : nonterminal_carrierT -> bool)
        (ext : forall s, str_matches_nonterminal s = str_matches_nonterminal' s)
        (str : String)
        (it : item Char)
  : parse_item' str_matches_nonterminal str it
    = parse_item' str_matches_nonterminal' str it.
  Proof.
    change ((pointwise_relation _ eq) str_matches_nonterminal str_matches_nonterminal') in ext.
    rewrite ext; reflexivity.
  Qed.

  Hint Rewrite parse_item'_ext : boolr_ext_db.

  Inductive drop_takeT := drop_of (n : nat) | take_of (n : nat).

  Fixpoint drop_takes (ns : list drop_takeT) (str : String)
    := match ns with
         | nil => str
         | cons (drop_of n) ns' => drop n (drop_takes ns' str)
         | cons (take_of n) ns' => take n (drop_takes ns' str)
       end.

  Section production_drop_take.
    Context {len0}
            (parse_nonterminal parse_nonterminal'
             : forall (str : String) (len : nat),
                 len <= len0
                 -> nonterminal_carrierT
                 -> bool).

    Lemma parse_production'_for_ext_drop_take
          splits splits'
          (Hsplits : forall idx p, splits idx p = splits' idx p)
          (str : String)
          (ext : forall ns len pf nt,
                     @parse_nonterminal (drop_takes ns str) len pf nt
                     = @parse_nonterminal' (drop_takes ns str) len pf nt)
          (len : nat)
          (pf pf' : len <= len0)
          prod_idx
          (ns : list _)
    : parse_production'_for parse_nonterminal splits (drop_takes ns str) pf prod_idx
      = parse_production'_for parse_nonterminal' splits' (drop_takes ns str) pf' prod_idx.
    Proof.
      remember (to_production prod_idx) as prod eqn:Heq.
      unfold parse_production'_for;
      revert prod_idx Heq ns splits splits' Hsplits str ext len pf pf'; induction prod; simpl; intros;
      rewrite <- Heq; simpl;
      subst_le_proof;
      t_ext idtac.
      erewrite parse_item'_ext.
      { apply f_equal.
        specialize (IHprod (production_tl prod_idx)).
        rewrite production_tl_correct in IHprod.
        generalize dependent (to_production prod_idx); intros; subst.
        specialize (fun n ns => IHprod eq_refl (drop_of n :: ns)%list); simpl in IHprod.
        auto with nocore. }
      { specialize (fun n ns => ext (take_of n :: ns)%list); simpl in ext.
        auto with nocore. }
    Qed.

    Definition parse_production'_ext_drop_take
               (str : String)
               (ext : forall ns len pf nt,
                        @parse_nonterminal (drop_takes ns str) len pf nt
                        = @parse_nonterminal' (drop_takes ns str) len pf nt)
               (len : nat)
               (pf pf' : len <= len0)
               prod_idx
               (ns : list _)
    : parse_production' parse_nonterminal (drop_takes ns str) pf prod_idx
      = parse_production' parse_nonterminal' (drop_takes ns str) pf' prod_idx
      := parse_production'_for_ext_drop_take _ _ (fun _ _ => eq_refl) str ext pf pf' prod_idx ns.
  End production_drop_take.

  Section production.
    Context {len0}
            (parse_nonterminal parse_nonterminal'
             : forall (str : String) (len : nat),
                 len <= len0
                 -> nonterminal_carrierT
                 -> bool)
            (ext : forall str len pf nt,
                     parse_nonterminal str len pf nt
                     = parse_nonterminal' str len pf nt).

    Lemma parse_production'_for_ext
          splits splits'
          (Hsplits : forall idx p, splits idx p = splits' idx p)
          (str : String)
          (len : nat)
          (pf pf' : len <= len0)
          prod_idx
    : parse_production'_for parse_nonterminal splits str pf prod_idx
      = parse_production'_for parse_nonterminal' splits' str pf' prod_idx.
    Proof.
      apply parse_production'_for_ext_drop_take with (ns := nil); auto with nocore.
    Qed.

    Definition parse_production'_ext
               (str : String)
               (len : nat)
               (pf pf' : len <= len0)
               prod_idx
    : parse_production' parse_nonterminal str pf prod_idx
      = parse_production' parse_nonterminal' str pf' prod_idx
      := parse_production'_for_ext _ _ (fun _ _ => eq_refl) str pf pf' prod_idx.
  End production.

  Global Instance parse_production'_for_Proper
  : Proper ((pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq))))
              ==> (pointwise_relation _ (pointwise_relation _ eq))
              ==> eq
              ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
           (parse_production'_for (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_production'_for_ext;
    assumption.
  Qed.

  Global Instance parse_production'_Proper
  : Proper ((pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq))))
              ==> eq
              ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
           (parse_production' (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_production'_ext.
    assumption.
  Qed.

  Section productions_drop_take.
    Context {len0}
            (parse_nonterminal parse_nonterminal'
             : forall (str : String)
                      (len : nat)
                      (pf : len <= len0),
                 nonterminal_carrierT -> bool).

    Lemma parse_productions'_ext_drop_take
          (str : String)
          (ext : forall ns str len pf nt,
                   @parse_nonterminal (drop_takes ns str) len pf nt
                   = @parse_nonterminal' (drop_takes ns str) len pf nt)
          (len : nat)
          (pf pf' : len <= len0)
          (prods : list production_carrierT)
          ns
    : parse_productions' parse_nonterminal (drop_takes ns str) pf prods
      = parse_productions' parse_nonterminal' (drop_takes ns str) pf' prods.
    Proof.
      t_ext ltac:(erewrite parse_production'_for_ext_drop_take || expand').
    Qed.
  End productions_drop_take.

  Section productions.
    Context {len0}
            (parse_nonterminal parse_nonterminal'
             : forall (str : String)
                      (len : nat)
                      (pf : len <= len0),
                 nonterminal_carrierT -> bool)
            (ext : forall str len pf nt,
                     parse_nonterminal str len pf nt
                     = parse_nonterminal' str len pf nt).

    Lemma parse_productions'_ext
               (str : String)
               (len : nat)
               (pf pf' : len <= len0)
               (prods : list production_carrierT)
    : parse_productions' parse_nonterminal str pf prods
      = parse_productions' parse_nonterminal' str pf' prods.
    Proof.
      apply parse_productions'_ext_drop_take with (ns := nil); auto with nocore.
    Qed.
  End productions.

  Global Instance parse_productions'_Proper
  : Proper ((pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq))))
              ==> eq
              ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
           (parse_productions' (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_productions'_ext.
    assumption.
  Qed.

  Section nonterminals.
    Section step_drop_take.
      Context {len0 valid_len}
              (parse_nonterminal parse_nonterminal'
               : forall (p : nat * nat),
                   Wf.prod_relation lt lt p (len0, valid_len)
                   -> forall (valid : nonterminals_listT)
                             (str : String) (len : nat),
                        len <= fst p -> nonterminal_carrierT -> bool).

      Definition parse_nonterminal_step_ext_drop_take
                 (valid : nonterminals_listT)
                 (str : String)
                 (ext : forall ns p pf valid str len pf' nt,
                          @parse_nonterminal p pf valid (drop_takes ns str) len pf' nt
                          = @parse_nonterminal' p pf valid (drop_takes ns str) len pf' nt)
                 (len : nat)
                 (pf pf' : len <= len0)
                 (nt : nonterminal_carrierT)
                 ns
      : parse_nonterminal_step parse_nonterminal valid (drop_takes ns str) pf nt
        = parse_nonterminal_step parse_nonterminal' valid (drop_takes ns str) pf' nt.
      Proof.
        t_ext ltac:(erewrite parse_productions'_ext_drop_take || expand').
      Qed.
    End step_drop_take.

    Section step.
      Context {len0 valid_len}
              (parse_nonterminal parse_nonterminal'
               : forall (p : nat * nat),
                   Wf.prod_relation lt lt p (len0, valid_len)
                   -> forall (valid : nonterminals_listT)
                             (str : String) (len : nat),
                        len <= fst p -> nonterminal_carrierT -> bool)
              (ext : forall p pf valid str len pf' nt,
                       parse_nonterminal p pf valid str len pf' nt
                       = parse_nonterminal' p pf valid str len pf' nt).

      Definition parse_nonterminal_step_ext
                 (valid : nonterminals_listT)
                 (str : String)
                 (len : nat)
                 (pf pf' : len <= len0)
                 (nt : nonterminal_carrierT)
      : parse_nonterminal_step parse_nonterminal valid str pf nt
        = parse_nonterminal_step parse_nonterminal' valid str pf' nt.
      Proof.
        apply parse_nonterminal_step_ext_drop_take with (ns := nil); auto with nocore.
      Qed.
    End step.

    Global Instance parse_nonterminal_step_Proper
    : Proper ((forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq)))))))
                ==> eq
                ==> eq
                ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
             (parse_nonterminal_step (len0 := len0) (valid_len := valid_len)).
    Proof.
      repeat intro; subst.
      apply parse_nonterminal_step_ext.
      assumption.
    Qed.
  End nonterminals.
End recursive_descent_parser.
