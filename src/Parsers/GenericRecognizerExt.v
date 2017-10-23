(** * Extensionality of generic recognizer *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.GenericRecognizer.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.ListMorphisms.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {rdata : @parser_removal_dataT' _ G _}
          {gendata : generic_parser_dataT Char}.

  Create HintDb boolr_ext_db discriminated.
  Hint Unfold Proper respectful respectful_hetero pointwise_relation forall_relation pointwise2_relation sumbool_rect : boolr_ext_db.
  (** Dummy hint for [boolr_ext_db] to work around https://coq.inria.fr/bugs/show_bug.cgi?id=4479 *)
  Hint Rewrite production_tl_correct : boolr_ext_db.

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
    | [ |- context[match ?e with _ => _ end] ] => is_var e; destruct e
    | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
    | [ H : _ |- _ ] => rewrite H
    | _ => progress autorewrite with boolr_ext_db
    | _ => progress simpl option_rect
    | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
    | [ |- ret_nt _ _ = ret_nt _ _ ] => apply f_equal
    end.

  Local Ltac t_ext tac := repeat (t_ext' || tac).

  Global Instance parse_item'_Proper
    : Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq ==> eq ==> eq) (parse_item').
  Proof. t_ext expand'. Qed.

  Lemma parse_item'_ext
        (str : String)
        (str_matches_nonterminal str_matches_nonterminal' : nonterminal_carrierT -> parse_nt_T)
        (ext : forall s, str_matches_nonterminal s = str_matches_nonterminal' s)
        (offset : nat)
        (len : nat)
        (it : item Char)
    : parse_item' str str_matches_nonterminal offset len it
      = parse_item' str str_matches_nonterminal' offset len it.
  Proof.
    change ((pointwise_relation _ eq) str_matches_nonterminal str_matches_nonterminal') in ext.
    rewrite ext; reflexivity.
  Qed.

  Hint Rewrite parse_item'_ext : boolr_ext_db.

  Section production.
    Context {len0 : nat} (str : String)
            (parse_nonterminal parse_nonterminal'
             : forall (offset : nat) (len0_minus_len : nat),
                nonterminal_carrierT
                -> parse_nt_T)
            (ext : forall offset len0_minus_len nt,
                parse_nonterminal offset len0_minus_len nt
                = parse_nonterminal' offset len0_minus_len nt).

    Lemma parse_production'_for_ext
          splits splits'
          (Hsplits : forall idx offset len, splits idx str offset len = splits' idx str offset len)
          (offset : nat)
          (len0_minus_len : nat)
          prod_idx
      : parse_production'_for (len0 := len0) str parse_nonterminal splits offset len0_minus_len prod_idx
        = parse_production'_for (len0 := len0) str parse_nonterminal' splits' offset len0_minus_len prod_idx.
    Proof.
      remember (to_production prod_idx) as prod eqn:Heq.
      unfold parse_production'_for.
      revert prod_idx Heq offset len0_minus_len splits splits' Hsplits ext; induction prod; simpl; intros;
        rewrite <- Heq; simpl;
          t_ext idtac.
      erewrite parse_item'_ext.
      { apply f_equal.
        specialize (IHprod (production_tl prod_idx)).
        rewrite production_tl_correct in IHprod.
        generalize dependent (to_production prod_idx); intros; subst.
        specialize (IHprod eq_refl).
        apply IHprod; clear IHprod; simpl; auto with nocore. }
      { auto with nocore. }
    Qed.

    Definition parse_production'_ext
               (offset : nat)
               (len0_minus_len : nat)
               prod_idx
      : parse_production' str parse_nonterminal offset len0_minus_len prod_idx
        = parse_production' str parse_nonterminal' offset len0_minus_len prod_idx
      := parse_production'_for_ext _ _ (fun _ _ _ => eq_refl) _ _ _.
  End production.

  Global Instance parse_production'_for_Proper
    : Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)))
                ==> (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq))))
                ==> eq
                ==> eq
                ==> eq
                ==> eq)
             (parse_production'_for (len0 := len0) str).
  Proof.
    repeat intro; subst.
    apply parse_production'_for_ext;
      unfold pointwise_relation in *;
      eauto with nocore.
  Qed.

  Global Instance parse_production'_Proper
    : Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)))
                ==> eq
                ==> eq
                ==> eq
                ==> eq)
             (parse_production' str (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_production'_ext.
    assumption.
  Qed.

  Section productions.
    Context {len0 : nat} (str : String)
            (parse_nonterminal parse_nonterminal'
             : forall (offset : nat)
                      (len0_minus_len : nat),
                nonterminal_carrierT -> parse_nt_T)
            (ext : forall str len0_minus_len nt,
                parse_nonterminal str len0_minus_len nt
                = parse_nonterminal' str len0_minus_len nt).

    Lemma parse_productions'_ext
          (offset : nat)
          (len0_minus_len : nat)
          (prods : list production_carrierT)
      : parse_productions' (len0 := len0) str parse_nonterminal offset len0_minus_len prods
        = parse_productions' (len0 := len0) str parse_nonterminal' offset len0_minus_len prods.
    Proof.
      t_ext ltac:(erewrite parse_production'_for_ext || expand').
    Qed.
  End productions.

  Global Instance parse_productions'_Proper
    : Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)))
                ==> eq
                ==> eq
                ==> eq
                ==> eq)
             (parse_productions' str (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_productions'_ext.
    assumption.
  Qed.

  Section step.
    Context {len0 valid_len} (str : String)
            (parse_nonterminal parse_nonterminal'
             : forall (p : nat * nat),
                Wf.prod_relation lt lt p (len0, valid_len)
                -> forall (valid : nonterminals_listT)
                          (offset : nat) (len : nat),
                  len <= fst p -> nonterminal_carrierT -> parse_nt_T)
            (ext : forall p pf valid str len pf' nt,
                parse_nonterminal p pf valid str len pf' nt
                = parse_nonterminal' p pf valid str len pf' nt).

    Definition parse_nonterminal_step_ext
               (valid : nonterminals_listT)
               (offset : nat)
               (len : nat)
               (pf pf' : len <= len0)
               (nt : nonterminal_carrierT)
      : parse_nonterminal_step str parse_nonterminal valid offset pf nt
        = parse_nonterminal_step str parse_nonterminal' valid offset pf' nt.
    Proof.
      t_ext ltac:(apply parse_productions'_ext || expand').
    Qed.
  End step.

  Global Instance parse_nonterminal_step_Proper
    : Proper ((forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq)))))))
                ==> eq
                ==> eq
                ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
             (parse_nonterminal_step str (len0 := len0) (valid_len := valid_len)).
  Proof.
    repeat intro; subst.
    apply parse_nonterminal_step_ext.
    assumption.
  Qed.
End recursive_descent_parser.
