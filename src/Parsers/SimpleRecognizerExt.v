(** * Extensionality of simple recognizer *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.SimpleRecognizer.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.ListMorphisms.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Ltac subst_le_proof :=
  idtac;
  match goal with
    | [ H : ?x <= ?y, H' : ?x <= ?y |- _ ]
      => assert (H = H') by apply Le.le_proof_irrelevance; subst
  end.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {rdata : @parser_removal_dataT' _ G _}.

  Create HintDb simpler_ext_db discriminated.
  Hint Unfold Proper respectful respectful_hetero pointwise_relation forall_relation pointwise2_relation sumbool_rect : simpler_ext_db.
  (** Dummy hint for [simpler_ext_db] to work around https://coq.inria.fr/bugs/show_bug.cgi?id=4479 *)
  Hint Rewrite production_tl_correct : simpler_ext_db.

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
      | _ => progress autounfold with simpler_ext_db
      | [ |- appcontext[match ?e with _ => _ end] ] => is_var e; destruct e
      | [ |- appcontext[match ?e with _ => _ end] ] => destruct e eqn:?
      | [ H : _ |- _ ] => rewrite H
      | _ => progress autorewrite with simpler_ext_db
      | _ => progress simpl option_rect
      | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
    end.

  Local Ltac t_ext tac := repeat (t_ext' || tac).

  Global Instance parse_item'_Proper
  : Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq ==> eq ==> eq) (parse_item').
  Proof. t_ext expand'. Qed.

  Lemma parse_item'_ext
        (str : String)
        (str_matches_nonterminal str_matches_nonterminal' : nonterminal_carrierT -> _)
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

  Hint Rewrite parse_item'_ext : simpler_ext_db.

  Inductive drop_takeT := drop_of (n : nat) | take_of (n : nat).

  Fixpoint drop_takes_offset (ns : list drop_takeT) (offset : nat)
    := match ns with
         | nil => offset
         | cons (drop_of n) ns' => drop_takes_offset ns' offset + n
         | cons (take_of n) ns' => drop_takes_offset ns' offset
       end.

  Fixpoint drop_takes_len (ns : list drop_takeT) (len : nat)
    := match ns with
         | nil => len
         | cons (drop_of n) ns' => drop_takes_len ns' len - n
         | cons (take_of n) ns' => min n (drop_takes_len ns' len)
       end.

  Fixpoint drop_takes_len_pf {len0} (ns : list drop_takeT) (len : nat) (pf : len <= len0) {struct ns}
  : drop_takes_len ns len <= len0.
  Proof.
    refine match ns return drop_takes_len ns len <= len0 with
             | nil => pf
             | cons (drop_of n) ns' => Le.le_trans _ _ _ (Minus.le_minus _ _) (@drop_takes_len_pf len0 ns' _ pf)
             | cons (take_of n) ns' => Le.le_trans _ _ _ (Min.le_min_r _ _) (@drop_takes_len_pf len0 ns' _ pf)
           end.
  Defined.

  Section production_drop_take.
    Context {len0}
            (parse_nonterminal parse_nonterminal'
             : forall (offset : nat) (len : nat),
                 len <= len0
                 -> nonterminal_carrierT
                 -> option (@simple_parse_of Char)).

    Lemma parse_production'_for_ext_drop_take
          (str : String)
          splits splits'
          (offset : nat)
          (len : nat)
          (Hsplits : forall idx len ns, splits idx str (drop_takes_offset ns offset) (drop_takes_len ns len) = splits' idx str (drop_takes_offset ns offset) (drop_takes_len ns len))
          (ext : forall ns offset len pf nt,
                     @parse_nonterminal (drop_takes_offset ns offset) (drop_takes_len ns len) pf nt
                     = @parse_nonterminal' (drop_takes_offset ns offset) (drop_takes_len ns len) pf nt)
          (ns : list _)
          (pf pf' : drop_takes_len ns len <= len0)
          prod_idx
    : parse_production'_for str parse_nonterminal splits (drop_takes_offset ns offset) pf prod_idx
      = parse_production'_for str parse_nonterminal' splits' (drop_takes_offset ns offset) pf' prod_idx.
    Proof.
      remember (to_production prod_idx) as prod eqn:Heq.
      unfold parse_production'_for.
      revert prod_idx Heq ns offset len splits splits' Hsplits ext pf pf'; induction prod; simpl; intros;
      rewrite <- Heq; simpl;
      subst_le_proof;
      t_ext idtac.
      erewrite parse_item'_ext.
      { apply f_equal.
        specialize (IHprod (production_tl prod_idx)).
        rewrite production_tl_correct in IHprod.
        generalize dependent (to_production prod_idx); intros; subst.
        specialize (fun n ns => IHprod eq_refl (drop_of n :: ns)%list); simpl in IHprod.
        apply IHprod; clear IHprod; auto with nocore. }
      { specialize (fun n ns => ext (take_of n :: ns)%list); simpl in ext.
        auto with nocore. }
    Qed.

    Definition parse_production'_ext_drop_take
               (str : String)
               (offset : nat)
               (len : nat)
               (ext : forall ns offset len pf nt,
                        @parse_nonterminal (drop_takes_offset ns offset) (drop_takes_len ns len) pf nt
                        = @parse_nonterminal' (drop_takes_offset ns offset) (drop_takes_len ns len) pf nt)
               (ns : list _)
               (pf pf' : drop_takes_len ns len <= len0)
               prod_idx
    : parse_production' str parse_nonterminal (drop_takes_offset ns offset) pf prod_idx
      = parse_production' str parse_nonterminal' (drop_takes_offset ns offset) pf prod_idx
      := parse_production'_for_ext_drop_take _ _ _ _ _ (fun _ _ _ => eq_refl) ext _ _ _ _.
  End production_drop_take.

  Section production.
    Context {len0} (str : String)
            (parse_nonterminal parse_nonterminal'
             : forall (offset : nat) (len : nat),
                 len <= len0
                 -> nonterminal_carrierT
                 -> option (@simple_parse_of Char))
            (ext : forall offset len pf nt,
                     parse_nonterminal offset len pf nt
                     = parse_nonterminal' offset len pf nt).

    Lemma parse_production'_for_ext
          splits splits'
          (Hsplits : forall idx offset len, splits idx str offset len = splits' idx str offset len)
          (offset : nat)
          (len : nat)
          (pf pf' : len <= len0)
          prod_idx
    : parse_production'_for str parse_nonterminal splits offset pf prod_idx
      = parse_production'_for str parse_nonterminal' splits' offset pf' prod_idx.
    Proof.
      apply parse_production'_for_ext_drop_take with (ns := nil); auto with nocore.
    Qed.

    Definition parse_production'_ext
               (offset : nat)
               (len : nat)
               (pf pf' : len <= len0)
               prod_idx
    : parse_production' str parse_nonterminal offset pf prod_idx
      = parse_production' str parse_nonterminal' offset pf' prod_idx
      := parse_production'_for_ext _ _ (fun _ _ _ => eq_refl) _ _ _ _.
  End production.

  Global Instance parse_production'_for_Proper
  : Proper ((pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq))))
              ==> (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq))))
              ==> eq
              ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
           (parse_production'_for str (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_production'_for_ext;
    unfold pointwise_relation in *;
    eauto with nocore.
  Qed.

  Global Instance parse_production'_Proper
    : Proper ((pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq))))
                ==> eq
                ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
             (parse_production' str (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_production'_ext.
    assumption.
  Qed.

  Section productions_drop_take.
    Context {len0} (str : String)
            (parse_nonterminal parse_nonterminal'
             : forall (offset : nat)
                      (len : nat)
                      (pf : len <= len0),
                 nonterminal_carrierT -> option (@simple_parse_of Char)).

    Lemma parse_productions'_ext_drop_take
          (ext : forall ns offset len pf nt,
                   @parse_nonterminal (drop_takes_offset ns offset) (drop_takes_len ns len) pf nt
                   = @parse_nonterminal' (drop_takes_offset ns offset) (drop_takes_len ns len) pf nt)
          (offset : nat)
          (len : nat)
          ns
          (pf pf' : drop_takes_len ns len <= len0)
          (prods : list production_carrierT)
    : parse_productions' str parse_nonterminal (drop_takes_offset ns offset) pf prods
      = parse_productions' str parse_nonterminal' (drop_takes_offset ns offset) pf' prods.
    Proof.
      t_ext ltac:(erewrite parse_production'_for_ext_drop_take || expand').
    Qed.
  End productions_drop_take.

  Section productions.
    Context {len0} (str : String)
            (parse_nonterminal parse_nonterminal'
             : forall (offset : nat)
                      (len : nat)
                      (pf : len <= len0),
                 nonterminal_carrierT -> option (@simple_parse_of Char))
            (ext : forall str len pf nt,
                     parse_nonterminal str len pf nt
                     = parse_nonterminal' str len pf nt).

    Lemma parse_productions'_ext
          (offset : nat)
          (len : nat)
          (pf pf' : len <= len0)
          (prods : list production_carrierT)
    : parse_productions' str parse_nonterminal offset pf prods
      = parse_productions' str parse_nonterminal' offset pf' prods.
    Proof.
      apply parse_productions'_ext_drop_take with (ns := nil); auto with nocore.
    Qed.
  End productions.

  Global Instance parse_productions'_Proper
  : Proper ((pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq))))
              ==> eq
              ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
           (parse_productions' str (len0 := len0)).
  Proof.
    repeat intro; subst.
    apply parse_productions'_ext.
    assumption.
  Qed.

  Section nonterminals.
    Section step_drop_take.
      Context {len0 valid_len} (str : String)
              (parse_nonterminal parse_nonterminal'
               : forall (p : nat * nat),
                   Wf.prod_relation lt lt p (len0, valid_len)
                   -> forall (valid : nonterminals_listT)
                             (offset : nat) (len : nat),
                        len <= fst p -> nonterminal_carrierT -> option (@simple_parse_of Char)).

      Definition parse_nonterminal_step_ext_drop_take
                 (valid : nonterminals_listT)
                 (ext : forall ns p pf valid offset len pf' nt,
                          @parse_nonterminal p pf valid (drop_takes_offset ns offset) (drop_takes_len ns len) pf' nt
                          = @parse_nonterminal' p pf valid (drop_takes_offset ns offset) (drop_takes_len ns len) pf' nt)
                 (offset : nat)
                 (len : nat)
                 ns
                 (pf pf' : drop_takes_len ns len <= len0)
                 (nt : nonterminal_carrierT)
      : parse_nonterminal_step str parse_nonterminal valid (drop_takes_offset ns offset) pf nt
        = parse_nonterminal_step str parse_nonterminal' valid (drop_takes_offset ns offset) pf' nt.
      Proof.
        t_ext ltac:(erewrite parse_productions'_ext_drop_take || expand').
      Qed.
    End step_drop_take.

    Section step.
      Context {len0 valid_len} (str : String)
              (parse_nonterminal parse_nonterminal'
               : forall (p : nat * nat),
                   Wf.prod_relation lt lt p (len0, valid_len)
                   -> forall (valid : nonterminals_listT)
                             (offset : nat) (len : nat),
                        len <= fst p -> nonterminal_carrierT -> option (@simple_parse_of Char))
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
        apply parse_nonterminal_step_ext_drop_take with (ns := nil); auto with nocore.
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
  End nonterminals.
End recursive_descent_parser.
