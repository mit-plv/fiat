Require Import
        Coq.Bool.Bool
        Coq.omega.Omega
        Fiat.Common.DecideableEnsembles
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.Sequence
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Option
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.Bool
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Common.Sig.

Require Export
        Fiat.Narcissus.Automation.Common
        Fiat.Narcissus.Automation.NormalizeFormats
        Fiat.Narcissus.Automation.Decision
        Fiat.Narcissus.Automation.ExtractData
        Fiat.Narcissus.Automation.SynthesizeDecoder.

Ltac start_synthesizing_decoder :=
  match goal with
  | |- CorrectDecoderFor ?Invariant ?Spec =>
    try unfold Spec; try unfold Invariant
  | |- context [CorrectDecoder _ ?dataInv ?restInv ?formatSpec] =>
    first [unfold dataInv
          | unfold restInv
          | unfold formatSpec ]
  | |- context [CorrectDecoder _ ?dataInv ?restInv (?formatSpec _)] =>
    first [unfold dataInv
          | unfold restInv
          | unfold formatSpec ]
  end;

  (* Memoize any string constants *)
  pose_string_hyps;
  eapply Start_CorrectDecoderFor; simpl.

Lemma whd_word_1_refl :
  forall (b : word 1),
    WS (whd b) WO = b.
Proof.
  intros; destruct (shatter_word_S b) as [? [? ?] ]; subst.
  rewrite (shatter_word_0 x0); reflexivity.
Qed.

Lemma pow2_1 : pow2 1 = 2.
  reflexivity.
Qed.

Lemma pow2_2 : pow2 2 = 4.
  reflexivity.
Qed.

Lemma pow2_3 : pow2 3 = 8.
  reflexivity.
Qed.

Lemma pow2_4 : pow2 4 = 16.
  reflexivity.
Qed.

Lemma pow2_5 : pow2 5 = 32.
  reflexivity.
Qed.

Lemma pow2_6 : pow2 6 = 64.
  reflexivity.
Qed.

Lemma pow2_7 : pow2 7 = 128.
  reflexivity.
Qed.

Lemma pow2_8 : pow2 8 = 256.
  reflexivity.
Qed.

Ltac subst_pow2 :=
  rewrite ?pow2_1 in *;
  rewrite ?pow2_2 in *;
  rewrite ?pow2_3 in *;
  rewrite ?pow2_4 in *;
  rewrite ?pow2_5 in *;
  rewrite ?pow2_6 in *;
  rewrite ?pow2_7 in *;
  rewrite ?pow2_8 in *.

Hint Extern 4 => subst_pow2 : data_inv_hints.
Hint Extern 4 => omega : data_inv_hints.

Ltac synthesize_cache_invariant :=
  (* Synthesize an invariant satisfying the derived constraints *)
  (* on the cache. *)
  solve [repeat (instantiate (1 := fun _ => True));
         unfold cache_inv_Property; intuition].

Lemma optimize_under_if {A B}
  : forall (a a' : A) (f : {a = a'} + {a <> a'}) (t t' e e' : B),
    t = t'
    -> e = e'
    -> (if f then t else e) = if f then t' else e.
Proof.
  destruct f; congruence.
Qed.

Lemma optimize_under_if_bool {B}
  : forall (c : bool) (t t' e e' : B),
    t = t'
    -> e = e'
    -> (if c then t else e) = if c then t' else e.
Proof.
  destruct c; congruence.
Qed.

Lemma optimize_if_bind2 {A A' B C C'}
  : forall (a a' : C')
           (f : {a = a'} + {a <> a'})
           (t e : option (A * B * C))
           (k : A -> B -> C -> option (A' * B * C)),
    (`(a, b, env) <- (if f then t else e); k a b env) =
    if f then `(a, b, env) <- t; k a b env else `(a, b, env) <- e; k a b env.
Proof.
  destruct f; congruence.
Qed.

Lemma optimize_if_bind2_bool {A A' B C}
  : forall (c : bool)
           (t e : option (A * B * C))
           (k : A -> B -> C -> option (A' * B * C)),
    (`(a, b, env) <- (if c then t else e); k a b env) =
    if c then `(a, b, env) <- t; k a b env else `(a, b, env) <- e; k a b env.
Proof.
  destruct c; congruence.
Qed.

Lemma Option_predicate_True {B}
  : forall (s_opt : option B),
    match s_opt with
    | Some _ | _ => True
    end.
Proof.
  destruct s_opt; eauto.
Qed.

Lemma plus_minus : forall m n n',
    m + n = n' -> n = n' - m.
  intros; omega.
Qed.

Hint Extern 4 => eapply plus_minus.
Hint Extern 4 => eapply (proj2 (NPeano.Nat.lt_add_lt_sub_l _ _ _)).
Hint Extern 4 => eapply Option_predicate_True : data_inv_hints.
Hint Extern 4 => eapply decides_Option_eq_None : data_inv_hints.
Hint Resolve lt_1_pow2_16 : data_inv_hints.

Hint Resolve whd_word_1_refl' : decide_data_invariant_db.
Hint Resolve decides_length_firstn_skipn_app'' : decide_data_invariant_db.
Hint Resolve decides_length_firstn_skipn_app' : decide_data_invariant_db.
Hint Resolve decides_length_firstn_skipn_app : decide_data_invariant_db.
Hint Resolve firstn_lt_decides : decide_data_invariant_db.
Hint Resolve firstn_skipn_self'' : decide_data_invariant_db.
Hint Resolve decides_firstn_app : decide_data_invariant_db.
Hint Resolve decides_firstn_self : decide_data_invariant_db.
Hint Resolve decides_skipn_app : decide_data_invariant_db.
Hint Resolve decides_firstn_skipn_app : decide_data_invariant_db.

Ltac optimize_decoder_impl :=
  (* Perform algebraic simplification of the decoder implementation. *)
  simpl; intros;
  repeat (try rewrite !DecodeBindOpt2_assoc;
          try rewrite !Bool.andb_true_r;
          try rewrite !Bool.andb_true_l;
          try rewrite !optimize_if_bind2;
          try rewrite !optimize_if_bind2_bool;
          first [
              apply DecodeBindOpt2_under_bind; simpl; intros
            | eapply optimize_under_if_bool; simpl; intros
            | eapply optimize_under_if; simpl; intros]);
  higher_order_reflexivity.

Ltac apply_rules :=
  first [ extract_view
        | apply_base_rule
        | apply_combinator_rule apply_rules
        | idtac ].

Ltac synthesize_decoder :=
  (* Combines tactics into one-liner. *)
  start_synthesizing_decoder;
  [ apply_rules
  | cbv beta; synthesize_cache_invariant
  | cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl].

Global Instance : DecideableEnsembles.Query_eq () :=
  {| A_eq_dec a a' := match a, a' with (), () => left (eq_refl _) end |}.

Global Opaque pow2. (* Don't want to be evaluating this. *)
Global Opaque natToWord. (* Or this. *)
Global Opaque weqb. (* Or this. *)

(* Older tactics follow, leaving in for now for backwards compatibility. *)

Ltac enum_part eq_dec :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func in
    let h := fresh in
    evar (h:func_t);
    unify (fun n => if eq_dec _ n arg then res else h n) func;
    reflexivity
  end.

Ltac enum_finish :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func
    in  unify ((fun _  => res) : func_t) func;
        reflexivity
  end.

Ltac idtac' :=
  match goal with
  | |- _ => idtac (* I actually need this idtac for some unknown reason *)
  end.
