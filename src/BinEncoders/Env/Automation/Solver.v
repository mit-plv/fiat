Require Import
        Coq.Bool.Bool
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
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Lib2.Option
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.Bool
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.StringOpt
        Fiat.BinEncoders.Env.Common.Sig
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.BinLib.Char
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Enum
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.Lib.IList.

Ltac apply_compose :=
  intros;
  match goal with
    H : cache_inv_Property ?P ?P_inv |- _ =>
    first [eapply (compose_encode_correct_no_dep _ H); clear H
          | eapply (compose_encode_correct H); clear H
          | eapply (composeIf_encode_correct H); clear H;
            [ |
              | solve [intros; intuition (eauto with bin_split_hints) ]
              | solve [intros; intuition (eauto with bin_split_hints) ] ]
          ]
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac shelve_inv :=
  let H' := fresh in
  let data := fresh in
  intros data H';
  repeat destruct H';
  match goal with
  | H : ?P data |- ?P_inv' =>
    is_evar P;
    let P_inv' := (eval pattern data in P_inv') in
    let P_inv := match P_inv' with ?P_inv data => P_inv end in
    let new_P_T := type of P in
    makeEvar new_P_T
             ltac:(fun new_P =>
                     unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
  end.

Lemma decompose_pair_eq {A B}
  : forall (ab ab' : A * B),
    ab = ab' -> fst ab = fst ab' /\ snd ab = snd ab'.
Proof. intros; split; congruence. Qed.

Ltac decompose_pair_hyp :=
  repeat
    match goal with
    | H : _ = _ |- _ =>
      first [apply decompose_pair_eq in H;
             let H1 := fresh in
             let H2 := fresh in
             destruct H as [H1 H2];
             simpl in H1;
             simpl in H2
            | rewrite H in * ]
    end; subst.

(* Solves data invariants using the data_inv_hints database *)
Ltac solve_data_inv :=
  first [ simpl; intros; exact I
        | solve [intuition eauto with data_inv_hints]
        | solve [simpl;
                 intuition eauto with data_inv_hints;
                 repeat
                   match goal with
                   | H : _ = _ |- _ =>
                     first [apply decompose_pair_eq in H;
                            let H1 := fresh in
                            let H2 := fresh in
                            destruct H as [H1 H2];
                            simpl in H1;
                            simpl in H2
                           | rewrite H in * ]
                   end;
                 eauto with data_inv_hints]
        | shelve_inv ].

Ltac start_synthesizing_decoder :=
  match goal with
  | |- CorrectDecoderFor ?Invariant ?Spec =>
    try unfold Spec; try unfold Invariant
  | |- appcontext [encode_decode_correct_f _ _ ?dataInv ?restInv ?encodeSpec] =>
    first [unfold dataInv
          | unfold restInv
          | unfold encodeSpec ]
  | |- appcontext [encode_decode_correct_f _ _ ?dataInv ?restInv (?encodeSpec _)] =>
    first [unfold dataInv
          | unfold restInv
          | unfold encodeSpec ]
  end;

  (* Memoize any string constants *)
  pose_string_hyps;
  eapply Start_CorrectDecoderFor; simpl.

Ltac build_fully_determined_type cleanup_tac :=
  (* Build the parsed object by showing it can be built *)
  (* from previously parsed terms and that and that the *)
  (* byte string was a valid encoding of this object. *)
  (* Start by doing some simplification and *)
  (* destructing the encoded object  *)
  unfold Domain, GetAttribute, GetAttributeRaw in *;
  simpl in *;
  let a' := fresh in
  intros a'; repeat destruct a' as [? a'];
  (* Show that it is determined by the constraints (equalities) *)
  (* inferred during parsing. *)
  unfold Domain, GetAttribute, GetAttributeRaw in *;
  simpl in *; intros;
  (* Decompose data predicate *) intuition;
  (* Substitute any inferred equalities; decomposing *)
  (* any product types that might have been built up *)
  (* along the way *)
  repeat
    match goal with
    | H : _ = _ |- _ =>
      first [apply decompose_pair_eq in H;
             let H1 := fresh in
             let H2 := fresh in
             destruct H as [H1 H2];
             simpl in H1;
             simpl in H2
            | rewrite H in * ]
    end; cleanup_tac;
  (* And unify with original object *) reflexivity.

Lemma decides_True' {A}
  : forall a, decides true ((fun _ : A => True) a).
Proof.
  simpl; intros; exact I.
Qed.

Definition pair_eq_dec {A B}
           (A_eq_dec : forall a a' : A, {a = a'} + {a <> a'})
           (B_eq_dec : forall a a' : B, {a = a'} + {a <> a'})
  : forall a a' : A * B, {a = a'} + {a <> a'}.
Proof.
  refine (fun a a' => match A_eq_dec (fst a) (fst a'), B_eq_dec (snd a) (snd a') with
                      | left _, left _ => _
                      | _, _ => _
                      end);
    decide equality.
Defined.

Definition decides_pair_eq {A B}
           (t : A -> A -> bool)
           (t' : B -> B -> bool)
           (decides_t : forall a a' : A , decides (t a a') (a = a'))
           (decides_t' : forall b b' : B , decides (t' b b') (b = b'))
  : forall ab ab' : A * B,
    decides (andb (t (fst ab) (fst ab')) (t' (snd ab) (snd ab'))) (ab = ab').
Proof.
  destruct ab; destruct ab'; simpl in *.
  pose proof (decides_t a a0);   pose proof (decides_t' b b0);
    unfold decides, If_Then_Else in *.
  destruct (t a a0);  destruct (t' b b0); simpl in *; congruence.
Qed.

Lemma decides_nat_eq :
  forall (n n' : nat),
    decides (EqNat.beq_nat n n') (n = n').
Proof.
  unfold decides, If_Then_Else; intros.
  destruct (EqNat.beq_nat n n') eqn: ? ;
    try eapply EqNat.beq_nat_true_iff;
    try eapply EqNat.beq_nat_false_iff; eauto.
Qed.

Lemma decides_word_eq {sz}:
  forall (w w' : word sz),
    decides (weqb w w') (w = w').
Proof.
  unfold decides, If_Then_Else; intros.
  destruct (weqb w w') eqn: ? ;
    unfold not; setoid_rewrite <- weqb_true_iff; congruence.
Qed.

Lemma decides_bool_eq :
  forall (b b' : bool),
    decides (eqb b b') (b = b').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct b; destruct b'; simpl; congruence.
Qed.

Lemma decides_unit_eq :
  forall (b b' : unit),
    decides true (b = b').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct b; destruct b'; simpl; congruence.
Qed.

Lemma decides_Fin_eq {n} :
  forall (b b' : Fin.t n),
    decides (fin_eq_dec b b') (b = b').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct (fin_eq_dec b b'); simpl; congruence.
Qed.

Lemma decides_EnumType_eq {A} {n} {tags} :
  forall (b b' : @EnumType n A tags),
    decides (fin_beq b b') (b = b').
Proof.
  unfold decides, If_Then_Else; intros.
  destruct (fin_beq b b') eqn: H' ;
    unfold not; intros;
      try rewrite fin_beq_dec in H';
      try rewrite fin_beq_neq_dec in H'; eauto.
Qed.

  Lemma firstn_app {A}
    : forall (l1 l2 : list A),
      firstn (|l1 |) (l1 ++ l2) = l1.
  Proof.
    induction l1; intros; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma decides_firstn_app {A}
    : forall (l1 l2 : list A),
      decides true (firstn (|l1 |) (l1 ++ l2) = l1).
  Proof.
    apply firstn_app.
  Qed.

  Lemma firstn_self {A}
    : forall (l1 : list A),
      firstn (|l1 |) l1 = l1.
  Proof.
    induction l1; intros; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma decides_firstn_self {A}
    : forall (l1 : list A),
      decides true (firstn (|l1 |) l1 = l1).
  Proof.
    intros; apply firstn_self.
  Qed.

  Lemma skipn_app {A}
    : forall (l1 l2 : list A),
      skipn (|l1|) (l1 ++ l2) = l2.
  Proof.
    induction l1; intros; simpl; eauto.
  Qed.

  Lemma decides_skipn_app {A}
    : forall (l1 l2 : list A),
      decides true (skipn (|l1|) (l1 ++ l2) = l2).
  Proof.
    apply skipn_app.
  Qed.

  Lemma firstn_skipn_app {A}
    : forall (l1 l2 l3 : list A),
      firstn (|l3|) (skipn (|l1| + |l2|) (l1 ++ l2 ++ l3)) = l3.
  Proof.
    simpl; intros.
    rewrite <- app_length, List.app_assoc, skipn_app.
    apply firstn_self.
  Qed.

  Lemma decides_firstn_skipn_app {A}
    : forall (l1 l2 l3 : list A),
      decides true (firstn (|l3|) (skipn (|l1| + |l2|) (l1 ++ l2 ++ l3)) = l3).
  Proof.
    intros; apply firstn_skipn_app.
  Qed.

  Lemma firstn_skipn_self' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (firstn n l ++ firstn m (skipn n l) ++ firstn o (skipn (n + m) l))%list =
      l.
  Proof.
    induction n; simpl.
    induction m; simpl; eauto.
    induction o; simpl.
    destruct l; simpl; eauto.
    intros; discriminate.
    destruct l; simpl; eauto.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
  Qed.

  Lemma firstn_skipn_self'' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      ->
      decides true ((firstn n l ++ firstn m (skipn n l) ++ firstn o (skipn (n + m) l))%list =
                    l).
  Proof.
    intros; eapply firstn_skipn_self'.
    omega.
  Qed.

  Lemma word_eq_self
    : forall (w : word 1),
      decides true (WS (whd w) WO = w).
  Proof.
    simpl; intros; shatter_word w; reflexivity.
  Qed.

  Lemma firstn_skipn_self {A}
      : forall (n m o : nat) (l l1 l2 l3 : list A),
      (l1 ++ l2 ++ l3)%list = l ->
      (|l1|) = n ->
      (|l2|) = m ->
      (|l3|) = o ->
      l1 = firstn n l
      /\ l2 = firstn m (skipn n l)
      /\ l3 = firstn o (skipn (n + m) l).
  Proof.
    intros; subst; intuition;
    eauto using firstn_skipn_app, skipn_app, firstn_app.
    rewrite skipn_app; symmetry; apply firstn_app.
  Qed.

  Lemma length_firstn_skipn_app {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (|firstn m (skipn n l) |) = m.
  Proof.
    induction n; simpl.
    induction m; simpl; eauto.
    induction o; simpl.
    destruct l; simpl; eauto.
    intros; discriminate.
    destruct l; simpl; eauto.
    intros; discriminate.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
  Qed.

  Lemma length_firstn_skipn_app' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (|firstn o (skipn (n + m) l) |) = o.
  Proof.
    induction n; simpl.
    induction m; simpl; eauto.
    induction o; simpl.
    destruct l; simpl; eauto.
    destruct l; simpl; eauto.
    destruct l; simpl; eauto.
    intros; discriminate.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
  Qed.

  Lemma length_firstn_skipn_app'' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (|firstn n l |) = n.
  Proof.
    induction n; destruct l; simpl; intros;
      try discriminate; eauto.
  Qed.

  Lemma whd_word_1_refl :
    forall (b : word 1),
      WS (whd b) WO = b.
  Proof.
    intros; destruct (shatter_word_S b) as [? [? ?] ]; subst.
    rewrite (shatter_word_0 x0); reflexivity.
  Qed.

Ltac decide_data_invariant :=
  (* Show that the invariant on the data is decideable. Most *)
  (* of the clauses in this predicate are obviously true by *)
  (* construction, but there may be some that need to be checked *)
  (* by a decision procedure*)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros; intuition;
  repeat first [ progress subst
               | match goal with
                   |- decides ?A (?B ?C)  =>
                   let T := type of C in
                   unify B (fun _ : T => True);
                   apply (@decides_True' T C)
                 end
               | apply decides_eq_refl
               | solve [eauto with decide_data_invariant_db]
               | eapply decides_and
               | eapply decides_assumption; eassumption
               | apply decides_dec_lt
               | eapply decides_unit_eq
               | eapply decides_word_eq
               | eapply decides_nat_eq
               | eapply decides_pair_eq
               | eapply decides_bool_eq
               | eapply decides_Fin_eq
               | eapply decides_EnumType_eq
               | eapply decides_dec_eq; auto using Peano_dec.eq_nat_dec, weq, pair_eq_dec ].

Ltac ilist_of_evar B As k :=
  match As with
  | VectorDef.nil _ => k (@inil _ B)
  | VectorDef.cons _ ?a _ ?As' =>
    makeEvar (B a)
             ltac:(fun b =>
                     ilist_of_evar
                       B As'
                       ltac:(fun Bs' => k (icons (l := As') b Bs')))
  end.

Ltac Vector_of_evar n T k :=
  match n with
  | 0 => k (@Vector.nil T)
  | S ?n' => Vector_of_evar
               n' T
               ltac:(fun l =>
                       makeEvar
                         T
                         ltac:(fun a => k (@Vector.cons T a n' l)))
  end.

Ltac decode_step cleanup_tac :=
  (* Processes the goal by either: *)
  match goal with
  | |- appcontext [encode_decode_correct_f _ _ _ _ ?H _ _] =>
    progress unfold H

  (* D) Solving the goal once all the byte string has been parsed *)
  | |- context [encode_decode_correct_f _ _ _ _
                                        (fun _ _ => ret _) _ _] =>
    solve [simpl; intros;
           eapply encode_decode_correct_finish;
           [ build_fully_determined_type cleanup_tac
           | decide_data_invariant ] ]

  | |- appcontext [encode_unused_word_Spec] =>
    unfold encode_unused_word_Spec
  (* A) decomposing one of the parser combinators, *)
  | |- _ => apply_compose
  (* B) applying one of the rules for a base type  *)
  | H : cache_inv_Property _ _
    |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    intros; revert H; eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_unused_word_Spec' _ _) _ _] =>
    let H := eval simpl in unused_word_decode_correct in
        apply H

  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_Vector_Spec _) _ _] =>
    intros; eapply Vector_decode_correct

  | |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_nat_Spec _) _ _] =>
    eapply Nat_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_list_Spec _) _ _] => intros; apply FixList_decode_correct

  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_bool_Spec) _ _] =>
    apply bool_decode_correct

  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_bool_Spec) _ _] =>
    eapply bool_decode_correct

  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_option_Spec _ _) _ _] =>
    intros; eapply option_encode_correct;
    [ match goal with
        H : cache_inv_Property _ _ |- _ => eexact H
      end | .. ]

  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_enum_Spec ?tb) _ _] =>
    eapply (@Enum_decode_correct _ _ _ _ _ _ _ tb)

  | |- appcontext[encode_decode_correct_f _ _ _ _ encode_string_Spec _ _ ] =>
    eapply String_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_SumType_Spec (B := ?B) (cache := ?cache) (m := ?n) ?types _) _ _] =>
    let cache_inv_H := fresh in
    intros cache_inv_H;
    first
      [let types' := (eval unfold types in types) in
       ilist_of_evar
         (fun T : Type => T -> @CacheEncode cache -> Comp (B * @CacheEncode cache))
         types'
         ltac:(fun encoders' =>
                 ilist_of_evar
                   (fun T : Type => B -> @CacheDecode cache -> option (T * B * @CacheDecode cache))
                   types'
                   ltac:(fun decoders' =>
                           ilist_of_evar
                             (fun T : Type => Ensembles.Ensemble T)
                             types'
                             ltac:(fun invariants' =>
                                     ilist_of_evar
                                       (fun T : Type => T -> B -> Prop)
                                       types'
                                       ltac:(fun invariants_rest' =>
                                               Vector_of_evar
                                                 n
                                                 (Ensembles.Ensemble (CacheDecode -> Prop))
                                                 ltac:(fun cache_invariants' =>
                                                         eapply (SumType_decode_correct (m := n) types) with
                                                         (encoders := encoders')
                                                           (decoders := decoders')
                                                           (invariants := invariants')
                                                           (invariants_rest := invariants_rest')
                                                           (cache_invariants :=  cache_invariants')
              )))))
      |          ilist_of_evar
                   (fun T : Type => T -> @CacheEncode cache -> Comp (B * @CacheEncode cache))
                   types
                   ltac:(fun encoders' =>
                           ilist_of_evar
                             (fun T : Type => B -> @CacheDecode cache -> option (T * B * @CacheDecode cache))
                             types
                             ltac:(fun decoders' =>
                                     ilist_of_evar
                                       (fun T : Type => Ensembles.Ensemble T)
                                       types
                                       ltac:(fun invariants' =>
                                               ilist_of_evar
                                                 (fun T : Type => T -> B -> Prop)
                                                 types
                                                 ltac:(fun invariants_rest' =>
                                                         Vector_of_evar
                                                           n
                                                           (Ensembles.Ensemble (CacheDecode -> Prop))
                                                           ltac:(fun cache_invariants' =>
                                                                   eapply (SumType_decode_correct (m := n) types) with
                                                                   (encoders := encoders')
                                                                     (decoders := decoders')
                                                                     (invariants := invariants')
                                                                     (invariants_rest := invariants_rest')
                                                                     (cache_invariants :=  cache_invariants'))))))
      ];
    [ simpl; repeat (apply Build_prim_and; intros); try exact I
    | apply cache_inv_H ]
  (* C) Discharging a side condition of one of the base rules *)
  | |- NoDupVector _ => Discharge_NoDupVector
  | |- context[Vector_predicate_rest (fun _ _ => True) _ _ _ _] =>
    intros; apply Vector_predicate_rest_True
  | |- context[fun st b' => ith _ (SumType.SumType_index _ st) (SumType.SumType_proj _ st) b'] =>
    let a'' := fresh in
    intro a''; intros; repeat instantiate (1 := fun _ _ => True);
    repeat destruct a'' as [ ? | a''] ; auto
  | _ => solve [solve_data_inv]
  | _ => solve [intros; instantiate (1 := fun _ _ => True); exact I]

  end.

Ltac synthesize_cache_invariant :=
  (* Synthesize an invariant satisfying the derived constraints *)
  (* on the cache. *)
  solve [repeat (instantiate (1 := fun _ => True));
         unfold cache_inv_Property; intuition].

Ltac normalize_compose transformer :=
  (* Perform algebraic simplification of the encoder specification. *)
  intros; eapply encode_decode_correct_refineEquiv;
  [intros ? ?; symmetry;
   repeat first [ etransitivity; [apply refineEquiv_compose_compose with (transformer := transformer)| ]
                | etransitivity; [apply refineEquiv_compose_Done with (transformer := transformer) | ]
                | apply refineEquiv_under_compose with (transformer := transformer) ];
   intros; higher_order_reflexivity
  | pose_string_ids ].

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

Lemma firstn_lt_decides {A}:
  forall m n (l : list A),
    (lt m n)%nat
    -> decides true (lt (|firstn m l |) n)%nat.
Proof.
  simpl; intros; rewrite firstn_length.
  eapply NPeano.Nat.min_lt_iff; eauto.
Qed.

  Lemma whd_word_1_refl' :
    forall (b : word 1),
      decides true (WS (whd b) WO = b).
  Proof.
    intros; destruct (shatter_word_S b) as [? [? ?] ]; subst.
    rewrite (shatter_word_0 x0); reflexivity.
  Qed.

  Lemma decides_length_firstn_skipn_app {A}
    : forall (n m o : nat) (l : list A),
      length l = n + (m + o)
      -> decides true ((|firstn m (skipn n l) |) = m).
  Proof.
    setoid_rewrite plus_assoc'.
    eapply length_firstn_skipn_app.
  Qed.

  Lemma decides_length_firstn_skipn_app' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + (m + o)
      -> decides true ((|firstn o (skipn (n + m) l) |) = o).
  Proof.
    setoid_rewrite plus_assoc'.
    apply length_firstn_skipn_app'.
  Qed.

  Lemma decides_length_firstn_skipn_app'' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + (m + o)
      -> decides true ((|firstn n l |) = n).
  Proof.
    setoid_rewrite plus_assoc'.
    apply length_firstn_skipn_app''.
  Qed.

  Lemma lt_1_pow2_16
    : lt 1 (pow2 16).
  Proof.
    intros.
    rewrite <- (wordToNat_natToWord_idempotent 16 1).
    eapply wordToNat_bound.
    simpl; eapply BinNat.N.ltb_lt; reflexivity.
Qed.

  Hint Resolve lt_1_pow2_16 : data_inv_hints.
  Hint Resolve FixedList_predicate_rest_True : data_inv_hints.

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

Ltac synthesize_decoder :=
  (* Combines tactics into one-liner. *)
  start_synthesizing_decoder;
  [ repeat (decode_step idtac)
  | cbv beta; synthesize_cache_invariant
  | cbv beta; optimize_decoder_impl].


Ltac synthesize_decoder_ext
     transformer
     decode_step'
     determineHooks
     synthesize_cache_invariant' :=
  (* Combines tactics into one-liner. *)
  start_synthesizing_decoder;
  [ normalize_compose transformer;
    repeat first [decode_step' idtac | decode_step determineHooks]
  | cbv beta; synthesize_cache_invariant' idtac
  | cbv beta; optimize_decoder_impl ].

Global Instance : DecideableEnsembles.Query_eq () :=
  {| A_eq_dec a a' := match a, a' with (), () => left (eq_refl _) end |}.

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

Definition FixInt_eq_dec (size : nat) (n m : {n | (N.lt n (exp2 size))%N }) : {n = m} + {~ n = m}.
  refine (if N.eq_dec (proj1_sig n) (proj1_sig m) then left _ else right _);
    destruct n; destruct m; try congruence; simpl in *; rewrite <- sig_equivalence; eauto.
Defined.

Ltac solve_enum :=
  let h := fresh in
  intros h; destruct h;
  [ idtac'; enum_part FixInt_eq_dec ..
  | idtac'; enum_finish ].

Ltac solve_done :=
  intros ? ? ? ? data ? ? ? ?;
         instantiate (1:=fun _ b e => (_, b, e));
  intros; destruct data; simpl in *; repeat match goal with
                                            | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
                                            | H : _ /\ _ |- _ => inversion H; subst; clear H
                                            end; intuition eauto; fail 0.

Ltac solve_predicate :=
  unfold IList_predicate, FixList_predicate;
  intuition eauto; instantiate (1:=fun _ => True); solve_predicate.

Ltac eauto_typeclass :=
  match goal with
  | |- context [ Bool_encode ] => eapply Bool_encode_correct
  | |- context [ Char_encode ] => eapply Char_encode_correct
  | |- context [ FixInt_encode ] => eapply FixInt_encode_correct
  | |- context [ FixList_encode _ ] => eapply FixList_encode_correct
  | |- context [ IList_encode _ ] => eapply IList_encode_correct
  (*| |- context [ SteppingList_encode _ _ _ ] => eapply SteppingList_encode_correct *)
  end; eauto.

Ltac solve_decoder :=
  match goal with
  | |- _ => solve [ eauto_typeclass; solve_decoder ]
  | |- _ => solve [ eapply Enum_encode_correct; solve_enum ]
  | |- _ => solve [ solve_done ]
  | |- _ => eapply compose_encode_correct; [ solve_decoder | solve_predicate | intro; solve_decoder ]
  end.
