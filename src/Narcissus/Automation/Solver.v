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
        Fiat.Narcissus.Common.Sig
        Fiat.Narcissus.Automation.NormalizeFormats.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac build_ilist_evar :=
  match goal with
  | |- context[ith (m := ?n) (B := ?encT) (As := ?q ) ?z] =>
    is_evar z;
    match n with
    | S ?n' => let T := eval simpl in (Vector.hd q) in
                   makeEvar (encT T) ltac:(fun t' =>
                                             let H' := match (type of (@icons _ encT T n' (Vector.tl q) t')) with
                                                       | ?A -> _ => A
                                                       end in
                                             makeEvar H' ltac:(fun il' => unify z (@icons _ encT T n' (Vector.tl q) t' il')))
    | _ => idtac
    end
  | |- context[icons (n := ?n) (B := ?encT) (l := ?q) ?a ?z] =>
    is_evar z;
    match n with
    | S ?n' => let T := eval simpl in (Vector.hd q) in
                   makeEvar (encT T) ltac:(fun t' =>
                                             let H' := match (type of (@icons _ encT T n' (Vector.tl q) t')) with
                                                       | ?A -> _ => A
                                                       end in
                                             makeEvar H' ltac:(fun il' => unify z (@icons _ encT T n' (Vector.tl q) t' il')))
    | 0 => unify z (@inil _ encT)
    end
  end.

Ltac build_prim_prod_evar :=
  match goal with
  | |- context[ @ilist.prim_fst ?A unit ?z ?k] =>
    is_evar z;
    makeEvar A ltac:(fun a => unify z (Build_prim_prod a tt))
  | |- context[ @ilist.prim_fst ?A ?B ?z] =>
    is_evar z;
    makeEvar A ltac:(fun a =>
                       makeEvar B ltac:(fun b =>
                                          unify z (Build_prim_prod a b)))
  end.

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

Ltac decompose_source_predicate :=
  (* Decompose the source predicate into 'base' facts *)
  repeat match goal with
         | H : cache_inv_Property _ _ |- _ => clear H
         | H : _ |- _ =>
           let H1 := fresh in
           let H2 := fresh in
           pose proof (proj1 H) as H1;
           pose proof (proj2 H) as H2;
           clear H; simpl in H1;
           simpl in H2
         end.

Lemma IsProj_eq {S S'}
      {f : S -> S'}
      {s : S}
      {s' : S'}
      (H : IsProj f s' s) : f s = s'.
Proof.
  apply H.
Qed.

Ltac subst_projections :=
  (* Substitute any source projections learned during parsing *)
  repeat match goal with
         | H : ?s1 = ?s2 |- _ =>
           first [apply decompose_pair_eq in H; (let H1 := fresh in
                                                 let H2 := fresh in
                                                 destruct H as [H1 H2]; simpl in H1; simpl in H2)
                 ]
         | H : IsProj _ _ _ |- _ => apply IsProj_eq in H;
                                    unfold Basics.compose in H;
                                    simpl in H; rewrite H in *|-*
         end.

(* Solves data invariants using the data_inv_hints database *)
Ltac solve_data_inv :=
  first
    [ simpl; intros; exact I
    | (* Decompose the source predicate *)
    let src := fresh in
    let src_Pred := fresh in
    intros src src_Pred ;
    decompose_source_predicate;
    (* Substitute any equations on the source predicate where it is
      productive. We do not rewrite in the goal to avoid touching any
       evars. *)
    subst_projections; unfold Basics.compose;
    solve [intuition eauto with data_inv_hints]
    | shelve_inv ].

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

Ltac build_fully_determined_type cleanup_tac :=
  (* Build the parsed object by showing it can be built *)
  (* from previously parsed terms and that and that the *)
  (* byte string was a valid encoding of this object. *)
  (* Start by doing some simplification and *)
  (* destructing the formatd object  *)
  unfold Domain, GetAttribute, GetAttributeRaw, Basics.compose in *;
  simpl in *;
  let a' := fresh in
  intros a'; repeat destruct a' as [? a'];
  (* Show that it is determined by the constraints (equalities) *)
  (* inferred during parsing. *)
  unfold Domain, GetAttribute, GetAttributeRaw in *;
  simpl in *; intros;
  (* Decompose data predicate *)
  decompose_source_predicate;
  (* Substitute any inferred equalities; decomposing *)
  (* any product types that might have been built up *)
  (* along the way *)
  subst_projections;
  cleanup_tac;
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
  unfold GetAttribute, GetAttributeRaw, IsProj in *;
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


Ltac solve_side_condition :=
  (* Try to discharge a side condition of one of the base rules *)
  match goal with
  | |- NoDupVector _ => Discharge_NoDupVector
  | |- context[fun st b' => ith _ (SumType.SumType_index _ st) (SumType.SumType_proj _ st) b'] =>
    let a'' := fresh in
    intro a''; intros; repeat instantiate (1 := fun _ _ => True);
    repeat destruct a'' as [ ? | a''] ; auto
  | _ => solve [solve_data_inv]
  | _ => solve [intros; instantiate (1 := fun _ _ => True); exact I]
  end.

Ltac FinishDecoder :=
  solve [simpl; intros;
         eapply CorrectDecoderEmpty;
         [ build_fully_determined_type idtac
         | decide_data_invariant ] ].

(* Redefine this tactic to implement new decoder rules*)
Ltac new_decoder_rules := fail.

Ltac apply_rules :=
  (* Processes the goal by either: *)
  (* Unfolding an identifier *)
  match goal with
  | |- CorrectDecoder _ _ _ _ ?H _ _ _ =>
    progress unfold H
  (* Finishing a derivation *)
  | |- context [CorrectDecoder _ _ _ _ empty_Format _ _ _] => FinishDecoder
  (* Or applying one of our other decoder rules *)
  | H : cache_inv_Property ?P ?P_inv
    |- CorrectDecoder ?mnd _ _ _ (_ ◦ _ ++ _) _ _ _ =>
    first [
        eapply (format_const_sequence_correct H) with (monoid := mnd);
        clear H;
        [ intros; solve [repeat apply_rules]
        | solve [ solve_side_condition ]
        | intros ]
      | eapply (format_sequence_correct H) with (monoid := mnd);
        clear H;
        [ intros; solve [repeat apply_rules]
        | solve [ solve_side_condition ]
        | intros ]
      ]
  | H : cache_inv_Property ?P ?P_inv
    |- CorrectDecoder ?mnd _ _ _ (_ ++ _) _ _ _ =>
    eapply (format_unused_sequence_correct H) with (monoid := mnd);
    clear H;
    [ intros; solve [repeat apply_rules]
    | solve [ solve_side_condition ]
    | intros ]
  | H : cache_inv_Property ?P ?P_inv |- CorrectDecoder ?mnd _ _ _ (Either _ Or _)%format _ _ _ =>
    eapply (composeIf_format_correct H); clear H;
    [ intros
    | intros
    | solve [intros; intuition (eauto with bin_split_hints) ]
    | solve [intros; intuition (eauto with bin_split_hints) ] ]

  (* Here is the hook for new decoder rules *)
  | |- _ => new_decoder_rules

  | |- context [CorrectDecoder ?mnd _ _ _ (format_Vector _) _ _ _] =>
    intros; eapply (@Vector_decode_correct _ _ _ mnd)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ _ format_word _ _ _] =>
    intros; revert H; eapply Word_decode_correct
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ _ (format_nat _) _ _ _] =>
    intros; revert H; eapply Nat_decode_correct
  | |- context [CorrectDecoder _ _ _ _ (format_list _) _ _ _] =>
    intros; apply FixList_decode_correct

  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ _ (format_bool) _ _ _] =>
    intros; revert H; eapply bool_decode_correct

  | |- context [CorrectDecoder _ _ _ _ (Option.format_option _ _) _ _ _] =>
    intros; eapply Option.option_format_correct;
    [ match goal with
        H : cache_inv_Property _ _ |- _ => eexact H
      end | .. ]

  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _  _ _ _ (format_enum ?tb) _ _ _] =>
    eapply (fun NoDup => @Enum_decode_correct _ _ _ _ _ _ _ tb NoDup _ H);
    solve_side_condition

  | |- context[CorrectDecoder _ _ _ _ StringOpt.format_string _ _ _ ] =>
    eapply StringOpt.String_decode_correct
  | |- context [CorrectDecoder _ _ _ _ (format_SumType (B := ?B) (cache := ?cache) (m := ?n) ?types _) _ _ _] =>
    let cache_inv_H := fresh in
    intros cache_inv_H;
    first
      [let types' := (eval unfold types in types) in
       ilist_of_evar
         (fun T : Type => T -> @CacheFormat cache -> Comp (B * @CacheFormat cache))
         types'
         ltac:(fun formatrs' =>
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
                                                           (formatrs := formatrs')
                                                           (decoders := decoders')
                                                           (invariants := invariants')
                                                           (invariants_rest := invariants_rest')
                                                           (cache_invariants :=  cache_invariants')
              )))))
      |          ilist_of_evar
                   (fun T : Type => T -> @CacheFormat cache -> Comp (B * @CacheFormat cache))
                   types
                   ltac:(fun formatrs' =>
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
                                                                     (formatrs := formatrs')
                                                                     (decoders := decoders')
                                                                     (invariants := invariants')
                                                                     (invariants_rest := invariants_rest')
                                                                     (cache_invariants :=  cache_invariants'))))))
      ];
    [ simpl; repeat (apply IterateBoundedIndex.Build_prim_and; intros); try exact I
    | apply cache_inv_H ]
  end.

Ltac synthesize_cache_invariant :=
  (* Synthesize an invariant satisfying the derived constraints *)
  (* on the cache. *)
  solve [repeat (instantiate (1 := fun _ => True));
         unfold cache_inv_Property; intuition].

(*Lemma refineEquiv_If_Then_Else_Proper
  : forall (A : Type) (c : bool),
    Proper (@refineEquiv A ==> @refineEquiv A ==> @refineEquiv A) (If_Then_Else c).
Proof.
  unfold Proper, respectful; intros; destruct c; auto.
Qed.

Lemma refineEquiv_under_compose_map {cache : Cache}
  : forall (S S' T : Type) (monoid : Monoid T) (format1 : FormatM S' T) (format2 format2' : CacheFormat -> Comp (T * CacheFormat)) s (f : S -> S'),
    (forall ctx', refineEquiv (format2 ctx') (format2' ctx')) ->
    forall ctx, refineEquiv (((FMapFormat.Projection_Format format1 f s) ThenC format2) ctx) ((format1 (f s) ThenC format2') ctx).
Proof.
  unfold refineEquiv, refine; intros; intuition.
  unfold compose, Bind2 in *.
  computes_to_inv.
  computes_to_econstructor.
  eapply FMapFormat.EquivFormat_Projection_Format; eauto.
  computes_to_econstructor; eauto.
  eapply H; eauto.
  subst; eauto.
  unfold compose, Bind2 in *.
  computes_to_inv.
  computes_to_econstructor.
  eapply FMapFormat.EquivFormat_Projection_Format; eauto.
  computes_to_econstructor; eauto.
  eapply H; eauto.
  subst; eauto.
Qed.

Lemma EquivFormat_Projection_Format_DoneC
      {S S' T}
      {monoid : Monoid T}
      (format : FormatM S' T)
      (f : S -> S')
  : EquivFormat (FMapFormat.Projection_Format format f)
                (fun s => (format (f s)) DoneC).
Proof.
  unfold EquivFormat, FMapFormat.Projection_Format, FMapFormat.Compose_Format,
  compose, Bind2; split; intros ? ?.
  - apply unfold_computes; computes_to_inv; subst.
    eexists; split; simpl; eauto.
    rewrite mempty_right; destruct v0; eauto.
  - rewrite unfold_computes in H; destruct_ex; intuition; subst; eauto.
    repeat computes_to_econstructor; eauto.
    simpl.
    rewrite mempty_right; destruct v; eauto.
Qed.

  Ltac normalize_compose BitStringT :=
  (* Normalize formats by performing algebraic simplification. *)
  intros; eapply Specs.format_decode_correct_refineEquiv;
  unfold SequenceFormat.sequence_Format, Basics.compose;
  [intros ? ?; symmetry;
     repeat (first [ etransitivity; [apply refineEquiv_compose_compose with (monoid := BitStringT)| ]
                   | etransitivity; [apply refineEquiv_compose_Done with (monoid := BitStringT) | ]
                   | eapply refineEquiv_ComposeIf; intros
                   | etransitivity; [apply refineEquiv_If_Then_Else_ThenC with (monoid := BitStringT) | ]
                   | apply refineEquiv_If_Then_Else_Proper
                   | intros; match goal with
                       |- refineEquiv _ (_ ?env) =>
                       eapply refineEquiv_under_compose_map with (monoid := BitStringT)
                                                                 (ctx := env);
                       intros
                     end
                   | apply refineEquiv_under_compose with (monoid := BitStringT)
                   | eapply EquivFormat_Projection_Format_DoneC]; intros);
     intros; higher_order_reflexivity
  | pose_string_ids ]. *)

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

Lemma decides_Option_eq_None {B}
  : forall (s_opt : option B) b,
    (Ifopt s_opt as _ Then true Else false) = b
    -> decides (negb b) (s_opt = None).
Proof.
  intros; destruct s_opt; simpl in *; subst;
    simpl in *; congruence.
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

Ltac synthesize_decoder :=
  (* Combines tactics into one-liner. *)
  start_synthesizing_decoder;
  [ repeat apply_rules
  | cbv beta; synthesize_cache_invariant
  | cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl].

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
