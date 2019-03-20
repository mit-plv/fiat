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
        Fiat.Narcissus.Automation.Decision
        Fiat.Narcissus.Automation.Common.

Lemma decompose_pair_eq {A B}
  : forall (ab ab' : A * B),
    ab = ab' -> fst ab = fst ab' /\ snd ab = snd ab'.
Proof.
  intros; split; congruence.
Qed.

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
         | H : ?Inv _ |- _ =>
           unfold Inv in *
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
         end;
  unfold Basics.compose, IsProj in *.

Ltac decide_data_invariant :=
  (* Show that the invariant on the data is decideable. Most *)
  (* of the clauses in this predicate are obviously true by *)
  (* construction, but there may be some that need to be checked *)
  (* by a decision procedure*)
  unfold IsProj in *;
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


Ltac build_fully_determined_type :=
  (* Build the parsed object by showing it can be built *)
  (* from previously parsed terms and that and that the *)
  (* byte string was a valid encoding of this object. *)
  (* Start by doing some simplification and *)
  (* destructing the formatd object  *)
  unfold Basics.compose in *;
  simpl in *;
  let a' := fresh in
  intros a'; repeat destruct a' as [? a'];
  (* Show that it is determined by the constraints (equalities) *)
  (* inferred during parsing. *)
  simpl in *; intros;
  (* Decompose data predicate *)
  decompose_source_predicate;
  (* Substitute any inferred equalities; decomposing *)
  (* any product types that might have been built up *)
  (* along the way *)
  subst_projections;
  (* And unify with original object *) reflexivity.

Ltac ExtractSource :=
  solve [simpl; intros;
         eapply CorrectDecoderEmpty;
         [ build_fully_determined_type
         | decide_data_invariant ] ].

Ltac ExtractView :=
  simpl; intros;
  eapply ExtractViewFromRefined with (View_Predicate := fun _ => True); eauto;
  intros;
  decompose_source_predicate;
  subst_projections;
  try reflexivity;
  (* Try to instantiate and solve the goal with any variables in hand *)
  solve [match goal with
         | H : _ |- _ => solve [instantiate (1 := H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 2 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 3 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 4 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 5 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 6 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 7 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 8 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 9 * H); try omega;
                                auto with arith]
         | H : _ |- _ => solve [instantiate (1 := 10 * H); try omega;
                                auto with arith]
         | H : ?x = ?y |- _ => solve [instantiate (1 := x); try omega;
                                      auto with arith]
         | H : ?x = ?y |- _ => solve [instantiate (1 := y); try omega;
                                      auto with arith]
         end] .

Ltac extract_view :=
  (* Finish a decoder derivation *)
  match goal with
  | |- context [ CorrectDecoder _ _ _ _ empty_Format _ _ _ ] => ExtractSource
  | H : cache_inv_Property ?mnd _
    |- CorrectRefinedDecoder _ _ _ _ (_ ++ _)%format _ _ _ _ => ExtractView
  end.
