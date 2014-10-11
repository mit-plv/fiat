(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification Parsers.BooleanRecognizer.
Require Import Common Common.ilist.
Require Import Eqdep_dec.

Local Hint Extern 0 =>
match goal with
  | [ H : false = true |- _ ] => solve [ destruct (Bool.diff_false_true H) ]
  | [ H : true = false |- _ ] => solve [ destruct (Bool.diff_true_false H) ]
end.

Coercion is_true (b : bool) := b = true.

Section sound.
  Section general.
    Context CharType (String : string_like CharType) (G : grammar CharType).
    Context (productions_listT : Type)
            (initial_productions_data : productions_listT)
            (is_valid_productions : productions_listT -> productions CharType -> bool)
            (remove_productions : productions_listT -> productions CharType -> productions_listT)
            (productions_listT_R : productions_listT -> productions_listT -> Prop)
            (remove_productions_dec : forall ls prods, is_valid_productions ls prods = true
                                                       -> productions_listT_R (remove_productions ls prods) ls)
            (ntl_wf : well_founded productions_listT_R).
    Context (split_string_for_production
             : forall (str0 : String)
                      (prod : production CharType),
                 list (list { str : String | str_le _ str str0 })).

    Section parts.
      Local Hint Constructors parse_of_item parse_of parse_of_production.

      Section item.
        Context (str : String)
                (str_matches_productions : productions CharType -> bool).

        Definition str_matches_productions_soundT
          := forall prods, str_matches_productions prods = true
                           -> parse_of _ G str prods.

        Definition str_matches_productions_completeT
          := forall prods, parse_of _ G str prods
                           -> str_matches_productions prods = true.

        Lemma parse_item_sound
              (str_matches_productions_sound : str_matches_productions_soundT)
              (it : item CharType)
        : parse_item String G str str_matches_productions it = true -> parse_of_item _ G str it.
        Proof.
          unfold parse_item, str_matches_productions_soundT in *.
          repeat match goal with
                   | _ => intro
                   | [ H : context[match ?E with _ => _ end] |- _ ] => atomic E; destruct E
                   | [ |- context[match ?E with _ => _ end] ] => atomic E; destruct E
                   | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                   | _ => progress subst
                   | _ => solve [ eauto ]
                 end.
        Defined.

        Lemma parse_item_complete
              (str_matches_productions_complete : str_matches_productions_completeT)
              (it : item CharType)
        : parse_of_item _ G str it -> parse_item String G str str_matches_productions it = true.
        Proof.
          unfold parse_item, str_matches_productions_completeT in *.
          repeat match goal with
                   | _ => intro
                   | _ => reflexivity
                   | [ H : parse_of_item _ _ ?s ?i |- _ ] => atomic s; atomic i; destruct H
                   | [ |- _ = true ] => apply bool_eq_correct
                   | _ => solve [ eauto ]
               end.
        Qed.
      End item.

      Section production0.
        Context (str0 : String)
                (parse_productions : forall (str : String),
                                       str_le _ str str0
                                       -> productions CharType
                                       -> bool).

        Definition parse_productions_soundT
          := forall str pf prods,
               @parse_productions str pf prods = true
               -> parse_of _ G str prods.

        Definition parse_productions_completeT
          := forall str pf prods,
               parse_of _ G str prods
               -> @parse_productions str pf prods = true.

        Definition split_list_correctT (split_list : list { str : String | str_le _ str str0 })
                   (prod : production CharType)
          := ((bool_eq _ (fold_right (Concat _) (Empty _) (map (@proj1_sig _ _) split_list)) str0)
                && if Arith.Peano_dec.eq_nat_dec (Datatypes.length split_list) (Datatypes.length prod)
                   then true
                   else false)%bool.

        Lemma parse_production_from_split_list_sound
              (parse_productions_sound : parse_productions_soundT)
              (strs : list { str : String | str_le _ str str0 })
              (prod : production CharType)
              (strs_correct : split_list_correctT strs prod)
        : parse_production_from_split_list G parse_productions strs prod = true
          -> parse_of_production _ G str0 prod.
        Proof.
          unfold parse_production_from_split_list, parse_productions_soundT, split_list_correctT, is_true in *.
          intro H.
          apply Bool.andb_true_iff in strs_correct.
          rewrite bool_eq_correct in strs_correct.
          destruct strs_correct as [strs_correct ?].
          rewrite <- strs_correct; clear strs_correct.
          edestruct Arith.Peano_dec.eq_nat_dec;
            generalize dependent strs;
            induction prod;
            intro strs; destruct strs;
            repeat match goal with
                     | _ => intro
                     | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                     | _ => progress subst
                     | _ => progress simpl in *
                     | [ H : S _ = 0 |- _ ] => solve [ destruct (NPeano.Nat.neq_succ_0 _ H) ]
                     | [ H : 0 = S _ |- _ ] => solve [ destruct (NPeano.Nat.neq_0_succ _ H) ]
                     | [ H : 0 > 0 |- _ ] => solve [ destruct (Le.le_Sn_0 _ H) ]
                     | [ H : S _ = S _ |- _ ] => apply NPeano.Nat.succ_inj in H
                     | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
                     | [ H : _ /\ _ |- _ ] => destruct H
                     | [ H : parse_item _ _ _ _ _ = true |- _ ] => apply parse_item_sound in H; hnf; []
                     | [ H : parse_item _ _ _ _ _ = true |- _ ] => apply parse_item_sound in H; hnf; eauto; []
                     | [ H : parse_item _ _ _ _ _ = true |- _ ] => apply parse_item_sound in H; hnf; solve [ eauto ]
                     | _ => solve [ eauto ]
                   end.
        Defined.

        Lemma fold_right_map {A B C} (f : A -> B) g c ls
        : @fold_right C B g
                      c
                      (map f ls)
          = fold_right (g ∘ f) c ls.
        Proof.
          induction ls; unfold compose; simpl; f_equal; auto.
        Qed.

        Lemma fold_right_orb_true ls
        : fold_right orb true ls = true.
        Proof.
          induction ls; destruct_head_hnf bool; simpl in *; trivial.
        Qed.

        Lemma fold_right_orb b ls
        : fold_right orb b ls = true
          <-> fold_right or (b = true) (map (fun x => x = true) ls).
        Proof.
          induction ls; simpl; intros; try reflexivity.
          rewrite <- IHls; clear.
          repeat match goal with
                   | _ => assumption
                   | _ => split
                   | _ => intro
                   | _ => progress subst
                   | _ => progress simpl in *
                   | _ => progress destruct_head or
                   | _ => progress destruct_head bool
                   | _ => left; reflexivity
                   | _ => right; assumption
                 end.
        Qed.

        Lemma fold_right_map_andb_andb {T} x y f g (ls : list T)
        : fold_right andb x (map f ls) = true /\ fold_right andb y (map g ls) = true
          <-> fold_right andb (andb x y) (map (fun k => andb (f k) (g k)) ls) = true.
        Proof.
          induction ls; simpl; intros; destruct_head_hnf bool; try tauto;
          rewrite !Bool.andb_true_iff;
          try tauto.
        Qed.

        Lemma fold_right_map_andb_orb {T} x y f g (ls : list T)
        : fold_right andb x (map f ls) = true /\ fold_right orb y (map g ls) = true
          -> fold_right orb (andb x y) (map (fun k => andb (f k) (g k)) ls) = true.
        Proof.
          induction ls; simpl; intros; destruct_head_hnf bool; try tauto;
          repeat match goal with
                   | [ H : _ |- _ ] => progress rewrite ?Bool.orb_true_iff, ?Bool.andb_true_iff in H
                   | _ => progress rewrite ?Bool.orb_true_iff, ?Bool.andb_true_iff
                 end;
          try tauto.
        Qed.

        Lemma fold_right_map_and_and {T} x y f g (ls : list T)
        : fold_right and x (map f ls) /\ fold_right and y (map g ls)
          <-> fold_right and (x /\ y) (map (fun k => f k /\ g k) ls).
        Proof.
          revert x y.
          induction ls; simpl; intros; try reflexivity.
          rewrite <- IHls; clear.
          tauto.
        Qed.

        Lemma fold_right_map_and_or {T} x y f g (ls : list T)
        : fold_right and x (map f ls) /\ fold_right or y (map g ls)
          -> fold_right or (x /\ y) (map (fun k => f k /\ g k) ls).
        Proof.
          revert x y.
          induction ls; simpl; intros; try assumption.
          intuition.
        Qed.

        Functional Scheme fold_right_rect := Induction for fold_right Sort Type.

        Definition split_lists_correctT (split_lists : list (list { str : String | str_le _ str str0 }))
                   (prod : production CharType)
          := fold_right andb true (map (fun ls => split_list_correctT ls prod) split_lists).

        Lemma parse_production_from_any_split_list_sound
              (parse_productions_sound : parse_productions_soundT)
              (strs : list (list { str : String | Length _ str < Length _ str0 \/ str = str0 }))
              (prod : production CharType)
              (strs_correct : split_lists_correctT strs prod)
        : parse_production_from_any_split_list G parse_productions strs prod = true
          -> parse_of_production _ G str0 prod.
        Proof.
          unfold parse_production_from_any_split_list; intro.
          unfold split_lists_correctT, is_true in *.
          repeat match goal with
                   | _ => intro
                   | [ H0 : fold_right andb _ _ = true, H1 : fold_right andb _ _ = true |- _ ]
                     => pose proof (proj1 (@fold_right_map_andb_andb _ _ _ _ _ _) (conj H0 H1));
                       clear H0 H1
                   | [ H0 : fold_right andb _ _ = true, H1 : fold_right orb _ _ = true |- _ ]
                     => pose proof (@fold_right_map_andb_orb _ _ _ _ _ _) (conj H0 H1);
                       clear H0 H1
                 end.
          simpl in *.
          let H := match goal with H : fold_right orb _ _ = _ |- _ => constr:H end in
          rewrite fold_right_map in H;
            let T := match type of H with ?a = _ => constr:a end in
            functional induction T using fold_right_rect;
              intros; subst;
              destruct_head_hnf and;
              repeat match goal with
                       | _ => progress simpl in *
                       | _ => progress unfold compose in *
                       | _ => progress destruct_head_hnf sumbool
                       | _ => progress destruct_head_hnf and
                       | [ H : false = true |- _ ] => solve [ destruct (Bool.diff_false_true H) ]
                       | [ H : true = false |- _ ] => solve [ destruct (Bool.diff_true_false H) ]
                       | [ H : _ |- _ ] => apply Bool.orb_true_elim in H
                       | [ H : _ |- _ ] => rewrite Bool.andb_true_iff in H
                       | [ H : context[Peano_dec.eq_nat_dec ?a ?b] |- _ ] => destruct (Peano_dec.eq_nat_dec a b)
                       | [ H : (_ =s _)%string_like = true |- _ ] => apply bool_eq_correct in H
                       | _ => eapply parse_production_from_split_list_sound; eassumption
                       | _ => auto
                     end.
        Defined.
      End production0.

      Section production1.
        Context (str0 : String)
                (parse_productions : forall (str : String),
                                       str_le _ str str0
                                       -> productions CharType
                                       -> bool).

        Definition or_transitivity' {A B} `{@Transitive B R} {f : A -> B} {a0 a}
                   (pf : R (f a) (f a0) \/ a = a0) a' (pf' : R (f a') (f a) \/ a' = a)
        : R (f a') (f a0) \/ a' = a0.
        Proof.
          destruct_head or; subst;
          first [ right; reflexivity | left; assumption | left; etransitivity; eassumption ].
        Defined.

        Lemma or_transitivity_eq' {A B} `{@Transitive B R} `{@Irreflexive B R} {f : A -> B} {a0 a}
              (isprop_r : forall x y (pf1 pf2 : R x y), pf1 = pf2)
              (isset_a : forall pf : a0 = a0, pf = eq_refl)
              (pf : R (f a) (f a0) \/ a = a0) a' (pf' : R (f a') (f a) \/ a' = a)
        : or_transitivity pf pf' = or_transitivity' pf pf'.
        Proof.
          destruct pf, pf'; simpl in *; subst; compute;
          match goal with
            | [ |- ?a = _ ] => case_eq a
          end;
          repeat match goal with
                   | _ => intro
                   | _ => progress subst
                   | [ |- _ = _ :> or _ _ ] => progress f_equal
                   | _ => apply isprop_r
                   | _ => apply isset_a
                   | [ |- or_intror _ = or_introl _ ] => exfalso
                   | [ |- or_introl _ = or_intror _ ] => exfalso
                   | [ H : R ?a ?b, H' : R ?b ?a |- _ ] => destruct (irreflexivity (transitivity H H'))
                   | [ H : R ?a ?a |- _ ] => destruct (irreflexivity H)
                 end.
        Qed.

        Fixpoint le_0_n_transparent n : 0 <= n
          := match n with
               | 0 => le_n _
               | S n' => le_S _ _ (le_0_n_transparent n')
             end.

        Fixpoint le_n_S_transparent {n m} (H : n <= m) : S n <= S m
          := match H with
               | le_n => le_n _
               | le_S _ H0 => le_S _ _ (le_n_S_transparent H0)
             end.

        Fixpoint le_pred_transparent {n m} (H : n <= m) : pred n <= pred m.
        Proof.
          destruct H; try constructor.
          destruct m; simpl.
          { change 0 with (pred 0); apply le_pred_transparent; assumption. }
          { constructor.
            change m with (pred (S m)).
            apply le_pred_transparent; assumption. }
        Defined.

        Definition le_S_n_transparent {n m} (H : S n <= S m) : n <= m
          := le_pred_transparent H.

        Fixpoint le_dec_transparent n m : {n <= m} + {~n <= m}
          := match n, m with
               | 0, _ => left (le_0_n_transparent _)
               | S _, 0 => right (Le.le_Sn_0 _)
               | S n', S m' => match le_dec_transparent n' m' with
                                 | left H => left (le_n_S_transparent H)
                                 | right nH => right (fun H => nH (le_S_n_transparent H))
                               end
             end.

        Definition lt_dec_transparent n m : {n < m} + {~n < m}
          := le_dec_transparent _ _.

        Fixpoint lt_irrelevant n m pf : match lt_dec_transparent n m with
                                          | left pf2 => pf = pf2
                                          | right pf2 => False
                                        end.
        Proof.
          revert lt_irrelevant.
          clear.
          intro lt_irrelevant.
          destruct pf as [|? pf]; simpl;
          [ clear lt_irrelevant | specialize (lt_irrelevant _ _ pf) ];
          unfold lt_dec_transparent in *;
          simpl in *;
          repeat match goal with
                   | _ => reflexivity
                   | _ => progress simpl in *
                   | _ => intros; clear lt_irrelevant; exfalso; abstract intuition
                   | [ |- context[match ?m with _ => _ end] ]
                     => destruct m; intros; exfalso; abstract intuition
                   | [ |- context[le_dec_transparent ?n ?n] ]
                     => atomic n;
                       match goal with
                         | [ H : context[le_dec_transparent n n] |- _ ]
                           => destruct (le_dec_transparent n n);
                             [ rewrite <- H; reflexivity | assumption ]
                         | _ => induction n
                       end
                 end.
(*
          destruct m0.
          destruct lt_irrelevant.
          destruct n; simpl in *.
          subst; reflexivity.
          destruct m0.
          destruct lt_irrelevant.

          Focus 2.
          repeat match goal with

                 end.
          end.
          destruct m; intros. exfalso; abstract intuition.
          destruct (le_dec_transparent n m).
          exfalso; abstract intuition.
          intros; exfalso; abstract intuition.
            rewrite <- IHn.
            repeat match goal with
                     | _ => reflexivity
                     | _ => assumption
                     | _ => progress simpl in *
                   end.
                 simpl
          end.
          { induction n; try reflexivity; try assumption.
            unfold lt_dec_transparent in *.
            simpl in *.
            edestruct le_dec_transparent; try assumption.
            rewrite <- IHn.
            reflexivity. }
          { unfold lt_dec_transparent in *.
            simpl in *.
            edestruct le_dec_transparent.
            Set Printing All.
            compute.
            unfold Gt.gt_le_S.
          SearchAbout lt_dec
          unfold lt_dec; simpl.

        Lemma map_or_transitivity'
              str ls pf
        : (map
             (map
                (fun sp : {str1 : String | str_le String str1 str} =>
                   exist (fun str1 : String => str_le String str1 str0)
                         (` sp) (or_transitivity pf (proj2_sig sp))))
             ls)
          = (map
               (map
                  (fun sp : {str1 : String | str_le String str1 str} =>
                     exist (fun str1 : String => str_le String str1 str0)
                           (` sp) (or_transitivity' pf (proj2_sig sp))))
               ls).
        Proof.
          clear.
          repeat match goal with
                   | [ |- map ?f ?ls = map ?g ?ls ] => let IHls := fresh in
                                                       induction ls as [|? ? IHls]; simpl; trivial; [];
                                                       rewrite IHls; clear IHls
                   | [ |- ?a::?b = ?a::?c ] => apply f_equal
                   | [ |- ?a::?b = ?c::?b ] => apply f_equal2; [ | reflexivity ]
                 end.
          f_equal; apply or_transitivity_eq'.

          { intros.
            apply eq_proofs_unicity.
            intros x y.
            case_eq (bool_eq _ x y); intro H.
            { apply bool_eq_correct in H.
              left; assumption. }
            { right; intro H'.
              apply bool_eq_correct in H'.
              generalize dependent (x =s y)%string_like; clear; intros; subst;
              discriminate. }


          Focus 2.
          Require Import Eqdep_dec.

          SearchAbout (_ < _).
*)
          Lemma or_to_sumbool (s1 s2 : String) (f : String -> nat)
                (H : f s1 < f s2 \/ s1 = s2)
          : {f s1 < f s2} + {s1 = s2}.
          Proof.
            case_eq (bool_eq _ s1 s2).
            { intro H'; right; apply bool_eq_correct in H'; exact H'. }
            { intro H'; left; destruct H; trivial.
              apply bool_eq_correct in H.
              generalize dependent (s1 =s s2)%string_like; intros; subst.
              discriminate. }
          Qed.

          Lemma fold_right_andb_map_impl {T} x y f g (ls : list T)
                (H0 : x = true -> y = true)
                (H1 : forall k, f k = true -> g k = true)
          : (fold_right andb x (map f ls) = true -> fold_right andb y (map g ls) = true).
          Proof.
            induction ls; simpl; intros; try tauto.
            rewrite IHls; simpl;
            repeat match goal with
                     | [ H : _ = true |- _ ] => apply Bool.andb_true_iff in H
                     | [ |- _ = true ] => apply Bool.andb_true_iff
                     | _ => progress destruct_head and
                     | _ => split
                     | _ => auto
                   end.
          Qed.

        Lemma parse_production_sound_helper
              (parse_productions_sound
               : forall str pf prods,
                   @parse_productions str pf prods = true
                   -> parse_of _ G str prods)
              (str : String) (pf : Length _ str < Length _ str0 \/ str = str0)
              (prod : production CharType)
              (strs_correct : forall str (pf : Length _ str < Length _ str0 \/ str = str0),
                                fold_right
                                  andb
                                  true
                                  (map (fun strs' => fold_right (Concat _) (Empty _) (map (@proj1_sig _ _) strs') =s str0)%string_like
                                       (map
                                          (map
                                             (fun sp : {str1 : String | str_le String str1 str} =>
                                                exist (fun str1 : String => str_le String str1 str0)
                                                      (` sp) (or_transitivity pf (proj2_sig sp))))
                                          (split_string_for_production str prod)))
                                = true)
              (strs_length_correct : forall str (pf : Length _ str < Length _ str0 \/ str = str0),
                                       fold_right
                                         andb
                                         true
                                         (map (fun strs' => if Arith.Peano_dec.eq_nat_dec (Datatypes.length strs') (Datatypes.length prod) then true else false)
                                              (map
                                                 (map
                                                    (fun sp : {str1 : String | str_le String str1 str} =>
                                                       exist (fun str1 : String => str_le String str1 str0)
                                                             (` sp) (or_transitivity pf (proj2_sig sp))))
                                                 (split_string_for_production str prod)))
                                       = true)
        : parse_production G split_string_for_production parse_productions pf prod = true
          -> parse_of_production _ G str prod.
        Proof.
          unfold parse_production.
          pose proof (or_to_sumbool _ pf) as pf'.
          generalize dependent (split_string_for_production str prod); intros.
          destruct prod;
            repeat match goal with
                     | _ => intro
                     | _ => progress simpl in *
                     | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                     | [ H : sumbool _ _ |- _ ] => destruct H
                     | _ => progress subst
                     | _ => progress simpl in *
                     | [ H : 0 > 0 |- _ ] => solve [ destruct (Le.le_Sn_0 _ H) ]
                     | _ => solve [ eauto ]
                   end.
          eapply parse_production_from_any_split_list_sound.
          eapply parse_productions_sound.
            try (eapply parse_production_from_any_split_list_sound; eassumption).

          solve [ eapply parse_production_from_any_split_list_sound; eapply_hyp ].
          pose (fun str pf' => @parse_productions str (or_transitivity pf pf')) as parse_productions'.
          let strs' := match goal with strs : list (list _) |- _ => constr:strs end in
          eapply parse_production_from_any_split_list_sound
          with (parse_productions := parse_productions')
                 (strs := strs'); try eassumption;
          intros; subst parse_productions';
          try solve [ eapply_hyp ];
          repeat match goal with
                   | _ => intro
                   | [ H : _ |- _ ] => rewrite map_map in H
                 end.
          move strs_correct at bottom.
          match goal with
            | [ H : context[Concat String] |- context[Concat String] ]
              => revert H; apply fold_right_andb_map_impl; trivial
          end.
          repeat match goal with
                   | _ => intro
                   | [ H : _ |- _ ] => rewrite map_map in H
                 end.
          simpl in *.
          intro
          intros; rewrite
          match goal with
          rewrite fold_right_map.
          unfold compose in *; simpl in *.
          Lemma fold_right_f_fold_right_map_map {A B C D E F f f' k k' k'' g h ls}
          : @fold_right A B (fun x => f (@fold_right C D f' k (map (g x) (map (A := F x) (B := E x) (h x) (ls x))))) k' k''
            = fold_right (fun x => f (fold_right f' k (map (g x ∘ h x) (ls x)))) k' k''.
          Proof.
            clear.
            induction k''; simpl; trivial.
            rewrite <- IHk''; clear IHk''.
            rewrite map_map.
            reflexivity.
          Qed.

          match type of strs_correct with
            | @fold_right ?A ?B (fun x => andb (@fold_right ?C ?D ?f' ?k (map (@?g x) (map (A := @?F x) (B := @?E x) (@?h x) (@?ls x)))))
          rewrite fold_right_f_fold_right_map_map in strs_correct.
          setoid_rewrite map_map in strs_correct.
          match type of strs_correct with ?a = _ => functional induction a using fold_right_rect end.
          simpl.
          reflexivity.
          simpl

          setoid_rewrite map_map in strs_correct.

                   | [ |- _ ] => rewrite fold_right_map
                 end.
          move strs_correct at bottom.
          eapply parse_productions_sound.
          apply H1.

          eauto.
          eapply p.
 with (parse_productions := parse_productions); try eassumption.
          eapply
          move parse_productions_sound at bottom.

          exact parse_productions_sound.
          intros ? ?.
          exact parse_productions_sound.
          intros; apply parse_productions_sound.


          Focus 2.
          { eapply parse_production_from_any_split_list_sound; try eassumption.
            repeat match goal with
                     | _ => progress destruct_head or
                     | [ H : ?a < ?a |- _ ] => destruct (Lt.lt_irrefl _ H)
                   end.
            unfold or_transitivity in *.
          rewrite !map_map.
            rewrite <- fold_right_andb.
; try eassumption.

          induction (split_string_for_production str (a::prod)).
          simpl in *.
          inversion H.
          apply IHl.
          move H at bottom.
          simpl in *.


        (*Lemma parse_production_from_split_list_complete
              (parse_productions_correct
               : forall str pf prods,
                   parse_of _ G str prods
                   -> @parse_productions str pf prods = true)
              (prod : production CharType)
              (H : parse_of_production _ G str0 prod)
        : { strs : list { str : String | str_le _ str str0 }
          | fold_right (Concat _) (Empty _) (map (@proj1_sig _ _) strs) = str0
            /\ Datatypes.length strs = Datatypes.length prod
            /\ parse_production_from_split_list G parse_productions strs prod = true }.
        Proof.
          unfold parse_production_from_split_list.
          revert parse_productions parse_productions_correct.
          induction H; subst; simpl in *.
          { eexists nil; simpl; clear; abstract tauto. }
          { intros.
            refine (exist _ (
          -> parse_of_production _ G str0 prod.
        Proof.*)




          := fold_left andb
                       (map (fun sp => parse_item (proj1_sig (fst sp))
                                                  (parse_productions (proj2_sig (fst sp)))
                                                  (snd sp))
                            (combine strs prod))
                       true.

        Lemma parse_production_sound
              (parse_productions_sound
               : forall str pf prods,
                   @parse_productions str pf prods = true
                   -> parse_of _ G str prods)
              (str : String) (pf : Length _ str < Length _ str0 \/ str = str0)
              (prod : production CharType)
        : parse_production String G split_string_for_production parse_productions pf prod = true
          -> parse_of_production _ G str prod.
        Proof.
          unfold parse_production, parse_production_from_any_split_list, parse_production_from_split_list.
          revert str pf.
          induction prod;
            repeat match goal with
                     | _ => intro
                     | [ H : _ = true |- _ ] => apply bool_eq_correct in H
                     | _ => progress subst
                     | _ => progress simpl in *
                     | [ H : 0 > 0 |- _ ] => solve [ destruct (Le.le_Sn_0 _ H) ]
                     | _ => solve [ eauto ]
                   end; [].
          induction (split_string_for_production str (a::prod)).
          simpl in *.
          inversion H.
          apply IHl.
          move H at bottom.
          simpl in *.

          apply ParseProductionCons.
          hnf in g.
          SearchAbout (S _ <= 0).

            := if (gt_dec (Datatypes.length prod) 0)
             then (@parse_production_from_any_split_list
                     (map (map (fun sp => exist _ (proj1_sig sp) (or_transitivity pf (proj2_sig sp))))
                          (@split_string_for_production str prod))
                     prod)
             else (** 0-length production, only accept empty *)
               (str =s Empty _).



        (** To match a [production], any split of the string can match. *)
        Definition parse_production_from_any_split_list
                   (strs : list (list { str : String | Length _ str < Length _ str0 \/ str = str0 }))
                   (prod : production CharType)
        : bool
          := fold_left orb
                       (map (fun strs' => parse_production_from_split_list strs' prod)
                            strs)
                       false.

        (** We assume the splits we are given are valid (are actually splits of the string, rather than an unrelated split) and are the same length as the given [production].  Behavior in other cases is undefined *)
        (** We match a production if any split of the string matches that production *)
      End production.

      Section productions.
        Section step.
          Variable str0 : String.
          Variable parse_productions : forall (str : String)
                                              (pf : Length _ str < Length _ str0 \/ str = str0),
                                         productions CharType -> bool.

          (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
          Definition parse_productions_step (str : String) (pf : Length _ str < Length _ str0 \/ str = str0) (prods : productions CharType)
          : bool
            := fold_left orb
                         (map (parse_production parse_productions pf)
                              prods)
                         false.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_productions_or_abort_helper
          : forall (p : String * productions_listT) (str : String),
              Length String str < Length String (fst p) \/ str = fst p ->
              productions CharType -> bool
            := @Fix (prod String productions_listT)
                    _ (@well_founded_prod_relation
                         String
                         productions_listT
                         _
                         _
                         (well_founded_ltof _ (Length String))
                         ntl_wf)
                    _
                    (fun sl parse_productions str pf (prods : productions CharType)
                     => let str0 := fst sl in
                        let valid_list := snd sl in
                        match lt_dec (Length _ str) (Length _ str0) with
                          | left pf' =>
                            (** [str] got smaller, so we reset the valid productions list *)
                            parse_productions_step
                              (parse_productions
                                 (str, initial_productions_data)
                                 (or_introl pf'))
                              (or_intror eq_refl)
                              prods
                          | right pf' =>
                            (** [str] didn't get smaller, so we cache the fact that we've hit this productions already *)
                            (if is_valid_productions valid_list prods as is_valid
                                return is_valid_productions valid_list prods = is_valid -> _
                             then (** It was valid, so we can remove it *)
                               fun H' =>
                                 parse_productions_step
                                   (parse_productions
                                      (str0, remove_productions valid_list prods)
                                      (or_intror (conj eq_refl (remove_productions_dec H'))))
                                   (or_intror eq_refl)
                                   prods
                             else (** oops, we already saw this productions in the past.  ABORT! *)
                               fun _ => false
                            ) eq_refl
                        end).

          Definition parse_productions_or_abort (str0 str : String)
                     (valid_list : productions_listT)
                     (pf : Length _ str < Length _ str0 \/ str = str0)
                     (prods : productions CharType)
          : bool
            := parse_productions_or_abort_helper (str0, valid_list) pf prods.

          Definition parse_productions (str : String) (prods : productions CharType)
          : bool
            := @parse_productions_or_abort str str initial_productions_data
                                           (or_intror eq_refl) prods.
        End wf.

      End productions.
    End parts.
  End bool.
End recursive_descent_parser.

Section recursive_descent_parser_list.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.
  Variable (CharType_eq_dec : forall x y : CharType, {x = y} + {x <> y}).
  Definition rdp_list_productions_listT : Type := list (productions CharType).
  Definition rdp_list_is_valid_productions : rdp_list_productions_listT -> productions CharType -> bool
    := fun ls nt => if in_dec (productions_dec CharType_eq_dec) nt ls then true else false.
  Definition rdp_list_remove_productions : rdp_list_productions_listT -> productions CharType -> rdp_list_productions_listT
    := fun ls nt =>
         filter (fun x => if productions_dec CharType_eq_dec nt x then false else true) ls.
  Definition rdp_list_productions_listT_R : rdp_list_productions_listT -> rdp_list_productions_listT -> Prop
    := ltof _ (@List.length _).
  Lemma filter_list_dec {T} f (ls : list T) : List.length (filter f ls) <= List.length ls.
  Proof.
    induction ls; trivial; simpl in *.
    repeat match goal with
             | [ |- context[if ?a then _ else _] ] => destruct a; simpl in *
             | [ |- S _ <= S _ ] => solve [ apply Le.le_n_S; auto ]
             | [ |- _ <= S _ ] => solve [ apply le_S; auto ]
           end.
  Qed.
  Lemma rdp_list_remove_productions_dec : forall ls prods,
                                            @rdp_list_is_valid_productions ls prods = true
                                            -> @rdp_list_productions_listT_R (@rdp_list_remove_productions ls prods) ls.
  Proof.
    intros.
    unfold rdp_list_is_valid_productions, rdp_list_productions_listT_R, rdp_list_remove_productions, ltof in *.
    destruct (in_dec (productions_dec CharType_eq_dec) prods ls); [ | discriminate ].
    match goal with
      | [ H : In ?prods ?ls |- context[filter ?f ?ls] ]
        => assert (~In prods (filter f ls))
    end.
    { intro H'.
      apply filter_In in H'.
      destruct H' as [? H'].
      destruct (productions_dec CharType_eq_dec prods prods); congruence. }
    { match goal with
        | [ |- context[filter ?f ?ls] ] => generalize dependent f; intros
      end.
      induction ls; simpl in *; try congruence.
      repeat match goal with
               | [ |- context[if ?x then _ else _] ] => destruct x; simpl in *
               | [ H : _ \/ _ |- _ ] => destruct H
               | _ => progress subst
               | [ H : ~(_ \/ _) |- _ ] => apply Decidable.not_or in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : ?x <> ?x |- _ ] => exfalso; apply (H eq_refl)
               | _ => apply Lt.lt_n_S
               | _ => apply Le.le_n_S
               | _ => apply filter_list_dec
               | [ H : _ -> _ -> ?G |- ?G ] => apply H; auto
             end. }
  Qed.
  Lemma rdp_list_ntl_wf : well_founded rdp_list_productions_listT_R.
  Proof.
    unfold rdp_list_productions_listT_R.
    intro.
    apply well_founded_ltof.
  Defined.
End recursive_descent_parser_list.

Section example_parse_string_grammar.
  Fixpoint make_all_single_splits (str : string) : list { strs : string * string | (fst strs ++ snd strs = str)%string }.
  Proof.
    refine ((exist _ (""%string, str) eq_refl)
              ::(match str with
                   | ""%string => nil
                   | String.String ch str' =>
                     map (fun p => exist _ (String.String ch (fst (proj1_sig p)),
                                            snd (proj1_sig p))
                                         _)
                         (make_all_single_splits str')
                 end)).
    clear.
    abstract (simpl; apply f_equal; apply proj2_sig).
  Defined.

  Lemma length_append (s1 s2 : string) : length (s1 ++ s2) = length s1 + length s2.
  Proof.
    revert s2.
    induction s1; simpl; trivial; [].
    intros.
    f_equal; auto.
  Qed.

  Fixpoint flatten1 {T} (ls : list (list T)) : list T
    := match ls with
         | nil => nil
         | x::xs => (x ++ flatten1 xs)%list
       end.

  Lemma flatten1_length_ne_0 {T} (ls : list (list T)) (H0 : Datatypes.length ls <> 0)
        (H1 : Datatypes.length (hd nil ls) <> 0)
  : Datatypes.length (flatten1 ls) <> 0.
  Proof.
    destruct ls as [| [|] ]; simpl in *; auto.
  Qed.

  Local Ltac t' :=
    match goal with
      | _ => progress simpl in *
      | _ => progress subst
      | [ H : ?a = ?b |- _ ] => progress subst a
      | [ H : ?a = ?b |- _ ] => progress subst b
      | _ => rewrite (LeftId string_stringlike _)
      | _ => rewrite (RightId string_stringlike _)
      | _ => reflexivity
      | _ => split
      | _ => right; reflexivity
      | _ => rewrite map_length
      | _ => rewrite map_map
      | _ => rewrite length_append
      | _ => progress destruct_head_hnf prod
      | _ => progress destruct_head_hnf and
      | _ => progress destruct_head_hnf or
      | _ => progress destruct_head_hnf sig
      | _ => progress auto with arith
      | _ => apply f_equal
      | _ => solve [ apply proj2_sig ]
      | _ => solve [ left; auto with arith ]
      | [ str : string |- _ ] => solve [ destruct str; simpl; auto with arith ]
      | [ str : string |- _ ] => solve [ left; destruct str; simpl; auto with arith ]
    end.
  Local Ltac t'' :=
    match goal with
      | _ => progress t'
      | [ str : string |- _ ] => solve [ destruct str; repeat t' ]
    end.
  Local Ltac t :=
    solve [ repeat t'' ].

  Local Hint Resolve NPeano.Nat.lt_lt_add_l NPeano.Nat.lt_lt_add_r NPeano.Nat.lt_add_pos_r NPeano.Nat.lt_add_pos_l : arith.

  Fixpoint brute_force_splitter_helper
           (prod : production Ascii.ascii)
  : forall str : string_stringlike,
      list
        (list
           {str_part : string_stringlike |
            Length string_stringlike str_part < Length string_stringlike str \/
            str_part = str}).
  Proof.
    refine (match prod with
              | nil => fun str =>
                         (** We only get one thing in the list *)
                         (((exist _ str _)::nil)::nil)
              | _::prod' => fun str =>
                              (flatten1
                                 (map (fun s1s2p =>
                                         map
                                           (fun split_list => ((exist _ (fst (proj1_sig s1s2p)) _)
                                                                 ::(map (fun s => exist _ (proj1_sig s) _)
                                                                        split_list)))
                                           (@brute_force_splitter_helper prod' (snd (proj1_sig s1s2p))))
                                      (make_all_single_splits str)))
            end);
    subst_body;
    clear;
    abstract t.
  Defined.

  Definition brute_force_splitter
  : forall (str : string_stringlike) (prod : production Ascii.ascii),
      list
        (list
           { str_part : string_stringlike |
             Length string_stringlike str_part < Length string_stringlike str \/
             str_part = str })
    := fun str prods =>
         match prods with
           | nil => nil (** no patterns, no split (actually, we should never encounter this case *)
           | _::prods' => brute_force_splitter_helper prods' str
         end.

  Variable G : grammar Ascii.ascii.
  Variable all_productions : list (productions Ascii.ascii).

  Definition brute_force_make_parse_of : @String Ascii.ascii string_stringlike
                                         -> productions Ascii.ascii
                                         -> bool
    := parse_productions
         string_stringlike
         G
         all_productions
         (rdp_list_is_valid_productions Ascii.ascii_dec)
         (rdp_list_remove_productions Ascii.ascii_dec)
         (rdp_list_remove_productions_dec Ascii.ascii_dec) rdp_list_ntl_wf
         brute_force_splitter.
End example_parse_string_grammar.

Module example_parse_empty_grammar.
  Definition make_parse_of : forall (str : string)
                                    (prods : productions Ascii.ascii),
                               bool
    := @brute_force_make_parse_of (trivial_grammar _) (map (Lookup (trivial_grammar _)) (""::nil)%string).



  Definition parse : string -> bool
    := fun str => make_parse_of str (trivial_grammar _).

  Time Compute parse "".
  Check eq_refl : true = parse "".
  Time Compute parse "a".
  Check eq_refl : false = parse "a".
  Time Compute parse "aa".
  Check eq_refl : false = parse "aa".
End example_parse_empty_grammar.

Section examples.
  Section ab_star.

    Fixpoint production_of_string (s : string) : production Ascii.ascii
      := match s with
           | EmptyString => nil
           | String.String ch s' => (Terminal ch)::production_of_string s'
         end.

    Coercion production_of_string : string >-> production.

    Fixpoint list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
      := match ls with
           | nil => fun _ => default
           | (str, t)::ls' => fun s => if string_dec str s
                                       then t
                                       else list_to_productions default ls' s
         end.

    Delimit Scope item_scope with item.
    Bind Scope item_scope with item.
    Delimit Scope production_scope with production.
    Delimit Scope production_assignment_scope with prod_assignment.
    Bind Scope production_scope with production.
    Delimit Scope productions_scope with productions.
    Delimit Scope productions_assignment_scope with prods_assignment.
    Bind Scope productions_scope with productions.
    Notation "n0 ::== r0" := ((n0 : string)%string, (r0 : productions _)%productions) (at level 100) : production_assignment_scope.
    Notation "[[[ x ;; .. ;; y ]]]" :=
      (list_to_productions (nil::nil) (cons x%prod_assignment .. (cons y%prod_assignment nil) .. )) : productions_assignment_scope.

    Local Open Scope string_scope.
    Notation "<< x | .. | y >>" :=
      (@cons (production _) (x)%production .. (@cons (production _) (y)%production nil) .. ) : productions_scope.

    Notation "$< x $ .. $ y >$" := (cons (NonTerminal _ x) .. (cons (NonTerminal _ y) nil) .. ) : production_scope.

    Definition ab_star_grammar : grammar Ascii.ascii :=
      {| Top_name := "ab_star";
         Lookup := [[[ ("" ::== (<< "" >>)) ;;
                       ("ab" ::== << "ab" >>) ;;
                       ("ab_star" ::== << $< "" >$
                                        | $< "ab" $ "ab_star" >$ >> ) ]]]%prods_assignment |}.

    Definition make_parse_of : forall (str : string)
                                      (prods : productions Ascii.ascii),
                                 bool
      := @brute_force_make_parse_of ab_star_grammar (map (Lookup ab_star_grammar) (""::"ab"::"ab_star"::nil)%string).



    Definition parse : string -> bool
      := fun str => make_parse_of str ab_star_grammar.

    Time Compute parse "".
    Check eq_refl : parse "" = true.
    Time Compute parse "a".
    Check eq_refl : parse "a" = false.
    Time Compute parse "ab".
    Check eq_refl : parse "ab" = true.
    Time Compute parse "aa".
    Check eq_refl : parse "aa" = false.
    Time Compute parse "ba".
    Check eq_refl : parse "ba" = false.
    Time Compute parse "aba".
    Check eq_refl : parse "aba" = false.
    Time Compute parse "abab".
    Time Compute parse "ababab".
    Check eq_refl : parse "abab" = true.
  (* For debugging: *)(*
  Goal True.
    pose proof (eq_refl (parse "abab")) as s.
    unfold parse in s.
    unfold make_parse_of in s.
    unfold brute_force_make_parse_of in s.
    cbv beta zeta delta [parse_productions] in s.
    cbv beta zeta delta [parse_productions_or_abort] in s.
    rewrite Init.Wf.Fix_eq in s.
    Ltac do_compute_in c H :=
      let c' := (eval compute in c) in
      change c with c' in H.
    do_compute_in (lt_dec (Length string_stringlike "abab"%string) (Length string_stringlike "abab"%string)) s.
    change (if in_right then ?x else ?y) with y in s.
    cbv beta zeta delta [rdp_list_is_valid_productions] in s.
                       *)
  End ab_star.
End examples.

    Lemma
