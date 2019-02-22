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
        Fiat.Narcissus.Automation.Decision
        Fiat.Narcissus.Automation.Common
        Fiat.Narcissus.Automation.ExtractData.

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
