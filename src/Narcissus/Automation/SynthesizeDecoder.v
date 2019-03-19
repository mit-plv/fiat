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
        Fiat.Narcissus.Formats.ByteBuffer
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
    solve [intuition eauto 3 with data_inv_hints]
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

(* Redefine this tactic to implement new base rules*)
Ltac apply_new_base_rule := fail.

(* Apply rules for *)
Ltac apply_base_rule :=
  match goal with

  (* Word *)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ _ format_word _ _ _] =>
    intros; eapply (Word_decode_correct H)

  (* Natural Numbers *)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ _ (format_nat _) _ _ _] =>
    intros; revert H; eapply Nat_decode_correct

  (* Booleans *)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ _ (format_bool) _ _ _] =>
    intros; revert H; eapply bool_decode_correct

  (* Strings *)
  | H : cache_inv_Property _ _
  |- context[CorrectDecoder _ _ _ _ StringOpt.format_string _ _ _ ] =>
    eapply StringOpt.String_decode_correct

  (* Enumerated Types *)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _  _ _ _ (format_enum ?tb) _ _ _] =>
    intros;
    eapply (fun NoDup => @Enum_decode_correct _ _ _ _ _ _ _ tb NoDup _ H);
    solve_side_condition

  (* Unused words *)
  | |- context [CorrectDecoder _  _ _ _ (format_unused_word _) _ _ _] =>
    intros; eapply unused_word_decode_correct; eauto

  (* ByteBuffers *)
  | H : cache_inv_Property ?mnd _
    |- CorrectDecoder _ _ _ _ format_bytebuffer _ _ _ =>
    intros; eapply @ByteBuffer_decode_correct;
    first [exact H | solve [intros; intuition eauto] ]

  (* Hook for new base rules. *)
  | |- _ => apply_new_base_rule
  end.

(* Redefine this tactic to implement new combinator rules*)
Ltac apply_new_combinator_rule := fail.

(* The rules for higher-order types (lists, sums, sequences. *)

Ltac apply_combinator_rule'
     option_fail_Some_format

     sequence_fail_first_format
     sequence_fail_invariant

     union_on_fail_first_format
     union_on_fail_second_format
     union_on_fail_first_check

     apply_rules :=
  first [
  match goal with

  (* Options *)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder _ _ _ _ (Option.format_option _ _) _ _ _] =>
    intros;
    sequence_two_tactics
      ltac:(eapply (Option.option_format_correct _ H))
      ltac:(apply_rules)
      ltac:(apply_rules)
      option_fail_Some_format

    (* Vector *)
  | H : cache_inv_Property _ _
    |- context [CorrectDecoder ?mnd _ _ _ (format_Vector _) _ _ _] =>
    intros; eapply (@Vector_decode_correct _ _ _ mnd);
    apply_rules

  | |- context [CorrectDecoder _ _ _ _ (format_list _) _ _ _] =>
    intros; apply FixList_decode_correct;
    apply_rules

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
                   (fun T : Type => B -> @CacheDecode cache -> option (T * B * @CacheDecode cache)) types'
         ltac:(fun decoders' =>
                 ilist_of_evar
                   (fun T : Type => Ensembles.Ensemble T) types'
         ltac:(fun invariants' =>
                 ilist_of_evar
                   (fun T : Type => T -> B -> Prop) types'
         ltac:(fun invariants_rest' =>
                 Vector_of_evar n (Ensembles.Ensemble (CacheDecode -> Prop))
         ltac:(fun cache_invariants' =>
                 eapply (SumType_decode_correct (m := n) types) with
                   (formatrs := formatrs')
                   (decoders := decoders')
                   (invariants := invariants')
                   (invariants_rest := invariants_rest')
                   (cache_invariants :=  cache_invariants')
              ))))); apply_rules
      | ilist_of_evar
          (fun T : Type => T -> @CacheFormat cache -> Comp (B * @CacheFormat cache)) types
          ltac:(fun formatrs' =>
                  ilist_of_evar
                    (fun T : Type => B -> @CacheDecode cache -> option (T * B * @CacheDecode cache)) types
                   ltac:(fun decoders' =>
                           ilist_of_evar
                             (fun T : Type => Ensembles.Ensemble T) types
                   ltac:(fun invariants' =>
                           ilist_of_evar
                             (fun T : Type => T -> B -> Prop) types
                   ltac:(fun invariants_rest' =>
                           Vector_of_evar n
                              (Ensembles.Ensemble (CacheDecode -> Prop))
                   ltac:(fun cache_invariants' =>
                           eapply (SumType_decode_correct (m := n) types) with
                             (formatrs := formatrs')
                             (decoders := decoders')
                             (invariants := invariants')
                             (invariants_rest := invariants_rest')
                             (cache_invariants :=  cache_invariants'))))))
      ];
    [ simpl; repeat (apply IterateBoundedIndex.Build_prim_and; intros); try exact I;
      apply_rules
    | apply cache_inv_H ]
  end
    | match goal with
(* Or applying one of our sequencing rules *)
  | H : cache_inv_Property ?P ?P_inv
    |- CorrectDecoder ?mnd _ _ _ (_ ◦ _ ++ _)%format _ _ _ =>
    first [
        sequence_three_tactics
          ltac:(eapply (format_sequence_correct H) with (monoid := mnd))
          ltac:(clear H; intros; apply_rules)
          ltac:(clear H; solve [ solve_side_condition ])
          ltac:(clear H; intros; apply_rules)
          sequence_fail_first_format
          sequence_fail_invariant
      ]

  | H : cache_inv_Property ?P ?P_inv
    |- CorrectDecoder ?mnd _ _ _ (_ ++ _)%format _ _ _ =>
    sequence_three_tactics
      ltac:(eapply (format_unused_sequence_correct H) with (monoid := mnd))
          ltac:(clear H; intros; apply_rules)
          ltac:(clear H; solve [ solve_side_condition ])
          ltac:(clear H; intros; apply_rules)
          sequence_fail_first_format
          sequence_fail_invariant

  | H : cache_inv_Property ?mnd _
    |- CorrectRefinedDecoder _ _ _ _ (_ ++ _)%format _ _ _ _ =>
    eapply format_sequence_refined_correct;
           [ apply H
           | clear H; intros; solve [ apply_rules ]
           | clear H; solve [solve_side_condition ]
           | clear H; intros; solve [ apply_rules]  ]

  | H : cache_inv_Property ?mnd _
    |- CorrectDecoder _ _ _ _ (Either ?fmt1 Or ?format2) _ _ _ =>
    sequence_four_tactics
      ltac:(eapply composeIf_format_correct')
      ltac:(apply H; intros)
      ltac:(intros; apply_rules)
      ltac:(intros; apply_rules)
      ltac:(intros; apply_rules)
             union_on_fail_first_format
             union_on_fail_second_format
             union_on_fail_first_check

      end
    | match goal with
  (* Here is the hook for new decoder rules *)
  | |- _ => apply_new_combinator_rule

      end].

Ltac apply_combinator_rule apply_rules :=
  apply_combinator_rule'
    continue_on_fail

    halt_on_fail_1
    halt_on_fail

    continue_on_fail_2
    continue_on_fail_1
    halt_on_fail

    apply_rules.
