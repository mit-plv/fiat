(*Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import Fiat.ADTNotation.BuildADT Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.ADTRefinement.GeneralRefinements.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Transfer.
Require Import Fiat.Parsers.ContextFreeGrammar.TransferProperties.
Require Import Fiat.ADTRefinement.Core.
Require Import Fiat.Common Fiat.Common.Equality.
Require Import Fiat.Common.BoundedLookup.
Require Import Fiat.Common.IterateBoundedIndex.
Require Import Fiat.Common.StringOperations.
Require Import Fiat.Common.StringFacts.
Require Import Fiat.ADTNotation.BuildComputationalADT.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.
Section parser.
  Context (G : grammar Ascii.ascii).
  Context (splitter_impl : FullySharpened (string_spec G)).

  Local Notation StringT := { r : cRep (projT1 splitter_impl) | exists orig, AbsR (projT2 splitter_impl) orig r }%type (only parsing).
  Local Notation StringT_lite := (cRep (projT1 splitter_impl)) (only parsing).

  Local Notation mcall0 proj s := (fun st => proj (callcADTMethod (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                                                                    (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) s _ ) st)) (only parsing).

  Local Notation mcall1 proj s := (fun n st => proj (callcADTMethod (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                                                  (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) s _ ) st n)) (only parsing).

  Local Notation mcall2 proj s := (fun n n' st => proj (callcADTMethod (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                                                  (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) s _ ) st n n')) (only parsing).

  Local Notation ccall0 proj s :=
    (fun st => proj ((callcADTConstructor (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                                          (@Build_BoundedIndex _ _ (ConstructorNames (string_rep Ascii.ascii)) s _ )) st))
      (only parsing).

  Local Notation mcall01 s := (mcall0 (fun x => x) s) (only parsing).
  Local Notation mcall02 s := (mcall0 snd s) (only parsing).
  Local Notation mcall11 s := (mcall1 (fun x => x) s) (only parsing).
  Local Notation mcall12 s := (mcall1 snd s) (only parsing).
  Local Notation mcall21 s := (mcall2 (fun x => x) s) (only parsing).
  Local Notation mcall22 s := (mcall2 snd s) (only parsing).
  Local Notation ccall01 s := (ccall0 (fun x => x) s) (only parsing).

  Definition mto_string := Eval simpl in mcall02 "to_string".
  Definition mis_char := Eval simpl in mcall12 "is_char".
  Definition mget := Eval simpl in mcall12 "get".
  Definition mlength := Eval simpl in mcall02 "length".
  Definition mtake := Eval simpl in mcall11 "take".
  Definition mdrop := Eval simpl in mcall11 "drop".
  Definition cnew := Eval simpl in ccall01 "new".

  Definition premsplits :=
    Eval simpl in (callcADTMethod
                     (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                     (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) "splits" _ )).
  Definition msplits := Eval simpl in mcall22 "splits".

  (*Local Notation mcall1_R meth st arg str H :=
    (@fst_cMethods_comp (ibound (indexb (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) meth _ ))) st arg str _ eq_refl H)
      (only parsing).

  Local Notation mcall2_eq meth st arg str H :=
    (@snd_cMethods_comp (ibound (indexb (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) meth _ ))) st arg str _ eq_refl H)
      (only parsing). *)

  Local Ltac destruct_twice_faster term :=
    let H' := fresh in
    pose proof term as H';
      unfold ibound, indexb in H'; simpl Methods in *;
      hnf in H'; cbv beta in H'; destruct H' as [? H'];
      hnf in H'; cbv beta in H'; destruct H'.

  Local Ltac fix_string_of_list :=
    repeat match goal with
             | _ => progress change string_of_list with of_string in *
             | [ H : context[to_string (of_string ?x)] |- _ ] => rewrite to_of_string in H
             | [ H : context[of_string (to_string ?x)] |- _ ] => rewrite of_to_string in H
             | [ H : context[of_string (list_of_string ?x)] |- _ ] => simpl of_string in H; rewrite string_of_list_of_string in H
           end.

  Local Ltac fast_injections :=
    repeat match goal with
             | [ H : (?x, ?y) = (?x', ?y') |- _ ]
               => assert (x = x') by exact (f_equal fst H);
                 assert (y = y') by exact (f_equal snd H);
                 clear H
           end.

  Ltac prove_string_eq :=
    match goal with
      |- ?z _ = _ => unfold z;
        match goal with
          H : ?str ≃ ?st
          |- snd (callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st) = _ =>
          destruct_twice_faster (cMethods_AbsR splitter_impl (proj idx) _ _ H)
        end
    | |- ?z _ _ = _ => unfold z;
        match goal with
          H : ?str ≃ ?st
          |- snd (callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st ?arg1) = _ =>
          destruct_twice_faster (cMethods_AbsR splitter_impl (proj idx) _ _ H arg1)
        end
    | |- ?z _ _ = _ => unfold z;
        match goal with
          H : ?str ≃ ?st
          |- snd (callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st ?arg1 ?arg2) = _ =>
          destruct_twice_faster (cMethods_AbsR splitter_impl (proj idx) _ _ H arg1 arg2)
        end
    end;
    simpl Methods in *;
    computes_to_inv;
    fast_injections;
    fix_string_of_list;
    eauto.

  Definition mto_string_eq {st str} (H : AbsR (projT2 splitter_impl) str st)
    : mto_string st = str.
  Proof. prove_string_eq. Qed.
  Definition mis_char_eq {arg st str} (H : AbsR (projT2 splitter_impl) str st)
    : mis_char arg st = string_beq str (String.String arg "").
  Proof. prove_string_eq. Qed.
  Definition mget_eq {arg st str} (H : AbsR (projT2 splitter_impl) str st)
  : mget arg st = get arg str.
  Proof. prove_string_eq. Qed.
  Definition mlength_eq {st str} (H : AbsR (projT2 splitter_impl) str st)
    : mlength st = String.length str.
  Proof. prove_string_eq. Qed.

  Ltac prove_string_AbsR :=
    match goal with
      | [ |- _ ≃ ?z _ _ ] => unfold z
      | [ |- _ ≃ ?z _ ] => unfold z
    end;
    match goal with
      | [ H : ?str ≃ ?st
          |- _ ≃ callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st ?arg ]
        => destruct_twice_faster (cMethods_AbsR splitter_impl (proj idx) _ _ H arg)
      | [ |- _ ≃ callcADTConstructor (projT1 ?splitter_impl) ?proj ?idx ?arg ]
        => destruct_twice_faster (cConstructors_AbsR splitter_impl (proj idx) arg)
    end;
    simpl Methods in *; simpl Constructors in *;
    computes_to_inv;
    fix_string_of_list;
    subst;
    eauto.

  Definition mtake_R {arg st str} (H : AbsR (projT2 splitter_impl) str st)
  : AbsR (projT2 splitter_impl) (take arg str) (mtake arg st).
  Proof. prove_string_AbsR. Qed.

  Definition mdrop_R {arg st str} (H : AbsR (projT2 splitter_impl) str st)
  : AbsR (projT2 splitter_impl) (drop arg str) (mdrop arg st).
  Proof. prove_string_AbsR. Qed.

  Definition cnew_R {str}
  : AbsR (projT2 splitter_impl) str (cnew str).
  Proof. prove_string_AbsR. Qed.

  Local Ltac handle_rep0 :=
    repeat intro; cbv beta;
    repeat match goal with
           | [ st : { r : cRep (projT1 splitter_impl) | exists orig, AbsR (projT2 splitter_impl) orig r }%type |- exists orig, AbsR (projT2 splitter_impl) orig (cMethods ?impl _ _ ?arg) ]
             => let H := fresh in
                destruct st as [? [? H] ];
                  eexists; first [ eapply (mtake_R H)
                                 | eapply (mdrop_R H) ]
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (cConstructors ?impl _ ?arg) ]
             => eexists; eapply cnew_R
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _ _ _ _)  ]
             => unfold f, callcADTMethod, callcADTConstructor
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _ _ _)  ]
             => unfold f, callcADTMethod, callcADTConstructor
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _ _)  ]
             => unfold f, callcADTMethod, callcADTConstructor
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _)  ]
             => unfold f, callcADTMethod, callcADTConstructor
           end.

  Local Obligation Tactic := handle_rep0.

  Local Instance adt_based_StringLike_lite : StringLike Ascii.ascii
    := { String := StringT_lite;
         take n str := mtake n str;
         drop n str := mdrop n str;
         length str := mlength str;
         is_char str ch := mis_char ch str;
         get n str := mget n str;
         bool_eq s1 s2 := string_beq (mto_string s1) (mto_string s2) }.
  Local Instance adt_based_StringIso_lite : @StringIso Ascii.ascii adt_based_StringLike_lite
    := { of_string str := cnew (string_of_list str) }.

  Local Program Instance adt_based_StringLike : StringLike Ascii.ascii
    := { String := StringT;
         take n str := mtake n str;
         drop n str := mdrop n str;
         length str := mlength str;
         is_char str ch := mis_char ch str;
         get n str := mget n str;
         bool_eq s1 s2 := string_beq (mto_string s1) (mto_string s2) }.

  Local Program Instance adt_based_StringIso : @StringIso Ascii.ascii adt_based_StringLike
    := { of_string str := cnew (string_of_list str) }.

  Create HintDb parser_adt_method_db discriminated.
  (** We would like to just do
<<
  Hint Resolve @mtake_R @mdrop_R @cnew_R : parser_adt_method_db.
>>

  But [Hint Resolve] only resolves on the head symbol, so this will
  try to unify [mtake] with [mdrop], which is slow.  We have a choice:
  either we can make them [Opaque], or we can use an explicit [Hint
  Extern] for matching.  The latter is about 3x faster (0.015s vs
  0.047s), so we use that one, rather than
<<
  Hint Resolve @mtake_R @mdrop_R @cnew_R : parser_adt_method_db.
  Local Opaque mtake mdrop cnew.
>>
   *)
  Hint Extern 1 (_ ≃ mtake _ _) => apply @mtake_R : parser_adt_method_db.
  Hint Extern 1 (_ ≃ mdrop _ _) => apply @mdrop_R : parser_adt_method_db.
  Hint Extern 1 (_ ≃ cnew _) => apply @cnew_R : parser_adt_method_db.

  Local Ltac match_erewrite_by match_term lem tac :=
    idtac;
    (* work around bug https://coq.inria.fr/bugs/show_bug.cgi?id=4388 *)
    progress (
        try match goal with
              | [ |- appcontext[match_term] ] => erewrite !lem by tac
            end;
        try match goal with
              | [ H : appcontext[match_term] |- _ ] => erewrite !lem in H by tac
            end
      ).

  Local Ltac match_erewrite2_by match_term lem tac :=
    idtac;
    match goal with
      | [ |- context[match_term ?x ?y] ] => erewrite !lem by tac
      | [ H : context[match_term ?x ?y] |- _ ] => erewrite !lem in H by tac
    end.

  Local Ltac match_erewrite_by_eauto match_term lem :=
    match_erewrite_by match_term lem ltac:(eauto with nocore parser_adt_method_db).

  Local Ltac handle_rep :=
    repeat intro;
    destruct_head_hnf' sig;
    destruct_head_hnf' ex;
    unfold beq, bool_eq, adt_based_StringIso, adt_based_StringLike, proj1_sig, take, drop, is_char, length, get, of_string in *;
    repeat first [ match_erewrite_by_eauto (@mto_string) (@mto_string_eq)
                 | match_erewrite_by_eauto (@mis_char) (@mis_char_eq)
                 | match_erewrite_by_eauto (@mget) (@mget_eq)
                 | match_erewrite_by_eauto (@mlength) (@mlength_eq) ].

  Local Ltac t'' H meth :=
    first [ pose proof (meth Ascii.ascii string_stringlike string_stringlike_properties) as H
          | pose proof (meth Ascii.ascii string_stringlike string_stringiso string_stringiso_properties) as H ];
    simpl in H; unfold beq in H; simpl in H;
    unfold take, drop, of_string; simpl.
  Local Ltac t' meth :=
    let H := fresh in
    t'' H meth;
      eapply H; clear H; simpl.
  Local Ltac t meth := t' meth; eassumption.

  Local Obligation Tactic := handle_rep.

  Local Program Instance adt_based_StringLikeProperties : @StringLikeProperties Ascii.ascii adt_based_StringLike
    := { bool_eq_Equivalence := {| Equivalence_Reflexive := _ |} }.
  Next Obligation. t @singleton_unique. Qed.
  Next Obligation.
  Proof.
    let H := fresh in
    t'' H (@singleton_exists);
      edestruct H; try (eexists; erewrite mis_char_eq); intuition eauto.
  Qed.
  Next Obligation. t @get_0. Qed.
  Next Obligation. t @get_S. Qed.
  Next Obligation. t @length_singleton. Qed.
  Next Obligation. t @bool_eq_char. Qed.
  Next Obligation. t @is_char_Proper. Qed.
  Next Obligation. t @length_Proper. Qed.
  Next Obligation. t @take_Proper. Qed.
  Next Obligation. t @drop_Proper. Qed.
  Next Obligation. t @bool_eq_Equivalence. Qed.
  Next Obligation. t @bool_eq_Equivalence. Qed.
  Next Obligation. t (fun x y z => @Equivalence_Transitive _ _ (@bool_eq_Equivalence x y z)). Qed.
  Next Obligation. t @bool_eq_empty. Qed.
  Next Obligation. t @take_short_length. Qed.
  Next Obligation. t @take_long. Qed.
  Next Obligation. t @take_take. Qed.
  Next Obligation. t @drop_length. Qed.
  Next Obligation. t @drop_0. Qed.
  Next Obligation. t @drop_drop. Qed.
  Next Obligation. t @drop_take. Qed.
  Next Obligation. t @take_drop. Qed.
  Next Obligation.
  Proof.
    let H := fresh in
    t'' H (@bool_eq_from_get);
      apply H; intro; erewrite <- !mget_eq by eassumption; trivial.
  Qed.

  Local Program Instance adt_based_StringIsoProperties : @StringIsoProperties Ascii.ascii adt_based_StringLike _
    := { }.
  Next Obligation. t (@get_of_string). Qed.

  Definition splits :=
    ibound (indexb (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) "splits" _ )).

  Lemma adt_based_splitter_splits_for_complete
  : forall (str : String) (it : item Ascii.ascii)
           (its : production Ascii.ascii),
      split_list_is_complete G str it its (msplits it its (` str)).
  Proof.
    repeat intro.
    destruct_head_hnf' sig.
    destruct_head' ex.
    unfold length, take, drop, adt_based_StringLike, proj1_sig in *.
    (* if we use [match_erewrite_by], it picks up [mlength] inside of
    a [StringLike] type, under binders, and the rewrite fails
    (slowly). *)
    repeat match_erewrite_by (@mlength) (@mlength_eq) ltac:eassumption.
    match goal with
      | [ H : AbsR ?Ok ?str ?st
          |- appcontext[msplits ?arg1 ?arg2 ?st] ]
        => let T := type of Ok in
           let impl := (match eval cbv beta in T with refineADT _ (LiftcADT ?impl) => constr:impl end) in
           let H' := fresh in
           pose proof (ADTRefinementPreservesMethods Ok splits _ _ H arg1 arg2 ((cMethods impl splits st arg1 arg2)) (ReturnComputes _)) as H';
             change (msplits arg1 arg2 st) with (snd (premsplits st arg1 arg2));
             match type of H' with
               | appcontext G[cMethods _ splits ?st ?arg1 ?arg2]
                 => let G' := context G[premsplits st arg1 arg2] in
                    change G' in H'
             end
    end.
    simpl Methods in *.
    computes_to_inv; subst.
    simpl @fst in *. simpl @snd in *.
    match goal with
      | [ H : ?x = premsplits _ _ _ |- _ ] => rewrite <- H; clear H; simpl @snd
    end.
    lazymatch goal with
      | [ H : split_list_is_complete _ _ _ _ _, H' : ?n <= _,
          p0 : parse_of_item _ _ _, p1 : parse_of_production _ _ _,
          H'' : production_is_reachable _ _
          |- List.In ?n ?v ]
        => hnf in H;
          specialize (fun H0'' H0' H1' =>
                        H n H' H''
                          (@transfer_parse_of_item
                             Ascii.ascii adt_based_StringLike string_stringlike G
                             (fun s1 s2 => AbsR (projT2 splitter_impl) s2 (` s1))
                             H0'' _ _ _ H0' p0)
                          (@transfer_parse_of_production
                             Ascii.ascii adt_based_StringLike string_stringlike G
                             (fun s1 s2 => AbsR (projT2 splitter_impl) s2 (` s1))
                             H0'' _ _ _ H1' p1));
          apply H; clear H p0 p1; try assumption
    end; [ split | | ];
    handle_rep; eauto with parser_adt_method_db.
  Qed.

  Definition adt_based_splitter : Splitter G
    := {| string_type := adt_based_StringLike;
          string_type_properties := adt_based_StringLikeProperties;
          splits_for str it its := msplits it its (` str);
          splits_for_complete := adt_based_splitter_splits_for_complete |}.
End parser.
