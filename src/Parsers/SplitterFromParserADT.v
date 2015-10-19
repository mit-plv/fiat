(*Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import Fiat.ADTNotation.BuildADT Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.ADTRefinement.GeneralRefinements.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.ContextFreeGrammarTransfer.
Require Import Fiat.Parsers.ContextFreeGrammarTransferProperties.
Require Import Fiat.ADTRefinement.Core.
Require Import Fiat.Common Fiat.Common.Equality.
Require Import Fiat.Common.BoundedLookup.
Require Import Fiat.Common.IterateBoundedIndex.
Require Import Fiat.ADTNotation.BuildComputationalADT.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.
Section parser.
  Context (G : grammar Ascii.ascii).
  Context (splitter_impl : FullySharpened (string_spec G)).

  (* Lemma fst_cMethods_ex {method} *)
  (*       (st : { r : cRep (projT1 splitter_impl) | exists orig, AbsR (projT2 splitter_impl) orig r }) *)
  (*   : *)
  (*     @Lift_cMethodP _ _ _ *)
  (*                    (fun _ cMeth => *)
  (*                       exists orig, AbsR (projT2 splitter_impl) orig (fst cMeth)) *)
  (*                    (fun cMeth => *)
  (*                       exists orig, AbsR (projT2 splitter_impl) orig cMeth) *)
  (*                    (cMethods (projT1 splitter_impl) method (proj1_sig st)). *)
  (* Proof. *)
  (*   destruct st as [st [ orig H ] ]. *)
  (*   generalize  (ADTRefinementPreservesMethods (projT2 splitter_impl) method _ _ H). *)
  (*   revert st orig H; pattern method. *)
  (*   eapply (Lookup_Iterate_Dep_Type); repeat split; simpl; intros. *)
  (*   abstract (intros; specialize (H0 _ (ReturnComputes _)); computes_to_inv; *)
  (*             eexists; substs; simpl in *; rewrite <- H0''; eassumption). *)
  (*   abstract (intros; specialize (H0 t _ (ReturnComputes _)); computes_to_inv; *)
  (*             eexists; substs; simpl in *; rewrite <- H0''; eassumption). *)
  (*   abstract (intros; specialize (H0 t _ (ReturnComputes _)); computes_to_inv; *)
  (*             eexists; substs; simpl in *; rewrite <- H0''; eassumption). *)
  (*   abstract (intros; specialize (H0 _ (ReturnComputes _)); computes_to_inv; *)
  (*             eexists; substs; simpl in *; rewrite <- H0''; eassumption). *)
  (*   abstract (intros; specialize (H0 t _ (ReturnComputes _)); computes_to_inv; *)
  (*             eexists; substs; eassumption). *)
  (*   abstract (intros; specialize (H0 t _ (ReturnComputes _)); computes_to_inv; *)
  (*             eexists; substs; eassumption). *)
  (*   abstract (intros; specialize (H0 t t0 _ (ReturnComputes _)); computes_to_inv; *)
  (*             eexists; substs; simpl in *; rewrite <- H0''; eassumption). *)
  (* Qed. *)

  (* Lemma fst_cMethods_comp {method st arg v retv} *)
  (*       (H0 : Methods (string_spec G) method v arg = ret retv) *)
  (*       (H1 : AbsR (projT2 splitter_impl) v st) *)
  (* : AbsR (projT2 splitter_impl) (fst retv) (fst (cMethods (projT1 splitter_impl) method st arg)). *)
  (* Proof. *)
  (*   pose proof (ADTRefinementPreservesMethods (projT2 splitter_impl) method _ _ arg H1 (cMethods (projT1 splitter_impl) method st arg) (ReturnComputes _)) as H''. *)
  (*   rewrite H0 in H''; clear H0. *)
  (*   computes_to_inv. *)
  (*   match goal with *)
  (*     | [ H : (_, _) = _ |- _ ] *)
  (*       => pose proof (f_equal (@fst _ _) H); *)
  (*         pose proof (f_equal (@snd _ _) H); *)
  (*         clear H *)
  (*   end. *)
  (*   subst. *)
  (*   destruct_head' prod. *)
  (*   simpl @fst in *. *)
  (*   simpl @snd in *. *)
  (*   subst. *)
  (*   assumption. *)
  (* Qed. *)

  (* Lemma snd_cMethods_comp {method st arg v retv} *)
  (*       (H0 : Methods (string_spec G) method v arg = ret retv) *)
  (*       (H1 : AbsR (projT2 splitter_impl) v st) *)
  (* : snd (cMethods (projT1 splitter_impl) method st arg) = snd retv. *)
  (* Proof. *)
  (*   pose proof (ADTRefinementPreservesMethods (projT2 splitter_impl) method _ _ arg H1 (cMethods (projT1 splitter_impl) method st arg) (ReturnComputes _)) as H''. *)
  (*   rewrite H0 in H''; clear H0. *)
  (*   computes_to_inv. *)
  (*   match goal with *)
  (*     | [ H : (_, _) = _ |- _ ] *)
  (*       => pose proof (f_equal (@fst _ _) H); *)
  (*         pose proof (f_equal (@snd _ _) H); *)
  (*         clear H *)
  (*   end. *)
  (*   subst. *)
  (*   destruct_head' prod. *)
  (*   simpl @fst in *. *)
  (*   simpl @snd in *. *)
  (*   subst. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Local Ltac snd_cMethods_comp' := *)
  (*   idtac; *)
  (*   match goal with *)
  (*     | [ |- appcontext G[snd (cMethods ?impl ?meth ?st ?arg)] ] *)
  (*       => let G' := context G[snd (cMethods impl meth st arg)] in *)
  (*          progress change G' *)
  (*     | [ H : appcontext G[snd (cMethods ?impl ?meth ?st ?arg)] |- _ ] *)
  (*       => let G' := context G[snd (cMethods impl meth st arg)] in *)
  (*          progress change G' in H *)
  (*     | [ H : appcontext G[snd (cMethods ?impl ?meth ?st ?arg)] |- _ ] *)
  (*       => erewrite (@snd_cMethods_comp meth st arg) in H by (eassumption || reflexivity); *)
  (*         simpl @snd in H *)
  (*     | [ |- appcontext G[snd (cMethods ?impl ?meth ?st ?arg)] ] *)
  (*       => erewrite (@snd_cMethods_comp meth st arg) by (eassumption || reflexivity); *)
  (*         simpl @snd *)
  (*   end. *)
  (* Local Ltac snd_cMethods_comp := repeat snd_cMethods_comp'. *)

  Local Notation StringT := { r : cRep (projT1 splitter_impl) | exists orig, AbsR (projT2 splitter_impl) orig r }%type (only parsing).
  Local Notation StringT_lite := (cRep (projT1 splitter_impl)) (only parsing).

  Local Notation mcall0 proj s := (fun st => proj (callcADTMethod (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                                                                    (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) s _ ) st)) (only parsing).

  Local Notation mcall1 proj s := (fun n st => proj (callcADTMethod (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                                                  (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) s _ ) st n)) (only parsing).

  Local Notation mcall2 proj s := (fun n n' st => proj (callcADTMethod (projT1 splitter_impl) (fun idx => ibound (indexb idx))
                                                  (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) s _ ) st n n')) (only parsing).

  Local Notation mcall01 s := (mcall0 (fun x => x) s) (only parsing).
  Local Notation mcall02 s := (mcall0 snd s) (only parsing).
  Local Notation mcall11 s := (mcall1 (fun x => x) s) (only parsing).
  Local Notation mcall12 s := (mcall1 snd s) (only parsing).
  Local Notation mcall21 s := (mcall2 (fun x => x) s) (only parsing).
  Local Notation mcall22 s := (mcall2 snd s) (only parsing).
  
  Definition mto_string := Eval simpl in mcall02 "to_string".
  Definition mis_char := Eval simpl in mcall12 "is_char".
  Definition mget := Eval simpl in mcall12 "get".
  Definition mlength := Eval simpl in mcall02 "length".
  Definition mtake := Eval simpl in mcall11 "take".
  Definition mdrop := Eval simpl in mcall11 "drop".
  
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

  Definition to_strings := ibound (indexb (@Build_BoundedIndex _ _ (MethodNames (string_rep Ascii.ascii)) "to_string" _ )).

  Ltac prove_string_eq :=
    match goal with
      |- ?z _ = _ => unfold z;
        match goal with
          H : ?str ≃ ?st
          |- snd (callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st) = _ =>
          destruct (cMethods_AbsR splitter_impl (proj idx) _ _ H) as [? [? ?]]; simpl in *;
          computes_to_inv; injections; eauto
        end
    | |- ?z _ _ = _ => unfold z;
        match goal with
          H : ?str ≃ ?st
          |- snd (callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st ?arg1) = _ =>
          destruct (cMethods_AbsR splitter_impl (proj idx) _ _ H arg1) as [? [? ?]]; simpl in *;
          computes_to_inv; injections; eauto
        end
    | |- ?z _ _ = _ => unfold z;
        match goal with
          H : ?str ≃ ?st
          |- snd (callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st ?arg1 ?arg2) = _ =>
          destruct (cMethods_AbsR splitter_impl (proj idx) _ _ H arg1 arg2) as [? [? ?]]; simpl in *;
          computes_to_inv; injections; eauto
        end
    end.
  
  Definition mto_string_eq {st str} (H : AbsR (projT2 splitter_impl) str st)
    : mto_string st = str.
  Proof. prove_string_eq.  Qed.
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
      |- _ ≃ ?z _ _ => unfold z;
        match goal with
          H : ?str ≃ ?st
          |- _ ≃ callcADTMethod (projT1 ?splitter_impl) ?proj ?idx ?st ?arg =>
          destruct (cMethods_AbsR splitter_impl (proj idx) _ _ H arg) as [? [? ?]];
            simpl in *; computes_to_inv; subst; eauto
        end
    end.
  
  Definition mtake_R {arg st str} (H : AbsR (projT2 splitter_impl) str st)
  : AbsR (projT2 splitter_impl) (take arg str) (mtake arg st).
  Proof. prove_string_AbsR. Qed.
    
  Definition mdrop_R {arg st str} (H : AbsR (projT2 splitter_impl) str st)
  : AbsR (projT2 splitter_impl) (drop arg str) (mdrop arg st).
  Proof. prove_string_AbsR. Qed.

  Local Ltac handle_rep0 :=
    repeat intro; cbv beta;
    repeat match goal with
           | [ st : { r : cRep (projT1 splitter_impl) | exists orig, AbsR (projT2 splitter_impl) orig r }%type |- exists orig, AbsR (projT2 splitter_impl) orig (cMethods ?impl _ _ ?arg) ]
             => let H := fresh in
                destruct st as [? [? H] ];
                  eexists; first [eapply (mtake_R H)
                                 | eapply (mdrop_R H) ]
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _ _ _ _)  ]
             => unfold f, callcADTMethod
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _ _ _)  ]
             => unfold f, callcADTMethod
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _ _)  ]
             => unfold f, callcADTMethod
           | [ |- exists orig, AbsR (projT2 splitter_impl) orig (?f _)  ]
             => unfold f, callcADTMethod
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

  Local Program Instance adt_based_StringLike : StringLike Ascii.ascii
    := { String := StringT;
         take n str := mtake n str;
         drop n str := mdrop n str;
         length str := mlength str;
         is_char str ch := mis_char ch str;
         get n str := mget n str;
         bool_eq s1 s2 := string_beq (mto_string s1) (mto_string s2) }.
    
  Create HintDb parser_adt_method_db discriminated.
  (** We would like to just do
<<
  Hint Resolve @mtake_R @mdrop_R : parser_adt_method_db.
>>

  But [Hint Resolve] only resolves on the head symbol, so this will
  try to unify [mtake] with [mdrop], which is slow.  We have a choice:
  either we can make them [Opaque], or we can use an explicit [Hint
  Extern] for matching.  The latter is about 3x faster (0.015s vs
  0.047s), so we use that one, rather than
<<
  Hint Resolve @mtake_R @mdrop_R : parser_adt_method_db.
  Local Opaque mtake mdrop.
>>
   *)
  Hint Extern 1 (_ ≃ mtake _ _) => apply @mtake_R : parser_adt_method_db.
  Hint Extern 1 (_ ≃ mdrop _ _) => apply @mdrop_R : parser_adt_method_db.

  Local Ltac match_erewrite_by match_term lem tac :=
    idtac;
    match goal with
      | [ |- appcontext[match_term] ] => erewrite !lem by tac
      | [ H : appcontext[match_term] |- _ ] => erewrite !lem in H by tac
    end.

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
    unfold beq, bool_eq, adt_based_StringLike, proj1_sig, take, drop, is_char, length, get in *;
    repeat first [ match_erewrite_by_eauto (@mto_string) (@mto_string_eq)
                 | match_erewrite_by_eauto (@mis_char) (@mis_char_eq)
                 | match_erewrite_by_eauto (@mget) (@mget_eq)
                 | match_erewrite_by_eauto (@mlength) (@mlength_eq) ].

  Local Ltac t'' H meth :=
    pose proof (meth Ascii.ascii string_stringlike string_stringlike_properties) as H;
    simpl in H; unfold beq in H; simpl in H;
    unfold take, drop; simpl.
  Local Ltac t' meth :=
    let H := fresh in
    t'' H meth;
      eapply H; clear H; simpl.
  Local Ltac t meth := t' meth; eassumption.

  Local Obligation Tactic := handle_rep.

  Local Program Instance adt_based_StringLikeProperties : @StringLikeProperties Ascii.ascii adt_based_StringLike
    := { bool_eq_Equivalence := {| Equivalence_Reflexive := _ |} }.
  Next Obligation. handle_rep; t @singleton_unique. Qed.
  Next Obligation.
  Proof. handle_rep.
    let H := fresh in
    t'' H (@singleton_exists);
      edestruct H; try (eexists; erewrite mis_char_eq); intuition eauto.
  Qed.
  Next Obligation. handle_rep; t @get_0. Qed.
  Next Obligation. handle_rep; t @get_S. Qed.
  Next Obligation. handle_rep; t @length_singleton. Qed.
  Next Obligation. handle_rep; t @bool_eq_char. Qed.
  Next Obligation. handle_rep; t @is_char_Proper. Qed.
  Next Obligation. handle_rep; t @length_Proper. Qed.
  Next Obligation. handle_rep; t @take_Proper. Qed.
  Next Obligation. handle_rep; t @drop_Proper. Qed.
  Next Obligation. handle_rep; t @bool_eq_Equivalence. Qed.
  Next Obligation. handle_rep; t @bool_eq_Equivalence. Qed.
  Next Obligation. handle_rep; t (fun x y z => @Equivalence_Transitive _ _ (@bool_eq_Equivalence x y z)). Qed.
  Next Obligation. handle_rep; t @bool_eq_empty. Qed.
  Next Obligation. handle_rep; t @take_short_length. Qed.
  Next Obligation. handle_rep; t @take_long. Qed.
  Next Obligation. handle_rep; t @take_take. Qed.
  Next Obligation. handle_rep; t @drop_length. Qed.
  Next Obligation. handle_rep; t @drop_0. Qed.
  Next Obligation. handle_rep; t @drop_drop. Qed.
  Next Obligation. handle_rep; t @drop_take. Qed.
  Next Obligation. handle_rep; t @take_drop. Qed.

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
          H'' : production_is_reachable _ _,
          p0H : ContextFreeGrammarProperties.Forall_parse_of_item _ _,
          p1H : ContextFreeGrammarProperties.Forall_parse_of_production _ _
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
                             H0'' _ _ _ H1' p1)
                          (@transfer_forall_parse_of_item
                             Ascii.ascii adt_based_StringLike string_stringlike G
                             (fun s1 s2 => AbsR (projT2 splitter_impl) s2 (` s1))
                             H0'' _ _ _ _ H0' p0 p0H)
                          (@transfer_forall_parse_of_production
                             Ascii.ascii adt_based_StringLike string_stringlike G
                             (fun s1 s2 => AbsR (projT2 splitter_impl) s2 (` s1))
                             H0'' _ _ _ _ H1' p1 p1H));
          apply H; clear H p0H p1H p0 p1; try assumption; simpl
    end; [ split | | ];
    handle_rep;  eauto with parser_adt_method_db.
    exact (@mdrop_R n _ _ a).
  Qed.

  Definition adt_based_splitter : Splitter G
    := {| string_type := adt_based_StringLike;
          string_type_properties := adt_based_StringLikeProperties;
          splits_for str it its := msplits it its (` str);
          splits_for_complete := adt_based_splitter_splits_for_complete |}.
End parser.
