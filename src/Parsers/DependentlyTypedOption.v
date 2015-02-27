(** * Transform CFG parser into an optional one *)
Require Import Coq.Lists.List Coq.Program.Program Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar.
Require Import Parsers.StringLike.Properties.
Require Import Parsers.DependentlyTyped.
Require Import Common Common.Equality.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context {CharType : Type}
          {String : string_like CharType}
          {G : grammar CharType}.

  Context {predata : @parser_computational_types_dataT _ String}.
  Context {methods' : @parser_computational_dataT' _ String predata}.

  (** some helper lemmas to help Coq with inference *)
  Definition split_string_for_production_correct'
             H0 H1 str0 valid it its str st
    := @split_string_for_production_correct CharType String H0 H1 str0 valid it its {| string_val := str ; state_val := st |}.

  Hint Unfold compose : dtp_option_db.
  Hint Extern 1 => apply split_string_for_production_correct' : dtp_option_db.

  Local Ltac t_option' :=
    idtac;
    match goal with
      | _ => progress simpl
      | _ => progress intros
      | _ => progress destruct_head' @StringWithSplitState
      | _ => progress destruct_head' option
      | [ |- Forall _ (map _ _) ] => apply Forall_map
      | _ => progress autounfold with dtp_option_db in *
      | _ => progress simpl in *
      | _ => solve [ eauto with dtp_option_db ]
    end.

  Local Ltac t_option := repeat t_option'.

  Local Instance option_types_data : @parser_computational_types_dataT _ String
    := { split_stateT str0 valid g str := option (split_stateT str0 valid g str) }.

Set Printing Implicit.
  Local Instance option_methods' : @parser_computational_dataT' _ String option_types_data
    := { split_string_for_production str0 valid it its str
         := match state_val str with
              | None
                => nil
              | Some st
                => map
                     (fun s1s2 =>
                        (lift_StringWithSplitState (fst s1s2) (@Some _),
                         lift_StringWithSplitState (snd s1s2) (@Some _)))
                     (@split_string_for_production _ _ predata methods' str0 valid it its {| string_val := string_val str ; state_val := st |})
            end }.
  Proof. clear; abstract t_option. Defined.

  Local Instance option_methods : @parser_computational_dataT _ String
    := { methods' := option_methods' }.

  Local Notation orig_methods := {| DependentlyTyped.methods' := methods' |}.

  Context (prestrdata : @parser_computational_prestrdataT _ String G orig_methods option).

  Global Instance option_prestrdata : @parser_computational_prestrdataT _ String G option_methods idM
    := { prelower_nonterminal_name_state str0 valid nonterminal_name s
         := option_bind (@prelower_nonterminal_name_state _ _ _ _ _ prestrdata _ _ _ _);
         prelower_string_head str0 valid prod prods s
         := option_bind (@prelower_string_head _ _ _ _ _ prestrdata _ _ _ _ _);
         prelower_string_tail str0 valid prod prods s
         := option_bind (@prelower_string_tail _ _ _ _ _ prestrdata _ _ _ _ _);
         prelift_lookup_nonterminal_name_state_lt str0 valid nonterminal_name s pf
         := option_bind (@prelift_lookup_nonterminal_name_state_lt _ _ _ _ _ prestrdata _ _ _ _ pf);
         prelift_lookup_nonterminal_name_state_eq str0 valid nonterminal_name s pf
         := option_bind (@prelift_lookup_nonterminal_name_state_eq _ _ _ _ _ prestrdata _ _ _ _ pf) }.

  Global Instance option_strdata : @parser_computational_strdataT _ String G option_methods := option_prestrdata.

  Context (stypes' : @parser_dependent_types_success_dataT' _ String orig_methods).

  Definition option_rect_str {A} {B : StringWithSplitState String (fun s => option (A s)) -> Type}
             (f : forall x : StringWithSplitState String A, B (lift_StringWithSplitState x (@Some _)))
             (none_case : forall s, B {| string_val := s; state_val := None |})
             (x : StringWithSplitState String (fun s => option (A s)))
  : B x
    := match x return B x with
         | {| string_val := s ; state_val := None |} => none_case s
         | {| string_val := s ; state_val := Some st |}
           => f {| string_val := s ; state_val := st |}
       end.

  Global Instance option_stypes' : @parser_dependent_types_success_dataT' _ String option_methods
    := { T_nonterminal_name_success str0 valid name
         := option_rect_str (@T_nonterminal_name_success _ _ _ stypes' str0 valid name) (fun _ => True);
         T_item_success str0 valid it
         := option_rect_str (@T_item_success _ _ _ stypes' str0 valid it) (fun _ => True);
         T_production_success str0 valid prod
         := option_rect_str (@T_production_success _ _ _ stypes' str0 valid prod) (fun _ => True) ;
         T_productions_success str0 valid prods
         := option_rect_str (@T_productions_success _ _ _ stypes' str0 valid prods) (fun _ => True)  }.

  Definition option_stypes : @parser_dependent_types_success_dataT _ String
    := {| methods := option_methods;
          DependentlyTyped.stypes' := option_stypes' |}.

  Context (ftypes' : @parser_dependent_types_failure_dataT' _ String {| DependentlyTyped.stypes' := stypes' |}).

  Global Instance option_ftypes' : @parser_dependent_types_failure_dataT' _ String option_stypes
    := { T_nonterminal_name_failure str0 valid name
         := option_rect_str (@T_nonterminal_name_failure _ _ _ ftypes' str0 valid name) (fun _ => True);
         T_item_failure str0 valid it
         := option_rect_str (@T_item_failure _ _ _ ftypes' str0 valid it) (fun _ => True);
         T_production_failure str0 valid prod
         := option_rect_str (@T_production_failure _ _ _ ftypes' str0 valid prod) (fun _ => True) ;
         T_productions_failure str0 valid prods
         := option_rect_str (@T_productions_failure _ _ _ ftypes' str0 valid prods) (fun _ => True)  }.

  Definition option_types : @parser_dependent_types_dataT _ String
    := {| DependentlyTyped.stypes := option_stypes;
          DependentlyTyped.ftypes' := option_ftypes' |}.
(*
  Context (extra_success_data : @parser_dependent_types_extra_success_dataT' _ String G {| DependentlyTyped.stypes' := stypes' |} strdata).

  Local Notation eta s := {| string_val := string_val s ; state_val := state_val s |}.

  Lemma impossible_in_str {A B}
        {s0s1 : StringWithSplitState String (fun s => option (A s))
                * StringWithSplitState String (fun s => option (B s))}
        {ls : list (StringWithSplitState String A * StringWithSplitState String B)}
        (H : state_val (fst s0s1) = None \/ state_val (snd s0s1) = None)
  : ~(In
        s0s1
        (map (fun s1s2 =>
                (lift_StringWithSplitState (fst s1s2) Some,
                 lift_StringWithSplitState (snd s1s2) Some))
             ls)).
  Proof.
    intro H'.
    apply in_map_iff in H'.
    destruct H' as [? [H' _] ].
    destruct s0s1 as [ [? ?] [? ?] ]; simpl in *;
    destruct H; subst;
    [ apply (f_equal (@fst _ _)) in H'
    | apply (f_equal (@snd _ _)) in H' ];
    pose proof (state_val_path H') as H''; simpl in *;
    set (H''' := string_val_path H') in *;
    simpl in *; clearbody H'''; clear -H'' H''';
    destruct H''';
    simpl in *;
    congruence.
  Qed.

  Local Obligation Tactic :=
    try (simpl; intros;
         solve [ repeat intro; exact I
               | assumption
               | exfalso; eapply impossible_in_str; eauto; instantiate; eauto
               | apply Some_injective; assumption ]).

  Global Program Instance option_extra_success_data : @parser_dependent_types_extra_success_dataT' _ String G option_stypes option_strdata
    := { lift_success str0 valid nonterminal_name
         := option_rect_str (fun str => @lift_success _ _ _ _ _ extra_success_data _ _ _ (eta str)) _;
         parse_terminal_success str0 valid ch
         := option_rect_str (fun str => @parse_terminal_success _ _ _ _ _ extra_success_data _ _ _ (eta str)) _;
         parse_empty_success str0 valid
         := option_rect_str (fun str => @parse_empty_success _ _ _ _ _ extra_success_data _ _ (eta str)) _;
         cons_success str0 valid it its
         := option_rect_str
              (fun s1 =>
                 option_rect_str
                   (fun s2 =>
                      option_rect_str
                        (fun str pf H' H'' =>
                           @cons_success
                             _ _ _ _ _ extra_success_data _ _ _ _ (eta s1) (eta s2) (eta str) pf H'
                             (in_lift_pair_StringWithSplitState_iff_injective
                                (lift := fun _ => Some) (lift' := fun _ => Some)
                                _))
                        _)
                   (fun s2 => option_rect_str _ _))
              (fun s1 => option_rect_str
                           (fun s2 => option_rect_str _ _)
                           (fun s2 => option_rect_str _ _));
         lift_prods_success_head str0 valid prod prods
         := option_rect_str (fun str => @lift_prods_success_head _ _ _ _ _ extra_success_data _ _ _ _ (eta str)) _;
         lift_prods_success_tail str0 valid prod prods
         := option_rect_str (fun str => @lift_prods_success_tail _ _ _ _ _ extra_success_data _ _ _ _ (eta str)) _;
         lift_parse_nonterminal_name_success_lt str0 valid nonterminal_name
         := option_rect_str (fun str => @lift_parse_nonterminal_name_success_lt _ _ _ _ _ extra_success_data _ _ _ (eta str)) _;
         lift_parse_nonterminal_name_success_eq str0 valid nonterminal_name
         := option_rect_str (fun str => @lift_parse_nonterminal_name_success_eq _ _ _ _ _ extra_success_data _ _ _ (eta str)) _
       }.

  Context (extra_failure_data : @parser_dependent_types_extra_failure_dataT' _ String G {| DependentlyTyped.ftypes' := ftypes' |} strdata).

  Global Program Instance option_extra_failure_data : @parser_dependent_types_extra_failure_dataT' _ String G option_types option_strdata
    := { lift_failure str0 valid nonterminal_name
         := option_rect_str (fun str => @lift_failure _ _ _ _ _ extra_failure_data _ _ _ (eta str)) _;
         parse_terminal_failure str0 valid ch
         := option_rect_str (fun str => @parse_terminal_failure _ _ _ _ _ extra_failure_data _ _ _ (eta str)) _;
         parse_empty_failure str0 valid
         := option_rect_str (fun str => @parse_empty_failure _ _ _ _ _ extra_failure_data _ _ (eta str)) _;
         fail_parse_nil_productions str0 valid
         := option_rect_str (fun str => @fail_parse_nil_productions _ _ _ _ _ extra_failure_data _ _ (eta str)) _;
         lift_prods_failure str0 valid prod prods
         := option_rect_str (fun str => @lift_prods_failure _ _ _ _ _ extra_failure_data _ _ _ _ (eta str)) _;
         H_prod_split str0 valid it its
         := option_rect_str (fun str pf => (@H_prod_split _ _ _ _ _ extra_failure_data _ _ _ _ (eta str) pf)
                                             ∘ (fun H => eq_rect _ _ H _ _)) _;
         lift_parse_nonterminal_name_failure_lt str0 valid nonterminal_name
         := option_rect_str (fun str => @lift_parse_nonterminal_name_failure_lt _ _ _ _ _ extra_failure_data _ _ _ (eta str)) _;
         lift_parse_nonterminal_name_failure_eq str0 valid nonterminal_name
         := option_rect_str (fun str => @lift_parse_nonterminal_name_failure_eq _ _ _ _ _ extra_failure_data _ _ _ (eta str)) _;
         elim_parse_nonterminal_name_failure str0 valid nonterminal_name
         := option_rect_str (fun str => @elim_parse_nonterminal_name_failure _ _ _ _ _ extra_failure_data _ _ _ (eta str)) _
       }.
  Next Obligation.
  Proof.
    intros; simpl.
    rewrite map_map; apply map_ext; simpl.
    intros [ [? ?] [? ?] ]; reflexivity.
  Defined.

  Definition option_extra_data : @parser_dependent_types_extra_dataT _ String G
    := {| DependentlyTyped.types := option_types;
          DependentlyTyped.strdata := option_strdata;
          DependentlyTyped.extra_success_data := option_extra_success_data;
          DependentlyTyped.extra_failure_data := option_extra_failure_data |}.*)
End recursive_descent_parser.
