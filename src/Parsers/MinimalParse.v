(** * Definition of minimal parse trees *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid.
Require Import Parsers.ContextFreeGrammar.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (names_listT : Type)
          (initial_names_data : names_listT)
          (is_valid_name : names_listT -> string -> bool)
          (remove_name : names_listT -> string -> names_listT)
          (names_listT_R : names_listT -> names_listT -> Prop)
          (remove_name_dec : forall ls name,
                               is_valid_name ls name = true
                               -> names_listT_R (remove_name ls name) ls)
          (remove_name_1
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = true
               -> is_valid_name ls ps' = true)
          (remove_name_2
           : forall ls ps ps',
               is_valid_name (remove_name ls ps) ps' = false
               <-> is_valid_name ls ps' = false \/ ps = ps')
          (ntl_wf : well_founded names_listT_R).

  Definition sub_names_listT (x y : names_listT) : Prop
    := forall p, is_valid_name x p = true -> is_valid_name y p = true.

  Context (names_listT_R_respectful : forall x y,
                                        sub_names_listT x y
                                        -> x <> y
                                        -> names_listT_R x y).

  Lemma remove_name_3
        ls ps ps' (H : is_valid_name ls ps = false)
  : is_valid_name (remove_name ls ps) ps' = is_valid_name ls ps'.
  Proof.
    case_eq (is_valid_name (remove_name ls ps) ps');
    case_eq (is_valid_name ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_name_1 in H''
          | apply remove_name_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Lemma remove_name_4
        ls ps ps' (H : is_valid_name (remove_name ls ps) ps' = true)
  : ps <> ps'.
  Proof.
    intro H'.
    pose proof (proj2 (remove_name_2 ls _ _) (or_intror H')).
    congruence.
  Qed.

  Lemma remove_name_5
        ls ps ps' (H : ps <> ps')
  : is_valid_name (remove_name ls ps) ps' = is_valid_name ls ps'.
  Proof.
    case_eq (is_valid_name (remove_name ls ps) ps');
    case_eq (is_valid_name ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_name_1 in H''
          | apply remove_name_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Lemma remove_name_6
        ls ps
  : is_valid_name (remove_name ls ps) ps = false.
  Proof.
    apply remove_name_2; right; reflexivity.
  Qed.

  (** The [names_listT] is the current list of valid names to compare
      against; the extra [String] argument to some of these is the
      [String] we're using to do well-founded recursion, which the
      current [String] must be no longer than. *)
  Inductive minimal_parse_of
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      productions CharType -> Type :=
  | MinParseHead : forall str0 valid str pat pats,
                     @minimal_parse_of_production str0 valid str pat
                     -> @minimal_parse_of str0 valid str (pat::pats)
  | MinParseTail : forall str0 valid str pat pats,
                     @minimal_parse_of str0 valid str pats
                     -> @minimal_parse_of str0 valid str (pat::pats)
  with minimal_parse_of_production
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      production CharType -> Type :=
  | MinParseProductionNil : forall str0 valid,
                              @minimal_parse_of_production str0 valid (Empty _) nil
  | MinParseProductionCons : forall str0 valid str strs pat pats,
                               str ++ strs ≤s str0
                               -> @minimal_parse_of_item str0 valid str pat
                               -> @minimal_parse_of_production str0 valid strs pats
                               -> @minimal_parse_of_production str0 valid (str ++ strs) (pat::pats)
  with minimal_parse_of_item
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      item CharType -> Type :=
  | MinParseTerminal : forall str0 valid x,
                         @minimal_parse_of_item str0 valid [[ x ]]%string_like (Terminal x)
  | MinParseNonTerminal
    : forall str0 valid str name,
        @minimal_parse_of_name str0 valid str name
        -> @minimal_parse_of_item str0 valid str (NonTerminal CharType name)
  with minimal_parse_of_name
  : forall (str0 : String) (valid : names_listT)
           (str : String),
      string -> Type :=
  | MinParseNonTerminalStrLt
    : forall str0 valid name str,
        Length str < Length str0
        -> @minimal_parse_of str initial_names_data str (Lookup G name)
        -> @minimal_parse_of_name str0 valid str name
  | MinParseNonTerminalStrEq
    : forall str valid name,
        is_valid_name valid name = true
        -> @minimal_parse_of str (remove_name valid name) str (Lookup G name)
        -> @minimal_parse_of_name str valid str name.

  Global Instance sub_names_listT_Reflexive : Reflexive sub_names_listT
    := fun x y f => f.

  Global Instance sub_names_listT_Transitive : Transitive sub_names_listT.
  Proof.
    lazy; auto.
  Defined.

  Global Add Parametric Morphism : remove_name
  with signature sub_names_listT ==> eq ==> sub_names_listT
    as remove_name_mor.
  Proof.
    intros x y H z w H'.
    hnf in H.
    pose proof (remove_name_4 H').
    apply remove_name_1 in H'.
    rewrite remove_name_5 by assumption.
    auto.
  Qed.

  Lemma sub_names_listT_remove ls ps
  : sub_names_listT (remove_name ls ps) ls.
  Proof.
    intros p.
    apply remove_name_1.
  Qed.

  Lemma sub_names_listT_remove_2 ls ls' ps (H : sub_names_listT ls ls')
  : sub_names_listT (remove_name ls ps) ls'.
  Proof.
    etransitivity; eauto using sub_names_listT_remove.
  Qed.

  Lemma sub_names_listT_remove_3 ls ls' p
        (H0 : is_valid_name ls p = false)
        (H1 : sub_names_listT ls ls')
  : sub_names_listT ls (remove_name ls' p).
  Proof.
    intros p' H'.
    rewrite remove_name_5; intuition (subst; eauto; congruence).
  Qed.
End cfg.
