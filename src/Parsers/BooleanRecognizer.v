(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Omega.
Require Import Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Arith.Compare_dec Coq.Classes.RelationClasses Coq.Strings.String.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Common Common.ilist Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

(** TODO: move this elsewhere *)
Fixpoint combine_sig {T P} (ls : list T) : List.Forall P ls -> list (sig P).
Proof.
  refine match ls with
           | nil => fun _ => nil
           | x::xs => fun H => (exist _ x _)::@combine_sig _ _ xs _
         end;
  clear combine_sig;
  abstract (inversion H; subst; assumption).
Defined.

Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (productions_listT : Type)
          (initial_productions_data : productions_listT)
          (is_valid_productions : productions_listT -> productions CharType -> bool)
          (remove_productions : productions_listT -> productions CharType -> productions_listT)
          (productions_listT_R : productions_listT -> productions_listT -> Prop)
          (remove_productions_dec : forall ls prods, is_valid_productions ls prods = true
                                                     -> productions_listT_R (remove_productions ls prods) ls)
          (ntl_wf : well_founded productions_listT_R).

  Definition str_le (s1 s2 : String) := Length _ s1 < Length _ s2 \/ s1 = s2.
  Local Infix "≤s" := str_le (at level 70, right associativity).
  Section bool.
    Context (split_string_for_production
             : forall (str0 : String)
                      (prod : production CharType),
                 list (list String))
            (split_string_for_production_correct
             : forall str0 prod,
                 List.Forall (List.Forall (fun str => str ≤s str0)) (split_string_for_production str0 prod)).

    Section parts.
      Section item.
        Context (str : String)
                (str_matches_productions : productions CharType -> bool).

        Definition parse_item (it : item CharType) : bool
          := match it with
               | Terminal ch => [[ ch ]] =s str
               | NonTerminal name => str_matches_productions (Lookup G name)
             end.
      End item.

      Section production.
        Variable str0 : String.
        Variable parse_productions : forall (str : String),
                                       str ≤s str0
                                       -> productions CharType
                                       -> bool.

        (** To match a [production], we must match all of its items.
            If the lengths do match up, we don't define the outcome. *)
        Definition parse_production_from_split_list
                   (strs : list String)
                   (strs_correct : List.Forall (fun str => str ≤s str0) strs)
                   (prod : production CharType)
        : bool
          := fold_right andb
                        true
                        (map (fun sp => parse_item (proj1_sig (fst sp))
                                                   (parse_productions (proj2_sig (fst sp)))
                                                   (snd sp))
                             (combine (combine_sig strs_correct) prod)).

        (** To match a [production], any split of the string can match. *)
        Definition parse_production_from_any_split_list
                   (strs : list (list String))
                   (strs_correct : List.Forall (List.Forall (fun str => str ≤s str0)) strs)
                   (prod : production CharType)
        : bool
          := fold_right orb
                        false
                        (map (fun strs' => parse_production_from_split_list (proj2_sig strs') prod)
                             (combine_sig strs_correct)).

        Definition or_transitivity {A B} `{@Transitive B R} {f : A -> B} {a0 a}
                   (pf : R (f a) (f a0) \/ a = a0) a' (pf' : R (f a') (f a) \/ a' = a)
        : R (f a') (f a0) \/ a' = a0.
        Proof.
          destruct_head or; subst;
          first [ right; reflexivity | left; assumption | left; etransitivity; eassumption ].
        Qed.

        (** We assume the splits we are given are valid (are actually splits of the string, rather than an unrelated split) and are the same length as the given [production].  Behavior in other cases is undefined *)
        (** We match a production if any split of the string matches that production *)
        Definition parse_production
                   (str : String) (pf : str ≤s str0)
                   (prod : production CharType)
        : bool.
        Proof.
          refine (if (gt_dec (Datatypes.length prod) 0)
                  then (@parse_production_from_any_split_list
                          (@split_string_for_production str prod)
                          _
                          prod)
                  else (** 0-length production, only accept empty *)
                    (str =s Empty _)).
          specialize (split_string_for_production_correct str prod).
          revert split_string_for_production_correct.
          revert pf; clear; intro pf.
          abstract (
              repeat first [ apply Forall_impl
                           | eapply or_transitivity; eassumption
                           | intro ]
            ).
        Defined.
      End production.

      Section productions.
        Section step.
          Variable str0 : String.
          Variable parse_productions : forall (str : String)
                                              (pf : str ≤s str0),
                                         productions CharType -> bool.

          (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
          Definition parse_productions_step (str : String) (pf : str ≤s str0) (prods : productions CharType)
          : bool
            := fold_right orb
                          false
                          (map (parse_production parse_productions pf)
                               prods).
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_productions_or_abort_helper
          : forall (p : String * productions_listT) (str : String),
              str ≤s fst p ->
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
                     (pf : str ≤s str0)
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

(** TODO: move this elsewhere *)
Local Ltac str_le_append_t :=
  repeat match goal with
           | _ => intro
           | _ => progress subst
           | [ H : (_ =s _)%string_like = true |- _ ] => apply bool_eq_correct in H
           | _ => progress rewrite ?LeftId, ?RightId
           | _ => right; reflexivity
           | [ H : Length _ _ = 0 |- _ ] => apply Empty_Length in H
           | [ H : Length _ ?s <> 0 |- _ ] => destruct (Length _ s)
           | [ H : ?n <> ?n |- _ ] => destruct (H eq_refl)
           | [ |- ?x < ?x + S _ \/ _ ] => left; omega
           | [ |- ?x < S _ + ?x \/ _ ] => left; omega
         end.

Lemma str_le1_append CharType (String : string_like CharType) (s1 s2 : String)
: str_le _ s1 (s1 ++ s2)%string_like.
Proof.
  hnf.
  rewrite <- Length_correct.
  case_eq (bool_eq _ s2 (Empty _));
  destruct (NPeano.Nat.eq_dec (Length _ s2) 0);
  str_le_append_t.
Qed.

Lemma str_le2_append CharType (String : string_like CharType) (s1 s2 : String)
: str_le _ s2 (s1 ++ s2)%string_like.
Proof.
  hnf.
  rewrite <- Length_correct.
  case_eq (bool_eq _ s1 (Empty _));
  destruct (NPeano.Nat.eq_dec (Length _ s1) 0);
  str_le_append_t.
Qed.

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

  Local Hint Constructors List.Forall.

  Lemma Forall_app {T} P (ls1 ls2 : list T)
  : List.Forall P ls1 /\ List.Forall P ls2 <-> List.Forall P (ls1 ++ ls2).
  Proof.
    split.
    { intros [H1 H2].
      induction H1; simpl; auto. }
    { intro H; split; induction ls1; simpl in *; auto.
      { inversion_clear H; auto. }
      { inversion_clear H; auto. } }
  Qed.

  Lemma Forall_flatten1 {T ls P}
  : List.Forall P (@flatten1 T ls) <-> List.Forall (List.Forall P) ls.
  Proof.
    induction ls; simpl.
    { repeat first [ esplit | intro | constructor ]. }
    { etransitivity; [ symmetry; apply Forall_app | ].
      split_iff.
      split.
      { intros [? ?]; auto. }
      { intro H'; inversion_clear H'; split; auto. } }
  Qed.


  Lemma Forall_map {A B} {f : A -> B} {ls P}
  : List.Forall P (map f ls) <-> List.Forall (P ∘ f) ls.
  Proof.
    induction ls; simpl.
    { repeat first [ esplit | intro | constructor ]. }
    { split_iff.
      split;
        intro H'; inversion_clear H'; auto. }
  Qed.

  (*Local Ltac t' :=
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
    solve [ repeat t'' ].*)

  Local Hint Resolve NPeano.Nat.lt_lt_add_l NPeano.Nat.lt_lt_add_r NPeano.Nat.lt_add_pos_r NPeano.Nat.lt_add_pos_l : arith.
  Local Hint Resolve str_le1_append str_le2_append.

  Fixpoint brute_force_splitter_helper
           (prod : production Ascii.ascii)
  : string_stringlike
    -> list (list string_stringlike)
    := match prod with
         | nil => fun str =>
                    (** We only get one thing in the list *)
                    ((str::nil)::nil)
         | _::prod' => fun str =>
                         (flatten1
                            (map (fun s1s2p =>
                                    map
                                      (fun split_list => (fst (proj1_sig s1s2p))::split_list)
                                      (@brute_force_splitter_helper prod' (snd (proj1_sig s1s2p))))
                                 (make_all_single_splits str)))
       end.

  Definition brute_force_splitter
  : forall (str : string_stringlike) (prod : production Ascii.ascii),
      list (list string_stringlike)
    := fun str prods =>
         match prods with
           | nil => nil (** no patterns, no split (actually, we should never encounter this case *)
           | _::prods' => brute_force_splitter_helper prods' str
         end.

  Lemma brute_force_splitter_helper_correct
           (prod : production Ascii.ascii)
           (str : string_stringlike)
  : List.Forall (List.Forall (fun str_part => str_le _ str_part str)) (brute_force_splitter_helper prod str).
  Proof.
    revert str.
    induction prod; simpl; intro.
    { repeat first [ right; reflexivity | constructor ]. }
    { repeat match goal with
               | [ |- Forall _ (flatten1 _) ] => apply Forall_flatten1
               | [ |- Forall _ (map _ _) ] => apply Forall_map; unfold compose; simpl
               | [ |- Forall _ (make_all_single_splits _) ] => apply Forall_forall; intros
               | [ H : forall str : String string_stringlike, _ |- context[brute_force_splitter_helper _ ?str] ]
                 => specialize (H str)
               | [ H : Forall _ ?l |- Forall _ ?l ] => revert H; apply Forall_impl; intros
               | [ |- Forall _ (_ :: _) ] => constructor
               | _ => progress destruct_head sig
               | _ => progress subst
               | _ => solve [ eauto ]
               | _ => apply str_le1_append
               | _ => apply str_le2_append
               | [ H : str_le _ ?a _ |- str_le _ ?a _ ] => eapply or_transitivity; [ | exact H ]; clear H a
             end. }
  Qed.

  Lemma brute_force_splitter_correct
             (str : string_stringlike) (prod : production Ascii.ascii)
  : List.Forall (List.Forall (fun str_part => str_le _ str_part str)) (brute_force_splitter str prod).
  Proof.
    unfold brute_force_splitter.
    destruct prod; auto.
    apply brute_force_splitter_helper_correct.
  Qed.

  Variable G : grammar Ascii.ascii.
  Variable all_productions : list (productions Ascii.ascii).

  Definition brute_force_make_parse_of : @String Ascii.ascii string_stringlike
                                         -> productions Ascii.ascii
                                         -> bool
    := parse_productions
         G
         all_productions
         (rdp_list_is_valid_productions Ascii.ascii_dec)
         (rdp_list_remove_productions Ascii.ascii_dec)
         (rdp_list_remove_productions_dec Ascii.ascii_dec) rdp_list_ntl_wf
         brute_force_splitter
         brute_force_splitter_correct.
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
