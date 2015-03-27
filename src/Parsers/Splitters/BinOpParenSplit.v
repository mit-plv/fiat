(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String NPeano.
Require Import Parsers.ContextFreeGrammar.
Require Import Parsers.BaseTypes Parsers.BooleanBaseTypes.
Require Import Parsers.Splitters.RDPList.
Require Import Common.
Require Import Common.List.Operations Common.List.ListFacts Common.Equality.

Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Common.Wf.

Require Import Parsers.Splitters.Reflective.
Require Import Parsers.Splitters.OnlyOneNonterminal.

Require Import Parsers.MinimalParse.
Require Import Parsers.ContextFreeGrammarNotations.
Require Import Parsers.Grammars.ExpressionNumPlus.

Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.
Section StringT.
  Context {CharType} {String : string_like CharType}
          (is_bin_op : CharType -> bool)
          (is_open : CharType -> bool) (is_close : CharType -> bool).

  (** We build a table to tell us where to split.

      For each character, we store an [option nat], and keep a
      transient [list nat].

      For '(', we store where the corresponding ')' is.

      For ')', we store [None].

      For everything else, we store where the next '+' at the current
      level of parenthetization is.  We take advantage of
      associativity; once we cross a '(' ... ')' at the current level,
      we stop caring about where the next '+' is.

      The transient list stores where the corresponding ')' is for
      higher levels. *)

  Definition list_of_next_bin_ops_closes (s : String) (next_op__higher_closes : option nat * list nat)
  : list (option nat) * (option nat * list nat)
    := Fold
         String
         (fun _ => list (option nat) * (option nat * list nat))%type
         (nil, next_op__higher_closes)
         (fun ch _ table_op_higher_closes =>
            let '(table, (next_op, higher_closes))
                := (fst table_op_higher_closes,
                    (option_map S (fst (snd table_op_higher_closes)),
                     map S (snd (snd table_op_higher_closes)))) in
            let '(cur_mark, new_next_op, new_higher_closes)
                := (if is_bin_op ch
                    then (Some 0,
                          Some 0,
                          higher_closes)
                    else if is_close ch
                         then (None,
                               None,
                               0::higher_closes)
                         else if is_open ch
                              then ((hd None (map Some higher_closes)),
                                    None,
                                    tl higher_closes)
                              else (next_op,
                                    next_op,
                                    higher_closes)) in
            (cur_mark::table, (new_next_op, new_higher_closes)))
         s.

  Lemma list_of_next_bin_ops_closes_compute_empty {hc}
  : list_of_next_bin_ops_closes (Empty String) hc
    = (nil, hc).
  Proof.
    unfold list_of_next_bin_ops_closes.
    rewrite Fold_compute_empty; reflexivity.
  Qed.

  Lemma list_of_next_bin_ops_closes_compute_cons {ch s hc}
  : list_of_next_bin_ops_closes ([[ ch ]] ++ s) hc
    = (let table_op_higher_closes := list_of_next_bin_ops_closes s hc in
       let '(table, (next_op, higher_closes))
           := (fst table_op_higher_closes,
               (option_map S (fst (snd table_op_higher_closes)),
                map S (snd (snd table_op_higher_closes)))) in
       ((if is_bin_op ch
         then Some 0
         else if is_close ch
              then None
              else if is_open ch
                   then hd None (map Some higher_closes)
                   else next_op)
          ::table,
        ((if is_bin_op ch
          then Some 0
          else if is_close ch
               then None
               else if is_open ch
                    then None
                    else next_op),
         (if is_bin_op ch
          then higher_closes
          else if is_close ch
               then 0::higher_closes
               else if is_open ch
                    then tl higher_closes
                    else higher_closes)))).
  Proof.
    unfold list_of_next_bin_ops_closes; simpl.
    rewrite Fold_compute_cons; simpl.
    destruct (is_bin_op ch), (is_close ch), (is_open ch); simpl;
    reflexivity.
  Qed.

  Lemma list_of_next_bin_ops_closes_compute_append {s1 s2 hc}
  : list_of_next_bin_ops_closes (s1 ++ s2) hc
    = (let table_hc' := list_of_next_bin_ops_closes s2 hc in
       let '(table, hc') := (fst table_hc', snd table_hc') in
       ((fst (list_of_next_bin_ops_closes s1 hc') ++ table)%list,
        snd (list_of_next_bin_ops_closes s1 hc'))).
  Proof.
    simpl.
    revert s1 s2.
    match goal with
      | [ |- forall s, @?P s ]
        => refine (Fold _ P _ _)
    end.
    { intro s2.
      rewrite list_of_next_bin_ops_closes_compute_empty; simpl.
      rewrite LeftId.
      apply injective_projections; reflexivity. }
    { intros ch ? IHs s2.
      rewrite Associativity.
      rewrite !list_of_next_bin_ops_closes_compute_cons, !IHs; simpl.
      reflexivity. }
  Qed.

  Lemma length_fst_list_of_next_bin_ops_closes {s hc}
  : List.length (fst (list_of_next_bin_ops_closes s hc)) = Length s.
  Proof.
    revert s.
    apply Fold.
    { rewrite list_of_next_bin_ops_closes_compute_empty, Length_Empty; reflexivity. }
    { intros ? ? H; rewrite list_of_next_bin_ops_closes_compute_cons; simpl.
      rewrite <- Length_correct, Singleton_Length, H; reflexivity. }
  Qed.

  Let dec : forall a b : list (option nat), {a = b} + {a <> b}
    := list_eq_dec (option_dec Nat.eq_dec).

  Let dec_refl {x}
  : dec x x = left match dec x x with
                     | left pf => pf
                     | right _ => eq_refl
                   end.
  Proof.
    edestruct dec as [pf | n]; trivial.
    destruct (n eq_refl).
  Defined.

  Local Notation "x =? y" := (is_true (if dec x y then true else false)) (at level 70, right associativity).

  Let split_stateT := (fun s => { ls : list (option nat)
                                | exists hc, ls =? fst (list_of_next_bin_ops_closes s hc) }).
  Let String' : Type := String.
  Let StringT := (StringWithSplitState String split_stateT).

  Definition drop_split_stateT {s} (st : split_stateT s) : { ls : list (option nat) | inhabited _ }
    := exist
         _
         (proj1_sig st)
         (match proj2_sig st return inhabited _ with
            | ex_intro hc _ => inhabits hc
          end).

  (*Lemma split_stateT_eq {s} {st st' : split_stateT s} (H : drop_split_stateT st = drop_split_stateT st')
  : st = st'.
  Proof.
    unfold drop_split_stateT in *.
    destruct st as [ls [hc st] ], st' as [ls' [hc' st'] ]; simpl in *.
    generalize (proj2_sig_path H).
    generalize (proj1_sig_path H).
    simpl in *.
    clear H.
    intros H H'.
    destruct H; simpl in *.
    f_equal.
    unfold is_true in *.
    match goal with
      | [ H : ?x = true |- _ ] => generalize dependent
    match goal with
      | [ |- context[ex_intro ?P ?hc ?st]
    lazymatch goal with
      | [ H : context[if ?e then _ else _] |- _ ] => destruct e
    end.
    inversion H'.*)

  Definition StringT_of_string (s : String') : StringT.
  Proof.
    refine {| string_val := s ; state_val := exist _ (fst (list_of_next_bin_ops_closes s (None, nil))) (ex_intro _ (None, nil) _) |}.
    abstract (rewrite dec_refl; reflexivity).
  Defined.

  Lemma drop_list_of_next_bin_ops_closes {s n hc}
  : drop n (fst (list_of_next_bin_ops_closes s hc)) =
    fst (list_of_next_bin_ops_closes (snd (SplitAt n s)) hc).
  Proof.
    revert s n.
    match goal with
      | [ |- forall s, @?P s ]
        => refine (Fold _ P _ _)
    end.
    { intros.
      rewrite SplitAtEmpty; simpl.
      unfold list_of_next_bin_ops_closes; simpl.
      rewrite Fold_compute_empty; simpl.
      destruct n; reflexivity. }
    { intros ? ? H n.
      induction n; simpl.
      { rewrite SplitAt0; reflexivity. }
      { rewrite SplitAtS; simpl.
        rewrite <- H.
        rewrite list_of_next_bin_ops_closes_compute_cons; simpl; reflexivity. } }
  Qed.

  Lemma take_list_of_next_bin_ops_closes {s n hc}
  : take n (fst (list_of_next_bin_ops_closes s hc)) =
    fst
      (list_of_next_bin_ops_closes (fst (SplitAt n s))
                                   (snd (list_of_next_bin_ops_closes (snd (SplitAt n s)) hc))).
  Proof.
    rewrite <- (SplitAt_correct String n s) at 1.
    generalize (SplitAtLength_correct String n s).
    apply NPeano.Nat.min_case_strong.
    { intros H H'.
      rewrite SplitAtPastEnd by assumption; simpl.
      rewrite RightId.
      rewrite list_of_next_bin_ops_closes_compute_empty; simpl.
      rewrite take_all by (rewrite length_fst_list_of_next_bin_ops_closes; assumption).
      reflexivity. }
    { intros _.
      rewrite list_of_next_bin_ops_closes_compute_append; simpl.
      intro H.
      rewrite take_append; simpl.
      rewrite length_fst_list_of_next_bin_ops_closes, H, Minus.minus_diag; simpl.
      rewrite take_all by (rewrite length_fst_list_of_next_bin_ops_closes, H; reflexivity).
      rewrite app_nil_r; reflexivity. }
  Qed.

  Section SplitAtT.
    Context (n : nat) (s : StringT).

    Definition SplitAtT_fst
    : exists hc : option nat * list nat,
        take n (` (state_val s)) =?
        fst (list_of_next_bin_ops_closes (fst (SplitAt n s)) hc).
    Proof.
      destruct (state_val s) as [ table [ hc H ] ].
      exists (snd (list_of_next_bin_ops_closes (snd (SplitAt n s)) hc)); simpl.
      revert H; generalize (string_val s); clear s; clear -dec_refl.
      abstract (intros; edestruct dec; subst; rewrite ?take_list_of_next_bin_ops_closes, ?dec_refl; congruence).
    Defined.

    Definition SplitAtT_snd
    : exists hc : option nat * list nat,
        drop n (` (state_val s)) =?
        fst (list_of_next_bin_ops_closes (snd (SplitAt n s)) hc).
    Proof.
      destruct (state_val s) as [ table [ hc H ] ].
      exists hc; simpl.
      revert H; generalize (string_val s); clear s; clear -dec_refl.
      abstract (intros; edestruct dec; subst; rewrite ?drop_list_of_next_bin_ops_closes, ?dec_refl; congruence).
    Defined.

    Definition split_state_at' : split_stateT (fst (SplitAt n s)) * split_stateT (snd (SplitAt n s))
      := (exist _ (take n (proj1_sig (state_val s))) SplitAtT_fst,
          exist _ (drop n (proj1_sig (state_val s))) SplitAtT_snd).
  End SplitAtT.

  Definition split_state_at (n : nat) (s : String) (st : split_stateT s)
    := split_state_at' n {| string_val := s ; state_val := st |}.

  Let empty_state : split_stateT (Empty String).
  Proof.
    refine (exist _ nil (ex_intro _ (None, nil) _)).
    abstract (rewrite list_of_next_bin_ops_closes_compute_empty; reflexivity).
  Defined.

  Local Ltac destruct_matched_equality e :=
    subst;
    let T := type of e in
    match eval simpl in T with
      | ?a = ?b
        => generalize e; simpl;
           first [ generalize dependent b; intros; progress subst
                 | generalize dependent a; generalize dependent b; intros; progress subst
                 | generalize b; intros; progress subst
                 | generalize a; generalize dependent b; intros; progress subst
                 | generalize dependent a; generalize b; intros; progress subst
                 | generalize a; generalize b; intros; progress subst ]
    end.


  Lemma split_state_at_right_id s st
  : @split_state_at (Length s) (s ++ Empty _) st
    = (eq_rect
         _ split_stateT
         (eq_rect
            _ split_stateT
            st _
            (RightId _ _))
         _
         (f_equal fst (eq_sym (SplitAt_concat_correct _ _ _))),
       eq_rect
         _ split_stateT
         empty_state _
         (f_equal snd (eq_sym (SplitAt_concat_correct _ _ _)))).
  Proof.
    apply injective_projections; simpl.
    { destruct st as [ls [hc st] ]; simpl.
      unfold split_stateT; simpl.
      rewrite !eq_rect_sig; simpl.
      rewrite !eq_rect_ex; simpl.
    eapply path_sig; simpl.

    lazymatch goal with
    | [ |- appcontext[@eq_rect ?A ?x (fun _ => ?P) ?u ?y ?H] ]
      => pattern (@eq_rect A x (fun _ => P) u y H)
    end.


    unfold eq_rect.

    unfold split_state_at, split_state_at'; simpl.
    unfold SplitAtT_fst, SplitAtT_snd.

    simpl.
    revert st; simpl.
    match goal with
      | [ |- context[match ?e with eq_refl => _ end] ] => destruct_matched_equality e
      | [ |- context[match ?e with eq_refl => _ end] ] => generalize e; simpl
    end.
    generalize (fst (SplitAt (Length s) (s ++ Empty String))).

  Definition bin_op_split_nat
             (it : item CharType)
             (its : production CharType)
             (str : StringT)
  : list nat
    := match CharAt_option 0 str with
         | Some ch => match hd None (` (state_val str)) with
                        | None => nil (** table says this isn't a valid location to split *)
                        | Some n
                          => [if is_open ch
                              then (* it's an open paren; we must be being asked to split for '+';  we assume the table stores the location of the close, and split at one after it *)
                                S n
                              else (* it's not an open paren, so we assume the table stores the location of the next '+', and split there *)
                                n]
                      end
         | None => nil
       end.

  Definition bin_op_split
             (it : item CharType)
             (its : production CharType)
             (str : StringT)
  : list (StringT * StringT)
    := only_one_nt_split
         empty_state split_state_at bin_op_split_nat
         it its str.
  Check only_one_nt_split_complete.



  Definition first_char_split
             (it : item CharType)
             (its : production CharType)
             (str : StringT)
  : list (StringT * StringT).
  Proof.




End StringT.


  Local Coercion StringT_of_string (s : String') : StringT :=
    {| string_val := s ; state_val := I |}.

  Lemma StringT_eq {x y : StringT} (H : string_val x = string_val y)
  : x = y.
  Proof.
    destruct x as [? [] ], y as [? [] ]; simpl in *; subst; reflexivity.
  Qed.

  Local Ltac t_equality :=
    repeat match goal with
             | _ => intro
             | _ => reflexivity
             | [ H : is_true false |- _ ] => hnf in H; clear -H; exfalso; abstract discriminate
             | [ H : false = true |- _ ] => hnf in H; clear -H; exfalso; abstract discriminate
             | _ => progress simpl in *
             | _ => progress subst
             | _ => progress destruct_head sigT
             | _ => progress destruct_head prod
             | _ => progress destruct_head @StringWithSplitState
             | [ |- _ = _ :> (_ * _)%type ] => apply f_equal2
             | [ |- _ = _ :> StringT ] => apply StringT_eq
             | [ |- _ \/ False ] => left
             | _ => rewrite RightId
             | _ => rewrite LeftId
             | [ H : context[string_dec ?str ?x] |- _ ] => atomic x; destruct (string_dec str x)
             | [ |- context[match ?s with _ => _ end] ] => atomic s; destruct s
             | [ H : context[match ?s with _ => _ end] |- _ ] => atomic s; destruct s
             | _ => rewrite substring_correct3'
             | [ |- context[SplitAt _ ?n (?s1 ++ ?s2)] ]
               => replace n with (Length s1) by (rewrite Singleton_Length; trivial);
                 rewrite SplitAt_concat_correct
             | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (Terminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_item _ _ _ _ _ _ _ _ (NonTerminal _) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ (_::_) |- _ ] => inversion H; clear H
             | [ H : minimal_parse_of_production _ _ _ _ _ _ _ _ nil |- _ ] => inversion H; clear H
             | _ => solve [ eauto ]
           end.

  Section first_char_splitter.
    Context (fallback_split
             : forall (it : item CharType)
                      (its : production CharType)
                      (str : StringT),
                 list (StringT * StringT)).

    Definition first_char_split
               (it : item CharType)
               (its : production CharType)
               (str : StringT)
    : list (StringT * StringT)
      := match its with
           | nil => [(str, (Empty _ : String') : StringT)]
           | _::_ => match it with
                       | Terminal _
                         => [(((fst (SplitAt _ 1 str) : String') : StringT),
                              ((snd (SplitAt _ 1 str) : String') : StringT))]
                       | NonTerminal _
                         => fallback_split it its str
                     end
         end.

    Lemma first_char_split_correct_seq {it its} {str : StringT}
          (f := fun strs : StringT * StringT => fst strs ++ snd strs =s str)
          (fallback_split_correct_eq : List.Forall f (fallback_split it its str))
    : List.Forall f (first_char_split it its str).
    Proof.
      unfold first_char_split; subst f.
      repeat match goal with
               | _ => reflexivity
               | _ => assumption
               | _ => progress simpl in *
               | [ |- context[match ?l with _ => _ end] ]
                 => atomic l; destruct l
               | [ |- is_true (_ =s _)%string_like ] => apply bool_eq_correct
               | _ => progress rewrite ?LeftId, ?RightId
               | _ => apply SplitAt_correct
               | [ |- List.Forall _ [] ] => constructor
               | [ |- List.Forall _ (_::_) ] => constructor
             end.
    Qed.

    Context (G : grammar CharType).
    Context (fallback_split_correct_eq
             : forall it its (str : StringT),
                 List.Forall
                   (fun strs : StringT * StringT => fst strs ++ snd strs =s str)
                   (fallback_split it its str)).

    Global Instance first_char_premethods : @parser_computational_dataT' _ _ (@rdp_list_data' _ _ G)
      := { split_string_for_production str0 valid := first_char_split;
           split_string_for_production_correct str0 valid it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

    Global Instance first_char_data : @boolean_parser_dataT _ _
      := { predata := @rdp_list_predata _ G;
           split_stateT str := True;
           split_string_for_production := first_char_split;
           split_string_for_production_correct it its str := first_char_split_correct_seq (fallback_split_correct_eq it its str) }.

    Fixpoint first_char_valid_prod
             (first_char_valid : string -> bool)
             (p : production CharType)
    : bool
      := match p with
           | nil => true
           | (NonTerminal nt)::nil => first_char_valid nt
           | (Terminal _)::p' => first_char_valid_prod first_char_valid p'
           | (NonTerminal _)::_::_ => false
         end.

    Definition first_char_valid : bool
      := split_valid (G := G) first_char_valid_prod.

    Lemma first_char_split_complete
          (H : first_char_valid = true)
    : forall str0 valid str pf nt,
        is_valid_nonterminal initial_nonterminals_data nt ->
        ForallT
          (Forall_tails
             (fun prod =>
                match prod with
                  | [] => True
                  | it :: its =>
                    @split_list_completeT _ String G first_char_data str0 valid str pf
                                          (@first_char_split it its str) it its
                end)) (Lookup G nt).
    Proof.
      apply (split_complete_simple first_char_valid_prod).
      { intros ? ? ? p.
        induction p; t_equality. }
      { t_equality. }
      { intros.
        exists (I, I).
        unfold first_char_split.
        t_equality. }
      { exact H. }
    Qed.

    Global Instance first_char_cdata' H : @boolean_parser_completeness_dataT' _ _ G first_char_data
      := { remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
           remove_nonterminal_2 := rdp_list_remove_nonterminal_2;
           split_string_for_production_complete := @first_char_split_complete H }.

    Global Instance first_char_cdata H : @boolean_parser_correctness_dataT _ _ G
      := { data := first_char_data;
           cdata' := first_char_cdata' H }.
  End first_char_splitter.
End StringT.

Section on_ab_star.
  Definition ab_star_linear_split := first_char_split (String := string_stringlike) (fun _ _ _ => nil).
  Definition ab_star_linear_split_correct_seq {it its str} : List.Forall _ _
    := @first_char_split_correct_seq _ string_stringlike (fun _ _ _ => nil) it its str (Forall_nil _).

  Global Instance ab_star_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ ab_star_grammar)
    := first_char_premethods (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _).
  Global Instance ab_star_data : @boolean_parser_dataT _ string_stringlike
    := first_char_data (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _).

  Global Instance ab_star_cdata' : @boolean_parser_completeness_dataT' _ _ ab_star_grammar ab_star_data
    := first_char_cdata' (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _) eq_refl.

  Global Instance ab_star_cdata : @boolean_parser_correctness_dataT _ _ ab_star_grammar
    := first_char_cdata (String := string_stringlike) (fun _ _ _ => nil) ab_star_grammar (fun _ _ _ => Forall_nil _) eq_refl.
End on_ab_star.

Section on_ab_star'.
  Definition ab_star'_linear_split := first_char_split (String := string_stringlike) (fun _ _ _ => nil).
  Definition ab_star'_linear_split_correct_seq {it its str} : List.Forall _ _
    := @first_char_split_correct_seq _ string_stringlike (fun _ _ _ => nil) it its str (Forall_nil _).

  Global Instance ab_star'_premethods : @parser_computational_dataT' _ string_stringlike (@rdp_list_data' _ _ ab_star_grammar')
    := first_char_premethods (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _).
  Global Instance ab_star'_data : @boolean_parser_dataT _ string_stringlike
    := first_char_data (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _).

  Global Instance ab_star'_cdata' : @boolean_parser_completeness_dataT' _ _ ab_star_grammar' ab_star'_data
    := first_char_cdata' (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _) eq_refl.

  Global Instance ab_star'_cdata : @boolean_parser_correctness_dataT _ _ ab_star_grammar'
    := first_char_cdata (String := string_stringlike) (fun _ _ _ => nil) ab_star_grammar' (fun _ _ _ => Forall_nil _) eq_refl.
End on_ab_star'.
