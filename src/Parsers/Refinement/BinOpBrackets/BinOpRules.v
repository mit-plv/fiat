(** Refinement rules for binary operations *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Refinement.DisjointRulesCommon.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.MakeBinOpTable.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalancedLemmas.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalancedGrammar.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Export Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Export DisjointLemmas.Exports.

Local Open Scope string_like_scope.

Set Implicit Arguments.

Section helper_lemmas.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  Lemma paren_balanced_hiding'_prefix__index_points_to_binop
        (str : StringLike.String)
        (n idx len : nat)
        (H_hiding : paren_balanced_hiding' (take len (drop n str)) 0)
        (H_points_to : index_points_to_binop n idx str)
        (H_pre_hiding : paren_balanced' (take idx (drop n str)) 0)
        (H_small : idx < min len (StringLike.length (drop n str)))
  : False.
  Proof.
    unfold index_points_to_binop in *.
    repeat match goal with
             | [ H : context[StringLike.get ?n ?str] |- _ ]
               => not constr_eq n 0;
                 let H' := fresh in
                 revert H;
                   case_eq (StringLike.get n str);
                   rewrite get_drop; intros
             | _ => progress destruct_head ex
             | _ => progress split_and
             | [ H : StringLike.get 0 _ = Some _ |- _ ] => apply get_0 in H
             | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
             | [ H : ?idx < _, H' : context[drop (?n + ?idx) _] |- _ ]
               => replace (n + idx) with (idx + n) in H' by omega
             | [ H : ?idx < _, H' : context[drop (?idx + _) _] |- _ ]
               => rewrite <- drop_drop in H'
             | [ H : _ |- _ ] => progress rewrite ?take_length, ?drop_length in H
             | [ H : context[take _ (drop _ (take _ _))] |- _ ] => rewrite drop_take in H
             | [ H : is_true (take _ (take _ _) ~= [ _ ]) |- _ ] => rewrite take_take in H
             | [ H : is_true (_ ~= [ _ ]) |- _ ] => progress apply take_n_1_singleton in H
             | [ H : FirstChar.for_first_char _ _, H' : _ < _, H'' : _ < _ |- _ ]
               => apply FirstChar.for_first_char_exists in H;
                 [
                     | rewrite !drop_length; clear -H' H''; omega ]
             | [ H : _ < min _ _ |- _ ] => apply NPeano.Nat.min_glb_lt_iff in H
           end.
    eapply (paren_balanced_hiding'_prefix);
      [ exact H_hiding
      | exact H_pre_hiding
      | eassumption
      | eassumption
      | assumption ].
  Qed.
End helper_lemmas.

Section refine_rules.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}
          {HSI : StringIso Ascii.ascii} {HSIP : StringIsoProperties Ascii.ascii}.
  Context {G : pregrammar' Ascii.ascii}
          (ptdata : possible_data G)
          {str : StringLike.String} {n m : nat} {nt : string} {ch : Ascii.ascii} {its : production Ascii.ascii}.
  Local Notation possible_first_terminals_of_production its
    := (@possible_first_ascii_of_production G ptdata its).
  Context {pf : match possible_first_terminals_of_production its return Prop with
                  | nil => False
                  | ls => fold_right and True (map (eq ch) ls)
                end}
          (Hnt_valid : let predata := rdp_list_predata (G := G) in is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)).

  Local Opaque rdp_list_predata.

  Local Notation retT table
    := (refine {splits : list nat
               | split_list_is_complete
                   G str n m
                   (NonTerminal nt::its) splits}
               (ret [match List.nth n table None with
                       | Some idx => idx
                       | None => m
                     end])).

  Lemma length_helper {n' m' table}
        (Hlen : m' = 0 \/ n' + m' <= length str)
  : match List.nth n' table None with
      | Some idx => idx
      | None => m'
    end
    = match List.nth n' table None with
        | Some idx => idx
        | None => length (substring n' m' str)
      end.
  Proof.
    destruct (List.nth n' table None); try reflexivity.
    rewrite substring_length.
    destruct Hlen; subst; simpl;
    apply Min.min_case_strong; omega.
  Qed.

  Section general_table.
    Context {pdata : paren_balanced_hiding_dataT Ascii.ascii}
            (Hch : is_bin_op ch).
    Context (table : list (option nat)).
    Context (Htable : list_of_next_bin_ops_spec table str).

    Lemma refine_binop_table'
          (H_nt_hiding
           : forall str', parse_of_item G str' (NonTerminal nt)
                          -> paren_balanced_hiding str')
    : retT table.
    Proof.
      intros ls H.
      computes_to_inv; subst.
      apply PickComputes.
      specialize (Htable n).
      hnf; cbv zeta.
      intros Hlen it' its' Heq idx' Hsmall Hreachable pit pits; simpl.
      rewrite length_helper by assumption.
      inversion Heq; subst it' its'; clear Heq.
      specialize (H_nt_hiding _ pit).
      unfold paren_balanced_hiding in *.
      set (s_str := (substring n m str) : @StringLike.String _ HSLM) in *.
      destruct (Compare_dec.zerop (StringLike.length (drop idx' s_str))) as [iszero|isnonzero].
      { (* Deal with the case where drop idx' s_str is empty *)
        rewrite drop_length in iszero.
        assert (lenequal : idx' = StringLike.length s_str)
          by omega.
        subst.
        destruct (nth n table None) eqn:nth_equals.
        {
          destruct (Compare_dec.le_lt_dec (StringLike.length s_str) n0) as [|g].
          { rewrite Min.min_l by assumption.
            left.
            reflexivity. }
          { exfalso.
            destruct (Htable n0) as [some_impl _].
            pose (some_impl nth_equals) as Hn0.
            destruct Hn0 as [Hn0_binop Hn0_balanced].
            apply paren_balanced_hiding_impl_paren_balanced' in Hn0_balanced.
            subst s_str.
            rewrite take_take in H_nt_hiding.
            refine (paren_balanced_hiding'_prefix__index_points_to_binop _ H_nt_hiding Hn0_binop Hn0_balanced _).
            rewrite <- Min.min_assoc.
            rewrite <- take_length.
            rewrite Min.min_idempotent.
            assumption.
          }
        }
        {
          rewrite Min.min_idempotent.
          tauto.
        }
      }

      destruct Hlen as [Hlen|Hlen].
      { subst s_str m; exfalso; revert isnonzero.
        rewrite drop_length, substring_length; apply Min.min_case_strong; simpl; intros; omega. }

      subst s_str.
      rewrite take_take in H_nt_hiding.
      inversion pits as [|idx'' pat pats H_parse_item H_parse_production Hits].
      {
        (* Deal with the silly case where [] = its *)
        subst.
        simpl in *.
        tauto.
      }

      assert (take 1 (drop idx' (substring n m str)) ~= [ch]).
      {
        destruct (possible_first_terminals_of_production its) eqn:terminals.
        {
          simpl in *.
          tauto.
        }
        {
          pose proof (possible_first_ascii_parse_of_production pits) as H_first_char.
          apply FirstChar.first_char_in_exists in H_first_char.
          {
            destruct H_first_char as [ch0 [take_equals in_list] ].
            rewrite terminals in in_list.
            clear terminals.
            set (ls := (a :: l)) in *.
            induction ls;
              destruct pf;
              destruct in_list;
              subst;
              tauto.
          }
          { omega. }
        }
      }

      repeat match goal with
               | [ H : context[length (drop _ (substring _ _ _))] |- _ ]
                 => rewrite drop_length in H
             end.
      unfold list_of_next_bin_ops_spec'' in *.
(*
      repeat match goal with
               | [ H : parse_of_item _ _ (Terminal _) |- _ ] => inversion H; clear H
             end.
               | [ H : context[substring _ _ _] |- _ ] => rewrite substring_take_drop in H
               | [ H : is_true (take ?n ?str ~= [ ?ch ]) |- _ ]
                 => progress apply take_n_1_singleton in H
             end.

               | [ H : context[take _ (drop _ (take _ _))] |- _ ] => rewrite drop_take in H
               | [ H : is_true (take _ (take _ _) ~= [ _ ]) |- _ ] => rewrite take_take in H
               | [ H : _ <= StringLike.length _ |- _ ] => rewrite take_length in H
               | [ H : context[min ?x ?y], H' : ?x <= min ?y _ |- _ ]
                 => replace (min x y) with x in H
                                             by (revert H'; clear; abstract (repeat apply Min.min_case_strong; intros; omega))
               | _ => progress subst
             end. *)
      destruct (List.nth n table None) as [idx|].
      { edestruct Htable as [ [Htable0 Htable1] _]; clear Htable; [ reflexivity | ].
        left.
        destruct (Compare_dec.lt_eq_lt_dec idx idx') as [ [?|?]|?];
          [
          | subst; apply Min.min_r; omega
          | ];
          exfalso.
        { (** idx < idx'; this contradicts the paren-balanced-hiding
          assumption about [nt], because we have a character in the
          middle of the string of length idx', where the prefix is
          paren-balanced-hiding at level 0, and the character is a
          bin-op. *)
          apply paren_balanced_hiding_impl_paren_balanced' in Htable1; [ | exact _ .. ].
          eapply paren_balanced_hiding'_prefix__index_points_to_binop; try eassumption.
          rewrite <- take_length, <- take_take, take_length.
          apply Min.min_case_strong; intros; try assumption; omega.

 }
        { (** idx' < idx; this contradicts the paren-balanced-hiding
          assumption about the string of length idx, because we have a
          string parsing as a valid nt, with an unhidden bin-op right
          after it. *)
          apply paren_balanced_hiding_impl_paren_balanced' in H_nt_hiding; [ | exact _ .. ].

          eapply (paren_balanced_hiding'_prefix);
            [ exact Htable1
            | exact H_nt_hiding
            |
            |
            | eassumption ].
          { apply Min.min_case_strong; omega. }
          { rewrite Min.min_l
              by (rewrite substring_length, Min.min_r in Hsmall by omega;
                  omega).
            rewrite drop_take, take_take in H.
            apply take_n_1_singleton in H.
            assumption. } } }
      { simpl.
        pose proof (fun idx => proj2 (Htable idx) eq_refl) as Htable'.
        clear Htable.
        apply paren_balanced_hiding_impl_paren_balanced' in H_nt_hiding.
        specialize (Htable' _ H_nt_hiding).
        unfold index_not_points_to_binop in *.
        apply FirstChar.for_first_char_exists in Htable';
          [
          | solve [ repeat
                      match goal with
                        | _ => rewrite Min.min_l in Hsmall by omega
                        | _ => rewrite Min.min_l in isnonzero by omega
                        | _ => rewrite Min.min_l by assumption
                        | [ H : is_true (_ ~= [ _ ]) |- _ ] => apply length_singleton in H
                        | [ H : _ |- _ ] => progress rewrite ?drop_length, ?take_length in H
                        | _ => progress rewrite ?drop_length, ?take_length
                        | [ H : min _ _ = _ |- _ ] => revert H; apply Min.min_case_strong; clear; intros; omega
                        | _ => omega
                      end ] ].
        destruct Htable' as [ch' [Ht0 Ht1] ].
        rewrite substring_length, Min.min_r, NPeano.Nat.add_sub in Hsmall by omega.
        repeat match goal with
                 | _ => rewrite Min.min_idempotent
                 | [ |- _ \/ False ] => left
                 | [ H : 0 < ?x - ?y |- ?x = ?y ] => exfalso
                 | [ H : context[min] |- _ ] => rewrite Min.min_r in H by omega
                 | [ H : context[min] |- _ ] => rewrite Min.min_l in H by omega
                 | [ H : is_true (is_char (substring _ _ (substring _ _ _)) _) |- _ ]
                   => rewrite substring_substring in H;
                     apply take_n_1_singleton in H
                 | [ H : context[(?x + ?y)%nat], H' : context[(?y + ?x)%nat] |- _ ]
                   => not constr_eq x y; replace (y + x) with (x + y) in H' by omega
                 | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
                   => assert (ch = ch') by (eapply singleton_unique; eassumption);
                     clear H'
                 | _ => progress subst
                 | _ => congruence
               end. }
    Qed.

    Lemma refine_binop_table''
          (predata := rdp_list_predata (G := G))
          (H_nt_hiding : paren_balanced_hiding_correctness_type G nt)
    : retT table.
    Proof.
      apply refine_binop_table'.
      apply paren_balanced_hiding_nt_correct;
      assumption.
    Qed.
  End general_table.

  Section derive_table.
    Context {pdata : paren_balanced_hiding_dataT Ascii.ascii}
            (Hch : is_bin_op ch).

    Lemma refine_binop_table'''
          (predata := rdp_list_predata (G := G))
          (H_nt_hiding : paren_balanced_hiding_correctness_type G nt)
    : retT (list_of_next_bin_ops_opt_nor str).
    Proof.
      apply refine_binop_table''; try assumption.
      apply list_of_next_bin_ops_opt_nor_satisfies_spec.
    Qed.
  End derive_table.

  Section derive_pbhd.
    Definition bin_op_data_of_gen_bin_op (f_bin_op : Ascii.ascii -> bool) (open close : Ascii.ascii)
    : paren_balanced_hiding_dataT Ascii.ascii
      := {| is_bin_op := f_bin_op;
            is_open := ascii_beq open;
            is_close := ascii_beq close |}.

    Definition bin_op_data_of (open close : Ascii.ascii)
    : paren_balanced_hiding_dataT Ascii.ascii
      := bin_op_data_of_gen_bin_op (ascii_beq ch) open close.

    Definition maybe_open_closes {Char} {HEC : Enumerable.Enumerable Char}
               (p : production Char)
    : list ((Char -> bool) * (Char -> bool))
      := match hd None (map Some p), hd None (map Some (rev p)) with
           | Some (Terminal open), Some (Terminal close)
             => [(open, close)]
           | _, _ => nil
         end.

    Definition possible_open_closes_pre
    : list ((Ascii.ascii -> bool) * (Ascii.ascii -> bool))
      := flat_map (flat_map maybe_open_closes) (map snd (pregrammar_productions G)).

    Definition possible_open_closes
    : list (Ascii.ascii * Ascii.ascii)
      := Operations.List.uniquize
           Equality.beq
           (List.flat_map
              (fun openf_closef
               => let openf := fst openf_closef in
                  let closef := snd openf_closef in
                  let opens := List.filter openf (Enumerable.enumerate Ascii.ascii) in
                  let closes := List.filter closef (Enumerable.enumerate Ascii.ascii) in
                  match opens, closes with
                  | cho::nil, chc::nil => if ascii_beq cho chc
                                          then nil
                                          else [(cho, chc)]
                  | _, _ => nil
                  end)
              possible_open_closes_pre).

    Definition possible_balanced_open_closes
    : list (Ascii.ascii * Ascii.ascii)
      := List.filter
           (fun oc => paren_balanced_correctness_type
                        (pdata := {| is_bin_op := fun _ => false;
                                     is_open := ascii_beq (fst oc);
                                     is_close := ascii_beq (snd oc) |})
                        G nt)
           possible_open_closes.

    Let make_f := fun ls ch' => List.fold_right orb false (List.map (ascii_beq ch') ls).


    Definition possible_valid_open_closes
    : option (list Ascii.ascii * list Ascii.ascii)
      := let possible_opens := List.map fst possible_balanced_open_closes in
         let possible_closes := List.map snd possible_balanced_open_closes in
         let open_f := make_f possible_opens in
         let close_f := make_f possible_closes in
         if paren_balanced_hiding_correctness_type
              (pdata := {| is_bin_op := ascii_beq ch;
                           is_open := open_f;
                           is_close := close_f |})
              G nt
         then Some (possible_opens, possible_closes)
         else None.

    Definition bin_op_gen_ch_data_of_maybe (is_bin_op_f : Ascii.ascii -> bool)
               (oc : option (list Ascii.ascii * list Ascii.ascii))
    : paren_balanced_hiding_dataT Ascii.ascii
      := {| is_bin_op := is_bin_op_f;
            is_open ch' := match oc with
                             | Some oc' => make_f (fst oc') ch'
                             | None => false
                           end;
            is_close ch' := match oc with
                              | Some oc' => make_f (snd oc') ch'
                              | None => false
                            end |}.

    Definition bin_op_data_of_maybe (oc : option (list Ascii.ascii * list Ascii.ascii))
    : paren_balanced_hiding_dataT Ascii.ascii
      := bin_op_gen_ch_data_of_maybe (ascii_beq ch) oc.

    Definition correct_open_close
    : paren_balanced_hiding_dataT Ascii.ascii
      := bin_op_data_of_maybe possible_valid_open_closes.

    Section lemmas.
      Let predata := rdp_list_predata (G := G).
      Let pdata := correct_open_close.
      Local Existing Instance predata.
      Local Existing Instance pdata.

      Context (H_nt_hiding
               : match possible_valid_open_closes with
                   | None => false
                   | _ => true
                 end).

      Local Opaque Enumerable.enumerable_ascii.

      Lemma refine_binop_table
      : retT (list_of_next_bin_ops_opt_nor str).
      Proof.
        unfold correct_open_close, possible_valid_open_closes in *.
        subst pdata.
        revert H_nt_hiding.
        destruct (paren_balanced_hiding_correctness_type G nt) eqn:Heq.
        { intros _.
          apply refine_binop_table'''.
          { apply ascii_lb; reflexivity. }
          { assumption. } }
        { intro; congruence. }
      Qed.

      Section idx.
        Context {idx} {Heq : default_to_production (G := G) idx = NonTerminal nt :: its}.

        Local Notation retT table
          := (refine {splits : list nat
                     | split_list_is_complete_idx
                         G str n m
                         idx splits}
                     (ret [match List.nth n table None with
                             | Some idx' => idx'
                             | None => m
                           end])).

        Lemma refine_binop_table_idx
        : retT (list_of_next_bin_ops_opt_nor str).
        Proof.
          rewrite <- refine_binop_table.
          apply refine_pick_pick; intro.
          unfold split_list_is_complete_idx.
          rewrite Heq; trivial.
        Qed.
      End idx.
    End lemmas.
  End derive_pbhd.
End refine_rules.

Global Arguments bin_op_data_of / _ _ _.
Global Arguments possible_open_closes_pre / _.
Global Arguments possible_open_closes / _.
Global Arguments maybe_open_closes / _ _ _.
Global Arguments correct_open_close / _ _ _.
Global Arguments possible_open_closes / _.
Global Arguments possible_valid_open_closes / _ _ _.
Global Arguments bin_op_data_of_maybe / _ _.
Global Arguments default_list_of_next_bin_ops_opt_data / _ _ _.
Global Arguments take : simpl never.
Global Arguments drop : simpl never.
Global Arguments list_of_next_bin_ops_opt_nor : simpl never.

(** [simpl] is very slow at simplifying [correct_open_close], so we
    help it along.  If the machinery of [Defined] changes, we may have
    to use [replace] rather than [change], and [vm_compute], or
    something. *)

(** Old helper tactic for refinement
<<<
Local Ltac presimpl_after_refine_binop_table :=
  unfold correct_open_close;
  match goal with
    | [ |- context[@possible_valid_open_closes ?G ?nt ?ch] ]
      => let c := constr:(@possible_valid_open_closes G nt ch) in
         let c' := (eval lazy in c) in
         let H := fresh in
         assert (H : c = c')
           by (clear; abstract (exact_no_check (eq_refl c)));
           rewrite H; clear H
  end;
  match goal with
    | [ |- context[@default_list_of_next_bin_ops_opt_data ?HSL ?data] ]
      => let c := constr:(@default_list_of_next_bin_ops_opt_data HSL data) in
         let c' := (eval cbv beta iota zeta delta [default_list_of_next_bin_ops_opt_data ParenBalanced.Core.is_open ParenBalanced.Core.is_close ParenBalanced.Core.is_bin_op bin_op_data_of_maybe List.hd List.map fst snd] in c) in
         change c with c'
  end.
>>> *)

(** Modulo some simplification, this is equivalent to
<<<
      let lem := constr:(@refine_binop_table_idx _ _ _ _ _) in
      setoid_rewrite lem;
             [ | reflexivity | | | reflexivity ];
             [ | solve [ clear; lazy; repeat esplit ] | ];
             [ | solve [ clear; lazy; reflexivity ] ];
      presimpl_after_refine_binop_table.
>>> *)
Definition Let_In {A B} (v : A) (f : A -> B) := let y := v in f y.
Definition app_to_opt_let_in {A B} v f
  : f v = @Let_In A B v f
  := eq_refl.
Definition cut_app_to_opt_let_in {A} v f
  : @Let_In A Prop v f -> f v
  := fun x => x.
Ltac cut_app_to_opt_let_in _ :=
  lazymatch goal with
  | [ |- @Let_In ?A Prop ?v ?f -> ?f ?v ]
    => clear; (*abstract*) exact_no_check (@cut_app_to_opt_let_in A v f)
  end.
Ltac abstract_exact_id _ :=
  match goal with
  | [ |- ?A -> ?B ]
    => clear; (*abstract*) exact (fun x : A => x)
  end.
Ltac solve_match_list_by_lazy_then_esplit _ :=
  clear;
  match goal with
    |- match ?e with nil => ?N | cons a b => ?P end
    => let f := uconstr:(fun e' => match e' with nil => N | cons a b => P end) in
       let lem := constr:(cut_app_to_opt_let_in e f) in
       change (f e);
       cut (Let_In e f);
       [
              | let e' := (eval lazy in e) in
                cut (Let_In e' f);
                [
                  | compute; repeat esplit ] ];
       [ cut_app_to_opt_let_in () | abstract_exact_id () ]
  end.
Ltac setoid_rewrite_refine_binop_table_idx args :=
  idtac;
  let lem := constr:(@refine_binop_table_idx _ _ _) in
  let G := match args with ParserInterface.split_list_is_complete_idx
                             ?G ?str ?offset ?len ?idx => G end in
  let str := match args with ParserInterface.split_list_is_complete_idx
                               ?G ?str ?offset ?len ?idx => str end in
  let offset := match args with ParserInterface.split_list_is_complete_idx
                                  ?G ?str ?offset ?len ?idx => offset end in
  let len := match args with ParserInterface.split_list_is_complete_idx
                               ?G ?str ?offset ?len ?idx => len end in
  let idx := match args with ParserInterface.split_list_is_complete_idx
                               ?G ?str ?offset ?len ?idx => idx end in
  let ps := (eval hnf in (Carriers.default_to_production (G := G) idx)) in
  match ps with
  | nil => fail 1 "The index" idx "maps to the empty production," "which is not valid for the binop-brackets rule"
  | _ => idtac
  end;
  let p := match ps with ?p::_ => p end in
  let p := (eval hnf in p) in
  match p with
  | NonTerminal _ => idtac
  | _ => fail 1 "The index" idx "maps to a production starting with" p "which is not a nonterminal; the index must begin with a nonterminal to apply the binop-brackets rule"
  end;
  let nt := match p with NonTerminal ?nt => nt end in
  let its := (eval simpl in (List.tl ps)) in
  let ptdata := get_hyp_of_shape (possible_data G) in
  let lem := constr:(fun its' H' ch H0 H1 => lem G ptdata str offset len nt ch its' H0 H1 idx H') in
  let lem := constr:(lem its eq_refl) in
  let chT := match type of lem with forall ch : ?chT, _ => chT end in
  let chE := fresh "ch" in
  evar (chE : chT);
  let ch := (eval unfold chE in chE) in
  let lem := constr:(lem ch) in
  let H0 := fresh in
  let T0 := match type of lem with ?T0 -> _ => T0 end in
  first [ assert (H0 : T0) by solve_match_list_by_lazy_then_esplit ()
        | fail 1 "Could not find a single binary operation to solve" T0 ];
  subst chE;
  let lem := constr:(lem H0) in
  let H := fresh in
  pose proof lem as H; clear H0;
  unfold correct_open_close in H;
  let c := match type of H with
           | context[@possible_valid_open_closes ?G ?nt ?ch]
             => constr:(@possible_valid_open_closes G nt ch)
           end in
  replace_with_vm_compute_in c H;
  first [ specialize (H eq_refl)
        | fail 1 "Could not find a set of good brackets for the binary operation" ch ];
  let c := match type of H with
           | context[@default_list_of_next_bin_ops_opt_data ?HSLM ?HSL ?data]
             => constr:(@default_list_of_next_bin_ops_opt_data HSLM HSL data)
           end in
  let c' := (eval cbv beta iota zeta delta [default_list_of_next_bin_ops_opt_data ParenBalanced.Core.is_open ParenBalanced.Core.is_close ParenBalanced.Core.is_bin_op bin_op_data_of_maybe List.hd List.map fst snd] in c) in
  let c' := match c' with
            | context[@StringLike.get _ ?HSLM ?HSL]
              => let HSLM' := head HSLM in
                 let HSL' := head HSL in
                 (eval cbv beta iota zeta delta [String StringLike.length StringLike.unsafe_get StringLike.get HSLM' HSL'] in c')
            | _ => c'
            end in
  change c with c' in H;
  lazymatch goal with
  | [ |- refine { splits : list nat | _ } _ ]
    => refine H
  | _ => first [ setoid_rewrite H
               | let T := type of H in
                 fail 1 "Unexpected failure to setoid_rewrite with" T ]
  end;
  clear H.
Ltac refine_binop_table :=
  idtac;
  match goal with
  | [ |- context[{ splits : list nat
                 | ParserInterface.split_list_is_complete_idx
                     ?G ?str ?offset ?len ?idx splits }%comp] ]
    => setoid_rewrite_refine_binop_table_idx
         (ParserInterface.split_list_is_complete_idx
            G str offset len idx)
  end.
