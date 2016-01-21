(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSONImpoverished.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Require Import Fiat.Parsers.Refinement.BinOpBrackets.BinOpRules.

Section IndexedImpl.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec json'_grammar HSL).
  Proof.

    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    {
      (*Start Profiling.*)
      Time simplify parser splitter.
      (*Show Profile.*)
      (*
total time:     21.428s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify parser splitter --------------   0.0% 100.0%       1   21.428s
─simplify ------------------------------   0.0% 100.0%       1   21.428s
─simplify_parser_splitter' -------------   0.1% 100.0%      19    5.232s
─rewrite <- !BoolFacts.andb_orb_distrib_  22.5%  22.5%       7    4.424s
─simplify with monad laws --------------   0.0%  17.3%      13    0.728s
─simplify_with_applied_monad_laws ------   0.1%  17.3%      13    0.728s
─rewrite !Bool.orb_false_r -------------  11.0%  11.0%      17    1.732s
─rewrite <- !Bool.andb_orb_distrib_r ---   8.8%   8.8%      28    0.420s
─rewrite <- !Bool.orb_assoc ------------   8.5%   8.5%       9    1.396s
─unguard -------------------------------   0.0%   8.1%      19    0.584s
─rewrite ?(unguard [0]) ----------------   7.8%   8.1%      19    0.584s
─rewrite <- !Bool.andb_orb_distrib_l ---   5.9%   5.9%      12    0.620s
─autounfold  with parser_sharpen_db ----   4.6%   4.6%      18    0.132s
─eapply refine_under_bind_helper -------   3.6%   3.6%      98    0.044s
─eapply refine_under_bind_helper_1 -----   3.4%   3.4%      98    0.040s
─eapply refine_under_bind_helper_2 -----   3.4%   3.4%      98    0.040s
─parser_pull_tac -----------------------   0.1%   2.8%       3    0.604s
─apply refine_bind_bind_helper ---------   2.5%   2.5%     100    0.036s
─apply refine_bind_unit_helper ---------   2.3%   2.3%     102    0.028s

 tactic                                    self  total   calls       max
────────────────────────────────────────┴──────┴──────┴───────┴─────────┘
─simplify parser splitter --------------   0.0% 100.0%       1   21.428s
└simplify ------------------------------   0.0% 100.0%       1   21.428s
└simplify_parser_splitter' -------------   0.1% 100.0%      19    5.232s
 ├─rewrite <- !BoolFacts.andb_orb_distri  22.5%  22.5%       7    4.424s
 ├─simplify with monad laws ------------   0.0%  17.3%      13    0.728s
 │└simplify_with_applied_monad_laws ----   0.1%  17.3%      13    0.728s
 │ ├─eapply refine_under_bind_helper ---   3.6%   3.6%      98    0.044s
 │ ├─eapply refine_under_bind_helper_1 -   3.4%   3.4%      98    0.040s
 │ ├─eapply refine_under_bind_helper_2 -   3.4%   3.4%      98    0.040s
 │ ├─apply refine_bind_bind_helper -----   2.5%   2.5%     100    0.036s
 │ └─apply refine_bind_unit_helper -----   2.3%   2.3%     102    0.028s
 ├─rewrite !Bool.orb_false_r -----------  11.0%  11.0%      17    1.732s
 ├─rewrite <- !Bool.andb_orb_distrib_r -   8.8%   8.8%      28    0.420s
 ├─rewrite <- !Bool.orb_assoc ----------   8.5%   8.5%       9    1.396s
 ├─unguard -----------------------------   0.0%   8.1%      19    0.584s
 │└rewrite ?(unguard [0]) --------------   7.8%   8.1%      19    0.584s
 ├─rewrite <- !Bool.andb_orb_distrib_l -   5.9%   5.9%      12    0.620s
 ├─autounfold  with parser_sharpen_db --   4.6%   4.6%      18    0.132s
 └─parser_pull_tac ---------------------   0.1%   2.8%       3    0.604s
 *)

      Ltac solve_disjoint_side_conditions :=
        idtac;
        lazymatch goal with
        | [ |- Carriers.default_to_production (G := ?G) ?k = ?e ]
          => cbv beta iota zeta delta [Carriers.default_to_production Lookup_idx fst snd List.map pregrammar_productions List.length List.nth minus Operations.List.drop G];
             try reflexivity
        | [ |- is_true (Operations.List.disjoint _ _ _) ]
          => vm_compute; try reflexivity
        end.

      Ltac pose_disjoint_search_for lem :=
        idtac;
        let G := match goal with |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] => G end in
        let lem' := constr:(@refine_disjoint_search_for_idx HSLM HSL _ _ _ G) in
        assert (H' : ValidReflective.grammar_rvalid G) by (vm_compute; reflexivity);
          let lem' := match goal with
                        | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
                          => constr:(fun idx' nt its => lem' str offset len nt its idx' H')
                      end in
          pose proof lem' as lem.
      Ltac rewrite_once_disjoint_search_for lem :=
        idtac;
        let G := (lazymatch goal with
                 | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
                   => G
                  end) in
        let lem' := fresh "lem'" in
        (lazymatch goal with
        | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
          => pose proof (lem idx) as lem'
         end);
          do 2 (lazymatch type of lem' with
               | forall a : ?T, _ => idtac; let x := fresh in evar (x : T); specialize (lem' x); subst x
                end);
          let T := match type of lem' with forall a : ?T, _ => T end in
          let H' := fresh in
          assert (H' : T) by solve_disjoint_side_conditions;
            specialize (lem' H'); clear H';
            let x := match type of lem' with
                       | context[DisjointLemmas.actual_possible_first_terminals ?ls]
                         => constr:(DisjointLemmas.actual_possible_first_terminals ls)
                     end in
            let x' := (eval vm_compute in x) in
            change x with x' in lem';
              simpl @Equality.list_bin in lem';
              let T := match type of lem' with forall a : ?T, _ => T end in
              let H' := fresh in
              assert (H' : T) by solve_disjoint_side_conditions;
                specialize (lem' H'); clear H';
                setoid_rewrite lem'; clear lem'.
      Ltac rewrite_disjoint_search_for_no_clear lem :=
        pose_disjoint_search_for lem;
        repeat rewrite_once_disjoint_search_for lem.
      Ltac rewrite_disjoint_search_for :=
        idtac;
        let lem := fresh "lem" in
        rewrite_disjoint_search_for_no_clear lem;
          clear lem.

      Time rewrite_disjoint_search_for.
      Time simplify parser splitter.
      idtac;
        match goal with
                      | [ |- context[{ splits : list nat
                                     | ParserInterface.split_list_is_complete_idx
                                         ?G ?str ?offset ?len ?idx splits }%comp] ]
                        => let args := constr:(ParserInterface.split_list_is_complete_idx
                                     G str offset len idx) in
      idtac;
        let lem := constr:(@refine_binop_table_idx _ _ _ _ _) in
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
            let lem := constr:(fun its' H' ch H0 H1 => lem G eq_refl str offset len nt ch its' H0 H1 idx H') in
            let lem := constr:(lem its eq_refl) in
            let chT := match type of lem with forall ch : ?chT, _ => chT end in
            let chE := fresh "ch" in
            evar (chE : chT);
              let ch := (eval unfold chE in chE) in
              let lem := constr:(lem ch) in
              let H0 := fresh in
              let T0 := match type of lem with ?T0 -> _ => T0 end in
              first [ assert (H0 : T0) by (clear; lazy; repeat esplit)
                    | fail 1 "Could not find a single binary operation to solve" T0 ];
                subst chE;
                let lem := constr:(lem H0) in
                let H := fresh in
                pose proof lem as H; clear H0;
                unfold correct_open_close in H;
                let c := match type of H with
                           | appcontext[@possible_valid_open_closes ?G ?nt ?ch]
                             => constr:(@possible_valid_open_closes G nt ch)
                         end in
                match type of H with
                  | appcontext[@possible_valid_open_closes ?G ?nt ?ch]
                    => pose (@possible_open_closes_pre G) as c''';
                      pose (@DisjointLemmas.possible_first_terminals_of G _ _ nt) as c'''''
                end;
                let c0 := fresh in
                set (c0 := c) in H(*;
                  lazy in c0*)
end.
exfalso.
clear H3.
cbv [DisjointLemmas.possible_first_terminals_of] in c'''''.
unfold possible_open_closes_pre in c'''.
unfold List.flat_map in c'''.
Set Printing All.
Show.
Check fun x => match x with pair a b => 1 end.
cbv beta iota delta [possible_valid_open_closes possible_balanced_open_closes] in H4.
set (x := (@possible_open_closes json'_pregrammar)) in H4.
Timeout 5 vm_compute in x.
subst x.
match (eval cbv delta [H4] in H4) with
| context[List.filter ?f ?ls] => set (x := (List.filter f ls)) in H4
end.
Timeout 1 cbv [ParenBalancedGrammar.paren_balanced_correctness_type] in x.
clear -x.
match (eval cbv delta [x] in x) with
| context[@BaseTypes.of_nonterminal ?a ?b ?c]
  => set (y := @BaseTypes.of_nonterminal a b c) in (value of x)
end.
vm_compute in y.
subst y.
match (eval cbv delta [x] in x) with
| appcontext[@ParenBalancedGrammar.paren_balanced_nonterminals ?a ?b _ ?d ?e]
  => set (y' := fun d' e' c => @ParenBalancedGrammar.paren_balanced_nonterminals a b c d' e') in (value of x);
       change (@ParenBalancedGrammar.paren_balanced_nonterminals a b)
       with (fun c' d' e' => y' d' e' c') in (value of x);
       cbv beta in x;
       set (y := y' d e) in (value of x);
       subst y';
       cbv beta in y
end.
clear -y.
cbv [BaseTypes.nonterminal_carrierT RDPList.rdp_list_predata Carriers.default_nonterminal_carrierT ParenBalancedGrammar.paren_balanced_nonterminals ParenBalancedGrammar.paren_balanced_nonterminals_of FoldGrammar.fold_nt BaseTypes.nonterminals_length BaseTypes.initial_nonterminals_data RDPList.rdp_list_initial_nonterminals_data fst List.length Operations.List.up_to] in y.
simpl @List.map in y.
cbv beta iota zeta in y.
Opaque FoldGrammar.fold_nt_step.
simpl in y.
Transparent FoldGrammar.fold_nt_step.
Opaque FoldGrammar.fold_nt'.
Timeout 5 cbv [FoldGrammar.fold_nt_step BaseTypes.nonterminals_listT ParenBalancedGrammar.paren_balanced_nonterminals_T RDPList.rdp_list_predata RDPList.rdp_list_nonterminals_listT BaseTypes.nonterminal_carrierT Carriers.default_nonterminal_carrierT FoldGrammar.fold_nt_step] in y.
match (eval cbv delta [y] in y) with
| context[if ?e then _ else _]
  => set (z := e) in (value of y)
end.
vm_compute in z.
subst z; cbv iota in y.
match (eval cbv delta [y] in y) with
| context[@BaseTypes.remove_nonterminal ?a ?b ?c ?d]
  => set (z := @BaseTypes.remove_nonterminal a b c d) in (value of y)
end.
vm_compute in z; subst z; cbv iota in y.
match (eval cbv delta [y] in y) with
| context[@Lookup ?a ?b ?c]
  => set (z := @Lookup a b c) in (value of y)
end.
cbv [Lookup grammar_of_pregrammar json'_pregrammar list_to_productions Lookup_string option_rect] in z.
change Equality.string_beq with BooleanRecognizerOptimized.opt.opt.string_beq in z.
cbv [Lookup grammar_of_pregrammar json'_pregrammar list_to_productions Lookup_string option_rect BooleanRecognizerOptimized.opt.opt.string_beq] in z.
simpl @grammar_of_pregrammar in
Timeout 1 cbv [ParenBalancedGrammar.paren_balanced_correctness_type] in y.
Timeout 1 cbv beta iota delta [List.filter] in x.
Print List.filter.
unfold List.filter in x.
About ParenBalancedGrammar.paren_balanced_correctness_type.
repeat match (eval cbv delta [x] in x) with
       | context[@ParenBalancedGrammar.paren_balanced_correctness_type ?a ?b ?c ?d ?e]
         => let H := fresh in set (H := @ParenBalancedGrammar.paren_balanced_correctness_type a b c d e) in (value of x)
       end.
clear -x.
cbv beta zeta delta [ParenBalancedGrammar.paren_balanced_correctness_type] in H2.
cbv beta zeta iota delta [ParenBalancedGrammar.paren_balanced_nonterminals ParenBalancedGrammar.paren_balanced_nonterminals_of BaseTypes.nonterminal_carrierT RDPList.rdp_list_predata Carriers.default_nonterminal_carrierT FoldGrammar.fold_nt] in x.
Timeout 2 cbv beta zeta iota delta [BaseTypes.nonterminals_length BaseTypes.initial_nonterminals_data RDPList.rdp_list_initial_nonterminals_data fst List.map list_to_productions pregrammar_productions json'_pregrammar List.length Operations.List.up_to] in x.
Opaque FoldGrammar.fold_nt_step.
Timeout 2 simpl in x.
Transparent FoldGrammar.fold_nt_step.
Timeout 2 cbv beta iota zeta delta [FoldGrammar.fold_nt_step] in x.
Timeout 5 simpl @BaseTypes.is_valid_nonterminal in x.
cbv beta iota in x.
match (eval cbv delta [x] in x) with
| context[@BaseTypes.of_nonterminal ?a ?b ?c]
  => set (y := @BaseTypes.of_nonterminal a b c) in (value of x)
end.
vm_compute in y.
subst y.
match (eval cbv delta [x] in x) with
| context[@BaseTypes.remove_nonterminal ?a ?b ?c ?d]
  => set (y := @BaseTypes.remove_nonterminal a b c d) in (value of x)
end.
vm_compute in y.
subst y.
Timeout 5 cbv beta iota zeta delta [FoldGrammar.fold_productions' List.map list_to_productions ParenBalancedGrammar.paren_balanced_nonterminals_T BaseTypes.nonterminal_carrierT List.fold_right RDPList.rdp_list_predata pregrammar_productions Carriers.default_nonterminal_carrierT list_to_productions Lookup grammar_of_pregrammar Lookup_string option_rect List.find fst snd FoldGrammar.on_nil_productions (*ParenBalancedGrammar.paren_balanced_nonterminals_fold_data FoldGrammar.fold_production' FoldGrammar.on_nil_production (*FoldGrammar.combine_productions  FoldGrammar.fold_production' ParenBalancedGrammar.paren_balanced_nonterminals_fold_data (*FoldGrammar.combine_production*) FoldGrammar.on_nonterminal FoldGrammar.on_nil_production (*BaseTypes.of_nonterminal Compare_dec.gt_dec List.app*)*)*)] in  x;
change Equality.string_beq with BooleanRecognizerOptimized.opt.opt.string_beq in x;
cbv beta iota zeta delta [BooleanRecognizerOptimized.opt.opt.string_beq] in x.
match (eval cbv delta [x] in x) with
| context[@FoldGrammar.fold_nt' ?a ?b ?c ?d ?e ?f ?g]
  => set (y := @FoldGrammar.fold_nt' a b c d e f g)
end.
clear -y.
unfold ParenBalancedGrammar.paren_balanced_nonterminals_T, BaseTypes.nonterminal_carrierT, RDPList.rdp_list_predata, Carriers.default_nonterminal_carrierT in *.
Opaque FoldGrammar.fold_nt_step.
Timeout 2 simpl in y.
Transparent FoldGrammar.fold_nt_step.
Timeout 2 cbv beta iota zeta delta [FoldGrammar.fold_nt_step] in y.

Print FoldGrammar.fold_nt'.
set (z := Compare_dec.lt_dec 0 0) in (value of x).
hnf in z.
subst z.
cbv beta iota zeta in x.
vm_compute in z.
Timeout 5 simpl @Compare_dec.lt_dec in x.
Timeout 5 unfold bool_of_sumbool in x.
set (z :=
Timeout 5 cbv beta iota zeta delta [] in x.

change Equality.
Timeout 2 cbv beta iota zeta delta [BaseTypes.remove_nonterminal BaseTypes.of_nonterminal RDPList.rdp_list_predata] in x.
Timeout 2 vm_compute in x.
subst x.

cbv iota
Timeout 5 cbv beta iota zeta delta [ParenBalancedGrammar.paren_balanced_correctness_type fst snd] in H2.
Timeout 5 cbv beta iota zeta delta [ParenBalancedGrammar.paren_balanced''_nt] in H2.

Timeout 5 vm_compute in H2.
Set Printing Implicit.
Timeout 2 vm_compute in H4.
lazymatch (eval unfold c''' in c''') with
      | @possible_open_closes_pre ?G =>
                      pose (@possible_open_closes G) as c''''
end.
(*Print possible_open_closes.
*)
(*

lazy in c'''.*)
exfalso.
vm_compute in c''''.
Timeout 2 vm_compute in c'''.
Start Profiling. (lazy in c''''). Show Profile.
unfold possible_open_closes, possible_open_closes_pre in c''''.
unfold List.flat_map at 2 3 in (value of c'''').
cbv beta iota zeta delta [possible_open_closes possible_open_closes_pre maybe_open_closes pregrammar_productions grammar_of_pregrammar list_to_productions Lookup_string json'_pregrammar List.map fst snd] in c''''.
cbv beta iota zeta delta [possible_open_closes possible_open_closes_pre maybe_open_closes pregrammar_productions grammar_of_pregrammar list_to_productions Lookup_string json'_pregrammar List.map fst snd List.hd List.rev] in c''''.
cbv beta iota zeta delta [possible_open_closes possible_open_closes_pre maybe_open_closes pregrammar_productions grammar_of_pregrammar list_to_productions Lookup_string json'_pregrammar List.map fst snd List.hd List.rev List.app] in c''''.
vm_compute in c''''.
cbv b
change Equality.string_beq with BooleanRecognizerOptimized.opt.opt.string_beq in c''''.
cbv beta iota zeta delta [List.find] in c''''.
cbv beta iota zeta delta [fst snd BooleanRecognizerOptimized.opt.opt.string_beq option_rect] in c''''.

cbv beta iota zeta delta [List.find fst snd BooleanRecognizerOptimized.opt.opt.string_beq option_rect] in c''''.


Timeout 1 cbv beta iota zeta delta [BooleanRecognizerOptimized.opt.opt.string_beq app List.rev List.app List.fold_right] in c''''.
idtac.
lazy in c''''.
Print possible_open_closes_pre.

                  first [ subst c0; specialize (H eq_refl)
                        | fail 1 "Could not find a set of good brackets for the binary operation" ch ];
                  let c := match type of H with
                             | context[@default_list_of_next_bin_ops_opt_data ?HSLM ?HSL ?data]
                               => constr:(@default_list_of_next_bin_ops_opt_data HSLM HSL data)
                           end in
                  let c' := (eval cbv beta iota zeta delta [default_list_of_next_bin_ops_opt_data ParenBalanced.Core.is_open ParenBalanced.Core.is_close ParenBalanced.Core.is_bin_op bin_op_data_of_maybe List.hd List.map fst snd] in c) in
                  let c' := match c' with
                              | appcontext[@StringLike.get _ ?HSLM ?HSL]
                                => let HSLM' := head HSLM in
                                   let HSL' := head HSL in
                                   (eval cbv beta iota zeta delta [String StringLike.length StringLike.unsafe_get StringLike.get HSLM' HSL'] in c')
                              | _ => c'
                            end in
                  change c with c' in H;
                    first [ setoid_rewrite H
                          | let T := type of H in
                            fail 1 "Unexpeected failure to setoid_rewrite with" T ];
                    clear H.


      setoid_rewrite lem; [ | try solve [ solve_disjoint_side_conditions ].. ].
      Focus 4.
      lazymatch goal with
        | [ |- is_true (?d _ ?x ?y) ]
          => set (x' := x); set (y' := y)
      end.
      vm_compute in x'.
      vm_compute in y'.
      exfalso.
      clear -l.
      vm_compute in l.
      cbv beta iota zeta delta [pregrammar_productions DisjointLemmas.actual_possible_first_terminals DisjointLemmas.possible_first_terminals_of_production FoldGrammar.fold_production FoldGrammar.fold_production' List.map FoldGrammar.on_nonterminal DisjointLemmas.only_first_fold_data FoldGrammar.on_nil_production FoldGrammar.combine_production List.fold_right FoldGrammar.fold_nt DisjointLemmas.might_be_empty BaseTypes.initial_nonterminals_data RDPList.rdp_list_predata RDPList.rdp_list_initial_nonterminals_data fst snd Datatypes.length Operations.List.up_to BaseTypes.nonterminals_length FoldGrammar.fold_nt_step] in l.
      lazymatch (eval unfold l in l) with
      | appcontext[@FoldGrammar.fold_nt' ?Char ?T ?FGD ?G ?initial]
        => change (@FoldGrammar.fold_nt' Char T FGD G initial) with (@FoldGrammar.fold_nt_step Char T FGD G initial (@FoldGrammar.fold_nt' Char T FGD G)) in l
      end.
      Time cbv beta iota zeta delta [FoldGrammar.fold_nt_step BaseTypes.is_valid_nonterminal BaseTypes.of_nonterminal RDPList.rdp_list_predata RDPList.rdp_list_is_valid_nonterminal RDPList.rdp_list_of_nonterminal] in l.
      change Equality.string_beq with BooleanRecognizerOptimized.opt.opt.string_beq in l.

      cbv
      cbv beta iota zeta delta [pregrammar_productions DisjointLemmas.actual_possible_first_terminals DisjointLemmas.possible_first_terminals_of_production FoldGrammar.fold_production FoldGrammar.fold_production' List.map FoldGrammar.on_nonterminal DisjointLemmas.only_first_fold_data FoldGrammar.on_nil_production FoldGrammar.combine_production List.fold_right FoldGrammar.fold_nt DisjointLemmas.might_be_empty BaseTypes.initial_nonterminals_data RDPList.rdp_list_predata RDPList.rdp_list_initial_nonterminals_data fst snd Datatypes.length Operations.List.up_to BaseTypes.nonterminals_length FoldGrammar.fold_nt_step BaseTypes.is_valid_nonterminal BaseTypes.of_nonterminal FoldGrammar.fold_productions' BaseTypes.remove_nonterminal RDPList.rdp_list_is_valid_nonterminal RDPList.rdp_list_of_nonterminal RDPList.list_bin_eq Operations.List.first_index_default FoldGrammar.on_redundant_nonterminal option_rect grammar_of_pregrammar Lookup orb Operations.List.first_index_helper] in l.
      change Equality.string_beq with BooleanRecognizerOptimized.opt.opt.string_beq in l.
Set Printing Coercions.
cbv beta iota zeta delta [] in l.



      unfold FoldGrammar.fold_nt_step in
      Print FoldGrammar.fold_nt'.
      simpl in l.

      unfold FoldGrammar.fold_nt' in l; fold @FoldGrammar.fold_nt' in l.
      unfold FoldGrammar.fold_nt_step at 1 in (value of l).
      cbv beta iota zeta delta [pregrammar_productions DisjointLemmas.actual_possible_first_terminals DisjointLemmas.possible_first_terminals_of_production FoldGrammar.fold_production FoldGrammar.fold_production' List.map FoldGrammar.on_nonterminal DisjointLemmas.only_first_fold_data FoldGrammar.on_nil_production FoldGrammar.combine_production List.fold_right FoldGrammar.fold_nt DisjointLemmas.might_be_empty BaseTypes.initial_nonterminals_data RDPList.rdp_list_predata RDPList.rdp_list_initial_nonterminals_data fst snd Datatypes.length Operations.List.up_to BaseTypes.nonterminals_length FoldGrammar.fold_nt_step] in l.
      cbv beta iota zeta delta
      cbv beta iota zeta delta [] in l.
      cbv beta iota zeta delta [FoldGrammar.fold_nt_step] in l.
solve_disjoint_side_conditions.
                    [ | solve [ solve_disjoint_side_conditions ].. ]
             end.
Focus 2.
match goal with
 end.
          (DisjointLemmas.possible_terminals_of json_pregrammar nt)
          (DisjointLemmas.actual_possible_first_terminals
             (DisjointLemmas.possible_first_terminals_of_production json_pregrammar its)) ->
        refine
          {splits
Focus 2.


Locate "-".
Set Printing Coercions.
list_to_grammar
change (z k = e);

match


Local Ltac special_solve_side z :=
lazymatch goal with
| [ H : is_true (ValidReflective.grammar_rvalid ?G) |- is_true (ValidReflective.grammar_rvalid ?G) ]
  => exact H
| [ |- Carriers.default_to_production ?k = ?e ]
  => change (z k = e);
       unfold z;
       simpl @fst;
       match goal with
       | [ |- context[Operations.List.first_index_error ?f ?ls] ]
         => let c := constr:(Operations.List.first_index_error f ls) in
            let c' := (eval cbv in c) in
            change c with c'
       end;
       unfold option_rect;
       simpl @snd;
       unfold List.nth at 2 3;
       unfold List.length, minus;
       unfold List.nth;
       unfold Operations.List.drop;
       reflexivity
| [ |- is_true (Operations.List.disjoint ?beq ?A ?B) ]
  => timeout 10 vm_compute; reflexivity
end.

      Set Printing Implicit.
      set (x := json_grammar).
      unfold json_grammar, list_to_grammar in x.
      repeat match eval unfold x in x with
             | context[Operations.List.uniquize ?beq ?ls]
               => change (Operations.List.uniquize beq ls) with ls in (value of x)
             | _ => progress simpl @List.hd in x
             end.
      Unset Printing Implicit.
simpl @List.map in x.
unfold list_to_productions in x.
    repeat match eval unfold x in x with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of x)
           | _ => progress simpl @List.hd in x
           end.
    simpl @List.map in x.
{ Time lazy.
  reflexivity. }
set (z := Carriers.default_to_production (G := x)).
unfold Carriers.default_to_production, Carriers.default_to_nonterminal in z.
simpl @Valid_nonterminals in z.
    repeat match eval unfold z in z with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of z)
           end.
unfold Lookup, x in z.
    repeat match eval unfold z in z with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of z)
           end.
Time let lem' := constr:(@refine_disjoint_search_for_idx HSLM HSL HSI HSLP HSIIP) in
pose proof lem' as lem.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.

match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len _] ]
        => specialize (fun idx nt its => lem G str offset len nt its idx H')
end.
setoid_rewrite lem.
change (Carriers.default_to_production (G := x)) with z in lem.

2:unfold z;
       simpl @fst;
       match goal with
       | [ |- context[Operations.List.first_index_error ?f ?ls] ]
         => let c := constr:(Operations.List.first_index_error f ls) in
            let c' := (eval cbv in c) in
            change c with c'
       end;
       unfold option_rect;
       simpl @snd;
       unfold List.nth at 2 3;
       unfold List.length, minus;
       unfold List.nth;
       unfold Operations.List.drop.




















match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
setoid_rewrite lem by ltac:(special_solve_side z).
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Focus 2.
match goal with
end.
Focus 2.
Time vm_compute.
match goal with
unfold List.nth at
Time lazy.
reflexivity.
Focus 2.
unfold Carriers.default_to_production, Carriers.default_to_nonterminal.
simpl @Valid_nonterminals.
    repeat match goal with
           | [ |- context[Operations.List.uniquize ?beq ?ls] ]
             => change (Operations.List.uniquize beq ls) with ls
           end.
simpl @fst.
unfold List.nth at 2 3.
simpl @snd.
unfold Lookup, x.
match goal with
| [ |- context[Operations.List.first_index_error ?f ?ls] ]
  => let c := constr:(Operations.List.first_index_error f ls) in
     let c' := (eval cbv in c) in
     change c with c'
end.
unfold option_rect.
simpl List.length.
simpl minus.
unfold List.nth.
simpl.
reflexivity.
Focus 2.
unfold DisjointLemmas.possible_terminals_of.
unfold DisjointLemmas.possible_first_terminals_of_production.
unfold FoldGrammar.fold_production.
unfold FoldGrammar.fold_production'.
unfold List.map.
unfold FoldGrammar.on_nonterminal.
unfold DisjointLemmas.only_first_fold_data.
unfold List.fold_right.
unfold FoldGrammar.combine_production, FoldGrammar.on_nil_production.
unfold DisjointLemmas.actual_possible_first_terminals at 1.
unfold DisjointLemmas.actual_possible_first_terminals at 2.
unfold FoldGrammar.fold_nt.
unfold DisjointLemmas.actual_possible_first_terminals at 2.
unfold DisjointLemmas.actual_possible_first_terminals at 5.
unfold DisjointLemmas.actual_possible_first_terminals at 7.
unfold BaseTypes.nonterminals_length, BaseTypes.initial_nonterminals_data.
unfold RDPList.rdp_list_predata.
unfold RDPList.rdp_list_initial_nonterminals_data.
    repeat match goal with
           | [ |- context[Operations.List.uniquize ?beq ?ls] ]
             => change (Operations.List.uniquize beq ls) with ls
           end.
simpl @Valid_nonterminals.
simpl @List.length.
simpl @Operations.List.up_to.
unfold FoldGrammar.fold_nt'.
unfold FoldGrammar.fold_nt_step at 1 3 5.
cbv beta iota zeta delta.
reflexivity.

Focus 2.
fold @FoldGrammar.fold_nt'.
unfold
match goal with
| [ |- context[
Timeout 5 2:reflexivity.
      lazymatch goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => pose (fun nt its => lem G str offset len nt its idx)
      end.


    lazymatch goal with
           | [ |- context[v ?nt] ]
             => let z' := fresh "z'" in
                set (z' := v nt);
                  unfold v in z';
                  match eval unfold z' in z' with
                  | context[Operations.List.first_index_error ?f ?ls]
                    => let c := constr:(Operations.List.first_index_error f ls) in
                       let c' := (eval cbv in c) in
                       change c with c' in (value of z')
                  end;
                  unfold option_rect in z';
                  unfold List.nth at 2 3 in (value of z');
                  unfold Datatypes.length in z';
                  simpl in z';
                  subst z'
           end.
    simpl_lookup v.
      unfold List.nth at 2 3 in (value of v).
      change (Valid_nonterminals x) with y in (value of v).
    unfold y in v.
    unfold Lookup, x, list_to_productions in v.
    simpl @List.map in v.

      simplify_parser_splitter'.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
repeat match goal with
       | [ |- context[If ?b Then _ Else _] ]
         => not is_var b;
              let b' := fresh "b" in set (b' := b)
       | [ |- context[If _ Then Pick ?P Else _] ]
         => not is_var P; let b' := fresh "P" in set (b' := P)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
Start Profiling.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
Show Profile.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => move P at bottom; pose v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => move P at bottom; pose v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => move P at bottom; pose v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
do 9 try lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
do 9 try lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
do 9 try lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
2:subst_body.


 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      finish honing parser method.
    }

    finish_Sharpening_SplitterADT.

  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json_grammar HSL).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ String.string_stringlike _ _). (* 0.82 s *)
Defined.

Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.

Print json_parser_ocaml.

Recursive Extraction json_parser_ocaml.

Definition main_json := premain json_parser.
Definition main_json_ocaml := premain_ocaml json_parser_ocaml.

Parameter reference_json_parser : Coq.Strings.String.string -> bool.
Parameter reference_json_parser_ocaml : Ocaml.Ocaml.string -> bool.
Extract Constant reference_json_parser
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (List.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".
Extract Constant reference_json_parser_ocaml
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (String.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".

Definition main_json_reference := premain reference_json_parser.
Definition main_json_reference_ocaml := premain_ocaml reference_json_parser_ocaml.

(*
(* val needs_b : bool Pervasives.ref;; *)
let needs_b = Pervasives.ref false;;

let chan = match Array.length Sys.argv with
| 0 | 1 -> Pervasives.stdin
| 2 -> let chan = Pervasives.open_in Sys.argv.(1)
       in Pervasives.at_exit (fun () -> Pervasives.close_in chan);
	  chan
| argc -> Pervasives.exit argc;;

(* val line : string;; *)
let line = Pervasives.input_line chan;;

String.iter (fun ch ->
  match ch, !needs_b with
  | 'a', false -> needs_b := true; ()
  | 'b', true  -> needs_b := false; ()
  | _, _       -> Pervasives.exit 1)
  line;;

Pervasives.exit 0;;
*)
(*
Definition test0 := json_parser "".
Definition test1 := json_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := json_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
*)
