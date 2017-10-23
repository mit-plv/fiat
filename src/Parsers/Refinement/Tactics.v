Require Export Coq.NArith.BinNat.
Require Export Fiat.ADTRefinement.
Require Export Fiat.ADTNotation.BuildADT.
Require Export Fiat.ADTRefinement.GeneralBuildADTRefinements.
Require Export Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Export Fiat.ADTNotation.BuildADTSig.
Require Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.
Require Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflectiveOpt.
Require Export Fiat.Parsers.ParserADTSpecification.
Require Export Fiat.Parsers.Refinement.ReductionTactics.
Require Export Fiat.Parsers.Refinement.PreTactics.
Require Export Fiat.Parsers.ContextFreeGrammar.Notations.
Require Export Fiat.Parsers.StringLike.String.

Export Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.PrettyNotations.

Require Import Fiat.Parsers.Refinement.DisjointLemmasEarlyDeclarations.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Common.Equality.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.Refinement.FinishingLemma.

Notation hiddenT := (ADTSig.methodType _ _ _).

Ltac finish_honing_by_eq tac
  := solve [ repeat (subst
                       || rewrite refineEquiv_pick_eq'
                       || (simplify with monad laws)
                       || (simpl @fst; simpl @snd)
                       || tac);
             change @fst with @myfst;
             change @snd with @mysnd;
             match goal with
               | [ |- refine (ret _) _ ] => finish honing
             end  ].

Ltac parser_hone_cleanup :=
  try (hone constructor "new"; [ finish_honing_by_eq idtac | ]);
  try (hone method "to_string"; [ finish_honing_by_eq idtac | ]);
  try (hone method "is_char"; [ finish_honing_by_eq idtac | ]);
  try (hone method "length"; [ finish_honing_by_eq idtac | ]);
  try (hone method "take"; [ finish_honing_by_eq idtac | ]);
  try (hone method "drop"; [ finish_honing_by_eq idtac | ]).

Ltac start_honing_ri repInv :=
  eapply SharpenStep;
  [ solve [ apply FirstStep ] | ];
  hone representation using repInv;
  parser_hone_cleanup.

Ltac change_with_cbv c :=
    let c' := (eval cbv in c) in
    change c with c'.

Ltac replace_by_vm_compute_opt0_proj v :=
  idtac;
  let vH := fresh in
  let H := fresh in
  let v'H := fresh in
  let v' := (eval vm_compute in v) in
  set (vH := v);
  pose v' as v'H;
  assert (H : v'H = vH) by (subst vH v'H; clear; vm_cast_no_check (eq_refl v'));
  clearbody vH;
  destruct H;
  cbv [opt0.fst opt0.snd v'H];
  clear v'H.

Ltac start_honing :=
  eapply SharpenStep;
  [ solve [ apply FirstStep ] | ];
  unfold opt_rindexed_spec;
  (*
  let p' := fresh "p'" in
  match goal with
  | [ |- context[pregrammar_productions ?G] ]
    => let p := constr:(pregrammar_productions G) in
       set (p' := p);
       hnf in p'
  end; *)
  lazymatch goal with
  | [ |- context[opt2.fold_right _ _ ?ls] ]
    => replace_with_vm_compute_by_set ls
  end;
  do_disjoint_precomputations ()(*;
  cbv [opt2.fold_right opt.map opt2.ret_cases_BoolDecR opt.fst opt.snd];
  change (orb false) with (fun x : bool => x); cbv beta*).

Tactic Notation "start" "honing" "parser" "representation" "using" open_constr(repInv)
  := (idtac;
      lazymatch goal with
      | [ |- FullySharpened _ ]
        => (eapply FullySharpened_Start; [ start_honing_ri repInv | | ])
      | _ => start_honing_ri repInv
      end).

Tactic Notation "start" "honing" "parser" "using" "indexed" "representation"
  := (idtac;
      lazymatch goal with
      | [ |- FullySharpened _ ]
        => (eapply FullySharpened_Start; [ start_honing | | ])
      | _ => start_honing
      end).

Tactic Notation "finish" "honing" "parser" "method"
  := finish_honing_by_eq parser_pull_tac.

Ltac finish_Sharpening_SplitterADT
  := solve [ refine finish_Sharpening_SplitterADT ].

Lemma simplify_monad_laws_first_step {A B C} (c : Comp A) (f : A -> B * C) v
      (H : refine (x0 <- c; ret (f x0)) v)
  : refine (r_o' <- a <- c; ret (f a); r_n' <- { r_n0 | fst r_o' = r_n0 }; ret (r_n', snd r_o'))
           v.
Proof.
  simplify with monad laws.
  setoid_rewrite General.refine_pick_eq'.
  simplify with monad laws.
  rewrite <- H.
  apply General.refine_under_bind; intros.
  rewrite <- surjective_pairing; reflexivity.
Qed.

Ltac apply_splitter_tower_lemma :=
  let lem := fresh in
  change @fst with @opt0.fst;
  change @snd with @opt0.snd;
  lazymatch goal with
  | [ |- refine (x0 <- (opt2.fold_right
                          (fun a a0 => If @?test a Then @?test_true a Else a0)
                          ?base
                          ?ls);
                 (@?r_o x0))
                ?retv ]
    => pose proof (@refine_opt2_fold_right_no_unif _ _ (@opt0.snd _ _) r_o retv test test_true base ls) as lem
  end;
  cbv [make_tower_no_unif opt0.snd opt0.fst] in lem |- *;
  eapply lem; clear lem;
  intros.

Ltac simplify_parser_splitter'' :=
  first [ progress autounfold with parser_sharpen_db;
          cbv beta iota zeta;
          simpl @Operations.List.uniquize;
          simpl @List.fold_right
        | progress simpl @ContextFreeGrammar.Reflective.opt.N_of_ascii
        | progress simplify with monad laws
        (*| progress unguard
        | progress change (orb false) with (fun x : bool => x); cbv beta
        | progress change (orb true) with (fun x : bool => true); cbv beta
        | progress change (andb false) with (fun x : bool => false); cbv beta
        | progress change (andb true) with (fun x : bool => x); cbv beta
        | progress change (Common.opt2.orb false) with (fun x : bool => x); cbv beta
        | progress change (Common.opt2.orb true) with (fun x : bool => true); cbv beta
        | progress change (Common.opt2.andb false) with (fun x : bool => false); cbv beta
        | progress change (Common.opt2.andb true) with (fun x : bool => x); cbv beta
        | rewrite !opt2.orb_false_r
        | rewrite <- !opt2.andb_orb_distrib_r
        | rewrite <- !opt2.andb_orb_distrib_r
        | rewrite <- !opt2.andb_orb_distrib_l
        | rewrite <- !opt2.orb_andb_distrib_r
        | rewrite <- !opt2.orb_andb_distrib_l
        | rewrite <- !opt2.andb_assoc
        | rewrite <- !opt2.orb_assoc
        | rewrite <- !opt2.andb_orb_distrib_r_assoc
        | rewrite !if_aggregate
        | rewrite !opt2.beq_0_1_leb
        | rewrite !opt2.beq_S_leb
        | idtac;
          match goal with
            | [ |- context[If ?b Then ?x Else If ?b' Then ?x Else _] ]
              => idtac
          end;
          progress repeat setoid_rewrite if_aggregate
        | rewrite !if_aggregate2 by solve_prod_beq
        | rewrite !if_aggregate3 by solve_prod_beq
        | progress parser_pull_tac
        | progress (simpl @fst; simpl @snd)*) ].

Ltac simplify_parser_splitter' :=
  lazymatch goal with
  | [ |- refine (r_o' <- a <- ?c; ret (@?f a); r_n' <- { r_n0 | fst r_o' = r_n0 }; ret (r_n', snd r_o'))
                ?v ]
    => apply (@simplify_monad_laws_first_step _ _ _ c f v);
       do_disjoint_precomputations ();
       apply_splitter_tower_lemma
  | [ |- refine { splits : list nat | _ } ?e ]
    => first [ is_evar e
             | simplify_parser_splitter'' ]
  | _ => simplify_parser_splitter''
  end.

Tactic Notation "simplify" "parser" "splitter" :=
  repeat simplify_parser_splitter'.

Ltac splitter_start :=
  idtac;
  let lem := match goal with
             | [ |- FullySharpened (@string_spec _ ?G _ ?HSLM ?HSL) ]
               => constr:(@FirstStep_splits G HSLM HSL)
             end in
  let lem := constr:(lem _ _) in
  eapply lem; [ intros ???? | cbv [opt_rindexed_spec_gen] ];
  [ let ev := match goal with
              | [ |- refine ?x ?y ]
                => head y
              end in
    is_evar ev;
    let e := fresh in
    set (e := ev);
    lazymatch goal with
    | [ |- context[opt2.fold_right _ _ ?ls] ]
      => replace_with_vm_compute_by_set ls
    end;
    do_disjoint_precomputations ();
    apply_splitter_tower_lemma
  | ];
  instantiate; cbv beta.
(*start sharpening ADT;
  start honing parser using indexed representation;
  hone method "splits";
  [ simplify parser splitter
  | ].*)

Ltac splitter_finish :=
  idtac;
  lazymatch goal with
  | [ |- refine _ _ ] => finish honing parser method
  | [ |- Sharpened _ ] => finish_Sharpening_SplitterADT
  end.

(** For [start honing ...] *)
Global Arguments opt3.fold_right : simpl never.
Global Arguments opt2.ret_cases_BoolDecR !_ !_ / .
Global Arguments opt2.fold_right : simpl never.
Global Arguments opt.map : simpl never.
