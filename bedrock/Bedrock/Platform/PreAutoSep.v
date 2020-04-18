Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSepExt.
Export AutoSepExt.

Ltac refold' A :=
  progress change (fix length (l : list A) : nat :=
    match l with
      | nil => 0
      | _ :: l' => S (length l')
    end) with (@length A) in *
  || (progress change (fix app (l0 m : list A) : list A :=
    match l0 with
      | nil => m
      | a1 :: l1 => a1 :: app l1 m
    end) with (@app A) in *)
  || (progress change (fix rev (l : list W) : list W :=
    match l with
      | nil => nil
      | x8 :: l' => (rev l' ++ x8 :: nil)%list
    end) with (@rev A) in *)
  || (progress change (fix rev_append (l l' : list A) : list A :=
    match l with
      | nil => l'
      | a1 :: l0 => rev_append l0 (a1 :: l')
    end) with (@rev_append A) in *).

Ltac refold :=
  fold plus in *; fold minus in *;
    repeat match goal with
             | [ _ : list ?A |- _ ] =>
               match A with
                 | _ => refold' A
                 | W => refold' (word 32)
               end
             | [ |- context[match ?X with nil => ?D | x :: _ => x end] ] =>
               change (match X with nil => D | x :: _ => x end) with (List.hd D X)
             | [ |- context[match ?X with nil => nil | _ :: x => x end] ] =>
               change (match X with nil => nil | _ :: x => x end) with (List.tl X)
           end.

Section Note_.
  Variable imps : LabelMap.t assert.
  Variable mn : string.

  Import DefineStructured.
  Transparent evalInstrs.

  Definition Note_ (P : Prop) : cmd imps mn.
    red; refine (fun pre => {|
      Postcondition := (fun st => pre st /\ [| P |])%PropX;
      VerifCond := P :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (nil, Uncond (RvLabel (mn, Local Exit)))) :: nil
      |}
    |}); abstract (struct; repeat esplit; eauto; propxFo).
  Defined.
End Note_.

Definition Note__ (P : Prop) : chunk := fun _ _ =>
  Structured nil (fun _ _ _ => Note_ _ _ P).

Notation "'Note' [ P ]" := (Note__ P) (no associativity, at level 95) : SP_scope.

Section SomethingStar.
  Variable imps : LabelMap.t assert.
  Variable mn : string.

  Fixpoint augment (specs : codeSpec W (settings * state)) (stn : settings) (ls : list (string * string)) : Prop :=
    match ls with
      | nil => True
      | (mn, f) :: ls =>
        match LabelMap.find (mn, Global f) imps with
          | None => True
          | Some p => (exists pc, stn.(Labels) (mn, Global f) = Some pc /\ specs pc = Some p) /\ augment specs stn ls
        end
    end.

  Lemma prove_augment : forall specs stn ls,
    (forall mn f (pre : assert),
      LabelMap.MapsTo (mn, Global f) pre imps
      -> exists w : W, Labels stn (mn, Global f) = Some w /\ specs w = Some pre)
    -> augment specs stn ls.
    induction ls; simpl; intuition.
    case_eq (LabelMap.find (a0, Global b) imps); intuition.
    apply LabelMap.find_2 in H1; eauto.
  Qed.

  Import DefineStructured.

  Variable ls : list (string * string).

  Transparent evalInstrs.

  Hint Resolve prove_augment.

  Section IGotoStar.
    Variable rv : rvalue.

    Definition IGotoStar_ : cmd imps mn.
      red; refine (fun pre => {|
        Postcondition := (fun _ => [|False|])%PropX;
        VerifCond := (forall specs stn st, interp specs (pre (stn, st))
          -> augment specs stn ls
          -> match evalRvalue stn st rv with
               | None => rvalueCrashes rv
               | Some w => exists pre', specs w = Some pre'
                 /\ interp specs (pre' (stn, st))
             end) :: nil;
        Generate := fun Base Exit => {|
          Entry := 0;
          Blocks := (pre, (nil, Uncond rv)) :: nil
        |}
      |}); abstract (solve [ struct
        | intros; repeat match goal with
                           | [ H : vcs nil |- _ ] => clear H
                           | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
                           | [ |- List.Forall _ _ ] => constructor; simpl
                           | [ |- blockOk _ _ _ ] => hnf; intros
                           | [ H : forall x y z, interp _ _ -> augment _ _ _ -> _, H' : interp _ _ |- _ ] =>
                             specialize (H _ _ _ H');
                               match type of H with
                                 | ?P -> _ => assert P by auto; intuition simpl
                               end
                           | [ H : match ?X with None => _ | _ => _ end |- _ ] => destruct X; intuition
                           | [ H : Logic.ex _ |- _ ] => destruct H; intuition eauto
                         end ]).
    Defined.
  End IGotoStar.

  Section AssertStar.
    Variable post : assert.

    Definition AssertStar_ : cmd imps mn.
      red; refine (fun pre => {|
        Postcondition := post;
        VerifCond := (forall stn_st specs, interp specs (pre stn_st)
          -> augment specs (fst stn_st) ls
          -> interp specs (post stn_st)) :: nil;
        Generate := fun Base Exit => {|
          Entry := 0;
          Blocks := (pre, (nil, Uncond (RvLabel (mn, Local Exit)))) :: nil
        |}
      |}); abstract solve [ struct
        | intros; repeat match goal with
                           | [ H : vcs nil |- _ ] => clear H
                           | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
                           | [ |- List.Forall _ _ ] => constructor; simpl
                           | [ |- blockOk _ _ _ ] => hnf; intros
                           | [ H : forall x y z, interp _ _ -> augment _ _ _ -> _, H' : interp _ _ |- _ ] =>
                             specialize (H _ _ _ H');
                               match type of H with
                                 | ?P -> _ => assert P by auto; intuition simpl
                               end
                           | [ H : match ?X with None => _ | _ => _ end |- _ ] => destruct X; intuition
                           | [ H : Logic.ex _ |- _ ] => destruct H; intuition eauto
                           | [ H : forall l : LabelMap.key, _ |- _ ] => destruct (H (mn, Local Exit) post) as [ ? [ ] ];
                             [ solve [ auto ] | ]; do 2 esplit; [ unfold evalBlock; simpl;
                               match goal with
                                 | [ H : _ |- _ ] => solve [ rewrite H; eauto ]
                               end | simpl; do 2 esplit; eauto; match goal with
                                                                  | [ H : _ |- _ ] => apply H; auto
                                                                end ]
                         end ].
    Defined.
  End AssertStar.
End SomethingStar.

Definition IGotoStar ls (rv : rvalue') : chunk := fun ns _ =>
  Structured nil (fun _ _ _ => IGotoStar_ _ _ ls (rv ns)).

Notation "'IGoto*' [ l1 , .. , lN ] rv" := (IGotoStar (cons l1 (.. (cons lN nil) ..)) rv) (no associativity, at level 95) : SP_scope.

Definition AssertStar ls (post : list string -> nat -> assert) : chunk := fun ns res =>
  Structured nil (fun _ _ _ => AssertStar_ _ _ ls (post ns res)).

Local Notation INV := (fun inv => inv true (fun w => w)).

Notation "'Assert*' [ l1 , .. , lN ] [ post ]" := (AssertStar (cons l1 (.. (cons lN nil) ..)) (INV post)) (no associativity, at level 95) : SP_scope.

Require Import Coq.Bool.Bool.

Definition localsInvariantCont (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    ExX, Ex vs, qspecOut (pre (sel vs) st#Rv) (fun pre =>
      ![ ^[locals ("rp" :: ns) vs res sp * pre] * #0 ] st).

Notation "'PREonly' [ vs ] pre" := (localsInvariantCont (fun vs _ => pre%qspec%Sep))
  (at level 89).

Notation "'PREonly' [ vs , rv ] pre" := (localsInvariantCont (fun vs rv => pre%qspec%Sep))
  (at level 89).

Notation "'bfunctionNoRet' name () [ p ] b 'end'" :=
  (let p' := p in
   let vars := nil in
   let b' := b%SP in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := ((fun _ _ =>
        Structured nil (fun im mn _ => Structured.Assert_ im mn (Precondition p' (Some vars))));;
      (fun ns res => b' ns (res - (List.length vars - List.length (Formals p')))%nat))%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Notation "'bfunctionNoRet' name ( x1 , .. , xN ) [ p ] b 'end'" :=
  (let p' := p in
   let vars := cons x1 (.. (cons xN nil) ..) in
   let b' := b%SP in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := ((fun _ _ =>
        Structured nil (fun im mn _ => Structured.Assert_ im mn (Precondition p' (Some vars))));;
      (fun ns res => b' ns (res - (List.length vars - List.length (Formals p')))%nat))%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

(* added Conditional *)
Require Import Bedrock.Platform.Conditional.
Export Conditional.

Ltac vcgen_simp := cbv beta iota zeta delta [map app imps
  LabelMap.add Entry Blocks Postcondition VerifCond
  Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_
  Structured.If_ Structured.While_ Goto_ Structured.Call_ IGoto
  setArgs Programming.Reserved Programming.Formals Programming.Precondition
  importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
  List.fold_left ascii_lt string_lt label'_lt
  LabelKey.compare' LabelKey.compare LabelKey.eq_dec
  LabelMap.find
  toCmd Seq Instr Diverge Fail Skip Assert_
  Programming.If_ Programming.While_ Goto Programming.Call_ RvImm'
  Assign' localsInvariant localsInvariantCont
  regInL lvalIn immInR labelIn variableSlot string_eq ascii_eq
  andb eqb qspecOut
  ICall_ Structured.ICall_
  Assert_ Structured.Assert_
  LabelMap.Raw.find LabelMap.this LabelMap.Raw.add
  LabelMap.empty LabelMap.Raw.empty string_dec
  Ascii.ascii_dec string_rec string_rect sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym
  fst snd labl
  Ascii.N_of_ascii Ascii.N_of_digits N.compare Nmult Pos.compare Pos.compare_cont
  Pos.mul Pos.add LabelMap.Raw.bal
  Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
  ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max LabelMap.Raw.height
  ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max
  ZArith_dec.Zcompare_rec ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
  ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect
  COperand1 CTest COperand2 Pos.succ
  makeVcs
  Note_ Note__
  IGotoStar_ IGotoStar AssertStar_ AssertStar
  Cond_ Cond
].

Ltac vcgen :=
(*TIME time "vcgen:structured_auto" ( *)
  structured_auto vcgen_simp
(*TIME ) *);
(*TIME time "vcgen:finish" ( *)
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold
(*TIME ) *).

Hint Extern 1 => tauto : contradiction.
Hint Extern 1 => congruence : contradiction.

Ltac sep_easy := auto with contradiction.

Lemma frame_reflexivity : forall pcT stateT p q specs,
  q = (fun pr => p (fst pr) (snd pr))
  -> himp (pcType := pcT) (stateType := stateT) specs p (fun st m => q (st, m)).
  intros; hnf; simpl; intros; subst.
  apply Imply_I; eauto.
Qed.

Ltac rereg :=
  repeat match goal with
           | [ _ : context[Regs (match ?st with
                                   | (_, y) => y
                                 end) ?r] |- _ ] =>
             change (Regs (let (_, y) := st in y) r) with (st#r) in *
           | [ |- context[Regs (match ?st with
                                  | (_, y) => y
                                end) ?r] ] =>
             change (Regs (let (_, y) := st in y) r) with (st#r) in *
         end.

Ltac sep_firstorder := sep_easy;
  repeat match goal with
           | [ H : Logic.ex _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- Logic.ex _ ] => sep_easy; eexists
           | [ |- _ /\ _ ] => split
           | [ |- forall x, _ ] => intro
           | [ |- _ = _ ] => reflexivity
           | [ |- himp _ _ _ ] => reflexivity
             || (apply frame_reflexivity; try match goal with
                                                | [ |- _ = ?X ] => instantiate (1 := X)
                                              end; apply refl_equal)
         end; sep_easy; autorewrite with sepFormula; rereg; try subst.

Require Import Coq.NArith.NArith.
Import TacPackIL.

Ltac hints_ext_simplifier hints := fun s1 s2 s3 H =>
  match H with
  | tt =>
      cbv beta iota zeta
       delta [s1 s2 s3 hints
         (** Symbolic Evaluation **)
         SymIL.MEVAL.PredEval.fold_args
         SymIL.MEVAL.PredEval.fold_args_update SymIL.MEVAL.PredEval.pred_read_word
         SymIL.MEVAL.PredEval.pred_write_word SymIL.MEVAL.PredEval.pred_read_byte SymIL.MEVAL.PredEval.pred_write_byte
         SymIL.MEVAL.LearnHookDefault.LearnHook_default
         SymIL.IL_ReadWord SymIL.IL_WriteWord SymIL.IL_ReadByte SymIL.IL_WriteByte
         SymILTac.unfolder_LearnHook
         SymIL.MEVAL.Composite.MemEvaluator_composite
         SymIL.MEVAL.Default.smemeval_read_word_default
         SymIL.MEVAL.Default.smemeval_write_word_default
         SymIL.sym_evalInstrs
         SymIL.sym_evalInstr SymIL.sym_evalLval SymIL.sym_evalRval
         SymIL.sym_evalLoc SymIL.sym_evalStream SymIL.sym_assertTest
         SymIL.sym_setReg SymIL.sym_getReg
         SymIL.SymMem SymIL.SymRegs SymIL.SymPures
(*         SymIL.SymVars SymIL.SymUVars *)
         SymIL.stateD
         SymILTac.quantifyNewVars
         SymILTac.unfolder_LearnHook
         ILAlgoTypes.Hints ILAlgoTypes.Prover
         SymIL.MEVAL.sread_word SymIL.MEVAL.swrite_word SymIL.MEVAL.sread_byte SymIL.MEVAL.swrite_byte
         ILAlgoTypes.MemEval ILAlgoTypes.Env ILAlgoTypes.Algos
         (*SymIL.quantifyNewVars*)
         ILAlgoTypes.Algos ILAlgoTypes.Hints ILAlgoTypes.Prover

         SymEval.quantD SymEval.appendQ
         SymEval.qex SymEval.qall
         SymEval.gatherAll SymEval.gatherEx
         SymILTac.sym_eval

         (** ILEnv **)
         ILEnv.comparator ILEnv.fPlus ILEnv.fMinus ILEnv.fMult
         ILEnv.bedrock_types_r ILEnv.bedrock_funcs_r
         ILEnv.bedrock_types
         ILEnv.BedrockCoreEnv.core
         ILEnv.BedrockCoreEnv.pc ILEnv.BedrockCoreEnv.st
         ILEnv.bedrock_type_W ILEnv.bedrock_type_nat
         ILEnv.bedrock_type_setting_X_state
         ILEnv.bedrock_type_state
(*         ILEnv.bedrock_type_test *)
         ILEnv.bedrock_type_reg

(*         ILEnv.test_seq *)
         ILEnv.reg_seq
         ILEnv.W_seq

         ILEnv.word_nat_r
         ILEnv.word_state_r
(*         ILEnv.word_test_r *)

         ILEnv.wplus_r
         ILEnv.wminus_r
         ILEnv.wmult_r
(*         ILEnv.word_test_r *)
(*         ILEnv.wcomparator_r *)
         ILEnv.Regs_r
         ILEnv.wlt_r
         ILEnv.natToW_r


         (** Env **)
         Env.repr_combine Env.default Env.footprint Env.repr'
         Env.updateAt Env.nil_Repr Env.repr Env.updateAt
         Env.repr_combine Env.footprint Env.default Env.repr

         (** Expr **)
         Expr.Range Expr.Domain Expr.Denotation Expr.Impl Expr.Eqb
         Expr.exists_subst Expr.forallEach Expr.existsEach
         Expr.AllProvable Expr.AllProvable_gen
         Expr.AllProvable_and Expr.AllProvable_impl
         Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
         Expr.liftExpr Expr.lookupAs
         Expr.Provable Expr.tvar_val_seqb
         Expr.Provable Expr.tvarD
         Expr.tvar_rec Expr.tvar_rect
         Expr.Default_signature Expr.EmptySet_type
         Expr.expr_seq_dec
         Expr.Eqb Expr.liftExpr Expr.exprSubstU
         Expr.typeof Expr.typeof_env
         Expr.typeof_sig Expr.typeof_funcs
         Expr.expr_ind
         Expr.get_Eq
         Expr.const_seqb
         Expr.tvar_seqb
         Expr.tvar_val_seqb_correct
         Expr.tvar_seqb_correct
         Expr.mentionsU
         ReifyExpr.default_type

         (** ExprUnify **)
         CancelIL.U.exprUnify CancelIL.U.exprUnify_recursor
         CancelIL.U.exprInstantiate CancelIL.U.subst_exprInstantiate
         CancelIL.U.Subst_lookup CancelIL.U.subst_lookup
         CancelIL.U.Subst_empty CancelIL.U.subst_empty
         CancelIL.U.Subst_set CancelIL.U.subst_set
         CancelIL.U.Subst_equations
         CancelIL.U.Subst_size
         CancelIL.U.dep_in

         CancelIL.U.FM.Raw.height CancelIL.U.FM.Raw.cardinal CancelIL.U.FM.Raw.assert_false CancelIL.U.FM.Raw.create
         CancelIL.U.FM.Raw.bal CancelIL.U.FM.Raw.remove_min CancelIL.U.FM.Raw.merge CancelIL.U.FM.Raw.join
         CancelIL.U.FM.Raw.t_left CancelIL.U.FM.Raw.t_opt CancelIL.U.FM.Raw.t_right
         CancelIL.U.FM.Raw.cardinal CancelIL.U.FM.Raw.empty CancelIL.U.FM.Raw.is_empty
         CancelIL.U.FM.Raw.mem CancelIL.U.FM.Raw.find
         CancelIL.U.FM.Raw.add  CancelIL.U.FM.Raw.remove
         CancelIL.U.FM.Raw.fold CancelIL.U.FM.Raw.map CancelIL.U.FM.Raw.mapi CancelIL.U.FM.Raw.map2

         CancelIL.U.FM.this CancelIL.U.FM.is_bst
         CancelIL.U.FM.empty CancelIL.U.FM.is_empty
         CancelIL.U.FM.add CancelIL.U.FM.remove
         CancelIL.U.FM.mem CancelIL.U.FM.find
         CancelIL.U.FM.map CancelIL.U.FM.mapi CancelIL.U.FM.map2
         CancelIL.U.FM.elements CancelIL.U.FM.cardinal CancelIL.U.FM.fold
         CancelIL.U.FM.equal
         CancelIL.U.FM.E.eq_dec

         (** Unfolder **)
         Unfolder.FM.empty Unfolder.FM.add Unfolder.FM.remove
         Unfolder.FM.fold Unfolder.FM.map
         Unfolder.FM.find
         UNF.Vars UNF.UVars UNF.Heap
         UNF.LEM.Foralls UNF.LEM.Hyps UNF.LEM.Lhs UNF.LEM.Rhs
         UNF.Forward UNF.forward UNF.unfoldForward
         UNF.Backward UNF.backward UNF.unfoldBackward
         UNF.findWithRest UNF.find equiv_dec
         UNF.findWithRest'
         Folds.allb
         UNF.find UNF.default_hintsPayload
         UNF.openForUnification
         UNF.quant
         UNF.liftInstantiate
         SH.applySHeap
         UNF.applicable UNF.checkAllInstantiated


         (** NatMap **)
         NatMap.singleton
         NatMap.IntMap.Raw.height NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.assert_false NatMap.IntMap.Raw.create
         NatMap.IntMap.Raw.bal NatMap.IntMap.Raw.remove_min NatMap.IntMap.Raw.merge NatMap.IntMap.Raw.join
         NatMap.IntMap.Raw.t_left NatMap.IntMap.Raw.t_opt NatMap.IntMap.Raw.t_right
         NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.empty NatMap.IntMap.Raw.is_empty
         NatMap.IntMap.Raw.mem NatMap.IntMap.Raw.find
         NatMap.IntMap.Raw.add  NatMap.IntMap.Raw.remove
         NatMap.IntMap.Raw.fold NatMap.IntMap.Raw.map NatMap.IntMap.Raw.mapi NatMap.IntMap.Raw.map2

         NatMap.IntMap.this NatMap.IntMap.is_bst
         NatMap.IntMap.empty NatMap.IntMap.is_empty
         NatMap.IntMap.add NatMap.IntMap.remove
         NatMap.IntMap.mem NatMap.IntMap.find
         NatMap.IntMap.map NatMap.IntMap.mapi NatMap.IntMap.map2
         NatMap.IntMap.elements NatMap.IntMap.cardinal NatMap.IntMap.fold
         NatMap.IntMap.equal

         Int.Z_as_Int._0 Int.Z_as_Int._1 Int.Z_as_Int._2 Int.Z_as_Int._3
         Int.Z_as_Int.plus Int.Z_as_Int.max
         Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec

         ZArith_dec.Z_gt_le_dec ZArith_dec.Z_ge_lt_dec ZArith_dec.Z_ge_dec
         ZArith_dec.Z_gt_dec
         ZArith_dec.Zcompare_rec ZArith_dec.Zcompare_rect

         BinInt.Z.add BinInt.Z.max BinInt.Z.pos_sub
         BinInt.Z.double BinInt.Z.succ_double BinInt.Z.pred_double

         BinInt.Z.compare

         BinPos.Pos.add BinPos.Pos.compare
         BinPos.Pos.succ BinPos.Pos.compare_cont

         Compare_dec.nat_compare CompOpp

         NatMap.Ordered_nat.compare

         sumor_rec sumor_rect
         sumbool_rec sumbool_rect
         eq_ind_r

         (** Prover **)
         Prover.Prove Prover.Prover Prover.Facts Prover.Learn Prover.Summarize
         Prover.composite_ProverT

         (** Provers **)
         Provers.ComboProver

(*
         (** TransitivityProver **)
         provers.TransitivityProver.transitivitySummarize
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.transitivityProve
         provers.TransitivityProver.groupsOf
         provers.TransitivityProver.addEquality
         provers.TransitivityProver.proveEqual
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.inSameGroup
         provers.TransitivityProver.in_seq
         provers.TransitivityProver.groupWith
         provers.TransitivityProver.transitivityProver
*)

         (** AssumptionProver **)
         provers.AssumptionProver.assumptionProver
         provers.AssumptionProver.assumptionSummarize
         provers.AssumptionProver.assumptionLearn
         provers.AssumptionProver.assumptionProve

         (** ReflexivityProver **)
         provers.ReflexivityProver.reflexivityProver
         provers.ReflexivityProver.reflexivitySummarize
         provers.ReflexivityProver.reflexivityLearn
         provers.ReflexivityProver.reflexivityProve

         (** WordProver **)
         provers.WordProver.wordProver provers.WordProver.Source provers.WordProver.Destination provers.WordProver.Difference
         provers.WordProver.pow32 provers.WordProver.wplus' provers.WordProver.wneg' provers.WordProver.wminus' wordBin NToWord Nplus minus
         provers.WordProver.decompose combine Expr.expr_seq_dec provers.WordProver.combineAll provers.WordProver.combine app
         provers.WordProver.alreadyCovered provers.WordProver.alreadyCovered' andb orb provers.WordProver.merge provers.WordProver.wordLearn1 provers.WordProver.wordLearn
         provers.WordProver.equalitysEq ILEnv.W_seq Word.weqb weq provers.WordProver.equalityMatches provers.WordProver.wordProve provers.WordProver.wordSummarize
         provers.WordProver.types ILEnv.bedrock_type_W provers.WordProver.zero Bool.bool_dec wzero' posToWord bool_rec bool_rect
         Nminus wordToN Nsucc Nmult Pos.mul Pos.add Pos.sub_mask Pos.succ_double_mask Pos.double_mask Pos.pred_double
         provers.WordProver.natToWord' mod2 Div2.div2 whd wtl Pos.double_pred_mask
         provers.WordProver.Equalities provers.WordProver.LessThans provers.WordProver.NotEquals
         provers.WordProver.lessThanMatches

         (** ArrayBoundProver **)
         provers.ArrayBoundProver.boundProver
         provers.ArrayBoundProver.deupd provers.ArrayBoundProver.factIn
         provers.ArrayBoundProver.boundLearn1 provers.ArrayBoundProver.boundLearn
         provers.ArrayBoundProver.boundSummarize provers.ArrayBoundProver.hypMatches
         provers.ArrayBoundProver.boundProve
         provers.ArrayBoundProver.types

         (** Induction **)
         list_ind list_rec list_rect
         sumbool_rect sumbool_rec
         nat_rect nat_ind
         eq_rect_r eq_rec_r eq_rec eq_rect eq_ind
         eq_sym f_equal
         sumbool_rec sumbool_rect
         sumbool_rec sumbool_rect
         sumor_rec sumor_rect
         nat_rec nat_rect

         (** Comparisons **)
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_eq_lt_dec
         Peano_dec.eq_nat_dec
         EquivDec_nat equiv_dec seq_dec
         nat_eq_eqdec
         EquivDec_SemiDec
         Compare_dec.nat_compare
         NPeano.leb NPeano.ltb

         (** SepExpr **)
         SEP.SDomain SEP.SDenotation
         SEP.Default_predicate
         SEP.himp SEP.sexprD
         SEP.heq
         SEP.liftSExpr
         SEP.typeof_pred SEP.typeof_preds

         (** SepHeap **)
         SH.impures SH.pures SH.other
         SH.liftSHeap UNF.HEAP_FACTS.sheapSubstU
         SH.starred SH.hash
         SH.star_SHeap
         SH.SHeap_empty
         SH.sheapD

         SepHeap.FM.empty
         SepHeap.FM.map
         SepHeap.FM.find
         SepHeap.FM.add
         SepHeap.FM.remove
         SepHeap.FM.fold

         (** SepCancel **)
         CancelIL.CANCEL.sepCancel
         CancelIL.CANCEL.expr_count_meta
         CancelIL.CANCEL.exprs_count_meta
         CancelIL.CANCEL.expr_size
         CancelIL.CANCEL.meta_order_funcs
         CancelIL.CANCEL.meta_order_args
         CancelIL.CANCEL.order_impures
         CancelIL.CANCEL.cancel_in_order
         CancelIL.CANCEL.unify_remove CancelIL.CANCEL.unifyArgs
         CancelIL.CANCEL.expr_size

         CancelIL.canceller
         CancelIL.substInEnv
         CancelIL.existsMaybe
         CancelIL.existsSubst

         (** Ordering **)
         Ordering.insert_in_order Ordering.list_lex_cmp Ordering.sort

         (** Multimaps **)
         SepHeap.MM.mmap_add SepHeap.MM.mmap_extend SepHeap.MM.mmap_join
         SepHeap.MM.mmap_mapi SepHeap.MM.mmap_map
         SepHeap.MM.empty

         (** PtsTo Plugin **)
         Plugin_PtsTo.ptsto32_ssig
         Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
         Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
         Plugin_PtsTo.types
         Plugin_PtsTo.MemEval_ptsto32
         Plugin_PtsTo.MemEvaluator_ptsto32

         (** General Recursion **)
         Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
         GenRec.guard Acc_rect well_founded_ind
         well_founded_induction_type Acc_inv ExprUnify.wf_R_expr

         (** Folds **)
         Folds.fold_left_2_opt Folds.fold_left_3_opt

         (** List Functions **)
         tl hd_error value error hd
         nth_error Datatypes.length fold_right firstn skipn rev
         rev_append map app fold_left

         (** Aux Functions **)
         fst snd projT1 projT2 Basics.impl value error
         projT1 projT2 andb orb
         plus minus

         (** Reflection **)
         (* Reflection.Reflect_eqb_nat *)

         (** Array *)
         Array.ssig Array.types_r Array.types
         Array.MemEval Array.MemEvaluator
         Array.div4 Array.deref Array.sym_read Array.sym_write
         Array.wlength_r Array.sel_r Array.upd_r

         (** Array8 *)
         Array8.ssig Array8.types_r Array8.types
         Array8.MemEval Array8.MemEvaluator
         Array8.deref Array8.sym_read Array8.sym_write
         Array8.blength_r Array8.sel_r Array8.upd_r Array8.BtoW_r Array8.WtoB_r

         (** Locals *)
         Locals.bedrock_type_string Locals.bedrock_type_listString Locals.bedrock_type_vals
         Locals.ssig Locals.types_r Locals.types
         Locals.MemEval Locals.MemEvaluator
         Locals.ascii_eq Locals.string_eq Bool.eqb
         Locals.nil_r Locals.cons_r Locals.sel_r Locals.upd_r
         Locals.deref Locals.listIn Locals.sym_sel Locals.sym_read Locals.sym_write

         (** ?? **)
         DepList.hlist_hd DepList.hlist_tl
         eq_sym eq_trans
         EqNat.beq_nat


         (** TODO: sort these **)
          ILAlgoTypes.Env ILAlgoTypes.Algos ILAlgoTypes.Algos_correct
          ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Preds ILAlgoTypes.PACK.Funcs
          ILAlgoTypes.PACK.applyTypes
          ILAlgoTypes.PACK.applyFuncs
          ILAlgoTypes.PACK.applyPreds

          ILAlgoTypes.BedrockPackage.bedrock_package
          Env.repr_combine Env.footprint Env.nil_Repr
          Env.listToRepr
          app map

          ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r
          ILAlgoTypes.AllAlgos_composite
          ILAlgoTypes.oplus Prover.composite_ProverT
          (*TacPackIL.MEVAL.Composite.MemEvaluator_composite*) Env.listToRepr

          Plugin_PtsTo.ptsto32_ssig Bedrock.sep.Array.ssig
       ]
  | _ =>
    cbv beta iota zeta
       delta [s1 s2 s3 hints
         (** Symbolic Evaluation **)
         SymIL.MEVAL.PredEval.fold_args
         SymIL.MEVAL.PredEval.fold_args_update SymIL.MEVAL.PredEval.pred_read_word
         SymIL.MEVAL.PredEval.pred_write_word SymIL.MEVAL.PredEval.pred_read_byte SymIL.MEVAL.PredEval.pred_write_byte
         SymIL.MEVAL.LearnHookDefault.LearnHook_default
         SymIL.IL_ReadWord SymIL.IL_WriteWord SymIL.IL_ReadByte SymIL.IL_WriteByte
         SymILTac.unfolder_LearnHook
         SymIL.MEVAL.Composite.MemEvaluator_composite
         SymIL.MEVAL.Default.smemeval_read_word_default
         SymIL.MEVAL.Default.smemeval_write_word_default
         SymIL.sym_evalInstrs
         SymIL.sym_evalInstr SymIL.sym_evalLval SymIL.sym_evalRval
         SymIL.sym_evalLoc SymIL.sym_evalStream SymIL.sym_assertTest
         SymIL.sym_setReg SymIL.sym_getReg
         SymIL.SymMem SymIL.SymRegs SymIL.SymPures
(*         SymIL.SymVars SymIL.SymUVars *)
         SymIL.stateD SymIL.qstateD
         SymILTac.quantifyNewVars
         SymILTac.unfolder_LearnHook
         ILAlgoTypes.Hints ILAlgoTypes.Prover
         SymIL.MEVAL.sread_word SymIL.MEVAL.swrite_word SymIL.MEVAL.sread_byte SymIL.MEVAL.swrite_byte
         ILAlgoTypes.MemEval ILAlgoTypes.Env ILAlgoTypes.Algos
         (*SymIL.quantifyNewVars*)
         ILAlgoTypes.Algos ILAlgoTypes.Hints ILAlgoTypes.Prover

         SymEval.quantD SymEval.appendQ
         SymEval.qex SymEval.qall
         SymEval.gatherAll SymEval.gatherEx
         SymILTac.sym_eval

         (** ILEnv **)
         ILEnv.comparator ILEnv.fPlus ILEnv.fMinus ILEnv.fMult
         ILEnv.bedrock_types_r ILEnv.bedrock_funcs_r
         ILEnv.bedrock_types
         ILEnv.BedrockCoreEnv.core
         ILEnv.BedrockCoreEnv.pc ILEnv.BedrockCoreEnv.st
         ILEnv.bedrock_type_W ILEnv.bedrock_type_nat
         ILEnv.bedrock_type_setting_X_state
         ILEnv.bedrock_type_state
(*         ILEnv.bedrock_type_test *)
         ILEnv.bedrock_type_reg

(*         ILEnv.test_seq *)
         ILEnv.reg_seq
         ILEnv.W_seq

         ILEnv.word_nat_r
         ILEnv.word_state_r
(*         ILEnv.word_test_r *)

         ILEnv.wplus_r
         ILEnv.wminus_r
         ILEnv.wmult_r
(*         ILEnv.word_test_r *)
(*         ILEnv.wcomparator_r *)
         ILEnv.Regs_r
         ILEnv.wlt_r
         ILEnv.natToW_r

         (** Env **)
         Env.repr_combine Env.default Env.footprint Env.repr'
         Env.updateAt Env.nil_Repr Env.repr Env.updateAt
         Env.repr_combine Env.footprint Env.default Env.repr

         (** Expr **)
         Expr.Range Expr.Domain Expr.Denotation Expr.Impl
         Expr.exists_subst Expr.forallEach Expr.existsEach
         Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
         Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
         Expr.tvar_rec Expr.tvar_rect Expr.liftExpr Expr.lookupAs Expr.Eqb
         Expr.Provable Expr.tvar_val_seqb
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs Expr.AllProvable Expr.AllProvable_gen
         Expr.Provable Expr.tvarD
         Expr.expr_seq_dec
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs
         Expr.tvarD Expr.Eqb
         Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
         Expr.Default_signature Expr.EmptySet_type Expr.Impl Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
         Expr.expr_seq_dec  Expr.expr_seq_dec
         Expr.tvar_val_seqb  Expr.liftExpr Expr.exprSubstU
         Expr.typeof Expr.typeof_env
         Expr.typeof_sig Expr.typeof_funcs
         Expr.Impl_ Expr.exprD
         Expr.expr_ind
         Expr.expr_seq_dec
         Expr.get_Eq
         Expr.const_seqb
         Expr.tvar_seqb
         Expr.tvar_val_seqb_correct
         Expr.tvar_seqb_correct
         Expr.mentionsU
         ReifyExpr.default_type


         (** ExprUnify **)
         CancelIL.U.exprUnify CancelIL.U.exprUnify_recursor
         CancelIL.U.exprInstantiate CancelIL.U.subst_exprInstantiate
         CancelIL.U.Subst_lookup CancelIL.U.subst_lookup
         CancelIL.U.Subst_empty CancelIL.U.subst_empty
         CancelIL.U.Subst_set CancelIL.U.subst_set
         CancelIL.U.Subst_equations
         CancelIL.U.Subst_size
         CancelIL.U.dep_in

         CancelIL.U.FM.Raw.height CancelIL.U.FM.Raw.cardinal CancelIL.U.FM.Raw.assert_false CancelIL.U.FM.Raw.create
         CancelIL.U.FM.Raw.bal CancelIL.U.FM.Raw.remove_min CancelIL.U.FM.Raw.merge CancelIL.U.FM.Raw.join
         CancelIL.U.FM.Raw.t_left CancelIL.U.FM.Raw.t_opt CancelIL.U.FM.Raw.t_right
         CancelIL.U.FM.Raw.cardinal CancelIL.U.FM.Raw.empty CancelIL.U.FM.Raw.is_empty
         CancelIL.U.FM.Raw.mem CancelIL.U.FM.Raw.find
         CancelIL.U.FM.Raw.add  CancelIL.U.FM.Raw.remove
         CancelIL.U.FM.Raw.fold CancelIL.U.FM.Raw.map CancelIL.U.FM.Raw.mapi CancelIL.U.FM.Raw.map2

         CancelIL.U.FM.this CancelIL.U.FM.is_bst
         CancelIL.U.FM.empty CancelIL.U.FM.is_empty
         CancelIL.U.FM.add CancelIL.U.FM.remove
         CancelIL.U.FM.mem CancelIL.U.FM.find
         CancelIL.U.FM.map CancelIL.U.FM.mapi CancelIL.U.FM.map2
         CancelIL.U.FM.elements CancelIL.U.FM.cardinal CancelIL.U.FM.fold
         CancelIL.U.FM.equal
         CancelIL.U.FM.E.eq_dec

         (** Unfolder **)
         Unfolder.FM.empty Unfolder.FM.add Unfolder.FM.remove
         Unfolder.FM.fold Unfolder.FM.map
         Unfolder.FM.find
         UNF.LEM.Foralls UNF.Vars
         UNF.UVars UNF.Heap UNF.LEM.Hyps UNF.LEM.Lhs UNF.LEM.Rhs
         UNF.Forward UNF.forward UNF.unfoldForward UNF.Backward
         UNF.backward UNF.unfoldBackward  equiv_dec
         UNF.find UNF.findWithRest UNF.findWithRest'
         Folds.allb
         UNF.openForUnification
         UNF.quant
         UNF.liftInstantiate
         SH.applySHeap
         UNF.find UNF.default_hintsPayload
         UNF.applicable UNF.checkAllInstantiated

         (** NatMap **)
         NatMap.singleton
         NatMap.IntMap.Raw.height NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.assert_false NatMap.IntMap.Raw.create
         NatMap.IntMap.Raw.bal NatMap.IntMap.Raw.remove_min NatMap.IntMap.Raw.merge NatMap.IntMap.Raw.join
         NatMap.IntMap.Raw.t_left NatMap.IntMap.Raw.t_opt NatMap.IntMap.Raw.t_right
         NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.empty NatMap.IntMap.Raw.is_empty
         NatMap.IntMap.Raw.mem NatMap.IntMap.Raw.find
         NatMap.IntMap.Raw.add  NatMap.IntMap.Raw.remove
         NatMap.IntMap.Raw.fold NatMap.IntMap.Raw.map NatMap.IntMap.Raw.mapi NatMap.IntMap.Raw.map2

         NatMap.IntMap.this NatMap.IntMap.is_bst
         NatMap.IntMap.empty NatMap.IntMap.is_empty
         NatMap.IntMap.add NatMap.IntMap.remove
         NatMap.IntMap.mem NatMap.IntMap.find
         NatMap.IntMap.map NatMap.IntMap.mapi NatMap.IntMap.map2
         NatMap.IntMap.elements NatMap.IntMap.cardinal NatMap.IntMap.fold
         NatMap.IntMap.equal

         Int.Z_as_Int._0 Int.Z_as_Int._1 Int.Z_as_Int._2 Int.Z_as_Int._3
         Int.Z_as_Int.plus Int.Z_as_Int.max
         Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec

         ZArith_dec.Z_gt_le_dec ZArith_dec.Z_ge_lt_dec ZArith_dec.Z_ge_dec
         ZArith_dec.Z_gt_dec
         ZArith_dec.Zcompare_rec ZArith_dec.Zcompare_rect

         BinInt.Z.add BinInt.Z.max BinInt.Z.pos_sub
         BinInt.Z.double BinInt.Z.succ_double BinInt.Z.pred_double

         BinInt.Z.compare

         BinPos.Pos.add BinPos.Pos.compare
         BinPos.Pos.succ BinPos.Pos.compare_cont

         Compare_dec.nat_compare CompOpp

         NatMap.Ordered_nat.compare

         sumor_rec sumor_rect
         sumbool_rec sumbool_rect
         eq_ind_r

         (** Prover **)
         Prover.Prove Prover.Prover Prover.Facts Prover.Learn Prover.Summarize
         Prover.composite_ProverT

         (** Provers **)
         Provers.ComboProver

(*
         (** TransitivityProver **)
         provers.TransitivityProver.transitivitySummarize
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.transitivityProve
         provers.TransitivityProver.groupsOf
         provers.TransitivityProver.addEquality
         provers.TransitivityProver.proveEqual
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.inSameGroup
         provers.TransitivityProver.in_seq
         provers.TransitivityProver.groupWith
         provers.TransitivityProver.transitivityProver
*)

         (** AssumptionProver **)
         provers.AssumptionProver.assumptionProver
         provers.AssumptionProver.assumptionSummarize
         provers.AssumptionProver.assumptionLearn
         provers.AssumptionProver.assumptionProve

         (** ReflexivityProver **)
         provers.ReflexivityProver.reflexivityProver
         provers.ReflexivityProver.reflexivitySummarize
         provers.ReflexivityProver.reflexivityLearn
         provers.ReflexivityProver.reflexivityProve

         (** WordProver **)
         provers.WordProver.wordProver provers.WordProver.Source provers.WordProver.Destination provers.WordProver.Difference
         provers.WordProver.pow32 provers.WordProver.wplus' provers.WordProver.wneg' provers.WordProver.wminus' wordBin NToWord Nplus minus
         provers.WordProver.decompose combine Expr.expr_seq_dec provers.WordProver.combineAll provers.WordProver.combine app
         provers.WordProver.alreadyCovered provers.WordProver.alreadyCovered' andb orb provers.WordProver.merge provers.WordProver.wordLearn1 provers.WordProver.wordLearn
         provers.WordProver.equalitysEq ILEnv.W_seq Word.weqb weq provers.WordProver.equalityMatches provers.WordProver.wordProve provers.WordProver.wordSummarize
         provers.WordProver.types ILEnv.bedrock_type_W provers.WordProver.zero Bool.bool_dec wzero' posToWord bool_rec bool_rect
         Nminus wordToN Nsucc Nmult Pos.mul Pos.add Pos.sub_mask Pos.succ_double_mask Pos.double_mask Pos.pred_double
         provers.WordProver.natToWord' mod2 Div2.div2 whd wtl Pos.double_pred_mask
         provers.WordProver.Equalities provers.WordProver.LessThans provers.WordProver.NotEquals
         provers.WordProver.lessThanMatches

         (** ArrayBoundProver **)
         provers.ArrayBoundProver.boundProver
         provers.ArrayBoundProver.deupd provers.ArrayBoundProver.factIn
         provers.ArrayBoundProver.boundLearn1 provers.ArrayBoundProver.boundLearn
         provers.ArrayBoundProver.boundSummarize provers.ArrayBoundProver.hypMatches
         provers.ArrayBoundProver.boundProve
         provers.ArrayBoundProver.types

         (** Induction **)
         list_ind list_rec list_rect
         sumbool_rect sumbool_rec
         sumor_rec sumor_rect
         nat_rec nat_rect nat_ind
         eq_rect_r eq_rec_r eq_rec eq_rect
         eq_sym f_equal
         nat_rect eq_ind eq_rec eq_rect
         eq_rec_r eq_rect eq_rec nat_rec nat_rect
         sumbool_rec sumbool_rect
         sumbool_rec sumbool_rect
         sumor_rec sumor_rect
         nat_rec nat_rect

         (** Comparisons **)
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_eq_lt_dec
         Peano_dec.eq_nat_dec
         EquivDec_nat  equiv_dec seq_dec
         nat_eq_eqdec
         EquivDec_SemiDec
         Compare_dec.nat_compare
         NPeano.leb NPeano.ltb

         (** SepExpr **)
         SEP.SDomain SEP.SDenotation
         SEP.Default_predicate
         SEP.himp SEP.sexprD
         SEP.heq
         nat_eq_eqdec
         SEP.liftSExpr

         (** SepHeap **)
         SH.impures SH.pures SH.other
         SH.liftSHeap UNF.HEAP_FACTS.sheapSubstU
         SH.starred SH.hash
         SH.star_SHeap
         SH.SHeap_empty
         SH.sheapD

         SepHeap.FM.empty
         SepHeap.FM.map
         SepHeap.FM.find
         SepHeap.FM.add
         SepHeap.FM.remove
         SepHeap.FM.fold

         (** SepCancel **)
         CancelIL.CANCEL.sepCancel
         CancelIL.CANCEL.expr_count_meta
         CancelIL.CANCEL.exprs_count_meta
         CancelIL.CANCEL.expr_size
         CancelIL.CANCEL.meta_order_funcs
         CancelIL.CANCEL.meta_order_args
         CancelIL.CANCEL.order_impures
         CancelIL.CANCEL.cancel_in_order
         CancelIL.CANCEL.unify_remove
         CancelIL.CANCEL.unifyArgs
         CancelIL.CANCEL.expr_size

         CancelIL.canceller
         CancelIL.substInEnv
         CancelIL.existsMaybe
         CancelIL.existsSubst

         (** Ordering **)
         Ordering.insert_in_order Ordering.list_lex_cmp Ordering.sort

         (** Multimaps **)
         SepHeap.MM.mmap_add SepHeap.MM.mmap_extend SepHeap.MM.mmap_join
         SepHeap.MM.mmap_mapi SepHeap.MM.mmap_map
         SepHeap.MM.empty

         (** PtsTo Plugin **)
         Plugin_PtsTo.ptsto32_ssig
         Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
         Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
         Plugin_PtsTo.types
         Plugin_PtsTo.MemEval_ptsto32
         Plugin_PtsTo.MemEvaluator_ptsto32

         (** General Recursion **)
         Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
         GenRec.guard Acc_rect well_founded_ind
         well_founded_induction_type Acc_inv ExprUnify.wf_R_expr

         (** Folds **)
         Folds.fold_left_2_opt Folds.fold_left_3_opt

         (** List Functions **)
         tl hd_error value error hd
         nth_error Datatypes.length fold_right firstn skipn rev
         rev_append List.map app fold_left

         (** Aux Functions **)
         fst snd projT1 projT2 Basics.impl value error
         projT1 projT2 andb orb
         plus minus

         (** Reflection **)
         (* Reflection.Reflect_eqb_nat *)

         (** Array *)
         Array.ssig Array.types_r Array.types
         Array.MemEval Array.MemEvaluator
         Array.div4 Array.deref Array.sym_read Array.sym_write
         Array.wlength_r Array.sel_r Array.upd_r

         (** Array8 *)
         Array8.ssig Array8.types_r Array8.types
         Array8.MemEval Array8.MemEvaluator
         Array8.deref Array8.sym_read Array8.sym_write
         Array8.blength_r Array8.sel_r Array8.upd_r Array8.BtoW_r Array8.WtoB_r

         (** Locals *)
         Locals.bedrock_type_string Locals.bedrock_type_listString Locals.bedrock_type_vals
         Locals.ssig Locals.types_r Locals.types
         Locals.MemEval Locals.MemEvaluator
         Locals.ascii_eq Locals.string_eq Bool.eqb
         Locals.nil_r Locals.cons_r Locals.sel_r Locals.upd_r
         Locals.deref Locals.listIn Locals.sym_sel Locals.sym_read Locals.sym_write

         (** ?? **)
         DepList.hlist_hd DepList.hlist_tl
         eq_sym eq_trans
         EqNat.beq_nat

         (** TODO: sort these **)
         ILAlgoTypes.Env ILAlgoTypes.Algos ILAlgoTypes.Algos_correct
         ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Preds ILAlgoTypes.PACK.Funcs
         ILAlgoTypes.PACK.applyTypes
         ILAlgoTypes.PACK.applyFuncs
         ILAlgoTypes.PACK.applyPreds

         ILAlgoTypes.BedrockPackage.bedrock_package
         Env.repr_combine Env.footprint Env.nil_Repr
         Env.listToRepr
         app map

         ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r
         ILAlgoTypes.AllAlgos_composite
         ILAlgoTypes.oplus Prover.composite_ProverT
         (*TacPackIL.MEVAL.Composite.MemEvaluator_composite*) Env.listToRepr

         Plugin_PtsTo.ptsto32_ssig Bedrock.sep.Array.ssig

       ] in H
  end; refold.

Ltac clear_junk := repeat match goal with
                            | [ H : True |- _ ] => clear H
                            | [ H : ?X = ?X |- _ ] => clear H
                                | [ H : ?X, H' : ?X |- _ ] => clear H'
                          end.

Ltac evaluate ext :=
  repeat match goal with
           | [ H : ?P -> False |- _ ] => change (not P) in H
         end;
  ILTac.sym_eval ltac:(ILTacCommon.isConst) ext ltac:(hints_ext_simplifier ext);
  clear_junk.

Ltac cancel ext := sep_canceller ltac:(ILTacCommon.isConst) ext ltac:(hints_ext_simplifier ext); sep_firstorder; clear_junk.

Ltac unf := unfold substH.
Ltac reduce := Programming.reduce unf.
Ltac ho := Programming.ho unf; reduce.

Theorem implyR : forall pc state specs (P Q R : PropX pc state),
  interp specs (P ---> R)
  -> interp specs (P ---> Q ---> R)%PropX.
  intros.
  do 2 apply Imply_I.
  eapply Imply_E.
  eauto.
  constructor; simpl; tauto.
Qed.

Inductive pureConsequences : HProp -> list Prop -> Prop :=
| PurePure : forall P, pureConsequences [| P |]%Sep (P :: nil)
| PureStar : forall P P' Q Q', pureConsequences P P'
  -> pureConsequences Q Q'
  -> pureConsequences (P * Q)%Sep (P' ++ Q')
| PureOther : forall P, pureConsequences P nil.

Theorem pureConsequences_correct : forall P P',
  pureConsequences P P'
  -> forall specs stn st, interp specs (P stn st ---> [| List.Forall (fun p => p) P' |]%PropX).
  induction 1; intros.

  unfold injB, inj.
  apply Imply_I.
  eapply Inj_E.
  eapply And_E1; apply Env; simpl; eauto.
  intro; apply Inj_I; repeat constructor; assumption.

  unfold starB, star.
  apply Imply_I.
  eapply Exists_E.
  apply Env; simpl; eauto.
  simpl; intro.
  eapply Exists_E.
  apply Env; simpl; left; eauto.
  simpl; intro.
  eapply Inj_E.
  eapply Imply_E.
  apply interp_weaken; apply IHpureConsequences1.
  eapply And_E1; eapply And_E2; apply Env; simpl; eauto.
  intro.
  eapply Inj_E.
  eapply Imply_E.
  apply interp_weaken; apply IHpureConsequences2.
  do 2 eapply And_E2; apply Env; simpl; eauto.
  intro.
  apply Inj_I.
  apply Forall_app; auto.

  apply Imply_I; apply Inj_I; auto.
Qed.

Theorem extractPure : forall specs P Q Q' R st,
  pureConsequences Q Q'
  -> (List.Forall (fun p => p) Q' -> interp specs (P ---> R))
  -> interp specs (P ---> ![Q] st ---> R)%PropX.
  intros.
  do 2 apply Imply_I.
  eapply Inj_E.
  eapply Imply_E.
  apply interp_weaken.
  apply pureConsequences_correct; eauto.
  rewrite sepFormula_eq.
  unfold sepFormula_def.
  apply Env; simpl; eauto.
  intro.
  eapply Imply_E.
  eauto.
  apply Env; simpl; eauto.
Qed.

Ltac words := repeat match goal with
                       | [ H : _ = _ |- _ ] => rewrite H
                     end; W_eq.

Definition locals_return ns vs avail p (ns' : list string) (avail' offset : nat) :=
  locals ns vs avail p.

Theorem create_locals_return : forall ns' avail' ns avail offset vs p,
  locals ns vs avail p = locals_return ns vs avail p ns' avail' offset.
  reflexivity.
Qed.

Definition ok_return (ns ns' : list string) (avail avail' offset : nat) :=
  (avail >= avail' + length ns')%nat
  /\ offset = 4 * length ns.

Ltac peelPrefix ls1 ls2 :=
  match ls1 with
    | nil => ls2
    | ?x :: ?ls1' =>
      match ls2 with
        | x :: ?ls2' => peelPrefix ls1' ls2'
      end
  end.

Global Opaque merge.

Theorem use_HProp_extensional : forall p, HProp_extensional p
  -> (fun st sm => p st sm) = p.
  auto.
Qed.

Ltac descend :=
  (*TIME time "descend:descend" *)
  Programming.descend;
  (*TIME time "descend:reduce" *)
  reduce;
  (*TIME time "descend:unfold_simpl" ( *)
  unfold hvarB; simpl; rereg
  (*TIME ) *);
  (*TIME time "descend:loop" *)
    (repeat match goal with
             | [ |- context[fun stn0 sm => ?f stn0 sm] ] =>
               rewrite (@use_HProp_extensional f) by auto
             | [ |- context[fun stn0 sm => ?f ?a stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d ?e stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d e)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d ?e ?f stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d e f)) by auto
           end);
    try match goal with
          | [ p : (ST.settings * state)%type |- _ ] => destruct p; simpl in *
        end.

Definition locals_call ns vs avail p (ns' : list string) (avail' : nat) (offset : nat) :=
  locals ns vs avail p.

Definition ok_call (ns ns' : list string) (avail avail' : nat) (offset : nat) :=
  (length ns' <= avail)%nat
  /\ (avail' <= avail - length ns')%nat
  /\ NoDup ns'
  /\ offset = 4 * length ns.

Definition excessStack (p : W) (ns : list string) (avail : nat) (ns' : list string) (avail' : nat) :=
  reserved (p ^+ natToW (4 * (length ns + length ns' + avail')))
  (avail - length ns' - avail').

Lemma make_call : forall ns ns' vs avail avail' p offset,
  ok_call ns ns' avail avail' offset
  -> locals_call ns vs avail p ns' avail' offset ===>
  locals ns vs 0 p
  * Ex vs', locals ns' vs' avail' (p ^+ natToW offset)
  * excessStack p ns avail ns' avail'.
  unfold ok_call; intuition; subst; eapply do_call; eauto.
Qed.

Lemma make_return : forall ns ns' vs avail avail' p offset,
  ok_return ns ns' avail avail' offset
  -> (locals ns vs 0 p
    * Ex vs', locals ns' vs' avail' (p ^+ natToW offset)
    * excessStack p ns avail ns' avail')
  ===> locals_return ns vs avail p ns' avail' offset.
  unfold ok_return; intuition; subst; apply do_return; omega || words.
Qed.

Definition locals_in ns vs avail p (ns' ns'' : list string) (avail' : nat) :=
  locals ns vs avail p.

Open Scope list_scope.

Definition ok_in (ns : list string) (avail : nat) (ns' ns'' : list string) (avail' : nat) :=
  ns ++ ns' = ns'' /\ (length ns' <= avail)%nat /\ NoDup (ns ++ ns')
  /\ avail' = avail - length ns'.

Theorem init_in : forall ns ns' ns'' vs avail p avail',
  ok_in ns avail ns' ns'' avail'
  -> locals_in ns vs avail p ns' ns'' avail' ===>
  Ex vs', locals ns'' (merge vs vs' ns) avail' p.
  unfold ok_in; intuition; subst; apply prelude_in; auto.
Qed.

Definition locals_out ns vs avail p (ns' ns'' : list string) (avail' : nat) :=
  locals ns vs avail p.

Definition ok_out (ns : list string) (avail : nat) (ns' ns'' : list string) (avail' : nat) :=
  ns ++ ns' = ns'' /\ (length ns' <= avail)%nat
  /\ avail' = avail - length ns'.

Theorem init_out : forall ns ns' ns'' vs avail p avail',
  ok_out ns avail ns' ns'' avail'
  -> locals ns'' vs avail' p
  ===> locals_out ns vs avail p ns' ns'' avail'.
  unfold ok_out; intuition; subst; apply prelude_out; auto.
Qed.

Ltac prepare fwd bwd :=
  let the_unfold_tac x :=
    eval unfold empB, injB, injBX, starB, exB, hvarB in x
  in
  ILAlgoTypes.Tactics.Extension.extend the_unfold_tac
    ILTacCommon.isConst auto_ext' tt tt (make_call, init_in, fwd) (make_return, init_out, bwd).

Definition auto_ext : TacPackage.
  prepare tt tt.
Defined.

Theorem create_locals_out : forall ns' ns'' avail' ns avail vs p,
  locals ns vs avail p = locals_out ns vs avail p ns' ns'' avail'.
  reflexivity.
Qed.

Theorem unandL : forall pc state specs (P Q R : PropX pc state),
  interp specs (P /\ Q ---> R)%PropX
  -> interp specs (P ---> Q ---> R)%PropX.
  intros; do 2 apply Imply_I.
  eapply Imply_E; eauto.
  apply And_I; eapply Env; simpl; eauto.
Qed.

Lemma breakout : forall A (P : A -> _) Q R x specs,
  (forall v, interp specs (![P v * Q] x ---> R)%PropX)
  -> interp specs (![exB P * Q] x ---> R)%PropX.
  rewrite sepFormula_eq; propxFo.
  unfold sepFormula_def, exB, ex.
  simpl.
  repeat (apply existsL; intros).
  apply andL; apply injL; intro.
  apply andL.
  apply existsL; intro.
  apply unandL.
  eapply Imply_trans; try apply H; clear H.
  do 2 eapply existsR.
  simpl.
  repeat apply andR.
  apply injR; eauto.
  apply andL; apply implyR.
  apply Imply_refl.
  apply andL; apply swap; apply implyR.
  apply Imply_refl.
Qed.

Ltac imply_simp'' := match goal with
                       | [ |- interp _ (PropX.Inj _ ---> _) ] => apply injL; intro
                       | [ |- interp _ (PropX.Cptr _ _ ---> _) ] => apply cptrL; intro
                       | [ |- interp _ (PropX.And _ _ ---> _) ] => apply andL
                       | [ |- interp _ (PropX.Exists _ ---> _) ] => apply existsL; intro
                     end.

Ltac toFront' which P k :=
  match P with
    | SEP.ST.star ?Q ?R =>
      toFront' which Q ltac:(fun it P' => k it (SEP.ST.star P' R))
      || toFront' which R ltac:(fun it P' => k it (SEP.ST.star P' Q))
    | (?Q * ?R)%Sep =>
      toFront' which Q ltac:(fun it P' => k it (SEP.ST.star P' R))
      || toFront' which R ltac:(fun it P' => k it (SEP.ST.star P' Q))
    | _ => which P; k P (@SEP.ST.emp W (settings * state) nil)
  end.

Ltac step ext :=
  let considerImp pre post :=
    try match post with
          | context[locals ?ns ?vs ?avail _] =>
            match pre with
              | context[excessStack _ ns avail ?ns' ?avail'] =>
                match avail' with
                  | avail => fail 1
                  | _ =>
                    match pre with
                      | context[locals ns ?vs' 0 ?sp] =>
                        match goal with
                          | [ _ : _ = sp |- _ ] => fail 1
                          | _ => equate vs vs';
                            let offset := eval simpl in (4 * List.length ns) in
                              rewrite (create_locals_return ns' avail' ns avail offset);
                                assert (ok_return ns ns' avail avail' offset)%nat by (split; [
                                  simpl; omega
                                  | reflexivity ] ); autorewrite with sepFormula;
                                generalize dependent vs'; intros
                        end
                    end
                end
            end
        end;
    progress cancel ext in

 let exBegone :=
   match goal with
     | [ |- interp ?specs (![ ?P ] ?x ---> ?Q)%PropX ] =>
       match P with
         | context[exB] =>
           toFront' ltac:(fun R => match R with
                                     | exB _ => idtac
                                   end) P
           ltac:(fun it P' =>
             apply Imply_trans with (![ it * P'] x)%PropX; [ cancel auto_ext; solve [ eassumption ] | ])
       end
   end; repeat match goal with
                 | [ |- interp _ (![ exB _ * _] _ ---> _)%PropX ] => apply breakout; intro
               end in

 try match goal with
       | [ |- interp _ (?P ---> _)%PropX ] =>
         match P with
           | context[exB] => repeat imply_simp''; descend; repeat exBegone
         end
     end;

  match goal with
    | [ |- _ _ = Some _ ] => solve [ eauto ]
    | [ _ : interp _ (![ ?pre ] _) |- interp _ (![ ?post ] _) ] => considerImp pre post
    | [ |- interp _ (![?pre]%PropX _ ---> ![?post]%PropX _) ] => considerImp pre post
    | [ |- himp _ ?pre ?post ] => considerImp pre post
    | [ |- interp _ (_ _ _ ?x ---> _ _ _ ?y ---> _ ?x)%PropX ] =>
      match y with
        | x => fail 1
        | _ => eapply extractPure; [ repeat constructor
          | cbv zeta; simpl; intro; repeat match goal with
                                             | [ H : List.Forall _ nil |- _ ] => clear H
                                             | [ H : List.Forall _ (_ :: _) |- _ ] => inversion H; clear H; subst
                                           end; clear_junk ]
        | _ => apply implyR
      end
    | _ => ho; rereg
  end.

Ltac slotVariable E :=
  match E with
    | 4 => constr:"0"
    | 8 => constr:"1"
    | 12 => constr:"2"
    | 16 => constr:"3"
    | 20 => constr:"4"
    | 24 => constr:"5"
    | 28 => constr:"6"
    | 32 => constr:"7"
    | 36 => constr:"8"
    | 40 => constr:"9"
  end.

Ltac slotVariables E :=
  match E with
    | Binop (LvReg Rv) (RvLval (LvReg Sp)) Plus (RvImm (natToW _))
      :: Assign (LvMem (Indir Rv (natToW ?slot))) _
      :: ?E' =>
      let v := slotVariable slot in
        let vs := slotVariables E' in
          constr:(v :: vs)
    | _ :: ?E' => slotVariables E'
    | nil => constr:(@nil string)
  end.

Ltac NoDup := repeat constructor; simpl; intuition congruence.

Ltac post :=
  (*TIME time "post:propxFo" *)
  propxFo;
  (*TIME time "post:autorewrite" ( *)
  autorewrite with sepFormula in *
  (*TIME ) *) ;
  unfold substH in *;
  (*TIME time "post:simpl" ( *)
  simpl in *; rereg; autorewrite with IL;
    try match goal with
          | [ H : context[locals ?ns ?vs ?avail ?p]
              |- context[locals ?ns' _ ?avail' _] ] =>
            match avail' with
              | avail => fail 1
              | _ =>
                (let ns'' := peelPrefix ns ns' in
                  let exposed := eval simpl in (avail - avail') in
                    let new := eval simpl in (List.length ns' - List.length ns) in
                      match new with
                        | exposed =>
                          let avail' := eval simpl in (avail - List.length ns'') in
                            change (locals ns vs avail p) with (locals_in ns vs avail p ns'' ns' avail') in H;
                              assert (ok_in ns avail ns'' ns' avail')%nat
                                by (split; [
                                  reflexivity
                                  | split; [simpl; omega
                                    | split; [ NoDup
                                      | reflexivity ] ] ])
                      end)
                || (let offset := eval simpl in (4 * List.length ns) in
                  change (locals ns vs avail p) with (locals_call ns vs avail p ns' avail' offset) in H;
                    assert (ok_call ns ns' avail avail' offset)%nat
                      by (split; [ simpl; omega
                        | split; [ simpl; omega
                          | split; [ NoDup
                            | reflexivity ] ] ]))
            end
          | [ _ : evalInstrs _ _ ?E = None, H : context[locals ?ns ?vs ?avail ?p] |- _ ] =>
            let ns' := slotVariables E in
            match ns' with
              | nil => fail 1
              | _ =>
                let ns' := constr:("rp" :: ns') in
                  let offset := eval simpl in (4 * List.length ns) in
                    change (locals ns vs avail p) with (locals_call ns vs avail p ns' 0 offset) in H;
                      assert (ok_call ns ns' avail 0 offset)%nat
                        by (split; [ simpl; omega
                          | split; [ simpl; omega
                            | split; [ NoDup
                              | reflexivity ] ] ])
            end
        end
  (*TIME ) *).

Ltac sep' ext :=
  post; evaluate ext; descend; repeat (step ext; descend).

Ltac sep ext :=
  match goal with
    | [ |- context[Assign (LvMem (Indir Sp (natToW 0))) (RvLval (LvReg Rp)) :: nil] ] =>
      sep' auto_ext (* Easy case; don't bring the hints into it *)
    | _ => sep' ext
  end.

Ltac sepLemma := unfold Himp in *; simpl; intros; cancel auto_ext.

Ltac sepLemmaLhsOnly :=
  let sllo Q := remember Q;
    match goal with
      | [ H : ?X = Q |- _ ] => let H' := fresh in
        assert (H' : bool -> X = Q) by (intro; assumption);
          clear H; rename H' into H;
            sepLemma; rewrite (H true); clear H
    end in
    simpl; intros;
      match goal with
        | [ |- _ ===> ?Q ] => sllo Q
        | [ |- himp _ _ ?Q ] => sllo Q
      end.

Ltac sep_auto := sep' auto_ext.

Hint Rewrite sel_upd_eq sel_upd_ne using congruence : sepFormula.

Lemma sel_merge : forall vs vs' ns nm,
  In nm ns
  -> sel (merge vs vs' ns) nm = sel vs nm.
  intros.
  generalize (merge_agree vs vs' ns); intro Hl.
  eapply Forall_forall in Hl; eauto.
Qed.

Hint Rewrite sel_merge using (simpl; tauto) : sepFormula.

Theorem lift0 : forall P, lift nil P = P.
  reflexivity.
Qed.

Hint Rewrite lift0 : sepFormula.

(* Within [H], find a conjunct [P] such that [which P] doesn't fail, and reassociate [H]
 * to put [P] in front. *)
Ltac toFront which H :=
  match type of H with
    | interp ?specs (![ ?P ] ?st) => toFront' which P ltac:(fun it P' =>
      let H' := fresh in
        assert (H' : interp specs (![ SEP.ST.star it P' ] st)) by step auto_ext;
          clear H; rename H' into H)
  end.

(* Just like [toFront], but for the conclusion rather than a hypothesis *)
Ltac toFront_conc which :=
  match goal with
    | [ |- interp ?specs (![ ?P ] ?st) ] => toFront' which P ltac:(fun it P' =>
      let H := fresh "H" in assert (H : interp specs (![ SEP.ST.star it P' ] st)); [ |
        generalize dependent H;
          repeat match goal with
                   | [ H : interp _ _ |- _ ] => clear H
                 end; intro; eapply Imply_sound; [ eapply sepFormula_himp_imply | ];
          [ | reflexivity | eassumption ]; solve [ step auto_ext ] ])
  end.

(* Handle a VC for an indirect function call, given the callee's formal arguments list. *)
Ltac icall formals :=
  match goal with
    | [ H : context[locals ?ns ?vs ?avail ?p] |- exists pre', _ (Regs _ Rv) = Some pre' /\ _ ] =>
      let ns' := constr:("rp" :: formals) in
        let avail' := constr:0 in
          let offset := eval simpl in (4 * List.length ns) in
            change (locals ns vs avail p) with (locals_call ns vs avail p ns' avail' offset) in H;
              assert (ok_call ns ns' avail avail' offset)%nat
                by (split; [ simpl; omega
                  | split; [ simpl; omega
                    | split; [ repeat constructor; simpl; intuition congruence
                      | reflexivity ] ] ])
  end.

Definition any : HProp := fun _ _ => [| True |]%PropX.

Theorem any_easy : forall P, P ===> any.
  unfold any; repeat intro; step auto_ext; auto.
Qed.
