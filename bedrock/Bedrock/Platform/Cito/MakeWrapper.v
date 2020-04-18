Require Import Coq.omega.Omega.
Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Notations3.

Notation "$ n" := (natToW n) : stmt_scope.

Require Import Bedrock.Platform.Cito.SyntaxFunc.
Require Import Coq.Lists.List.

Notation "'cfunction' name () b 'end'" :=
  {|
    Name := name;
    Core :=
      {|
        ArgVars := nil;
        RetVar := "ret";
        Body := b%stmt
      |}
  |} (no associativity, at level 95, name at level 0, only parsing) : Citofuncs_scope.

Notation "'cfunction' name ( x1 , .. , xN ) b 'end'" :=
  {|
    Name := name;
    Core :=
      {|
        ArgVars := cons x1 (.. (cons xN nil) ..);
        RetVar := "ret";
        Body := b%stmt
      |}
  |} (no associativity, at level 95, name at level 0, only parsing) : Citofuncs_scope.

Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : Citofuncs_scope.

Delimit Scope Citofuncs_scope with Citofuncs.

Require Import Bedrock.Platform.Cito.SyntaxModule.

Notation "'cmodule' name fs" :=
  {|
    Name := name;
    Functions := fs%Citofuncs
  |} (no associativity, at level 95, name at level 0, only parsing).

Definition f := (
  cfunction "return_zero"()
    "ret" <- $0
  end
)%Citofuncs.

Definition m := cmodule "return_zero" {{
  f
}}.

Require Import Bedrock.Platform.Cito.GoodModule.

Notation MName := SyntaxModule.Name.
Notation FName := SyntaxFunc.Name.
Notation Funcs := SyntaxModule.Functions.

Require Import Bedrock.Platform.Cito.GoodFunc.

Require Import Coq.Program.Basics.

Infix "*" := compose.

Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.GoodFunction.
Require Import Bedrock.Platform.Cito.IsGoodModule.

(* Should have a decider here for automatic syntactic checking *)

Ltac shakeup := hnf; simpl; intuition (auto; try congruence); hnf; simpl.

Ltac constructors :=
  repeat (match goal with
            | [ |- List.Forall _ _ ] => constructor
            | [ |- NoDup _ ] => constructor
            | [ |- WellFormed.args_not_too_long _ ] => constructor
          end; intros).

Ltac good_module := shakeup; repeat (constructors; shakeup).

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Require Import Bedrock.Platform.Cito.ADT Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).
  Require Import Bedrock.Platform.Cito.LinkSpec.
  Module Import LinkSpecMake := Make E.
  Module Import LinkSpecMake2 := Make M.

  Notation "'cimport' lab 'cmodules' [[ m1 , .. , mN ]] 'definition' d" :=
    (func_spec (cons m1 (.. (cons mN nil) ..)) (empty _)
      (match lab%SP with
         | (mname, Global fname) => (mname, fname)
         | _ => ("uhoh", "uhoh")
       end) d)
    (no associativity, at level 95, lab at level 0).

  Require Import Bedrock.Platform.Malloc.

  Require Import Coq.Arith.Arith.
  Require Import Bedrock.Platform.Cito.WordFacts.
  Require Import Bedrock.Platform.Cito.CompileStmtTactics.

  Import InvMake.SemanticsMake.

  Require Import Bedrock.Platform.Cito.MakeADT.
  Module Import Made := Make(E)(M).

  Ltac hiding tac :=
    clear_imports;
    ((let P := fresh "P" in
      match goal with
        | H : Safe ?fs _ _ |- _ => set (P := Safe fs) in *
        | H : RunsTo ?fs _ _ _ |- _ => set (P := RunsTo fs) in *
        | H : fs_good_to_use ?a ?b ?c ?d |- _ => set (P := fs_good_to_use a b c d) in *
      end;
      hiding tac;
      subst P) || tac).

  Ltac prelude_out :=
    match goal with
      | [ |- himp _ (locals ?ns1 _ _ _) (locals ?ns2 _ _ _) ] =>
        let ns := peelPrefix ns2 ns1 in
          etransitivity; [ | eapply prelude_out with (ns' := ns); simpl; omega ];
          sep_auto
    end.

  Ltac call_cito extra_stack args :=
    match goal with
      | [ H : context[locals ?ns ?vs ?res ?sp] |- _ ] =>
        let offset := eval simpl in (4 * length ns)%nat in
          change (locals ns vs res sp) with (locals_call ns vs res sp
            ("rp" :: "extra_stack" :: args) extra_stack offset) in H;
          assert (ok_call ns ("rp" :: "extra_stack" :: args) res extra_stack offset) by
            (split; [ simpl; omega
              | split; [ simpl; omega
                | split; [ NoDup
                  | reflexivity ] ] ])
    end.

  Theorem is_state_in' : forall vs sp args e_stack F,
    locals ("rp" :: "extra_stack" :: args) vs e_stack sp
    * mallocHeap 0 * F
    ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack nil
    (vs, heap_empty) (toArray args vs) * mallocHeap 0 * F.
    intros; sepLemma.
    etransitivity; [ | apply is_state_in ]; auto.
    sepLemma.
  Qed.

  Lemma replace_imp : forall specs P P' Q st,
    P ===> P'
    -> interp specs (![P'] st ---> Q)%PropX
    -> interp specs (![P] st ---> Q)%PropX.
    intros.
    eapply Imply_trans; try apply H0.
    rewrite sepFormula_eq.
    apply H.
  Qed.

  Import LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake.

  Require Import Bedrock.Platform.Cito.SemanticsUtil.

  Opaque mult.

  Theorem is_state_out'' : forall sp rp args pairs vs e_stack e_stack',
    NoDup args
    -> ~List.In "rp" args
    -> ~List.In "extra_stack" args
    -> length args = length pairs
    -> is_state sp rp e_stack e_stack' nil
    (vs, make_heap pairs) (List.map fst pairs)
    ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
    * is_heap (make_heap pairs) * [| sel vs' "extra_stack" = e_stack |]
    * [| saved_vars vs' args pairs |].
    unfold is_state, locals, Inv.has_extra_stack; simpl.
    intros.
    apply Himp_ex_c.
    exists (upd (upd (zip_vals args pairs) "extra_stack" e_stack) "rp" rp).
    selify.
    replace (S (S (length args)) * 4)%nat with (8 + 4 * length args)%nat by omega.
    rewrite map_length.
    rewrite <- H2.
    rewrite natToWord_plus.
    eapply Himp_trans; [ | do 4 (apply Himp_star_frame; [ | apply Himp_refl ]);
      apply Himp_star_frame; [ apply Himp_refl | apply ptsto32m'_out ] ].
    simpl.
    unfold SemanticsMake.ArgIn.
    generalize (List.map fst pairs); intro.
    unfold array at 1; simpl.
    sepLemma.
    do 2 (apply saved_vars_irrel; auto).
    eauto using saved_vars_zip_vars.

    etransitivity; [ apply himp_star_comm | ].
    apply himp_star_frame.
    etransitivity; [ | apply Arrays.ptsto32m'_in ].
    etransitivity; [ | apply ptsto32m_shift_base ].
    unfold array.
    instantiate (1 := 8).
    simpl.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    reflexivity.
    auto.
    rewrite <- wplus_assoc.
    rewrite <- natToWord_plus.
    unfold natToW.
    sepLemma.
  Qed.

  Theorem is_state_out' : forall sp rp F vs e_stack e_stack',
    (is_state sp rp e_stack e_stack' nil
      (vs, heap_empty) nil * mallocHeap 0) * F
    ===> Ex vs', locals ("rp" :: "extra_stack" :: nil) vs' e_stack' sp
    * [| sel vs' "extra_stack" = e_stack|]
    * mallocHeap 0 * F.
    intros.
    change heap_empty with (@make_heap ADTValue nil).
    change (@nil W) with (List.map (@fst W ArgIn) nil).
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]); apply is_state_out'' | ]; eauto.
    instantiate (1 := 0); simpl; tauto.
    simpl; tauto.
    auto.
    sepLemma.
  Qed.
  Require Import Coq.Arith.Mult.
  Require Import Bedrock.Platform.Cito.WordFacts.

  Theorem is_state_in'' : forall vs sp args e_stack h, locals ("rp" :: "extra_stack" :: args) vs e_stack sp * is_heap h ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack args (vs, h) nil.
  Proof.
    intros; sepLemma.
    set (_ :: _ :: _).
    set (_ * _)%Sep.
    etransitivity.
    instantiate (1 := (h0 * [| NoDup l |])%Sep).
    subst h0 l.
    unfold locals.
    set (array _ _).
    sepLemma.
    subst h0 l.
    sepLemma.
    etransitivity.
    etransitivity.
    2 : eapply is_state_in.
    sepLemma.
    change LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake2.is_state with is_state.
    unfold is_state, Inv.has_extra_stack, locals, array.
    sepLemma.
    inversion_clear H.
    inversion_clear H2.
    eauto.
    fold (@length W).
    rewrite mult_0_r.
    rewrite wplus_0.
    rewrite plus_0_r.
    rewrite length_toArray.
    sepLemma.
  Qed.

  Theorem is_state_in''' : forall vs sp args e_stack F,
                             locals ("rp" :: "extra_stack" :: args) vs e_stack sp
                             * mallocHeap 0 * F
                                                ===> is_state sp (sel vs "rp") (wordToNat (sel vs "extra_stack")) e_stack args
                                                (vs, heap_empty) nil * mallocHeap 0 * F.
    intros; sepLemma.
    etransitivity; [ | apply is_state_in'' ]; auto.
    sepLemma.
  Qed.

  Lemma toArray_map_length : forall A vs f ls1 ls2, toArray ls1 vs = @List.map A _ f ls2 -> length ls1 = length ls2.
    intros.
    eapply f_equal with (f := @length _) in H.
    rewrite length_toArray in *.
    rewrite map_length in *.
    eauto.
  Qed.

  Ltac clear_all :=
    repeat match goal with
             | H : _ |- _ => clear H
           end.

  Theorem is_state_out''' : forall sp rp args pairs vs e_stack e_stack',
                              NoDup args
                              -> ~List.In "rp" args
                              -> ~List.In "extra_stack" args
                              -> toArray args vs = List.map fst pairs
                              -> is_state sp rp e_stack e_stack' args
                                          (vs, make_heap pairs) nil
                                          ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
                                                       * is_heap (make_heap pairs) * [| sel vs' "extra_stack" = e_stack |]
                                                       * [| saved_vars vs' args pairs |].
    unfold Himp; intros.
    etransitivity.
    2 : eapply is_state_out''; eauto.
    2 : eapply toArray_map_length; eauto.
    change LinkSpecMake2.CompileFuncSpecMake.InvMake2.is_state with is_state.
    unfold is_state, locals, Inv.has_extra_stack; simpl.
    rewrite H2.
    rewrite mult_0_r.
    rewrite wplus_0.
    set (array (List.map _ _) _).
    set (is_heap _).
    rewrite map_length.
    replace (length args) with (length pairs).
    rewrite plus_0_r.
    clear_all.
    sepLemma.
    symmetry; eapply toArray_map_length; eauto.
    Grab Existential Variables.
    eauto.
  Qed.

  Lemma make_heap_heap_empty : forall ls, make_heap (List.map (fun w : W => (w, SCA _ w)) ls) = heap_empty.
    induction ls; simpl; intuition.
  Qed.

  Lemma map_id : forall A ls, List.map (fun x : A => x) ls = ls.
    induction ls; simpl; intuition.
  Qed.

  Theorem is_state_out'''' : forall vs sp rp F e_stack e_stack' args,
                               NoDup args
                               -> ~List.In "rp" args
                               -> ~List.In "extra_stack" args
                               -> (is_state sp rp e_stack e_stack' args
                                            (vs, heap_empty) nil * mallocHeap 0) * F
                                                                                     ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
                                                                                                  * [| sel vs' "extra_stack" = e_stack|]
                                                                                                  * mallocHeap 0 * F.
    intros.
    assert (make_heap (List.map (fun w => (w, SCA ADTValue w)) (toArray args vs)) = heap_empty).
    eapply make_heap_heap_empty.
    rewrite <- H2.
    eapply Himp_trans; [ do 2 (apply Himp_star_frame; [ | apply Himp_refl ]); apply is_state_out''' | ]; eauto.
    rewrite map_map; simpl.
    symmetry; eapply map_id.
    rewrite H2.
    set (_ :: _ :: _).
    set (List.map _ _).
    clear_all.
    sepLemma.
  Qed.

  Require Import Bedrock.Platform.Cito.WordMap.
  Lemma length_nil : forall A ls, @length A ls = 0 -> ls = nil.
    destruct ls; simpl in *; intuition.
  Qed.

  Theorem is_state_out''''' : forall vs h sp rp F e_stack e_stack' args,
                               NoDup args
                               -> ~List.In "rp" args
                               -> ~List.In "extra_stack" args
                               -> WordMap.Equal h heap_empty
                               -> (is_state sp rp e_stack e_stack' args
                                            (vs, h) nil * mallocHeap 0) * F
                                                                                     ===> Ex vs', locals ("rp" :: "extra_stack" :: args) vs' e_stack' sp
                                                                                                  * [| sel vs' "extra_stack" = e_stack|]
                                                                                                  * mallocHeap 0 * F.
    intros.
    unfold is_state.
    unfold is_heap.
    simpl.
    set (InvMake.SemanticsMake.heap_elements _).
    unfold InvMake.SemanticsMake.heap_elements in l.
    assert (l = nil).
    assert (WordMap.cardinal h = 0).
    rewrite H2.
    reflexivity.
    rewrite WordMap.cardinal_1 in H3.
    subst l.
    eapply length_nil; eauto.
    subst l.
    rewrite H3.
    replace (_ * array _ _ * _ * _ * _)%Sep with (is_state sp rp e_stack e_stack' args (vs, heap_empty) nil).
    Focus 2.
    unfold is_state.
    unfold is_heap.
    sepLemma.
    clear H2 H3.
    eapply is_state_out''''; eauto.
  Qed.

  Transparent mult.

  (* linking *)

  Require Import Bedrock.Platform.Cito.GoodOptimizer Bedrock.Platform.Cito.optimizers.ConstFolding Bedrock.Platform.Cito.optimizers.ElimDead.

  Definition opt := compose ConstFolding.opt ElimDead.opt.

  Module Import GoodOptimizerMake := GoodOptimizer.Make E.
  Module Import ConstFoldingMake := ConstFolding.Make E.
  Module Import ElimDeadMake := ElimDead.Make E.

  Lemma opt_good : GoodOptimizer opt.
    eapply GoodOptimizer_trans.
    eapply ConstFoldingMake.good_optimizer.
    eapply ElimDeadMake.good_optimizer.
  Qed.

  Require Import Bedrock.Platform.Cito.Link.
  Module Import LinkMake := Link.Make E M.

  Require Import Bedrock.Platform.Cito.GeneralTactics2.

  Import LabelMapFacts.
  Import LinkModuleImplsMake.

  Import StringSetFacts.
  Require Import Bedrock.Platform.Cito.StructuredModuleFacts.
  Require Import Bedrock.Platform.Cito.ConvertLabelMap.
  Import GLabelMapFacts.

  Import GLabelMap.

  Definition compile_to_bedrock modules imports := result modules imports opt_good.

  Require Import Bedrock.Platform.Cito.LinkFacts.
  Module Import LinkFactsMake := Make E.

  Ltac impl_ok :=
    match goal with
      | |- moduleOk (compile_to_bedrock ?Modules ?Imports ) =>
        let H := fresh in
        assert (GoodToLink_bool Modules Imports = true);
          [ unfold GoodToLink_bool; simpl |
            eapply GoodToLink_bool_sound in H; openhyp; simpl in *; eapply result_ok; simpl in * ]
          ; eauto
    end.

  Ltac ok_simpl :=
    simpl Imports; simpl Exports; unfold CompileModuleMake.mod_name; unfold impl_module_name;
      simpl GName; simpl append; unfold CompileModuleMake.imports;
        unfold LinkMake.StubsMake.StubMake.bimports_diff_bexports, StubsMake.StubMake.bimports_diff_bexports;
          unfold diff_map, GLabelMapFacts.diff_map; simpl List.filter;
            unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.func_impl_export, StubsMake.StubMake.LinkSpecMake2.func_impl_export;
              unfold LinkMake.StubsMake.StubMake.LinkSpecMake2.impl_label, StubsMake.StubMake.LinkSpecMake2.impl_label;
                simpl GName; unfold impl_module_name; simpl append; simpl IsGoodModule.FName; link_simp.

  Ltac link0 ok1 :=
    eapply linkOk; [ eapply ok1 | impl_ok
                     | reflexivity
                     | ok_simpl; unfold CompileModuleMake.mod_name; unfold impl_module_name;
                       simpl; unfold StubsMake.StubMake.bimports_diff_bexports;
                       simpl; unfold StubsMake.StubMake.LinkSpecMake2.func_impl_export;
                       simpl; unfold StubsMake.StubMake.LinkSpecMake2.impl_label;
                       unfold impl_module_name; simpl; unfold CompileModuleMake.imports; simpl;
                       link_simp; eauto ..
                   ].

  Ltac link m1 m2 :=
    apply linkOk; [ apply m1 | apply m2 | exact (refl_equal true)
      | ok_simpl; tauto | ok_simpl; tauto | ok_simpl; tauto ].

  Require Import Bedrock.Platform.Safety Bedrock.Platform.Bootstrap.

  Ltac safety ok := eapply Safety.safety; try eassumption; [
    ok_simpl; unfold Safety.labelSys, Safety.labelSys'; simpl; tauto
    | apply ok
    | apply LabelMap.find_2; ok_simpl; reflexivity
    | propxFo; apply materialize_allocated; assumption ].

  Export Notations3 IsGoodModule Malloc LinkSpecMake.SemanticsMake FuncCore LinkSpec.
  Export CompileFuncSpec LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake GeneralTactics.
  Export LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
End Make.
