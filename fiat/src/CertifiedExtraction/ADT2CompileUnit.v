Require Import Fiat.ADT.Core.
Require Import Bedrock.Platform.Facade.DFModule.
Require Import Fiat.ADTNotation.
Require Import Bedrock.Platform.Facade.CompileUnit2.
Require Import Fiat.Common.i3list.
Require Import Fiat.Common.ilist3.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.

Add Parametric Morphism av
  : (@RunsTo av)
    with signature
    (GLabelMapFacts.Submap ==> eq ==> StringMap.Equal ==> StringMap.Equal ==> impl)
      as Proper_RunsTo.
Proof.
  unfold impl; intros.
  revert y y1 y2 H0 H1 H.
  induction H2; intros.
  - econstructor; rewrite <- H0, <- H1; eauto.
  - econstructor 2; eauto.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 3; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 4; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 5; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 6; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H1; apply H.
    rewrite <- H1, <- H2; eauto.
  - econstructor 7;
    rewrite <- H2; eauto.
    rewrite <- H1; symmetry; eauto.
  - econstructor 8; eauto.
    rewrite <- H6; eauto.
    rewrite <- H6; eauto.
    rewrite <- H7.
    subst st'; subst st'0; rewrite <- H6; eauto.
  - econstructor 9; eauto.
    rewrite <- H7; eauto.
    rewrite <- H7; eauto.
    eapply IHRunsTo; eauto.
    reflexivity.
    reflexivity.
    subst st'; subst st'0; subst output; rewrite <- H8.
    rewrite <- H7; eauto.
Qed.

Record GoodWrapper av A :=
  { gWrap : FacadeWrapper (Value av) A;
    gWrapTag : bool;
    gWrapTagConsistent :
      if gWrapTag then
        forall a : A, exists adt, wrap a = ADT adt
      else
        forall a : A, exists w, wrap a = SCA _ w }.

Lemma GoodWrapperConsistent {av A} (gWrapper : GoodWrapper av A) :
  forall a1 a2: A, is_same_type (@wrap _ _ (gWrap gWrapper) a1) (@wrap _ _ (gWrap gWrapper) a2).
Proof.
  intros.
  unfold is_same_type.
  pose proof (gWrapTagConsistent gWrapper).
  find_if_inside; destruct (H a1); destruct (H a2); rewrite H0, H1; eauto.
Qed.

Definition CodWrapperT av (Cod : option Type) :=
  match Cod with
  | None => unit
  | Some CodT => GoodWrapper av CodT
  end.

Fixpoint DomWrapperT av (Dom : list Type) : Type :=
  match Dom with
  | nil => unit
  | cons DomT Dom' => prod (GoodWrapper av DomT)
                           (DomWrapperT av Dom')
  end.

Definition nthArgName n := "arg" ++ (NumberToString n).
Definition nthRepName n := "rep" ++ (NumberToString n).

Fixpoint list2Telescope av
         (l : list {T : _ & prod (NameTag av T) (Comp T)})
  : Telescope av:=
  match l with
  | nil => Nil
  | cons a l' => Cons (fst (projT2 a)) (snd (projT2 a)) (fun _ => list2Telescope l')
  end.

Fixpoint LiftMethod' (av : Type) (env : Env av) {Rep} {Cod} {Dom}
         (P : Rep -> Prop)
         (DecomposeRep : Rep -> Telescope av)
         (DecomposeRepPre : list {T : _ & prod (NameTag av T) (Comp T)})
         {struct Dom}
  :=
    match Dom return
          CodWrapperT av Cod
          -> DomWrapperT av Dom
          -> Stmt
          -> list {T : _ & prod (NameTag av T) (Comp T)}
          -> methodType' Rep Dom Cod
          -> Prop with
    | nil => match Cod return
                   CodWrapperT av Cod
                   -> DomWrapperT av nil
                   -> Stmt
                   -> list {T : _ & prod (NameTag av T) (Comp T)}
                   -> methodType' Rep nil Cod
                   -> Prop with
             | None => fun cWrap dWrap prog pre meth =>
                         {{ list2Telescope (pre ++ DecomposeRepPre) }}
                           prog
                           {{ [[meth as database]]
                                :: [[`"ret" ->> Word.natToWord 32 0 as _]]
                                :: (DecomposeRep database) }} ∪ {{ StringMap.empty _ }} // env
                         /\ forall r', computes_to meth r' -> P r'


             | Some CodT => fun cWrap dWrap prog pre meth =>
                              let v : FacadeWrapper (Value av) CodT := (gWrap cWrap) in
                              {{ list2Telescope (pre ++ DecomposeRepPre) }}
                                prog
                                {{[[meth as mPair]]
                                    :: [[`"ret" ->> snd mPair as _]]
                                    :: (DecomposeRep (fst mPair))}}  ∪ {{ StringMap.empty _ }} // env
                              /\ forall r' v', computes_to meth (r', v') -> P r'
             end
    | cons DomT Dom' =>
      fun cWrap dWrap prog tele meth =>
        forall d, let _ := gWrap (fst dWrap) in LiftMethod' env Dom' P DecomposeRep DecomposeRepPre cWrap (snd dWrap) prog ((existT _ _ (NTSome (nthArgName (List.length tele)), ret d)) :: tele) (meth d)
    end.

Definition LiftMethod
           (av : Type)
           env
           {Rep}
           {Cod}
           {Dom}
           (P : Rep -> Prop)
           (DecomposeRep : Rep -> list {T : _ & prod (NameTag av T) (Comp T)})
           (cWrap : CodWrapperT av Cod)
           (dWrap : DomWrapperT av Dom)
           (prog : Stmt)
           (meth : methodType Rep Dom Cod)
  : Prop :=
  forall r,
    P r ->
    LiftMethod' env Dom P (fun r => list2Telescope (DecomposeRep r)) (DecomposeRep r) cWrap dWrap prog [] (meth r).

Arguments LiftMethod [_] _ {_ _ _} _ _ _ _ _ _ / .

Arguments NumberToString _ / .

Lemma NoDup_is_no_dup
  : forall l, NoDup l -> ListFacts3.is_no_dup l = true.
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - inversion H; subst.
    apply Bool.andb_true_iff; split; eauto.
    apply forallb_forall; intros.
    unfold ListFacts3.string_bool; destruct (string_dec x a);
    subst; simpl; eauto.
Qed.

Lemma NoDup_rev {A} :
  forall (l : list A),
    NoDup l <-> NoDup (rev l).
Proof.
  induction l; simpl; split; eauto.
  - intros; apply ListFacts1.NoDup_app.
    + inversion H; subst; eapply IHl; eauto.
    + repeat econstructor; eauto.
    + unfold ListFacts1.Disjoint; unfold not; intros.
      inversion H; subst; apply H3.
      intuition; inversion H2; subst; eauto.
      * apply in_rev; auto.
      * inversion H5.
  - intros; pose proof (NoDup_remove_1 _ nil a H);
    pose proof (NoDup_remove_2 _ nil a H).
    rewrite app_nil_r in *.
    econstructor.
    + setoid_rewrite in_rev; eauto.
    + apply IHl; auto.
Qed.

Lemma app_inj
  : forall (A : Type) (l1 l1' l2 l2' : list A),
    List.length l1' = List.length l2'
    -> (l1' ++ l1)%list = (l2' ++ l2)%list
    -> l1' = l2' /\ l1 = l2.
Proof.
  induction l1'; destruct l2'; simpl; intros; try discriminate;
  intuition.
  injections; eauto.
  destruct (IHl1' l2 l2'); eauto; subst; eauto.
  injections; eauto.
  destruct (IHl1' l2 l2'); eauto; subst; eauto.
Qed.

Definition DFModuleEquiv
           av
           (env : Env av)
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           (P : Core.Rep adt -> Prop)
           (module : DFModule av)
           (consWrapper' : forall midx, CodWrapperT av (methCod (Vector.nth methSigs midx)))
           (domWrapper : forall midx, DomWrapperT av (methDom (Vector.nth methSigs midx)))
           (DecomposeRep : Core.Rep adt -> _)
           (DecomposeRepCount : nat)
  : Prop :=
  (* Environments match *)
  (* FIXME : (module.(Imports) = env) *)
  (* Method Correspondence *)
  forall midx : Fin.t n',
      let meth := Vector.nth methSigs midx in
      exists Fun,
        Fun.(Core).(RetVar) = "ret"
        /\ Fun.(Core).(ArgVars) = BuildArgNames (List.length (methDom meth)) DecomposeRepCount
        /\ LiftMethod env P DecomposeRep (consWrapper' midx) (domWrapper midx) (Body (Core Fun))
                      (Methods adt midx)
        /\ (StringMap.MapsTo (methID meth) Fun module.(Funs)).

Fixpoint AxiomatizeMethodPre'
         (av : Type)
         (RepArgs : list (Value av))
         {Dom}
         {struct Dom}
  : DomWrapperT av Dom
    -> list (Value av)
    -> list (Value av) -> Prop
  :=
    match Dom return
          DomWrapperT av Dom
          -> list (Value av)
          -> list (Value av)
          -> Prop with
    | nil => fun dWrap args' args =>
               app args' RepArgs = args
    | cons DomT Dom' =>
      fun dWrap args' args =>
        let wrap' := gWrap (fst dWrap) in
        exists x : DomT, AxiomatizeMethodPre' RepArgs Dom' (snd dWrap) (wrap x :: args') args
    end.

Definition AxiomatizeMethodPreSpec (av : Type)
           {RepImpl RepSpec}
           {Dom}
           {numRepArgs : nat}
           (AbsR : RepSpec -> RepImpl -> Prop)
           (P : RepImpl -> Prop)
           (f : RepImpl -> Vector.t (Value av) numRepArgs)
  : DomWrapperT av Dom
    -> list (Value av) -> Prop
  :=
    fun dWrap args =>
      exists r r', AbsR r r'
                   /\ P r'
                   /\ AxiomatizeMethodPre' (Vector.to_list (f r')) Dom dWrap [] args.

Fixpoint AxiomatizeMethodPostSpec'
         {Dom}
         {Cod}
         {RepSpec RepImpl}
         (av : Type)
         {numRepArgs : nat}
         (AbsR : RepSpec -> RepImpl -> Prop)
         {struct Dom}
  : CodWrapperT av Cod
    -> DomWrapperT av Dom
    -> list ((Value av) * option av)
    -> (RepImpl -> Vector.t ((Value av) * option av) numRepArgs)
    -> methodType' RepSpec Dom Cod
    -> list ((Value av) * option av) -> Value av -> Prop
  :=
    match Dom return
          CodWrapperT av Cod
          -> DomWrapperT av Dom
          -> list ((Value av) * option av)
          -> (RepImpl -> Vector.t ((Value av) * option av) numRepArgs)
          -> methodType' RepSpec Dom Cod
          -> list ((Value av) * option av)
          -> Value av -> Prop with
    | nil => match Cod return
                   CodWrapperT av Cod
                   -> DomWrapperT av nil
                   -> list ((Value av) * option av)
                   -> (RepImpl -> Vector.t ((Value av) * option av) numRepArgs)
                   -> methodType' RepSpec nil Cod
                   -> list ((Value av) * option av)
                   -> Value av -> Prop with
             | None => fun cWrap dWrap domArgs repArgs meth args ret =>
                         exists (r' : RepSpec)
                                (r'' : RepImpl),
                           computes_to meth r'
                           /\ AbsR r' r''
                           /\ args = List.app (domArgs) (Vector.to_list (repArgs r''))
                           /\ ret = wrap (Word.natToWord 32 0)
             | Some CodT => fun cWrap dWrap domArgs repArgs meth args ret =>
                              exists r' r'' v',
                                computes_to meth (r', v')
                                /\ AbsR r' r''
                                /\ args = List.app (domArgs) (Vector.to_list (repArgs r''))
                                /\ ret = wrap (FacadeWrapper := gWrap cWrap) v'
             end
    | cons DomT Dom' =>
      fun cWrap dWrap domArgs repArgs meth args ret =>
        let wrap' := gWrap (fst dWrap) in
        exists x : DomT,
          AxiomatizeMethodPostSpec'
            AbsR cWrap (snd dWrap)
            ((wrap x, None) :: domArgs)
            repArgs (meth x) args ret
    end.

Definition AxiomatizeMethodPostSpec
           (av : Type)
           {Dom}
           {Cod}
           {RepSpec RepImpl}
           {numRepArgs : nat}
           (AbsR : RepSpec -> RepImpl -> Prop)
           (f : RepImpl -> RepImpl -> Vector.t ((Value av) * option av) numRepArgs)
           (cWrap : CodWrapperT av Cod)
           (dWrap : DomWrapperT av Dom)
           (meth : methodType RepSpec Dom Cod)
           (args : list ((Value av) * option av))
           (ret : Value av)
  : Prop :=
  exists r' r,
    AbsR r r'
    /\ AxiomatizeMethodPostSpec' AbsR cWrap dWrap [] (f r') (meth r) args ret.

Lemma GenAxiomaticSpecs_type_conforming
      av
      {Dom}
      {RepSpec RepImpl}
      (AbsR : RepSpec -> RepImpl -> Prop)
      (RepInv : RepImpl -> Prop)
      (dWrap : DomWrapperT av Dom)
      {numRepArgs : nat}
      (DecomposeRepPre : RepImpl -> Vector.t (Value av) numRepArgs)
      (_ : forall x x0, is_same_types (Vector.to_list (DecomposeRepPre x0))
                                      (Vector.to_list (DecomposeRepPre x)) = true)
  : type_conforming (AxiomatizeMethodPreSpec AbsR RepInv DecomposeRepPre dWrap).
Proof.
  unfold type_conforming.
  unfold AxiomatizeMethodPreSpec in *.
  remember nil; remember l.
  assert (is_same_types l0 l = true)
    by (rewrite <- Heql0, Heql; reflexivity).
  intros; rewrite Heql0 in H2.
  generalize dependent DecomposeRepPre.
  generalize dependent Rep.
  generalize numRepArgs.
  generalize l l0 H3 H0; clear.
  induction Dom; simpl; repeat cleanup.
  - unfold is_same_types in H0.
    revert H0 H H3; clear.
    revert l0.
    induction l; destruct l0; simpl in *;
    intros; try discriminate.
    + eauto.
    + apply Bool.andb_true_iff in H0; intuition.
      unfold is_same_types in *; simpl; rewrite H1; simpl.
      eapply IHl; eauto.
  - destruct dWrap.
    eapply IHDom with (l := wrap (FacadeWrapper := gWrap g) x1 :: l)
                        (l0 := wrap (FacadeWrapper := gWrap g) x4 :: l0);
      eauto.
    unfold is_same_types in *.
    simpl; rewrite H0.
    rewrite GoodWrapperConsistent; simpl; eauto.
Qed.

Definition GenAxiomaticSpecs
           av
           {Cod}
           {Dom}
           {RepSpec RepImpl}
           (AbsR : RepSpec -> RepImpl -> Prop)
           (RepInv : RepImpl -> Prop)
           (cWrap : CodWrapperT av Cod)
           (dWrap : DomWrapperT av Dom)
           (meth : methodType RepSpec Dom Cod)
           {numRepArgs : nat}
           (DecomposeRepPre : RepImpl -> Vector.t (Value av) numRepArgs)
           (DecomposeRepPost : RepImpl -> RepImpl -> Vector.t ((Value av) * option av) numRepArgs)
           (H : forall x x0, is_same_types (Vector.to_list (DecomposeRepPre x0))
                                           (Vector.to_list (DecomposeRepPre x)) = true)
  : AxiomaticSpec av :=
  {| PreCond := AxiomatizeMethodPreSpec AbsR RepInv DecomposeRepPre dWrap;
     PostCond := AxiomatizeMethodPostSpec AbsR DecomposeRepPost cWrap dWrap meth;
     PreCondTypeConform := GenAxiomaticSpecs_type_conforming H
  |}.

Fixpoint BuildFinUpTo (n : nat) {struct n} : list (Fin.t n) :=
  match n return list (Fin.t n) with
  | 0  => nil
  | S n' => cons (@Fin.F1 _) (map (@Fin.FS _) (BuildFinUpTo n'))
  end.

Definition GenExports
           av
           (n n' : nat)
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adtSpec : DecoratedADT (BuildADTSig consSigs methSigs))
           (adtImpl : DecoratedADT (BuildADTSig consSigs methSigs))
           (consWrapper : (forall midx, CodWrapperT av (methCod (Vector.nth methSigs midx))))
           (domWrapper : (forall midx,  DomWrapperT av (methDom (Vector.nth methSigs midx))))
           (AbsR : Core.Rep adtSpec -> Core.Rep adtImpl -> Prop)
           (RepInv : Core.Rep adtImpl -> Prop)
           {numRepArgs : nat}
           (f : Core.Rep adtImpl -> Vector.t (Value av) numRepArgs)
           (f' : Core.Rep adtImpl -> Core.Rep adtImpl -> Vector.t ((Value av) * option av) numRepArgs)
           (H : forall x x0, is_same_types (Vector.to_list (f x0)) (Vector.to_list (f x)) = true)
           (ValidImpl : refineADT adtSpec adtImpl)
  : StringMap.t (AxiomaticSpec av) :=
  List.fold_left (fun acc el => StringMap.add (methID (Vector.nth methSigs el))
                                              (GenAxiomaticSpecs AbsR RepInv (consWrapper el) (domWrapper el) (Methods adtSpec el) f f' H) acc) (BuildFinUpTo n') (StringMap.empty _).

Definition CompileUnit2Equiv
           av
           env
           {A}
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           RepInv
           (f : A -> _)
           g
           ax_mod_name'
           op_mod_name'
           cWrap
           dWrap
           rWrap
           {exports}
           (compileUnit : CompileUnit exports)
  :=
    DFModuleEquiv (av := av) env adt RepInv compileUnit.(module) cWrap dWrap (f rWrap) g
    /\ compileUnit.(ax_mod_name) = ax_mod_name'
    /\ compileUnit.(op_mod_name) = op_mod_name'.

Definition BuildCompileUnit2TSpec
           av
           (env : Env av)
           {A}
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adtSpec : DecoratedADT (BuildADTSig consSigs methSigs))
           (adtImpl : DecoratedADT (BuildADTSig consSigs methSigs))
           (AbsR : Core.Rep adtSpec -> Core.Rep adtImpl -> Prop)
           RepInv
           numRepArgs
           (DecomposeRep : A -> _)
           DecomposeRepPre
           DecomposeRepPost
           g
           ax_mod_name'
           op_mod_name'
           cWrap
           dWrap
           rWrap
           H
           ValidImpl
           (exports := GenExports (numRepArgs := numRepArgs) cWrap dWrap AbsR RepInv DecomposeRepPre DecomposeRepPost H ValidImpl) :=
  {compileUnit : CompileUnit exports & (CompileUnit2Equiv env adtImpl RepInv DecomposeRep g ax_mod_name' op_mod_name' cWrap dWrap rWrap compileUnit) }.

  Lemma IsInjection_nthArgName
    : ListFacts1.IsInjection nthArgName.
  Proof.
    unfold ListFacts1.IsInjection.
    unfold nthArgName, not; intros.
    apply H.
    injections.
    destruct x; destruct y; simpl.
    + congruence.
    + elimtype False.
      symmetry in H1; apply (fun H H' => NumberToString_rec_10 _ _ H H' H1);
      auto with arith.
    + elimtype False.
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H1);
        auto with arith.
    + rewrite (@NumberToString_rec_inj' (S x) x y (S y));
      auto with arith.
  Qed.

  Lemma IsInjection_nthRepName
    : ListFacts1.IsInjection nthRepName.
  Proof.
    unfold ListFacts1.IsInjection.
    unfold nthRepName, not; intros.
    apply H.
    injections.
    destruct x; destruct y; simpl.
    + congruence.
    + elimtype False.
      symmetry in H1; apply (fun H H' => NumberToString_rec_10 _ _ H H' H1);
      auto with arith.
    + elimtype False.
      apply (fun H H' => NumberToString_rec_10 _ _ H H' H1);
        auto with arith.
    + rewrite (@NumberToString_rec_inj' (S x) x y (S y));
      auto with arith.
  Qed.

  Lemma BuildArgNamesNoDup n m
    : ListFacts3.is_no_dup (BuildArgNames n m) = true.
  Proof.
    apply NoDup_is_no_dup; unfold BuildArgNames.
    apply ListFacts1.NoDup_app; try rewrite <- NoDup_rev.
    - apply ListFacts1.Injection_NoDup.
      eapply IsInjection_nthArgName.
      apply NoDupNumUpTo; simpl; try constructor; intuition.
    - apply ListFacts1.Injection_NoDup.
      eapply IsInjection_nthRepName.
      apply NoDupNumUpTo; simpl; try constructor; intuition.
    - unfold ListFacts1.Disjoint, not; intros; intuition.
      rewrite <- in_rev in *.
      eapply in_map_iff in H0; eapply in_map_iff in H1;
      destruct_ex; intuition; subst.
      unfold nthRepName, nthArgName in H0; discriminate.
  Qed.

  Lemma BuildArgNames_args_name_ok
    : forall n m, forallb NameDecoration.is_good_varname (BuildArgNames n m) = true.
  Proof.
    intros; eapply forallb_forall; intros.
    unfold BuildArgNames in H; apply in_app_or in H; intuition;
    try rewrite <- in_rev in *;
    apply in_map_iff in H0; destruct_ex; intuition; subst;
    reflexivity.
  Qed.

  Lemma Ret_ret_name_ok : NameDecoration.is_good_varname "ret" = true.
  Proof.
    reflexivity.
  Qed.

  Lemma ret_NIn_BuildArgNames
    : forall n m, negb (is_in "ret" (BuildArgNames n m)) = true.
  Proof.
    intros.
    apply Bool.negb_true_iff.
    apply FacadeFacts.not_is_in_iff.
    intro.
    apply in_app_or in H; rewrite <- !in_rev in H; intuition; apply in_map_iff in H0.
    destruct_ex; intuition; unfold nthArgName in H0; discriminate.
    destruct_ex; intuition; unfold nthArgName in H0; discriminate.
  Qed.

Lemma BuildDFFun_is_syntax_ok
      av
      (* The calling environment is parameterized over an extension *)
      (* representing the operational specifications of the module. *)
      (env : StringMap.t DFFun -> Env av)
      {WrappedRepT RepT}
      cod
      dom
      WrappedCod
      WrappedDom
      meth
      RepInv
      (DecomposeRep : WrappedRepT -> RepT -> _)
      (numRepArgs : nat)
      wrappedRep
      (progOK : {prog : Stmt &
                        (forall env_ext,
                            LiftMethod (Cod := cod) (Dom := dom) (env env_ext)
                                       RepInv (DecomposeRep wrappedRep)
                                       WrappedCod WrappedDom prog meth)
                        (* Syntactic Checks *)
                        /\ NoUninitDec.is_no_uninited
                             {|
                               FuncCore.ArgVars := BuildArgNames (Datatypes.length dom) numRepArgs;
                               FuncCore.RetVar := "ret";
                               FuncCore.Body := Compile.compile
                                                  (CompileDFacade.compile prog) |} = true
                        /\ (GoodModuleDec.is_arg_len_ok
                              (Compile.compile (CompileDFacade.compile prog)) = true)
                        /\ (GoodModuleDec.is_good_size
                              (Datatypes.length
                                 (GetLocalVars.get_local_vars
                                    (Compile.compile (CompileDFacade.compile prog))
                                    (BuildArgNames (Datatypes.length dom) numRepArgs) "ret") +
                               Depth.depth (Compile.compile (CompileDFacade.compile prog))) =
                            true)
                        /\  is_disjoint (assigned prog)
                                        (StringSetFacts.of_list
                                           (BuildArgNames (Datatypes.length dom)
                                                          numRepArgs)) = true
                        /\ is_syntax_ok prog = true} )
  : FModule.is_syntax_ok
      (CompileDFacade.compile_op
         {|
           ArgVars := BuildArgNames (Datatypes.length dom) numRepArgs;
           RetVar := "ret";
           Body := projT1 progOK;
           args_no_dup := BuildArgNamesNoDup (Datatypes.length dom) numRepArgs;
           ret_not_in_args := ret_NIn_BuildArgNames (Datatypes.length dom)
                                                    numRepArgs;
           no_assign_to_args := proj1
                                  (proj2 (proj2 (proj2 (proj2 (projT2 progOK)))));
           args_name_ok := BuildArgNames_args_name_ok
                             (Datatypes.length dom) numRepArgs;
           ret_name_ok := Ret_ret_name_ok;
           syntax_ok := proj2 (proj2 (proj2 (proj2 (proj2 (projT2 progOK))))) |}) =
    true.
Proof.
  unfold FModule.is_syntax_ok; simpl.
  unfold GoodModuleDec.is_good_func; simpl.
  apply Bool.andb_true_iff; split; try eassumption.
  apply Bool.andb_true_iff; split; try eassumption.
  apply Bool.andb_true_iff; split; try eassumption.
  apply BuildArgNamesNoDup.
  destruct progOK; simpl in *; intuition.
  destruct progOK; simpl in *; intuition.
  destruct progOK; simpl in *; intuition.
Qed.

Definition BuildDFFun
           av
           (* The calling environment is parameterized over an extension *)
           (* representing the operational specifications of the module. *)
           (env : StringMap.t DFFun -> Env av)
           {WrappedRepT RepT}
           cod
           dom
           WrappedCod
           WrappedDom
           meth
           RepInv
           (DecomposeRep : WrappedRepT -> RepT -> _)
           (numRepArgs : nat)
           wrappedRep
           (progOK : {prog : Stmt &
                             (forall env_ext,
                             LiftMethod (Cod := cod) (Dom := dom) (env env_ext) RepInv (DecomposeRep wrappedRep)
                                        WrappedCod WrappedDom prog meth)
                             (* Syntactic Checks *)
                             /\ NoUninitDec.is_no_uninited
                                  {|
                                    FuncCore.ArgVars := BuildArgNames (Datatypes.length dom) numRepArgs;
                                    FuncCore.RetVar := "ret";
                                    FuncCore.Body := Compile.compile
                                                       (CompileDFacade.compile prog) |} = true
                             /\ (GoodModuleDec.is_arg_len_ok
                                   (Compile.compile (CompileDFacade.compile prog)) = true)
                             /\ (GoodModuleDec.is_good_size
                                   (Datatypes.length
                                      (GetLocalVars.get_local_vars
                                         (Compile.compile (CompileDFacade.compile prog))
                                         (BuildArgNames (Datatypes.length dom) numRepArgs) "ret") +
                                    Depth.depth (Compile.compile (CompileDFacade.compile prog))) =
                                 true)
                             /\  is_disjoint (assigned prog)
                                             (StringSetFacts.of_list
                                                (BuildArgNames (Datatypes.length dom)
                                                               numRepArgs)) = true
                             /\ is_syntax_ok prog = true} )
  : DFFun :=
  {| Core := {| ArgVars := BuildArgNames (List.length dom) numRepArgs;
                RetVar := "ret";
                Body := projT1 progOK;
                args_no_dup := BuildArgNamesNoDup _ _;
                ret_not_in_args := ret_NIn_BuildArgNames _ _;
                no_assign_to_args := proj1 (proj2 (proj2 (proj2 (proj2 (projT2 progOK)))));
                args_name_ok := BuildArgNames_args_name_ok _ _;
                ret_name_ok := Ret_ret_name_ok;
                syntax_ok := proj2 (proj2 (proj2 (proj2 (proj2 (projT2 progOK)))))

             |};
     compiled_syntax_ok := BuildDFFun_is_syntax_ok _ _ _ _ progOK
  |}.

Definition BuildFun
           av
           (* The calling environment is parameterized over an extension *)
           (* representing the operational specifications of the module. *)
           (env : StringMap.t DFFun -> Env av)
           {WrappedRepT}
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           P
           (DecomposeRep : WrappedRepT -> Rep adt -> _)
           (DecomposeRepCount : nat)
           codWrap
           domWrap
           wrappedRep
           (progsOK : forall midx,
               {prog : Stmt &
                       (forall env_ext,
                       LiftMethod (env env_ext) P (DecomposeRep wrappedRep)
                                  (codWrap midx) (domWrap midx) prog (Methods adt midx))
                       (* Syntactic Checks *)
                       /\ NoUninitDec.is_no_uninited
                            {|
                              FuncCore.ArgVars := BuildArgNames (Datatypes.length _)
                                                                DecomposeRepCount;
                              FuncCore.RetVar := "ret";
                              FuncCore.Body := Compile.compile
                                                 (CompileDFacade.compile prog) |} = true
                       /\ (GoodModuleDec.is_arg_len_ok
                             (Compile.compile (CompileDFacade.compile prog)) = true)
                       /\ (GoodModuleDec.is_good_size
                             (Datatypes.length
                                (GetLocalVars.get_local_vars
                                   (Compile.compile (CompileDFacade.compile prog))
                                   (BuildArgNames (Datatypes.length _) DecomposeRepCount) "ret") +
                              Depth.depth (Compile.compile (CompileDFacade.compile prog))) =
                           true)
                       /\  is_disjoint (assigned prog)
                                       (StringSetFacts.of_list
                                          (BuildArgNames (Datatypes.length _)
                                                         DecomposeRepCount)) = true
                       /\ is_syntax_ok prog = true} )
  : StringMap.t DFFun :=
  List.fold_left (fun acc el => StringMap.add (methID (Vector.nth methSigs el))
                                              (BuildDFFun env DecomposeRep
                                                          _ wrappedRep (progsOK el) ) acc) (BuildFinUpTo n') (StringMap.empty _).

Lemma AxiomatizeMethodPostSpec_OK
      av
      {RepSpec RepImpl}
      AbsR
      {numRepArgs}
      cod dom
      codWrap domWrap
  : forall args DecomposeRepPost meth,
    exists is_ret_adt : bool,
      forall (in_out : list (Value av * option av)) (ret : Value av),
        (exists (r : RepImpl) (r' : RepSpec),
            AbsR r' r /\
            @AxiomatizeMethodPostSpec' dom cod RepSpec RepImpl av numRepArgs
                                       AbsR
                                       codWrap domWrap args
                                       (DecomposeRepPost r)
                                       (meth r') in_out ret) ->
        if is_ret_adt
        then exists a : av, ret = ADT a
        else exists w : W, ret = SCA av w.
Proof.
  destruct cod.
  - exists (gWrapTag codWrap); simpl; revert args DecomposeRepPost meth.
    induction dom; simpl in *; intros.
    + destruct H as [r [r' [r'' [v' [? [? [? [? [? ? ] ] ] ] ] ] ] ] ]; subst.
      pose proof (gWrapTagConsistent codWrap); find_if_inside; eauto.
    + destruct H as [r [r' [? [x ? ] ] ] ]; subst.
      eapply (IHdom (snd domWrap)
                    ((@wrap _ _ (gWrap (fst domWrap)) x, None) :: args)
                    (fun r r' => (DecomposeRepPost r r'))
                    (fun r => meth r x)
                    in_out); eauto.
  - exists false; simpl; revert args DecomposeRepPost meth.
    induction dom; simpl in *; intros.
    + destruct H as [r [r' [r'' [? [? [? [? [? ? ] ] ] ] ] ] ] ]; subst; eauto.
    + destruct H as [r [r' [? [x ? ] ] ] ]; subst; eauto.
      eapply (IHdom (snd domWrap)
                    ((@wrap _ _ (gWrap (fst domWrap)) x, None) :: args)
                    (fun r r' =>  DecomposeRepPost r r')
                    (fun r => meth r x)
                    in_out); eauto.
Qed.

Lemma NumUpTo_length :
  forall n l,
    Datatypes.length (NumUpTo n l) =
    n + Datatypes.length l.
Proof.
  induction n; simpl; intros; eauto.
  rewrite IHn; simpl; omega.
Qed.

Lemma length_Vector_to_list {A} {n} :
  forall (v : Vector.t A n),
    Datatypes.length (Vector.to_list v) = n.
Proof.
  induction v; simpl; eauto.
Qed.

Lemma length_AxiomatizeMethodPre' av dom domWrap
  : forall l l' l'', AxiomatizeMethodPre' (av := av) l'' dom domWrap l' l
                     -> Datatypes.length l' + Datatypes.length l'' + Datatypes.length dom = Datatypes.length l.
Proof.
  induction dom; simpl in *; intros; subst.
  - rewrite app_length; eauto.
  - destruct H.
    eapply IHdom in H; simpl in H.
    rewrite <- H; omega.
Qed.

(* Generic decomposition functions that ensure consistency among *)
(* the three decomposition functions. These functions depend on there *)
(* being a decomposition function that maps a representation type to  *)
(* an ilist3. *)

(* A List of wrappers for each of the decomposed representation types. *)
Fixpoint RepWrapperT
         av
         {n}
         {A : Type}
         {B : A -> Type}
         (C : forall a, B a -> Type)
         (As : Vector.t A n)
  : ilist3 (B := B) As -> Type :=
  match As return ilist3 (B := B) As -> Type with
  | Vector.nil =>
    fun il => unit
  | Vector.cons a _ As' =>
    fun il =>
      prod (FacadeWrapper av (C a (prim_fst il)))
           (RepWrapperT av C _ (prim_snd il))
  end.

(* Conversion from decomposed representation to a telescope for *)
(* operational specifications. *)
Fixpoint Decomposei3list
         av
         {n}
         {A}
         {B}
         {C}
         {As : Vector.t A n}
         {struct As}
  :
    forall (il : ilist3 (B := B) As),
      RepWrapperT av C As il
      -> i3list C il
      -> list {T : _ & prod (NameTag av T) (Comp T)} :=
  match As return
        forall (il : ilist3 (B := B) As),
          RepWrapperT av C As il
          -> i3list C il
          -> list {T : _ & prod (NameTag av T) (Comp T)} with
  | Vector.nil => fun as' rWrap r => nil
  | Vector.cons a n' As' => fun as' rWrap r =>
                              let fWrap' := fst rWrap in
                              cons (existT _ _ (NTSome (nthRepName n'), ret (prim_fst r))) (Decomposei3list As' (prim_snd as') (snd rWrap) (prim_snd r))
  end.

(* Conversion from a decomposed representation to a list of values *)
(* for axiomatic preconditions. *)
Fixpoint DecomposePrei3list
         av
         {n}
         {A}
         {B}
         {C}
         {As : Vector.t A n}
         {struct As}
  :
    forall (il : ilist3 (B := B) As),
      RepWrapperT av C As il
      -> i3list C il
      -> Vector.t (Value av) n :=
  match As in Vector.t _ n return
        forall (il : ilist3 (B := B) As),
          RepWrapperT av C As il
          -> i3list C il
          -> Vector.t (Value av) n with
  | Vector.nil => fun as' rWrap r => Vector.nil _
  | Vector.cons a n' As' => fun as' rWrap r =>
                              let fWrap' := fst rWrap in
                              Vector.cons _ (ADT (wrap (prim_fst r)))
                                          _ (DecomposePrei3list As' (prim_snd as') (snd rWrap)
                                                                (prim_snd r))
  end.

(* Conversion from a decomposed representation to a list of pairs of values *)
(* and option values for axiomatic preconditions. *)
Fixpoint DecomposePosti3list
         av
         {n}
         {A}
         {B}
         {C}
         {As : Vector.t A n}
         {struct As}
  :
    forall (il : ilist3 (B := B) As),
      RepWrapperT av C As il
      -> i3list C il
      -> i3list C il
      -> Vector.t (((Value av) * option av)) n :=
  match As in Vector.t _ n return
        forall (il : ilist3 (B := B) As),
          RepWrapperT av C As il
          -> i3list C il
          -> i3list C il
          -> Vector.t (((Value av) * option av)) n with
  | Vector.nil => fun as' rWrap r r' => Vector.nil _
  | Vector.cons a n' As' => fun as' rWrap r r' =>
                              let fWrap' := fst rWrap in
                              Vector.cons
                                _
                                (ADT (wrap (prim_fst r)), Some (wrap (prim_fst r')))
                                _
                                (DecomposePosti3list As' (prim_snd as') (snd rWrap)
                                                     (prim_snd r) (prim_snd r'))
  end.

Lemma DecomposePrei3list_Agree
      av
      {numRepArgs}
      {A}
      {B}
      {C}
      {RepT' : Vector.t A numRepArgs}
      (RepT : ilist3 (B := B) RepT')
      (RepWrapper : @RepWrapperT av numRepArgs A B C RepT' RepT)
  : forall r' r, is_same_types (Vector.to_list (DecomposePrei3list (C := C) RepT' RepT RepWrapper r))
                               (Vector.to_list (DecomposePrei3list (C := C) RepT' RepT RepWrapper r')) = true.
Proof.

  induction RepT'; simpl.
  - reflexivity.
  - intros.
    unfold Vector.to_list, is_same_types in *; simpl in *.
    apply IHRepT'.
Qed.

Lemma NumUpTo_app :
  forall n l l',
    NumUpTo n (l' ++ l) = List.app (NumUpTo n l') l.
Proof.
  induction n; simpl; intros; eauto.
  rewrite app_comm_cons.
  apply IHn.
Qed.

Corollary NumUpTo_nil :
  forall n l,
    NumUpTo n l = List.app (NumUpTo n []) l.
Proof.
  intros; apply (NumUpTo_app n l nil).
Qed.

Lemma nth_error_NumUpTo :
  forall m n l,
    lt m n
    -> nth_error (NumUpTo n l) m = Some m .
Proof.
  induction n; simpl; intros.
  - omega.
  - inversion H; subst; eauto.
    rewrite NumUpTo_nil.
    rewrite Expr.nth_error_app_R; rewrite NumUpTo_length; simpl; eauto.
    rewrite Plus.plus_comm; simpl; rewrite NPeano.Nat.sub_diag; reflexivity.
Qed.

Lemma nth_error_NumUpTo_lt :
  forall m n l v,
    lt m n
    -> nth_error (NumUpTo n l) m = Some v
    -> lt v n.
Proof.
  induction n; simpl; intros.
  - omega.
  - inversion H; subst; eauto.
    rewrite NumUpTo_nil, Expr.nth_error_app_R in H0; try rewrite NumUpTo_length in *; simpl; eauto.
    simpl in *.
    rewrite Plus.plus_comm in H0; simpl.
    rewrite NPeano.Nat.sub_diag in H0.
    simpl in H0; injections; omega.
    apply IHn in H0; auto.
Qed.

Lemma nth_error_NumUpTo_eq :
  forall m n l v,
    nth_error (NumUpTo n l) m = Some v
    -> lt v n \/ In v l.
Proof.
  intros; destruct (Compare_dec.lt_eq_lt_dec m n) as [ [ | ] | ].
  - left; eapply nth_error_NumUpTo_lt; eauto.
  - subst.
    rewrite NumUpTo_nil in H; simpl in *.
    rewrite Expr.nth_error_app_R in H; try rewrite NumUpTo_length in *; simpl; eauto.
    rewrite Plus.plus_comm in H; simpl in *; rewrite NPeano.Nat.sub_diag in H.
    apply ListFacts4.nth_error_In in H; eauto.
  - rewrite NumUpTo_nil in H; simpl in *.
    rewrite Expr.nth_error_app_R in H; try rewrite NumUpTo_length in *; simpl; eauto.
    rewrite Plus.plus_comm in H; simpl in *.
    apply ListFacts4.nth_error_In in H; eauto.
Qed.

Lemma StringMap_remove_add av:
  forall k v rest tenv ext,
    rest ≲ tenv ∪ ext
    -> k ∉ rest
    -> StringMap.remove (elt:=Value av) k
                        ([k |> v ]:: rest)
                        ≲ tenv ∪ ext.
Proof.
  intros; eapply SameValues_Equal with (m1 := rest).
  unfold StringMap.Equal.
  intros; destruct (string_dec y k); subst.
  intros; symmetry; rewrite remove_eq_o; eauto.
  symmetry; rewrite <- not_find_in_iff; eauto.
  rewrite StringMapFacts.remove_neq_o; eauto.
  rewrite StringMapFacts.add_neq_o; eauto.
  eauto.
Qed.

Lemma combine_app_distrib {A B}
  : forall (l1 l1' : list A) (l2 l2' : list B),
    List.length l1 = List.length l2 ->
    combine (app l1 l1') (app l2 l2') =
    app (combine l1 l2) (combine l1' l2').
Proof.
  induction l1; destruct l2; simpl; intros; try discriminate.
  - reflexivity.
  - rewrite IHl1; eauto.
Qed.

Lemma lenth_combine {A B}
  : forall (l1 : list A) (l2 : list B),
    List.length l1 = List.length l2 ->
    List.length (combine l1 l2) = List.length l1
    /\ List.length (combine l1 l2) = List.length l2.
Proof.
  induction l1; destruct l2; simpl; intros;
  try discriminate; intuition.
  - erewrite (fun H => proj1 (IHl1 l2 H)); congruence.
  - erewrite (fun H => proj2 (IHl1 l2 H)); congruence.
Qed.

Lemma Vector_ToList_cons {A} n
  : forall a (v : Vector.t A n),
    Vector.to_list (Vector.cons _ a _ v) =
    a :: Vector.to_list v.
Proof.
  intros; reflexivity.
Qed.

Definition in_map {A B}
  : forall (f f' : A -> B) l,
    (forall a, In a l -> f a = f' a)
    -> map f l = map f' l.
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - rewrite H; eauto.
    rewrite IHl; eauto.
Qed.

Local Opaque Vector.to_list.

Lemma SameValues_remove2 av :
  forall k k' st',
    StringMap.Equal
      (StringMap.remove (elt:=Value av) k
                        (StringMap.remove (elt:=Value av) k' st'))
      (StringMap.remove (elt:=Value av) k'
                        (StringMap.remove (elt:=Value av) k st')).
Proof.
  unfold StringMap.Equal.
  intros; repeat rewrite remove_o.
  repeat find_if_inside; eauto.
Qed.

Arguments nthRepName _ / .
Arguments nthArgName _ / .
Arguments BuildArgNames !n !m / .

Lemma compiled_prog_op_refines_ax
      av
      (env : StringMap.t DFFun -> Env av)
      {numRepArgs}
      {A}
      {B}
      {C}
      {RepSpec RepImpl}
      (AbsR : RepSpec -> RepImpl -> Prop)
      {RepT' : Vector.t A numRepArgs}
      (RepT : ilist3 (B := B) RepT')
      (RepMap : RepImpl -> i3list C RepT)
      (RepWrapper : @RepWrapperT av numRepArgs A B C RepT' RepT)
      (DecomposeRep :=
         fun repWrapper rep =>
           Decomposei3list RepT' RepT repWrapper (RepMap rep))
      (DecomposeRepPre :=
         fun rep =>
           DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
      (DecomposeRepPost :=
         fun rep rep' =>
           DecomposePosti3list _ RepT RepWrapper (RepMap rep) (RepMap rep'))
      (DecomposeRepPrePostAgree :=
         fun r r' =>
           DecomposePrei3list_Agree av RepT RepWrapper (RepMap r) (RepMap r'))
      cod
      dom
      codWrap
      domWrap
      methSpec
      methImpl
      (ValidMeth : refineMethod AbsR methSpec methImpl)
      RepInv
      progOK
  : forall env_ext,
    op_refines_ax
      (env env_ext)
      (Core (BuildDFFun env (cod := cod) (dom := dom)
                        (WrappedCod := codWrap) (WrappedDom := domWrap)
                        (meth := methImpl) (RepInv := RepInv)
                        DecomposeRep numRepArgs RepWrapper progOK))
      (GenAxiomaticSpecs (numRepArgs := numRepArgs)
                         AbsR RepInv codWrap domWrap methSpec
                         DecomposeRepPre
                         DecomposeRepPost
                         DecomposeRepPrePostAgree).
Proof.
  unfold op_refines_ax; repeat split.
  - unfold GenAxiomaticSpecs; simpl.
    unfold AxiomatizeMethodPostSpec.
    eapply AxiomatizeMethodPostSpec_OK.
  - simpl. unfold BuildArgNames.
    rewrite app_length, !rev_length, !map_length, !NumUpTo_length; simpl.
    intros; destruct H as [r [r' [AbsR_r_r' [H' H ] ] ] ].
    apply length_AxiomatizeMethodPre' in H; subst.
    rewrite <- H, length_Vector_to_list, <- !plus_n_O; auto with arith.
  - destruct progOK as [prog [op_spec ?] ]; simpl.
    generalize ValidMeth op_spec; clear.
    unfold AxSafe; simpl; intros.
    destruct_ex; intuition; subst.
    unfold AxiomatizeMethodPreSpec in H2; simpl in H2;
    destruct_ex; intuition; subst.
    revert st x x1 H0 H x0 H1 H2 H4 X0.
    replace (Datatypes.length dom) with (Datatypes.length (@nil (Value av)) + Datatypes.length (dom)).
    assert (
        Datatypes.length (@nil (Value av))
        = Datatypes.length (@nil {T : Type & (NameTag av T * Comp T)%type})) as len_l_l'
        by reflexivity.
    assert (forall x0,
               make_map (BuildArgNames (List.length (@nil (Value av))) numRepArgs)
                        (nil ++ (Vector.to_list (DecomposeRepPre x0))) ≲ list2Telescope (nil ++ DecomposeRep RepWrapper x0) ∪
                        ∅) as H''.
    { unfold BuildArgNames.
      subst DecomposeRep; subst DecomposeRepPre; subst DecomposeRepPrePostAgree.
      simpl.
      clear methSpec methImpl ValidMeth op_spec RepInv.
      generalize RepT RepMap RepWrapper;
        clear; induction RepT'.
      - intros; simpl; reflexivity.
      - simpl; intros.
        rewrite NumUpTo_nil, map_app, rev_app_distr; simpl.
        rewrite Vector_ToList_cons.
        rewrite StringMapFacts.add_eq_o; eauto.
        eexists _; intuition eauto.
        eapply StringMap_remove_add; eauto.
        eapply (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep))).
        eapply make_map_not_in.
        rewrite <- in_rev, in_map_iff; intro; destruct_ex; intuition.
        injections.
        destruct x; destruct n.
        + intuition.
        + symmetry in H.
          apply NumberToString_rec_10 in H; intuition.
        + apply NumberToString_rec_10 in H; intuition.
        + apply NumberToString_rec_inj' in H; simpl in H; subst; eauto.
          simpl in H1.
          apply ListFacts4.in_nth_error in H1; destruct_ex.
          apply nth_error_NumUpTo_eq in H; simpl in H; intuition; subst.
    }
    remember (@nil (Value av)) as l; clear Heql.
    remember [] as l'; clear Heql'.
    remember DecomposeRep.
    assert (forall r,
               RepInv r ->
               LiftMethod' (env env_ext) dom RepInv
                           (fun r0 => list2Telescope (DecomposeRep RepWrapper r0))
                           (l0 RepWrapper r)
                           codWrap domWrap
                           prog l' (methImpl r)) as op_spec'
        by (subst; exact (op_spec env_ext)); clear op_spec.
    clear Heql0.
    generalize l l' DecomposeRep DecomposeRepPre l0 op_spec' len_l_l' H''.
    clear methSpec ValidMeth l l' DecomposeRep DecomposeRepPre l0 op_spec' len_l_l' H''.
    induction dom; simpl; intros.
    + destruct cod; simpl.
      { simpl in *; subst.
        eapply op_spec'; eauto.
        eapply SameValues_Equal.
        symmetry; apply H.
        rewrite <- plus_n_O.
        apply H''.
      }
      { eapply op_spec'; eauto.
        simpl in *; subst.
        eapply SameValues_Equal.
        symmetry; apply H.
        rewrite <- plus_n_O.
        apply H''. }
    + simpl in *; destruct_ex; subst.
      rewrite H.
      destruct domWrap.
      eapply IHdom with
      (methImpl := fun r => methImpl r x2)
        (l' :=
           (existT (fun T : Type => (NameTag av T * Comp T)%type) a
                   (NTSome
                      (String "a"
                              (String "r"
                                      (String "g"
                                              (NumberToString_rec (Datatypes.length l')
                                                                  (pred (Datatypes.length l')))))),
                    ret x2) :: l'))
        (DecomposeRepPre := DecomposeRepPre); auto.
      7:apply H3.
      6:eauto.
      5:eauto.
      simpl; eauto.
      unfold BuildArgNames; simpl.
      rewrite NumUpTo_nil, map_app, rev_app_distr; simpl.
      intros; rewrite len_l_l'.
      rewrite StringMapFacts.add_eq_o; eauto.
      eexists; intuition eauto.
      eapply StringMap_remove_add; eauto.
      unfold BuildArgNames in H''.
      rewrite NumUpTo_nil, map_app, rev_app_distr, len_l_l' in H''; simpl in H''.
      eapply H''.
      eapply make_map_not_in.
      intro H'; apply in_app_or in H';
      rewrite <- in_rev, in_map_iff in H';
      intuition; destruct_ex; intuition.
      injections.
      destruct x4; destruct l'.
      * intuition.
      * symmetry in H4.
        apply NumberToString_rec_10 in H4; intuition.
        simpl; omega.
      * apply NumberToString_rec_10 in H4; intuition.
      * apply NumberToString_rec_inj' in H4; simpl in H4; subst; eauto.
        simpl in H6.
        apply ListFacts4.in_nth_error in H6; destruct_ex.
        apply nth_error_NumUpTo_eq in H4; simpl in H4; intuition; subst.
      * rewrite <- in_rev, in_map_iff in H4; destruct_ex.
        unfold nthRepName in H4; simpl in H4; intuition.
        discriminate.
      * simpl; rewrite H0; repeat f_equal; omega.
      * simpl; f_equiv; f_equal; omega.
    + reflexivity.
  - destruct progOK as [prog [op_spec ?] ]; simpl.
    generalize ValidMeth op_spec; clear.
    unfold AxSafe, AxRunsTo; simpl; intros.
    unfold AxiomatizeMethodPreSpec in *.
    destruct_ex; intuition; subst.
    destruct_ex; intuition; subst.
    revert st x x0 H1 H0 H H1 H2 H5 H3 x.
    replace (Datatypes.length dom) with (Datatypes.length (@nil (Value av)) + Datatypes.length (dom)).
    assert (
        Datatypes.length (@nil (Value av))
        = Datatypes.length (@nil {T : Type & (NameTag av T * Comp T)%type})) as len_l_l'
        by reflexivity.
    assert (forall x0,
               make_map (BuildArgNames (List.length (@nil (Value av))) numRepArgs)
                        (nil ++ (Vector.to_list (DecomposeRepPre x0))) ≲ list2Telescope (nil ++ DecomposeRep RepWrapper x0) ∪
                        ∅) as H''.
    { unfold BuildArgNames.
      subst DecomposeRep; subst DecomposeRepPre.
      simpl.
      clear methSpec methImpl ValidMeth op_spec RepInv.
      generalize RepT RepMap RepWrapper;
        clear; induction RepT'; simpl; intros.
      - reflexivity.
      - rewrite NumUpTo_nil, map_app, rev_app_distr; simpl.
        rewrite Vector_ToList_cons.
        rewrite StringMapFacts.add_eq_o; eauto.
        eexists _; intuition eauto.
        eapply StringMap_remove_add; eauto.
        eapply (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep))).
        eapply make_map_not_in.
        rewrite <- in_rev, in_map_iff; intro; destruct_ex; intuition.
        injections.
        destruct x; destruct n.
        + intuition.
        + symmetry in H.
          apply NumberToString_rec_10 in H; intuition.
        + apply NumberToString_rec_10 in H; intuition.
        + apply NumberToString_rec_inj' in H; simpl in H; subst; eauto.
          simpl in H1.
          apply ListFacts4.in_nth_error in H1; destruct_ex.
          apply nth_error_NumUpTo_eq in H; simpl in H; intuition; subst.
    }
    unfold AxiomatizeMethodPostSpec.
    remember (@nil (Value av)) as l; clear Heql.
    remember (@nil {T : Type & (NameTag av T * Comp T)%type}) as l'.
    remember DecomposeRep.
    assert (forall r,
               RepInv r ->
               LiftMethod' (env env_ext) dom RepInv
                           (fun r0 => list2Telescope (DecomposeRep RepWrapper r0))
                           (l0 RepWrapper r)
                           codWrap domWrap
                           prog l' (methImpl r)) as op_spec'
        by (subst; exact (op_spec env_ext)); clear op_spec.
    replace (@nil (prod (Value av) (option av))) with (map (fun v : Value av => (v, @None av)) l) by
        (subst; destruct l; simpl in *; congruence).
    clear Heql'; clear Heql0.
    intros st x x0.
    generalize ValidMeth l l' l0 st x x0 op_spec' len_l_l' H''.
    clear l l' l0 st x x0 op_spec' len_l_l' H''.
    induction dom; simpl; intros.
    + destruct cod.
      { apply op_spec' in H3; destruct H3.
        destruct (H3 _ (H'' _)).
        rewrite H in H0; subst.
        rewrite <- plus_n_O in H0; apply H8 in H0.
        simpl in methSpec, methImpl.
        destruct H0; intuition; destruct x.
        repeat eexists _; intuition eauto.
        repeat (eexists _); intuition eauto.
        pose proof (ValidMeth _ _ H4 _ H5); computes_to_inv.
        destruct v; simpl in *.
        injections.
        repeat (eexists _); intuition eauto.
        unfold BuildArgNames.
        rewrite <- plus_n_O in *.
        unfold DecomposeRepPost.
        revert H9; case_eq (StringMap.find "ret" st'); try tauto; intros.
        destruct_ex; intuition; computes_to_inv; subst.
        rewrite !combine_app_distrib, map_app, combine_app_distrib.
        f_equal.
        unfold DecomposeRep in H13.
        apply StringMap.find_2 in H9.
        simpl in H13.
        generalize (SameValues_PushExt (fun _ => list2Telescope (Decomposei3list RepT' RepT RepWrapper (RepMap r))) _ _ H9 H13); clear.
        - induction l; simpl; eauto.
          rewrite NumUpTo_nil, map_app, rev_app_distr; simpl.
          intros; rewrite IHl; f_equal; eauto.
          destruct a; eauto.
          case_eq (StringMap.find (elt:=Value av)
                                  (String "a"
                                          (String "r"
                                                  (String "g"
                                                          (NumberToString_rec (Datatypes.length l)
                                                                              (pred (Datatypes.length l)))))) st'); intros; eauto.
          destruct v; eauto.
          elimtype False; generalize st' H0 H; clear.
          induction RepT'.
          + simpl; intros; unfold WeakEq in *; intuition.
            unfold SameADTs in H0.
            apply StringMap.find_2 in H0.
            apply H1 in H0.
            apply StringMap.add_3 in H0; try congruence.
            apply StringMap.is_empty_2 in H0; eauto.
          + intros.
            simpl in H; unfold nthRepName in H.
            simpl in H.
            destruct (StringMap.find (elt:=Value av)
                                     (String "r"
                                             (String "e" (String "p" (NumberToString_rec n (pred n))))) st'); eauto.
            destruct_ex; intuition.
            eapply (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep))).
            2: eauto.
            apply StringMap.find_1; apply StringMap.remove_2;
            eauto using StringMap.find_2.

        - apply StringMap.find_2 in H9.
          generalize st' (SameValues_PushExt (fun _ => list2Telescope (Decomposei3list RepT' RepT RepWrapper (RepMap r))) _ _ H9 H13); clear.
          induction RepT'.
          + reflexivity.
          + simpl.
            destruct RepWrapper; simpl in *.
            rewrite Vector_ToList_cons.
            intro; caseEq (StringMap.find (elt:=Value av)
                                          (String "r" (String "e" (String "p" (NumberToString_rec n (pred n)))))
                                          st'); intros; eauto.
            unfold DecomposeRepPre; simpl.
            rewrite NumUpTo_nil, map_app, rev_app_distr; simpl.
            rewrite Vector_ToList_cons.
            destruct_ex; split_and; subst.
            computes_to_inv; subst.
            simpl; rewrite H.
            f_equal.
            idtac.
            erewrite <- (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep))).
            2:apply H3.
            f_equal.
            destruct (RepMap x1); destruct RepT; simpl in *.
            intros; eapply in_map; clear; intros.
            unfold get_output; destruct a; simpl.
            destruct v; eauto.
            rewrite remove_neq_o; eauto.
            revert H; clear.
            intros.
            apply in_combine_l in H.
            apply In_rev in H; eapply in_map_iff in H; destruct_ex;
            intuition; subst; simpl in H1; injections.
            apply ListFacts4.in_nth_error in H2; destruct_ex;
            apply nth_error_NumUpTo_eq in H0; intuition.
            destruct x; destruct n; try omega.
            symmetry in H.
            apply NumberToString_rec_10 in H; intuition.
            apply NumberToString_rec_inj' in H; simpl in H; omega.
            intuition.
        - rewrite map_length.
          rewrite (fun H => proj1 (lenth_combine _ _ H)).
          rewrite rev_length, map_length, NumUpTo_length; simpl; omega.
          rewrite rev_length, map_length, NumUpTo_length; simpl; omega.
        - rewrite rev_length, map_length, NumUpTo_length; simpl; omega.
        - simpl in H7.
          pose proof (ValidMeth _ _ H4 _ H5); computes_to_inv; subst.
          simpl in H9.
          revert H9;
            caseEq (StringMap.find (elt:=Value av) "ret" st');
            intros; destruct_ex; intuition; subst.
          computes_to_inv; subst; auto.
        - unfold no_adt_leak; intros.
          unfold sel in H0.
          simpl in H7.
          destruct (string_dec "ret" var).
          intuition.
          rewrite <- remove_neq_o with (x := "ret") in H0; auto.
          right.
          simpl in H9.
          revert H9;
            caseEq (StringMap.find (elt:=Value av) "ret" st'); try tauto.
          destruct_ex; intuition; subst.
          generalize st' H0 H13 n.
          clear; induction l; simpl.
          + induction RepT'; simpl.
            * intros; destruct H13.
              unfold SameADTs in H.
              rewrite <- find_mapsto_iff in H0.
              rewrite <- H in H0.
              apply StringMap.empty_1 in H0; intuition.
            * intros; destruct (string_dec var ("rep" ++ (NumberToString_rec n (pred n)))); subst.
              { simpl in *.
                rewrite H0 in H13; destruct_ex; intuition; subst.
                computes_to_inv; subst.
                exists 0; eexists _; split; eauto; simpl.
                rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
                unfold DecomposeRepPre; simpl; rewrite Vector_ToList_cons; eauto.
              }
              destruct (StringMap.find (String "r"
                                               (String "e" (String "p" (NumberToString_rec n (pred n)))))
                                       (StringMap.remove (elt:=Value av) "ret" st'));
                try tauto.
              destruct_ex; intuition; computes_to_inv; subst.
              rewrite SameValues_remove2 in H3.
              eapply (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep))) in H3; eauto.
              repeat destruct_ex; intuition.
              unfold BuildArgNames in H1; simpl in H1.
              eexists (S x); exists x0; split.
              rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
              unfold DecomposeRepPre; simpl; rewrite Vector_ToList_cons; eauto.
              repeat rewrite remove_o in *; repeat find_if_inside; try discriminate.
              simpl in *; rewrite e in n1; congruence.
              eauto.
          + intros.
            destruct (IHl st') as [i' [ai' [? ? ] ] ]; eauto; eexists (S i'); simpl.
            eexists ai'.
            unfold BuildArgNames; simpl;
            rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
      }
      { apply op_spec' in H3; destruct H3.
        destruct (H3 _ (H'' _)).
        rewrite H in H0; subst.
        rewrite <- plus_n_O in H0; apply H8 in H0.
        simpl in *.
        simpl in H0.
        destruct H0; intuition.
        repeat eexists _; intuition eauto.
        repeat eexists _; intuition eauto.
        pose proof (ValidMeth _ _ H4 _ H5); computes_to_inv; subst.
        repeat (eexists _); intuition eauto.
        unfold BuildArgNames.
        rewrite <- plus_n_O in *.
        unfold DecomposeRepPost.
        revert H9;
          case_eq (StringMap.find (elt:=Value av) "ret" st'); intros; try tauto.
        destruct_ex; intuition; computes_to_inv; subst.
        rewrite !combine_app_distrib, map_app, combine_app_distrib.
        f_equal.
        unfold DecomposeRep in H13.
        apply StringMap.find_2 in H9.
        generalize st' (SameValues_PushExt (fun _ => list2Telescope (Decomposei3list RepT' RepT RepWrapper (RepMap x))) _ _ H9 H13); clear.
        - induction l; simpl; eauto.
          rewrite NumUpTo_nil, map_app, rev_app_distr; simpl.
          intros; rewrite IHl; f_equal; eauto.
          destruct a; eauto.
          case_eq (StringMap.find (elt:=Value av)
                                  (String "a"
                                          (String "r"
                                                  (String "g"
                                                          (NumberToString_rec (Datatypes.length l)
                                                                              (pred (Datatypes.length l)))))) st'); intros; eauto.
          destruct v; eauto.
          apply StringMap.find_2 in H0.
          apply (StringMap.remove_2 (x := "ret")) in H0; try congruence.
          apply StringMap.find_1 in H0.
          elimtype False; generalize st' H0 H; clear.
          induction RepT'.
          + simpl; intros; unfold WeakEq in *; intuition.
            unfold SameADTs in H1.
            apply StringMap.find_2 in H0.
            rewrite StringMapFacts.remove_mapsto_iff in H0; intuition.
            apply H1 in H3.
            rewrite StringMapFacts.add_mapsto_iff in H3; intuition try congruence.
            apply StringMap.is_empty_2 in H4; eauto.
          + intros.
            simpl in H.
            destruct (StringMap.find (elt:=Value av)
                                     (String "r"
                                             (String "e" (String "p" (NumberToString_rec n (pred n)))))
                                     st'
                     ); eauto.
            destruct_ex; intuition.
            eapply (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep))).
            2: eassumption.
            rewrite SameValues_remove2.
            apply StringMap.find_1; apply StringMap.remove_2;
            eauto using StringMap.find_2.
        - generalize st' H13; clear.
          induction RepT'.
          + reflexivity.
          + unfold DecomposeRep.
            simpl.
            destruct RepWrapper; simpl in *.
            rewrite Vector_ToList_cons.
            intro; caseEq (StringMap.find (elt:=Value av)
                                          (String "r" (String "e" (String "p" (NumberToString_rec n (pred n)))))
                                          (StringMap.remove (elt:=Value av) "ret" st')); intros; eauto.
            unfold DecomposeRepPre; simpl.
            rewrite NumUpTo_nil, map_app, rev_app_distr; simpl.
            rewrite Vector_ToList_cons.
            destruct_ex; split_and; subst.
            computes_to_inv; subst.
            rewrite remove_neq_o in H; try congruence.
            simpl; rewrite H.
            f_equal.
            rewrite SameValues_remove2 in H3.
            erewrite <- (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep))).
            2:apply H3.
            f_equal.
            destruct (RepMap x); destruct RepT; simpl in *.
            intros; eapply in_map; clear; intros.
            unfold get_output; destruct a; simpl.
            destruct v; eauto.
            rewrite remove_neq_o; eauto.
            revert H; clear.
            intros.
            apply in_combine_l in H.
            apply In_rev in H; eapply in_map_iff in H; destruct_ex;
            intuition; subst; simpl in H1; injections.
            apply ListFacts4.in_nth_error in H2; destruct_ex;
            apply nth_error_NumUpTo_eq in H0; intuition.
            destruct x; destruct n; try omega.
            symmetry in H.
            apply NumberToString_rec_10 in H; intuition.
            apply NumberToString_rec_inj' in H; simpl in H; omega.
            intuition.
        - rewrite map_length.
          rewrite (fun H => proj1 (lenth_combine _ _ H)).
          rewrite rev_length, map_length, NumUpTo_length; simpl; omega.
          rewrite rev_length, map_length, NumUpTo_length; simpl; omega.
        - rewrite rev_length, map_length, NumUpTo_length; simpl; omega.
        - simpl in H9.
          revert H9;
            caseEq (StringMap.find (elt:=Value av) "ret" st');
            intros; destruct_ex; intuition; subst.
          computes_to_inv; subst; auto.
        - unfold no_adt_leak; intros.
          unfold sel in H0.
          simpl in H9.
          destruct (string_dec "ret" var).
          intuition.
          rewrite <- remove_neq_o with (x := "ret") in H0; auto.
          right.
          revert H9;
            caseEq (StringMap.find (elt:=Value av) "ret" st'); try tauto.
          destruct_ex; intuition; subst.
          generalize st' H0 H13 n.
          clear; induction l; simpl.
          + induction RepT'; simpl.
            * intros; destruct H13.
              unfold SameADTs in H.
              rewrite <- find_mapsto_iff in H0.
              rewrite <- H in H0.
              apply StringMap.empty_1 in H0; intuition.
            * intros; destruct (string_dec var ("rep" ++ (NumberToString_rec n (pred n)))); subst.
              { simpl in *.
                rewrite H0 in H13; destruct_ex; intuition; subst.
                computes_to_inv; subst.
                exists 0; eexists _; split; eauto; simpl.
                rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
                unfold DecomposeRepPre; simpl; rewrite Vector_ToList_cons; eauto.
              }
              destruct (StringMap.find (String "r"
                                               (String "e" (String "p" (NumberToString_rec n (pred n)))))
                                       (StringMap.remove (elt:=Value av) "ret" st'));
                try tauto.
              destruct_ex; intuition; computes_to_inv; subst.
              rewrite SameValues_remove2 in H3.
              eapply (IHRepT' (prim_snd RepT) (fun rep => prim_snd (RepMap rep)))
                in H3; eauto.
              repeat destruct_ex; intuition.
              unfold BuildArgNames in H1; simpl in H1.
              eexists (S x0); exists x2; split.
              rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
              unfold DecomposeRepPre; simpl; rewrite Vector_ToList_cons; eauto.
              repeat rewrite remove_o in *; repeat find_if_inside; try discriminate.
              simpl in *; rewrite e in n1; congruence.
              eauto.
          + intros.
            destruct (IHl st') as [i' [ai' [? ? ] ] ]; eauto; eexists (S i'); simpl.
            eexists ai'.
            unfold BuildArgNames; simpl;
            rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
      }
    + repeat destruct_ex; intuition.
      setoid_rewrite H.
      destruct domWrap.
      rewrite Plus.plus_comm.
      simpl.
      simpl in ValidMeth.
      destruct (IHdom
                  d
                  (fun r => methSpec r x3)
                  (fun r => methImpl r x3)
                  (fun r_o r_n AbsR' => ValidMeth r_o r_n AbsR' x3)
                  (fun r_o r_n AbsR' => ValidMeth r_o r_n AbsR' x3)
                  ((wrap (FacadeWrapper := gWrap g) x3) :: l)
                  ((existT (fun T : Type => (NameTag av T * Comp T)%type) a
                           (@NTSome _ _
                                    (String "a"
                                            (String "r"
                                                    (String "g"
                                                            (NumberToString_rec (Datatypes.length l')
                                                                                (pred (Datatypes.length l'))))))
                                    (gWrap g),
                            ret x3)) :: l')
                  l0
                  st x x0); simpl; auto.
      intros; unfold BuildArgNames.
      rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
      rewrite NumUpTo_nil, map_app, rev_app_distr; simpl; eauto.
      rewrite len_l_l'.
      rewrite add_eq_o by eauto.
      pose proof (op_spec' _ H3 x3).
      eexists; intuition eauto.
      eapply StringMap_remove_add; eauto.
      unfold BuildArgNames in H''.
      rewrite <- len_l_l'; eauto.
      eapply make_map_not_in.
      intro; apply in_app_or in H7; intuition.
      rewrite <- in_rev, in_map_iff in H8; destruct_ex; intuition.
      simpl in H8.
      injections.
      destruct x5; destruct (Datatypes.length l').
      * intuition.
      * symmetry in H7.
        apply NumberToString_rec_10 in H7; intuition.
      * apply NumberToString_rec_10 in H7; intuition.
      * apply NumberToString_rec_inj' in H7; simpl in H7; subst; eauto.
        apply ListFacts4.in_nth_error in H9; destruct_ex.
        apply nth_error_NumUpTo_eq in H7; simpl in H7; intuition; subst.
      * rewrite <- in_rev, in_map_iff in H8; destruct_ex; intuition.
        simpl in H8; discriminate.
      * rewrite H1; f_equal; f_equal; omega.
      * rewrite Plus.plus_comm in H; simpl in H; rewrite Plus.plus_comm in H; eauto.
      * rewrite Plus.plus_comm in H1; simpl in H1; rewrite Plus.plus_comm in H1; eauto.
      * destruct_ex; intuition; eexists x4; exists x5; intuition eauto.
        simpl in H5; rewrite Plus.plus_comm; eauto.
        simpl in H4; rewrite Plus.plus_comm; eauto.
        rewrite Plus.plus_comm in H.
        rewrite <- H6, H. rewrite Plus.plus_comm; simpl; reflexivity.
        destruct_ex; simpl in H6.
        eexists x6; eexists x7; intuition.
        exists x3.
        rewrite Plus.plus_comm.
        apply H12.
        simpl in H9; rewrite Plus.plus_comm; eauto.
    + reflexivity.
Qed.

Lemma StringMap_fold_left_Eq {B C}
  : forall f f' l st st',
    let f' := (fun (acc : @StringMap.t C) (el : B)  => StringMap.add (f el) (f' el) acc) in
    StringMap.Equal st st'
    -> StringMap.Equal
         (fold_left f' l st)
         (fold_left f' l st').
Proof.
  induction l.
  - simpl; eauto.
  - simpl; intros.
    eapply IHl; rewrite H; reflexivity.
Qed.

Lemma StringMap_In_Permutation {B C}
  : forall f f' l st st' k,
    let f' := (fun (acc : @StringMap.t C) (el : B)  => StringMap.add (f el) (f' el) acc) in
    (forall k, StringMap.In k st
               -> StringMap.In k st')
    -> StringMap.In k (fold_left f' l st)
    -> StringMap.In k (fold_left f' l st').
Proof.
  induction l; simpl; intros.
  - eauto.
  - eapply IHl.
    2: apply H0.
    intros; destruct H1.
    apply add_mapsto_iff in H1; intuition; subst.
    eexists; apply StringMap.add_1; eauto.
    destruct (H k0).
    eexists; eauto.
    eexists x0.
    apply StringMap.add_2; eauto.
Qed.

Lemma StringMap_In_Permutation' {B C}
  : forall f f' l st st' k,
    let f' := (fun (acc : @StringMap.t C) (el : B)  => StringMap.add (f el) (f' el) acc) in
    (StringMap.In k st -> StringMap.In k st')
    -> StringMap.In k (fold_left f' l st)
    -> StringMap.In k (fold_left f' l st').
Proof.
  induction l; simpl; intros.
  - eauto.
  - eapply IHl.
    2: apply H0.
    intros; destruct H1.
    apply add_mapsto_iff in H1; intuition; subst.
    eexists; apply StringMap.add_1; eauto.
    destruct H.
    eexists; eauto.
    eexists x0.
    apply StringMap.add_2; eauto.
Qed.

Lemma fold_left_add2_Eq {B C}
  : forall f f' k (v : C) l st,
    let f' := (fun (acc : @StringMap.t C) (el : B)  => StringMap.add (f el) (f' el) acc) in
    ~ StringMap.In k (fold_left f' l (StringMap.empty _))
    -> StringMap.Equal
         (fold_left f' l ([k |> v]::st))
         ([k |> v]:: (fold_left f' l st)).
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - rewrite <- IHl.
    + rewrite StringMap_fold_left_Eq.
      reflexivity.
      unfold StringMap.Equal; simpl.
      intros; rewrite !add_o; repeat find_if_inside;
      eauto; subst.
      destruct H.
      remember (StringMap.empty C); clear.
      remember (f' a).
      clear; revert t c; induction l; simpl; intros.
      eexists; apply StringMap.add_1; eauto.
      destruct (string_dec (f a0) (f a)); subst; simpl.
      rewrite e; eapply IHl.
      destruct (IHl ([f a0 |> f' a0]::t) c).
      eexists x.
      setoid_rewrite find_mapsto_iff.
      setoid_rewrite StringMap_fold_left_Eq.
      setoid_rewrite <- find_mapsto_iff.
      eapply H.
      unfold StringMap.Equal; intros; rewrite !add_o;
      repeat find_if_inside; try congruence.
    + intro; apply H.
      remember (StringMap.empty C).
      revert H0; generalize a t; clear; induction l; simpl; intros.
      * destruct (string_dec k (f a)); subst.
        eexists (f' a); apply StringMap.add_1; eauto.
        destruct H0.
        eexists x; apply StringMap.add_2; eauto.
      * eapply (IHl a0) in H0.
        eapply StringMap_In_Permutation.
        2: apply H0.
        clear; intros; destruct H.
        apply add_mapsto_iff in H; intuition; subst.
        destruct (string_dec (f a) (f a0)); subst.
        eexists (f' a).
        apply StringMap.add_1; eauto.
        eexists (f' a0).
        apply StringMap.add_2; eauto.
        apply StringMap.add_1; eauto.
        apply add_mapsto_iff in H1; intuition; subst.
        eexists (f' a).
        apply StringMap.add_1; eauto.
        eexists x.
        apply StringMap.add_2; eauto.
        apply StringMap.add_2; eauto.
Qed.

Lemma StringMapsTo_fold_left A C
  : forall (f : A -> string)
           (f' : A -> C) l st idx,
    NoDup (map f l)
    -> In idx l
    -> StringMap.MapsTo
         (f idx)
         (f' idx)
         (fold_left
            (fun acc (el : A) =>
               [f el |> f' el] :: acc )
            l st).
Proof.
  induction l; simpl; intros.
  - intuition.
  - intuition; subst.
    + rewrite fold_left_add2_Eq.
      apply StringMap.add_1; eauto.
      inversion H; subst.
      assert (~ StringMap.In (f idx) (StringMap.empty C))
        by (rewrite empty_in_iff; tauto).
      remember (StringMap.empty C).
      generalize t H2 H0; clear; induction l; simpl; intros.
      * eauto.
      * intuition.
        eapply IHl; eauto.
        eapply StringMap_In_Permutation'.
        2:eauto.
        intros.
        destruct H2.
        eapply add_mapsto_iff in H2; intuition.
        eexists; eauto.
    + inversion H; subst; eapply IHl; eauto.
Qed.

Lemma NIn_StringMap_fold_left A C
  : forall (f : A -> string)
           (f' : A -> C) l st idx,
    ~ In idx l
    -> ListFacts1.IsInjection f
    -> ~ StringMap.In (f idx) st
    -> ~ StringMap.In
         (f idx)
         (fold_left
            (fun acc (el : A) =>
               [f el |> f' el] :: acc )
            l st).
Proof.
  induction l; simpl; intros.
  - intuition.
  - intuition; subst.
    apply IHl in H2; eauto.
    rewrite add_in_iff; intuition.
    apply H0 in H5; eauto.
Qed.

Lemma NoDup_BuildFinUpTo
  : forall n, NoDup (BuildFinUpTo n).
Proof.
  induction n; simpl; econstructor.
  - clear; induction (BuildFinUpTo n); simpl.
    + tauto.
    + intuition; discriminate.
  - eapply ListFacts1.Injection_NoDup; eauto.
    unfold ListFacts1.IsInjection; intros.
    unfold not; intros; apply H.
    apply Fin.FS_inj in H0; eauto.
Qed.

Lemma In_BuildFinUpTo
  : forall n idx, In idx (BuildFinUpTo n).
Proof.
  induction idx.
  - simpl; intuition.
  - simpl.
    right; apply in_map_iff; eauto.
Qed.

Corollary StringMapsTo_fold_left' {n} C
  : forall (f : Fin.t n -> string)
           (f' : Fin.t n -> C) st idx,
    ListFacts1.IsInjection f
    -> StringMap.MapsTo
         (f idx)
         (f' idx)
         (fold_left
            (fun acc (el : Fin.t n) =>
               [f el |> f' el] :: acc )
            (BuildFinUpTo n) st).
Proof.
  intros; eapply StringMapsTo_fold_left.
  - eapply ListFacts1.Injection_NoDup; eauto using NoDup_BuildFinUpTo.
  - eapply In_BuildFinUpTo.
Qed.

Lemma StringMapsTo_fold_left_ex A C
  : forall (f : A -> string)
           (f' : A -> C) l k v,
    ListFacts1.IsInjection f
    -> NoDup (map f l)
    -> StringMap.MapsTo
         k
         v
         (fold_left
            (fun acc (el : A) =>
               [f el |> f' el] :: acc )
            l (StringMap.empty _))
    -> exists idx, k = f idx /\ v = f' idx.
Proof.
  induction l; simpl; intros.
  - apply StringMap.empty_1 in H1; intuition.
  - inversion H0; subst.
    rewrite fold_left_add2_Eq in H1.
    rewrite add_mapsto_iff in H1; intuition.
    subst; eauto.
    eapply NIn_StringMap_fold_left; eauto.
    intro; apply H4; apply in_map_iff; eauto.
    rewrite empty_in_iff; tauto.
Qed.

Local Opaque Vector.to_list.

Lemma methID_injective {n'}
  : forall (methSigs : Vector.t methSig n'),
    NoDup (Vector.to_list (Vector.map methID methSigs))
    -> ListFacts1.IsInjection (fun midx => methID (Vector.nth methSigs midx)).
Proof.
  unfold ListFacts1.IsInjection.
  intros.
  revert methSigs H H0.
  pattern n', x, y.
  eapply Fin.rect2; intros.
  - congruence.
  - revert f H H0.
    pattern n, methSigs.
    eapply Vector.caseS; simpl; intros.
    rewrite Vector_ToList_cons in H; inversion H; subst.
    generalize t H3; clear.
    induction f; simpl.
    + intro; pattern n, t; eapply Vector.caseS; intros.
      simpl in *.
      rewrite Vector_ToList_cons in H3.
      simpl in H3; intuition.
    + intro; revert f IHf; pattern n, t; eapply Vector.caseS; intros.
      simpl in *.
      rewrite Vector_ToList_cons in H3; simpl in H3.
      eapply IHf; intuition.
  - revert f H H0.
    pattern n, methSigs.
    eapply Vector.caseS; simpl; intros.
    rewrite Vector_ToList_cons in H; inversion H; subst.
    generalize t H3; clear.
    induction f; simpl.
    + intro; pattern n, t; eapply Vector.caseS; intros.
      simpl in *.
      rewrite Vector_ToList_cons in H3.
      simpl in H3; intuition.
    + intro; revert f IHf; pattern n, t; eapply Vector.caseS; intros.
      simpl in *.
      rewrite Vector_ToList_cons in H3; simpl in H3.
      eapply IHf; intuition.
  - revert f g H H0 H1; clear. pattern n, methSigs.
    eapply Vector.caseS; intros.
    simpl in *.
    eapply H.
    rewrite Vector_ToList_cons in H0; inversion H0; subst; eauto.
    congruence.
Qed.

Lemma forallb_forall_false
  : forall (A : Type) (f : A -> bool) (l : list A),
    forallb f l = false <-> ~ (forall x : A, In x l -> f x = true).
Proof.
  setoid_rewrite <- forallb_forall.
  intros; destruct (forallb f l); split; congruence.
Qed.

Lemma is_sub_domain_equal_maps
      {elt elt2}
  : forall m1 m2 m1' m2',
    M.Equal (elt := elt) m1 m1'
    -> M.Equal (elt := elt2) m2 m2'
    -> is_sub_domain m1 m2 = is_sub_domain m1' m2'.
Proof.
  unfold is_sub_domain.
  unfold UWFacts.WFacts.keys.
  intros.
  case_eq (forallb (fun k : M.key => M.mem (elt:=elt2) k m2)
                   (map fst (M.elements (elt:=elt) m1))).
  intros.
  rewrite forallb_forall in H1.
  repeat rewrite (proj2 (forallb_forall _ _) ); eauto; intros.
  rewrite <- H0; apply H1.
  apply In_fst_elements_In; apply In_fst_elements_In in H2.
  rewrite H; eauto.
  intros.
  rewrite forallb_forall_false in H1.
  rewrite (proj2 (forallb_forall_false _ _) ); eauto.
  intro; apply H1; intros.
  rewrite H0; apply H2.
  apply In_fst_elements_In; apply In_fst_elements_In in H3.
  rewrite <- H; eauto.
Qed.

Lemma is_sub_domain_add
      {elt elt2}
  : forall k (v : elt) (v' : elt2) m1 m2,
    ~ StringMap.In k m1
    -> ~ StringMap.In k m2
    -> is_sub_domain ([k |> v] :: m1) ([k |> v'] :: m2) = is_sub_domain m1 m2.
Proof.
  intros; unfold is_sub_domain.
  case_eq (forallb (fun k0 : M.key => M.mem (elt:=elt2) k0 ([k |> v']::m2))
                   (UWFacts.WFacts.keys ([k |> v]::m1))); intros.
  - rewrite forallb_forall in H1.
    symmetry; apply forallb_forall; intros.
    erewrite <- add_neq_b.
    apply H1.
    apply In_fst_elements_In.
    apply add_in_iff; right.
    apply In_fst_elements_In; apply H2.
    intro; subst.
    apply H.
    apply In_fst_elements_In; apply H2.
  - rewrite forallb_forall_false in H1.
    symmetry; apply forallb_forall_false.
    intro; apply H1; intros.
    unfold UWFacts.WFacts.keys in H3.
    rewrite In_fst_elements_In in H3.
    apply mem_in_iff; apply add_in_iff.
    apply add_in_iff in H3; intuition subst.
    rewrite <- In_fst_elements_In in H4.
    apply H2 in H4; right.
    apply mem_in_iff; eauto.
Qed.


Lemma BuildCompileUnit2T_exports_in_domain
      av
      (env : GLabelMap.t (AxiomaticSpec av))
      (env' := GLabelMap.map (@Axiomatic av) env)
      {n n'}
      {consSigs : Vector.t consSig n}
      {methSigs : Vector.t methSig n'}
      (UniqueMeth : NoDup (Vector.to_list (Vector.map methID methSigs)))
      (adtSpec adtImpl : DecoratedADT (BuildADTSig consSigs methSigs))
      (AbsR : Rep adtSpec -> Rep adtImpl -> Prop)
      {numRepArgs}
      {A}
      {B}
      {C}
      {RepT' : Vector.t A numRepArgs}
      (RepT : ilist3 (B := B) RepT')
      (RepWrapper : @RepWrapperT av numRepArgs A B C RepT' RepT)
      (RepMap : Rep adtImpl -> i3list C RepT)
      ValidImpl
      RepInv
      (DecomposeRep := fun repWrapper rep => Decomposei3list RepT' RepT repWrapper (RepMap rep))
      (DecomposeRepPre := fun rep => DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
      (DecomposeRepPost := fun rep rep' => DecomposePosti3list _ RepT RepWrapper (RepMap rep) (RepMap rep'))
      op_mod_name'
      codWrap
      domWrap
      (DecomposeRepPrePoseAgree := fun r r' =>
                                     DecomposePrei3list_Agree av RepT RepWrapper (RepMap r) (RepMap r'))
      (env'' :=
                fun env''' : StringMap.t DFFun =>
                (GLabelMapFacts.UWFacts.WFacts.P.update
                   (GLabelMapFacts.UWFacts.WFacts.P.update
                      (GLabelMap.map (fun f : DFFun => Operational av f)
                                     (map_aug_mod_name op_mod_name' env'''))
                      (GLabelMap.map (Axiomatic (ADTValue:=av))
                                  (map_aug_mod_name op_mod_name'
                                                    (GenExports codWrap domWrap AbsR RepInv DecomposeRepPre
                                                                DecomposeRepPost DecomposeRepPrePoseAgree ValidImpl))))
                   env'))
      (progsOK : forall midx,
          {prog : Stmt &
                  (forall env_ext,
                      LiftMethod (env'' env_ext) RepInv (DecomposeRep RepWrapper)
                                 (codWrap midx) (domWrap midx) prog (Methods adtImpl midx))
                  (* Syntactic Checks *)
                  /\ NoUninitDec.is_no_uninited
                       {|
                         FuncCore.ArgVars := BuildArgNames (Datatypes.length (fst
                                                                                (MethodDomCod
                                                                                   (BuildADTSig consSigs methSigs) midx)))
                                                           numRepArgs;
                         FuncCore.RetVar := "ret";
                         FuncCore.Body := Compile.compile
                                            (CompileDFacade.compile prog) |} = true
                  /\ (GoodModuleDec.is_arg_len_ok
                        (Compile.compile (CompileDFacade.compile prog)) = true)
                  /\ (GoodModuleDec.is_good_size
                        (Datatypes.length
                           (GetLocalVars.get_local_vars
                              (Compile.compile (CompileDFacade.compile prog))
                              (BuildArgNames (Datatypes.length (fst
                                                                  (MethodDomCod
                                                                     (BuildADTSig consSigs methSigs) midx))) numRepArgs) "ret") +
                         Depth.depth (Compile.compile (CompileDFacade.compile prog))) =
                      true)
                  /\  is_disjoint (assigned prog)
                                  (StringSetFacts.of_list
                                     (BuildArgNames (Datatypes.length (fst
                                                                         (MethodDomCod
                                                                            (BuildADTSig consSigs methSigs) midx)))
                                                    numRepArgs)) = true
                  /\ is_syntax_ok prog = true} )
  : is_sub_domain
      (GenExports codWrap domWrap AbsR RepInv DecomposeRepPre
                  DecomposeRepPost DecomposeRepPrePoseAgree ValidImpl)
      (BuildFun _ adtImpl DecomposeRep numRepArgs codWrap domWrap
                RepWrapper progsOK).
Proof.
  simpl.
  unfold GenExports, BuildFun.
  generalize (NoDup_BuildFinUpTo n') UniqueMeth.
  clear; induction (BuildFinUpTo n'); simpl; intros.
  - reflexivity.
  - erewrite is_sub_domain_equal_maps.
    rewrite is_sub_domain_add.
    apply IHl; eauto.
    inversion H; eauto.
    3: simpl; rewrite fold_left_add2_Eq; [ reflexivity | ].
    4: simpl; rewrite fold_left_add2_Eq; [ reflexivity | ].
    + eapply NIn_StringMap_fold_left with
      (f := fun idx => methID (Vector.nth methSigs idx)).
      inversion H; subst; eauto.
      eapply methID_injective; eauto.
      rewrite empty_in_iff; tauto.
    + eapply NIn_StringMap_fold_left with
      (f := fun idx => methID (Vector.nth methSigs idx)).
      inversion H; subst; eauto.
      eapply methID_injective; eauto.
      rewrite empty_in_iff; tauto.
    + eapply NIn_StringMap_fold_left with
      (f := fun idx => methID (Vector.nth methSigs idx)).
      inversion H; subst; eauto.
      eapply methID_injective; eauto.
      rewrite empty_in_iff; tauto.
    + eapply NIn_StringMap_fold_left with
      (f := fun idx => methID (Vector.nth methSigs idx)).
      inversion H; subst; eauto.
      eapply methID_injective; eauto.
      rewrite empty_in_iff; tauto.
Qed.

Lemma BuildCompileUnit2T_projT2
      av
      (env : GLabelMap.t (AxiomaticSpec av))
      (env' := GLabelMap.map (@Axiomatic av) env)
      {n n'}
      {consSigs : Vector.t consSig n}
      {methSigs : Vector.t methSig n'}
      (UniqueMeth : NoDup (Vector.to_list (Vector.map methID methSigs)))
      (adtSpec adtImpl : DecoratedADT (BuildADTSig consSigs methSigs))
      {numRepArgs}
      {A}
      {B}
      {C}
      {RepT' : Vector.t A numRepArgs}
      (RepT : ilist3 (B := B) RepT')
      (RepWrapper : @RepWrapperT av numRepArgs A B C RepT' RepT)
      (RepMap : Rep adtImpl -> i3list C RepT)
      (AbsR : Rep adtSpec -> Rep adtImpl -> Prop)
      ValidImpl
      RepInv
      (DecomposeRep := fun repWrapper rep => Decomposei3list RepT' RepT repWrapper (RepMap rep))
      (DecomposeRepPre := fun rep => DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
      (DecomposeRepPost := fun rep rep' => DecomposePosti3list _ RepT RepWrapper (RepMap rep) (RepMap rep'))
      ax_mod_name'
      op_mod_name'
      codWrap
      domWrap
      (DecomposeRepPrePoseAgree := fun r r' =>
                                     DecomposePrei3list_Agree av RepT RepWrapper (RepMap r) (RepMap r'))
      (env'' :=
         fun env''' : StringMap.t DFFun =>
           (GLabelMapFacts.UWFacts.WFacts.P.update
              (GLabelMapFacts.UWFacts.WFacts.P.update
                 (GLabelMap.map (fun f : DFFun => Operational av f)
                                (map_aug_mod_name op_mod_name' env'''))
                 (GLabelMap.map (Axiomatic (ADTValue:=av))
                                (map_aug_mod_name op_mod_name'
                                                  (GenExports codWrap domWrap AbsR RepInv DecomposeRepPre
                                                              DecomposeRepPost DecomposeRepPrePoseAgree ValidImpl))))
              env'))
      (progsOK : forall midx,
          {prog : Stmt &
                  (forall env_ext,
                      LiftMethod (env'' env_ext) RepInv (DecomposeRep RepWrapper)
                                 (codWrap midx) (domWrap midx) prog (Methods adtImpl midx))
                  (* Syntactic Checks *)
                  /\ NoUninitDec.is_no_uninited
                       {|
                         FuncCore.ArgVars := BuildArgNames (Datatypes.length (fst
                                                                                (MethodDomCod
                                                                                   (BuildADTSig consSigs methSigs) midx)))
                                                           numRepArgs;
                         FuncCore.RetVar := "ret";
                         FuncCore.Body := Compile.compile
                                            (CompileDFacade.compile prog) |} = true
                  /\ (GoodModuleDec.is_arg_len_ok
                        (Compile.compile (CompileDFacade.compile prog)) = true)
                  /\ (GoodModuleDec.is_good_size
                        (Datatypes.length
                           (GetLocalVars.get_local_vars
                              (Compile.compile (CompileDFacade.compile prog))
                              (BuildArgNames (Datatypes.length (fst
                                                                  (MethodDomCod
                                                                     (BuildADTSig consSigs methSigs) midx))) numRepArgs) "ret") +
                         Depth.depth (Compile.compile (CompileDFacade.compile prog))) =
                      true)
                  /\  is_disjoint (assigned prog)
                                  (StringSetFacts.of_list
                                     (BuildArgNames (Datatypes.length (fst
                                                                         (MethodDomCod
                                                                            (BuildADTSig consSigs methSigs) midx)))
                                                    numRepArgs)) = true
                  /\ is_syntax_ok prog = true} )
      (distinct_mod_name : negb (ListFacts3.string_bool ax_mod_name' op_mod_name') = true)
      (unique_op_mod_name'
       : forallb (fun x : string => negb (ListFacts3.string_bool op_mod_name' x))
                 (map (fun x : string * string * AxiomaticSpec av => fst (fst x))
                      (GLabelMap.elements (elt:=AxiomaticSpec av) env)) = true)
      (no_cito_clash_op_mod
       : negb (prefix "__cmod_impl_" op_mod_name') = true)
      (no_cito_clash_env
       : forallb NameDecoration.is_good_module_name
                 (map (fun x => fst (fst x)) (GLabelMap.elements  env)) = true)
      proof
      env_ext
  : CompileUnit2Equiv (env'' env_ext) adtImpl RepInv DecomposeRep numRepArgs ax_mod_name'
                      op_mod_name' codWrap domWrap RepWrapper
                      {|
                        module := {|
                                   Imports := env;
                                   Funs := BuildFun _ adtImpl DecomposeRep numRepArgs codWrap domWrap
                                                    RepWrapper progsOK;
                                   import_module_names_good := no_cito_clash_env |};
                        ax_mod_name := ax_mod_name';
                        op_mod_name := op_mod_name';
                        exports_in_domain := BuildCompileUnit2T_exports_in_domain
                                               (UniqueMeth := UniqueMeth)
                                               env AbsR RepMap
                                               ValidImpl
                                               op_mod_name' codWrap domWrap progsOK;
                        op_mod_name_ok := no_cito_clash_op_mod;
                        op_mod_name_not_in_imports := unique_op_mod_name';
                        name_neq := distinct_mod_name;
                        proof := proof |}.
Proof.
  unfold CompileUnit2Equiv; repeat split; simpl; eauto.
  unfold DFModuleEquiv; intros.
  eexists (BuildDFFun _ DecomposeRep _ RepWrapper (progsOK midx)).
  simpl. repeat split.
  intros.
  eapply (proj1 (projT2 (progsOK midx)) _ r H).
  unfold BuildFun.
  eapply (@StringMapsTo_fold_left' _ _ (fun el => methID (Vector.nth methSigs el))
                                   (fun el => BuildDFFun _ DecomposeRep numRepArgs RepWrapper (progsOK el))).
  apply methID_injective; eauto.
Qed.

 Lemma BuildCompileUnit2T_proof
                     av
             (env : GLabelMap.t (AxiomaticSpec av))
             (env' := GLabelMap.map (@Axiomatic av) env)
             {n n'}
             {consSigs : Vector.t consSig n}
             {methSigs : Vector.t methSig n'}
             (UniqueMeth : NoDup (Vector.to_list (Vector.map methID methSigs)))
             (adtSpec adtImpl : DecoratedADT (BuildADTSig consSigs methSigs))
             {numRepArgs}
             {A}
             {B}
             {C}
             {RepT' : Vector.t A numRepArgs}
             (RepT : ilist3 (B := B) RepT')
             (RepWrapper : @RepWrapperT av numRepArgs A B C RepT' RepT)
             (RepMap : Rep adtImpl -> i3list C RepT)
             (ValidImpl : refineADT adtSpec adtImpl)
             (AbsR' := AbsR ValidImpl)
             RepInv
             (DecomposeRep :=
                fun repWrapper rep =>
                  Decomposei3list RepT' RepT repWrapper (RepMap rep))
             (DecomposeRepPre :=
                fun rep =>
                  DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
             (DecomposeRepPost :=
                fun rep rep' =>
                  DecomposePosti3list _ RepT RepWrapper (RepMap rep) (RepMap rep'))
             ax_mod_name'
             op_mod_name'
             codWrap
             domWrap
             (DecomposeRepPrePoseAgree :=
                fun r r' =>
                  DecomposePrei3list_Agree av RepT RepWrapper (RepMap r) (RepMap r'))
             (env'' :=
                fun env''' =>
                (GLabelMapFacts.UWFacts.WFacts.P.update
                   (GLabelMapFacts.UWFacts.WFacts.P.update
                      (GLabelMap.map (fun f : DFFun => Operational av f)
                                     (map_aug_mod_name op_mod_name' env'''))
                      (GLabelMap.map (Axiomatic (ADTValue:=av))
                                  (map_aug_mod_name op_mod_name'
                                                    (GenExports codWrap domWrap AbsR' RepInv DecomposeRepPre
                                                                DecomposeRepPost DecomposeRepPrePoseAgree ValidImpl))))
                   env'))

             (progsOK : forall midx,
                 {prog : Stmt &
                         (forall env_ext,
                         LiftMethod (env'' env_ext) RepInv (DecomposeRep RepWrapper)
                                    (codWrap midx) (domWrap midx) prog (Methods adtImpl midx))
                         (* Syntactic Checks *)
                         /\ NoUninitDec.is_no_uninited
                              {|
                                FuncCore.ArgVars := BuildArgNames (Datatypes.length (fst
                                                                                       (MethodDomCod
                                                                                          (BuildADTSig consSigs methSigs) midx)))
                                                                  numRepArgs;
                                FuncCore.RetVar := "ret";
                                FuncCore.Body := Compile.compile
                                                   (CompileDFacade.compile prog) |} = true
                         /\ (GoodModuleDec.is_arg_len_ok
                               (Compile.compile (CompileDFacade.compile prog)) = true)
                         /\ (GoodModuleDec.is_good_size
                               (Datatypes.length
                                  (GetLocalVars.get_local_vars
                                     (Compile.compile (CompileDFacade.compile prog))
                                     (BuildArgNames (Datatypes.length (fst
                                                                         (MethodDomCod
                                                                            (BuildADTSig consSigs methSigs) midx))) numRepArgs) "ret") +
                                Depth.depth (Compile.compile (CompileDFacade.compile prog))) =
                             true)
                         /\  is_disjoint (assigned prog)
                                         (StringSetFacts.of_list
                                            (BuildArgNames (Datatypes.length (fst
                                                                                (MethodDomCod
                                                                                   (BuildADTSig consSigs methSigs) midx)))
                                                           numRepArgs)) = true
                         /\ is_syntax_ok prog = true} )
             (distinct_mod_name : negb (ListFacts3.string_bool ax_mod_name' op_mod_name') = true)
             (unique_op_mod_name'
              : forallb (fun x : string => negb (ListFacts3.string_bool op_mod_name' x))
                        (map (fun x : string * string * AxiomaticSpec av => fst (fst x))
                             (GLabelMap.elements (elt:=AxiomaticSpec av) env)) = true)
             (no_cito_clash_op_mod
              : negb (prefix "__cmod_impl_" op_mod_name') = true)
             (no_cito_clash_env
              : forallb NameDecoration.is_good_module_name
                        (map (fun x => fst (fst x)) (GLabelMap.elements  env)) = true)
    : ops_refines_axs
     (get_env op_mod_name'
        (GenExports
           codWrap domWrap AbsR' RepInv
           (fun rep : Rep adtImpl =>
            DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
           (fun rep rep' : Rep adtImpl =>
            DecomposePosti3list RepT' RepT RepWrapper
              (RepMap rep) (RepMap rep'))
           (fun r r' : Rep adtImpl =>
            DecomposePrei3list_Agree av RepT RepWrapper
                                     (RepMap r) (RepMap r'))
           ValidImpl)
        {|
        Imports := env;
        Funs := BuildFun _ adtImpl DecomposeRep numRepArgs codWrap domWrap
                  RepWrapper progsOK;
        import_module_names_good := no_cito_clash_env |})
     (StringMap.map Core
        (Funs
           {|
           Imports := env;
           Funs := BuildFun _ adtImpl DecomposeRep numRepArgs codWrap domWrap
                     RepWrapper progsOK;
           import_module_names_good := no_cito_clash_env |}))
     (GenExports codWrap
        domWrap AbsR' RepInv
        (fun rep : Rep adtImpl =>
         DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
        (fun rep rep' : Rep adtImpl =>
         DecomposePosti3list RepT' RepT RepWrapper (RepMap rep) (RepMap rep'))
        (fun r r' : Rep adtImpl =>
           DecomposePrei3list_Agree av RepT RepWrapper (RepMap r) (RepMap r'))
        ValidImpl).
  Proof.
    unfold ops_refines_axs; intros.
    unfold GenExports in H.
    assert (exists midx, x = methID (Vector.nth methSigs midx)).
    setoid_rewrite <- find_mapsto_iff in H.
    apply StringMapsTo_fold_left_ex in H; destruct_ex; intuition eauto.
    eauto using methID_injective; eauto.
    eapply ListFacts1.Injection_NoDup; eauto using NoDup_BuildFinUpTo.
    eauto using methID_injective; eauto.
    destruct H0; subst.
    pose proof (@StringMapsTo_fold_left'
            _ _
            (fun el => methID (Vector.nth methSigs el))
            (fun el => GenAxiomaticSpecs AbsR' RepInv (codWrap el)
              (domWrap el) (Methods adtSpec el) DecomposeRepPre DecomposeRepPost
              DecomposeRepPrePoseAgree) ∅ x0 (methID_injective _ UniqueMeth)).
    setoid_rewrite find_mapsto_iff in H0.
    subst DecomposeRepPre; subst DecomposeRepPost; subst DecomposeRepPrePoseAgree.
    assert (Some ax_spec = Some
         (GenAxiomaticSpecs AbsR' RepInv (codWrap x0)
            (domWrap x0) (Methods adtSpec x0)
            (fun rep =>
             DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
            (fun rep rep' =>
             DecomposePosti3list RepT' RepT RepWrapper
               (RepMap rep) (RepMap rep'))
            (fun r r' =>
             DecomposePrei3list_Agree av RepT RepWrapper
               (RepMap r) (RepMap r')))) by
        (rewrite <- H, <- H0; f_equal).
    injections.
    eexists; intuition.
    unfold Funs.
    unfold BuildFun.
    setoid_rewrite <- find_mapsto_iff.
    eapply StringMap.map_1.
    eapply (@StringMapsTo_fold_left' _ _ (fun el => methID (Vector.nth methSigs el))
         (fun el => BuildDFFun _ DecomposeRep numRepArgs RepWrapper (progsOK el))).
    apply methID_injective; eauto.
    apply compiled_prog_op_refines_ax with (env := env'').
    apply (ADTRefinementPreservesMethods ValidImpl x0).
  Qed.

(* This is the main compilation tool. *)
Definition BuildCompileUnit2T'
           av
           (env : GLabelMap.t (AxiomaticSpec av))
           (env' := GLabelMap.map (@Axiomatic av) env)
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (UniqueMeth : NoDup (Vector.to_list (Vector.map methID methSigs)))
           (adtSpec adtImpl : DecoratedADT (BuildADTSig consSigs methSigs))
           {numRepArgs}
           {A}
           {B}
           {C}
           {RepT' : Vector.t A numRepArgs}
           (RepT : ilist3 (B := B) RepT')
           (RepWrapper : @RepWrapperT av numRepArgs A B C RepT' RepT)
           (RepMap : Rep adtImpl -> i3list C RepT)
           (ValidImpl : refineADT adtSpec adtImpl)
           (AbsR' := AbsR ValidImpl)

           RepInv
           (DecomposeRep := fun repWrapper rep => Decomposei3list RepT' RepT repWrapper (RepMap rep))
           (DecomposeRepPre := fun rep => DecomposePrei3list RepT' RepT RepWrapper (RepMap rep))
           (DecomposeRepPost := fun rep rep' => DecomposePosti3list _ RepT RepWrapper (RepMap rep) (RepMap rep'))
           ax_mod_name'
           op_mod_name'
           codWrap
           domWrap
           (DecomposeRepPrePoseAgree := fun r r' =>
                                          DecomposePrei3list_Agree av RepT RepWrapper (RepMap r) (RepMap r'))
           (env'' :=
                fun env''' =>
                (GLabelMapFacts.UWFacts.WFacts.P.update
                   (GLabelMapFacts.UWFacts.WFacts.P.update
                      (GLabelMap.map (fun f : DFFun => Operational av f)
                                     (map_aug_mod_name op_mod_name' env'''))
                      (GLabelMap.map (Axiomatic (ADTValue:=av))
                                  (map_aug_mod_name op_mod_name'
                                                    (GenExports codWrap domWrap AbsR' RepInv DecomposeRepPre
                                                                DecomposeRepPost DecomposeRepPrePoseAgree ValidImpl))))
                   env'))
           (progsOK : forall midx,
               {prog : Stmt &
                       (forall env_ext,
                           LiftMethod (env'' env_ext) RepInv (DecomposeRep RepWrapper)
                                      (codWrap midx) (domWrap midx) prog (Methods adtImpl midx))
                       (* Syntactic Checks *)
                       /\ NoUninitDec.is_no_uninited
                            {|
                              FuncCore.ArgVars := BuildArgNames (Datatypes.length (fst
                                                                                     (MethodDomCod
                                                                                        (BuildADTSig consSigs methSigs) midx)))
                                                                numRepArgs;
                              FuncCore.RetVar := "ret";
                              FuncCore.Body := Compile.compile
                                                 (CompileDFacade.compile prog) |} = true
                       /\ (GoodModuleDec.is_arg_len_ok
                             (Compile.compile (CompileDFacade.compile prog)) = true)
                       /\ (GoodModuleDec.is_good_size
                             (Datatypes.length
                                (GetLocalVars.get_local_vars
                                   (Compile.compile (CompileDFacade.compile prog))
                                   (BuildArgNames (Datatypes.length (fst
                                                                       (MethodDomCod
                                                                          (BuildADTSig consSigs methSigs) midx))) numRepArgs) "ret") +
                              Depth.depth (Compile.compile (CompileDFacade.compile prog))) =
                           true)
                       /\  is_disjoint (assigned prog)
                                       (StringSetFacts.of_list
                                          (BuildArgNames (Datatypes.length (fst
                                                                              (MethodDomCod
                                                                                 (BuildADTSig consSigs methSigs) midx)))
                                                         numRepArgs)) = true
                       /\ is_syntax_ok prog = true} )
           (distinct_mod_name : negb (ListFacts3.string_bool ax_mod_name' op_mod_name') = true)
           (unique_op_mod_name'
            : forallb (fun x : string => negb (ListFacts3.string_bool op_mod_name' x))
                      (map (fun x : string * string * AxiomaticSpec av => fst (fst x))
                           (GLabelMap.elements (elt:=AxiomaticSpec av) env)) = true)
           (no_cito_clash_op_mod
            : negb (prefix "__cmod_impl_" op_mod_name') = true)
           (no_cito_clash_env
            : forallb NameDecoration.is_good_module_name
                      (map (fun x => fst (fst x)) (GLabelMap.elements  env)) = true)

  : BuildCompileUnit2TSpec (env'' (StringMap.empty _))
                           AbsR'
                           RepInv
                           DecomposeRep
                           DecomposeRepPre
                           DecomposeRepPost
                           numRepArgs
                           ax_mod_name'
                           op_mod_name'
                           codWrap
                           domWrap
                           RepWrapper
                           DecomposeRepPrePoseAgree
                           ValidImpl.
Proof.
  eexists {| module := {| Funs :=
                            BuildFun _
                              adtImpl DecomposeRep _ codWrap domWrap
                              RepWrapper progsOK;
                          Imports := _;
                          import_module_names_good := no_cito_clash_env
                       |};
             exports_in_domain :=
               BuildCompileUnit2T_exports_in_domain (UniqueMeth := UniqueMeth) _ _ _ _ _ _ _ _;
             ax_mod_name := ax_mod_name';
             op_mod_name := op_mod_name';
             op_mod_name_ok := no_cito_clash_op_mod;
             name_neq := distinct_mod_name;
             op_mod_name_not_in_imports := unique_op_mod_name';
             proof := BuildCompileUnit2T_proof  (UniqueMeth := UniqueMeth)
                                                _ _ _ _ _ _ _ _
                                                distinct_mod_name unique_op_mod_name'
                                                no_cito_clash_op_mod no_cito_clash_env
          |}.
  eapply BuildCompileUnit2T_projT2; eauto.
Defined.

Arguments DecomposePosti3list _ _ _ _ _ _ _ _ _ _ / .
Arguments DecomposePrei3list _ _ _ _ _ _ _ _ _ / .
