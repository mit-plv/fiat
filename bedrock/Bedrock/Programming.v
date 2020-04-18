(* Final syntax for structured programming *)

Require Import Coq.Lists.List Coq.NArith.NArith Coq.Bool.Bool Coq.Strings.String.

Require Import Bedrock.Word Bedrock.PropX Bedrock.PropXTac Bedrock.IL Bedrock.LabelMap Bedrock.XCAP Bedrock.Structured Bedrock.StructuredModule Bedrock.Linker Bedrock.Memory Bedrock.SepIL.

Require Import Bedrock.sep.Locals.

Set Implicit Arguments.



(** * The type of context-independent structured program chunks *)

Inductive chunk' :=
| StraightLine : list instr -> chunk'
| Structured : list instr -> (forall im mn, importsGlobal im -> cmd im mn) -> chunk'.

Definition chunk := list string -> nat -> chunk'.
(* Arguments: local variables and amount of reserved stack space *)

Definition toCmd (ch : chunk) im mn (H : importsGlobal im) ns res : cmd im mn :=
  match ch ns res with
    | StraightLine is => Straightline_ im mn is
    | Structured nil c => c im mn H
    | Structured is c => Seq_ H (Straightline_ im mn is) (c im mn H)
  end.

Definition Seq (ch1 ch2 : chunk) : chunk := fun ns res =>
  match ch1 ns res, ch2 ns res with
    | StraightLine is1, StraightLine is2 => StraightLine (is1 ++ is2)
    | StraightLine is1, Structured is2 c => Structured (is1 ++ is2) c
    | Structured is1 c1, _ => Structured is1 (fun im mn H => Seq_ H (c1 im mn H) (toCmd ch2 mn H ns res))
  end.

Definition Instr (i : list string -> instr) : chunk := fun ns _ =>
  StraightLine (i ns :: nil).

Definition Diverge : chunk := fun _ _ =>
  Structured nil (fun im mn _ => Diverge_ im mn).

Definition Fail : chunk := fun _ _ =>
  Structured nil (fun im mn _ => Fail_ im mn).

Definition Skip : chunk := fun _ _ =>
  Structured nil (fun im mn _ => Skip_ im mn).

Definition Assert_ (post : list string -> nat -> assert) : chunk := fun ns res =>
  Structured nil (fun im mn _ => Assert_ im mn (post ns res)).

Definition rvalue' := list string -> rvalue.

Record condition := {
  COperand1 : rvalue';
  CTest : test;
  COperand2 : rvalue'
}.

Definition If_ (c : condition) (Then Else : chunk) : chunk := fun ns res =>
  Structured nil (fun im mn H => If_ H (COperand1 c ns) (CTest c) (COperand2 c ns)
    (toCmd Then mn H ns res) (toCmd Else mn H ns res)).

Definition While_ (inv : list string -> nat -> assert) (c : condition)
  (Body : chunk) : chunk := fun ns res =>
  Structured nil (fun im mn H => While_ H (inv ns res) (COperand1 c ns) (CTest c)
    (COperand2 c ns) (toCmd Body mn H ns res)).

Definition Goto (rv : rvalue') : chunk := fun ns _ =>
  Structured nil (fun im mn H => match rv ns with
                                   | RvLabel f => Goto_ H mn f
                                   | _ => IGoto im mn (rv ns)
                                 end).

Fixpoint setArgs (slot : nat) (args : list rvalue') (ns : list string) :=
  match args with
    | nil => nil
    | arg :: args' =>
      Binop Rv Sp Plus (natToW (4 + 4 * List.length ns))
      :: Assign (LvMem (Indir Rv (natToW slot))) (arg ns)
      :: setArgs (4 + slot) args' ns
  end.

Definition lvalue' := list string -> lvalue.

Definition Call_ (retOpt : option lvalue') (f : label) (args : list rvalue')
  (afterCall : list string -> nat -> assert) : chunk := fun ns res =>
  Structured (setArgs 4 args ns
    ++ Binop Sp Sp Plus (natToW (4 + 4 * List.length ns)) :: nil)
  (fun im mn H => Seq_ H (Call_ H mn f (afterCall ns res))
    (Straightline_ im mn
      (Binop Sp Sp Minus (natToW (4 + 4 * List.length ns))
        :: match retOpt with
             | None => nil
             | Some lv => Assign (lv ns) Rv :: nil
           end))).

Definition ICall_ (retOpt : option lvalue') (f : rvalue') (args : list rvalue')
  (afterCall : list string -> nat -> assert) : chunk := fun ns res =>
  Structured (Assign Rp (f ns)
    :: setArgs 4 args ns
    ++ Binop Sp Sp Plus (natToW (4 + 4 * List.length ns))
    :: Assign Rv Rp :: nil)
  (fun im mn H => Seq_ H (ICall_ im mn Rv (afterCall ns res))
    (Straightline_ im mn
      (Binop Sp Sp Minus (natToW (4 + 4 * List.length ns))
        :: match retOpt with
             | None => nil
             | Some lv => Assign (lv ns) Rv :: nil
           end))).


(** * Modules *)

Record function := {
  FName : string;
  FVars : list string;
  FReserved : nat;
  FPrecondition : assert;
  FBody : chunk
}.

Definition bmodule_ (im : list import) (mn : string)
  (fs : list function) : module :=
  bmodule_ im (List.map (fun p => match p with
                                    | {| FName := f; FVars := ns; FReserved := res;
                                      FPrecondition := pre; FBody := ch |} =>
                                    (f, pre, fun im' H => toCmd ch mn H ns res)
                                  end) fs).

Definition compile (m : module) : list (label * block) :=
  List.map (fun x => let '(k, (_, b)) := x in (k, b)) (LabelMap.elements (XCAP.Blocks m)).


(** * Notations *)

(** ** Expressions *)

Infix "+" := Indir : loc_scope.
Delimit Scope loc_scope with loc.

Notation "$[ v ]" := ((fun _ => LvMem v%loc) : lvalue') (at level 0) : SP_scope.
Notation "$8[ v ]" := ((fun _ => LvMem8 v%loc) : lvalue') (at level 0) : SP_scope.

Definition regInL (r : reg) : lvalue' := fun _ => LvReg r.
Coercion regInL : reg >-> lvalue'.

Coercion natToW: nat >-> W.

Definition NToW (n : N) : W := NToWord _ n.
Coercion NToW : N >-> W.

Definition labl (modl func : string) : label := (modl, Global func).

Infix "!" := labl (at level 0, only parsing) : SP_scope.

Delimit Scope SP_scope with SP.

Definition lvalIn (lv : lvalue') : rvalue' := fun ns => RvLval (lv ns).
Coercion lvalIn : lvalue' >-> rvalue'.

Definition immInR (w : W) : rvalue' := fun _ => RvImm w.
Coercion immInR : W >-> rvalue'.

Definition labelIn (l : label) : rvalue' := fun _ => RvLabel l.
Coercion labelIn : label >-> rvalue'.


(** ** Instructions *)

Inductive rhs :=
| Rvalue : rvalue' -> rhs
| Bop : rvalue' -> binop -> rvalue' -> rhs.

Coercion Rvalue : rvalue' >-> rhs.

Definition RvImm' (n : nat) := RvImm ($ n).

Coercion RvImm' : nat >-> rvalue.

Notation "x + y" := (Bop x Plus y) : SP_scope.
Notation "x - y" := (Bop x Minus y) : SP_scope.
Notation "x * y" := (Bop x Times y) : SP_scope.

Notation "x = y" := {| COperand1 := x; CTest := IL.Eq; COperand2 := y |} : SP_scope.
Notation "x <> y" := {| COperand1 := x; CTest := IL.Ne; COperand2 := y |} : SP_scope.
Notation "x < y" := {| COperand1 := x; CTest := IL.Lt; COperand2 := y |} : SP_scope.
Notation "x <= y" := {| COperand1 := x; CTest := IL.Le; COperand2 := y |} : SP_scope.
Notation "x > y" := {| COperand1 := y; CTest := IL.Lt; COperand2 := x |} : SP_scope.
Notation "x >= y" := {| COperand1 := y; CTest := IL.Le; COperand2 := x |} : SP_scope.

Definition Assign' (lv : lvalue') (rh : rhs) :=
  Instr (fun ns => match rh with
                     | Rvalue rv => Assign (lv ns) (rv ns)
                     | Bop rv1 bo rv2 => Binop (lv ns) (rv1 ns) bo (rv2 ns)
                   end).

Infix "<-" := Assign' (no associativity, at level 90) : SP_scope.
Infix ";;" := Seq (right associativity, at level 95) : SP_scope.
Notation "x <-* y" := (Rv <- y;; x <- $[Rv])%SP (at level 90) : SP_scope.
Notation "x *<- y" := (Rv <- x;; $[Rv] <- y)%SP (at level 90) : SP_scope.
Notation "x <-*8 y" := (Rv <- y;; x <- $8[Rv])%SP (at level 90) : SP_scope.
Notation "x *<-8 y" := (Rv <- x;; $8[Rv] <- y)%SP (at level 90) : SP_scope.

Definition variableSlot (nm : string) : lvalue' := fun ns =>
  LvMem (Indir Sp (4 + variablePosition ns nm)).

Coercion variableSlot : string >-> lvalue'.


(** ** Commands *)

Local Notation INV := (fun inv => inv true (fun w => w)).
Local Notation RET := (fun inv ns => inv true (fun w => w ^- $ (4 + 4 * List.length ns)) ns).

Notation "'Assert' [ p ]" := (Assert_ (INV p)) (no associativity, at level 95) : SP_scope.

Notation "'If' c { b1 } 'else' { b2 }" := (If_ c b1 b2)
  (no associativity, at level 95, c at level 0) : SP_scope.

Notation "[ p ] 'While' c { b }" := (While_ (INV p) c b)
  (no associativity, at level 95, c at level 0) : SP_scope.

Notation "'Call' f () [ p ]" :=
  (Call_ None f nil (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.
Notation "'Call' f ( x1 , .. , xN ) [ p ]" :=
  (Call_ None f (@cons rvalue' x1 (.. (@cons rvalue' xN nil) ..)) (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.
Notation "rv <-- 'Call' f () [ p ]" :=
  (Call_ (@Some lvalue' rv) f nil (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.
Notation "rv <-- 'Call' f ( x1 , .. , xN ) [ p ]" :=
  (Call_ (@Some lvalue' rv) f (@cons rvalue' x1 (.. (@cons rvalue' xN nil) ..)) (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.

Notation "'Return' e" := (Rv <- e;; Rp <- $[Sp+0];; Goto Rp)%SP
  (no associativity, at level 95) : SP_scope.

Notation "'ICall' f () [ p ]" :=
  (ICall_ None f nil (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.
Notation "'ICall' f ( x1 , .. , xN ) [ p ]" :=
  (ICall_ None f (@cons rvalue' x1 (.. (@cons rvalue' xN nil) ..)) (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.
Notation "rv <-- 'ICall' f () [ p ]" :=
  (ICall_ (@Some lvalue' rv) f nil (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.
Notation "rv <-- 'ICall' f ( x1 , .. , xN ) [ p ]" :=
  (ICall_ (@Some lvalue' rv) f (@cons rvalue' x1 (.. (@cons rvalue' xN nil) ..)) (RET p))
  (no associativity, at level 95, f at level 0) : SP_scope.


(** * Specs *)

Notation "st # r" := (Regs (snd st) r) (no associativity, at level 0).
Notation "st .[ a ]" := (ReadWord (fst st) (Mem (snd st)) a) (no associativity, at level 0).

Notation "st ~> p" := (fun st : settings * state => p%PropX%nat) (at level 100, only parsing).

Inductive qspec :=
| Body : HProp -> qspec
| Quant : forall A, (A -> qspec) -> qspec.

Notation "'Ex' x , b" := (Quant (fun x => b)) : qspec_scope.
Notation "'Ex' x : A , b" := (Quant (fun x : A => b)) : qspec_scope.

Notation "'Emp'" := (Body (empB _)) : qspec_scope.
Notation "[| P |]" := (Body (injB _ P)) : qspec_scope.
Notation "[|| P ||]" := (Body (injBX P%PropX)) : qspec_scope.
Notation "a =8> v" := (Body (ptsto8 _ a v)) : qspec_scope.
Notation "a =*> v" := (Body (ptsto32 _ a v)) : qspec_scope.
Notation "P * Q" := (Body (starB P%Sep Q%Sep)) : qspec_scope.
Coercion Body : HProp >-> qspec.

Delimit Scope qspec_scope with qspec.

Local Open Scope string_scope.

Fixpoint qspecOut (qs : qspec) pc st b (k : HProp -> propX pc st b) : propX pc st b :=
  match qs with
    | Body P => k P
    | Quant A f => Ex x : A, qspecOut (f x) k
  end%PropX.

Notation "i @@@ sp" := (ExX, Cptr (fst i) #0 /\ Al st, sp (snd i, st) ---> #0 (snd i, st))%PropX
  (no associativity, at level 39) : PropX_scope.

Definition localsInvariant (pre : vals -> W -> qspec) (post : vals -> W -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    ExX, Ex vs, qspecOut (pre (sel vs) st#Rv) (fun PRE =>
      ![ ^[locals ("rp" :: ns) vs res sp * PRE] * #0 ] st
      /\ (if rpStashed then sel vs "rp" else st#Rp, fst st) @@@ (st' ~>
        [| st'#Sp = sp |]
        /\ Ex vs', qspecOut (post (sel vs) st#Rv st'#Rv) (fun POST =>
          ![ ^[locals ("rp" :: ns) vs' res sp * POST] * #1 ] st'))).

Notation "'PRE' [ vs ] pre 'POST' [ rv ] post" := (localsInvariant (fun vs _ => pre%qspec%Sep) (fun vs _ rv => post%qspec%Sep))
  (at level 89).

Notation "'PRE' [ vs , rv ] pre 'POST' [ rv' ] post" := (localsInvariant (fun vs rv => pre%qspec%Sep) (fun vs rv rv' => post%qspec%Sep))
  (at level 89).

Notation "'Al' x , s" := (fun a b c d e => PropX.Exists (fun x => s a b c d e)).
Notation "'Al' x : A , s" := (fun a b c d e => PropX.Exists (fun x : A => s a b c d e)).

Record spec := {
  Reserved : nat;
  Formals : list string;
  Precondition : option (list string) -> assert
  (* Argument is used to tell the spec which additional local variables there are, for a use of the spec within a function body. *)
}.

Notation "'SPEC' 'reserving' n inv" :=
  (let n' := n in {| Reserved := n';
    Formals := nil;
    Precondition :=  fun extras =>
    match extras with
      | None => inv false (fun w => w) nil n'
      | Some extras => inv true (fun w => w) extras (n' - List.length extras)
    end |}) (at level 90, n at level 0, inv at next level).

Notation "'SPEC' ( x1 , .. , xN ) 'reserving' n inv" :=
  (let vars := cons x1 (.. (cons xN nil) ..) in
   let n' := n in
    {| Reserved := n';
      Formals := vars;
      Precondition := fun extras =>
      match extras with
        | None => inv false (fun w => w) vars n'
        | Some extras => inv true (fun w => w) extras (n' - (List.length extras - List.length vars))
      end |} ) (at level 90, n at level 0, x1 at level 0, xN at level 0, inv at next level).


(** ** Modules *)

Notation "'bfunction' name () [ p ] b 'end'" :=
  (let p' := p in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := ($[Sp+0] <- Rp;;
        (fun _ _ =>
          Structured nil (fun im mn _ => Structured.Assert_ im mn (Precondition p' (Some nil))));;
        b)%SP;
      FVars := nil;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, only parsing) : SPfuncs_scope.

Notation "'bfunction' name ( x1 , .. , xN ) [ p ] b 'end'" :=
  (let p' := p in
   let vars := cons x1 (.. (cons xN nil) ..) in
   let b' := b%SP in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := ($[Sp+0] <- Rp;;
        (fun _ _ =>
          Structured nil (fun im mn _ => Structured.Assert_ im mn (Precondition p' (Some vars))));;
        (fun ns res => b' ns (res - (List.length vars - List.length (Formals p')))%nat))%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Delimit Scope SPfuncs_scope with SPfuncs.


Notation "{{ x 'with' .. 'with' y }}" := (cons x .. (cons y nil) ..) (only parsing) : SPfuncs_scope.
Delimit Scope SPfuncs_scope with SPfuncs.

Notation "'bmodule' name fs" := (bmodule_ nil name fs%SPfuncs) (no associativity, at level 95, name at level 0, only parsing).

Notation "x ! y" := (x, y) (only parsing) : SPimps_scope.
Notation "name @ [ p ]" := (let (x, y) := name in (x, y, Precondition p None)) (at level 0, only parsing) : SPimps_scope.
Notation "[[ x , .. , y ]]" := (cons x .. (cons y nil) ..) (only parsing) : SPimps_scope.

Delimit Scope SPimps_scope with SPimps.

Notation "'bimport' is 'bmodule' name fs" := (bmodule_ is%SPimps name fs%SPfuncs) (no associativity, at level 95, name at level 0, only parsing).


(** * Tactics *)

Theorem evalInstrs_nil : forall stn st, evalInstrs stn st nil = Some st.
  reflexivity.
Qed.

Theorem evalInstrs_cons : forall stn st i is, evalInstrs stn st (i :: is)
  = match evalInstr stn st i with
      | None => None
      | Some st' => evalInstrs stn st' is
    end.
  reflexivity.
Qed.

Local Transparent evalInstrs.

Theorem evalInstrs_app : forall stn st2 st3 is2 is1 st1, evalInstrs stn st1 is1 = Some st2
  -> evalInstrs stn st2 is2 = st3
  -> evalInstrs stn st1 (is1 ++ is2) = st3.
  induction is1; simpl; intuition.
  congruence.
  destruct (evalInstr stn st1 a); auto; congruence.
Qed.

Global Opaque evalInstrs.

Ltac conditions :=
  unfold evalCond in *; simpl in *; unfold weqb, wneb, wltb, wleb in *; simpl in *;
    repeat match goal with
             | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
             | [ H : Some _ = None |- _ ] => discriminate H
             | [ H : (if ?E then _ else _) = _ |- _ ] => destruct E; try discriminate; clear H
             | [ H : evalInstrs _ _ _ = _ |- _ ] =>
               repeat (rewrite evalInstrs_cons in H; simpl in H; autorewrite with IL in H);
                 try rewrite evalInstrs_nil in H
           end; simpl.

Ltac structured := apply bmoduleOk; [ exact (refl_equal false) | exact I |
  simpl; repeat (apply List.Forall_nil || apply List.Forall_cons);
    (simpl; propxFo; conditions) ].

Fixpoint vcsImp (Ps : list Prop) (goal : Prop) : Prop :=
  match Ps with
    | nil => goal
    | P :: Ps' => P -> vcsImp Ps' goal
  end.

Local Hint Constructors vcs.

Lemma vcsImp_correct' : forall Ps (goal : Prop), (vcs Ps -> goal) -> vcsImp Ps goal.
  induction Ps; simpl; auto.
Qed.

Theorem vcsImp_correct : forall Ps, vcsImp Ps (vcs Ps).
  intros; apply vcsImp_correct'; auto.
Qed.

Ltac structured_auto simp := apply bmoduleOk; [ exact (refl_equal false) | exact I |
  simp; simpl; match goal with
                 | [ |- vcs ?Ps ] => apply (vcsImp_correct Ps)
               end ].

Ltac link_simp := simpl Imports; simpl Exports;
  cbv beta iota zeta delta [importsOk LabelMap.fold LabelMap.Raw.fold
    LabelMap.this importsMap fold_left LabelMap.add LabelMap.Raw.add
    LabelMap.empty LabelMap.Raw.empty
    LabelKey.compare LabelKey.compare' string_lt
    fst snd string_dec sumbool_rec sumbool_rect
    Ascii.N_of_ascii Ascii.N_of_digits N.compare Pos.compare
    string_rec string_rect Ascii.ascii_dec
    LabelMap.find LabelMap.Raw.find Nplus Nmult Pos.compare_cont
    Pos.add Pos.mul Ascii.ascii_rec Ascii.ascii_rect
    Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym
    label'_lt label'_eq label'_rec label'_rect
    LabelMap.Raw.bal LabelMap.Raw.create
    Int.Z_as_Int.gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.ge_lt_dec
    LabelMap.Raw.height
    ZArith_dec.Z_gt_le_dec Int.Z_as_Int._0
    BinInt.Z.add Int.Z_as_Int._1 Int.Z_as_Int._2
    ZArith_dec.Z_gt_dec ZArith_dec.Z_ge_lt_dec Int.Z_as_Int.max
    BinInt.Z.max BinInt.Z.compare union ZArith_dec.Z_ge_dec
    diff LabelMap.mem LabelMap.Raw.mem LabelMap.is_empty
    LabelMap.Raw.is_empty Pos.succ].

Ltac link m1 m2 :=
  apply linkOk; [ apply m1 | apply m2 | exact (refl_equal true)
    | link_simp; tauto | link_simp; tauto | link_simp; tauto ].

Lemma specs_cong : forall (specs : codeSpec W (settings * state)) x p,
  specs x = p
  -> forall y, x = y
    -> specs y = p.
  congruence.
Qed.

Implicit Arguments specs_cong [specs x p y].

Hint Extern 1 (?specs _ = Some _) =>
  match goal with
    | [ H : specs _ = Some _ |- _ ] => apply (specs_cong H); congruence
  end.

Lemma use_himp : forall pc state specs (P Q : hprop pc state nil), himp specs P Q
  -> forall s m, interp specs (P s m)
    -> interp specs (Q s m).
  intros; apply (Imply_sound (H _ _)); auto.
Qed.

Lemma Imply_refl : forall pc state specs (P : PropX pc state),
  interp specs (P ---> P).
  intros; apply Imply_I; apply Env; simpl; auto.
Qed.

Section PropX.
  Variables pc state : Type.
  Variable P : PropX pc state.
  Variable specs : codeSpec pc state.

  Open Scope PropX_scope.

  Theorem injL : forall (p : Prop),
    (p -> interp specs P)
    -> interp specs ([| p |] ---> P).
    intros.
    apply Imply_I.
    eapply Inj_E.
    eauto.
    auto.
  Qed.

  Theorem cptrL : forall i a,
    (specs i = Some (fun x => a x) -> interp specs P)
    -> interp specs (Cptr i a ---> P).
    intros.
    apply Imply_I.
    eapply Cptr_E.
    eauto.
    eauto.
  Qed.

  Theorem andL : forall Q R,
    interp specs (Q ---> (R ---> P))
    -> interp specs (Q /\ R ---> P).
    intros.
    apply Imply_I.
    eapply Imply_E.
    eapply Imply_E.
    eauto.
    eapply And_E1.
    eauto.
    eapply And_E2.
    eauto.
  Qed.

  Ltac hyp := eapply Env; simpl; eauto.

  Theorem existsL : forall A (p : A -> _),
    (forall x, interp specs (p x ---> P))
    -> interp specs ((Exists p) ---> P).
    intros.
    apply Imply_I.
    eapply Exists_E.
    eauto.
    intros.
    eapply Imply_E.
    eauto.
    hyp.
  Qed.

  Theorem injR : forall (p : Prop),
    p
    -> interp specs (P ---> [| p |]).
    intros.
    apply Imply_I.
    eapply Inj_I.
    auto.
  Qed.

  Theorem cptrR : forall i a,
    specs i = Some (fun x => a x)
    -> interp specs (P ---> Cptr i a).
    intros.
    apply Imply_I.
    apply Cptr_I.
    auto.
  Qed.

  Theorem andR : forall Q R,
    interp specs (P ---> Q)
    -> interp specs (P ---> R)
    -> interp specs (P ---> Q /\ R).
    intros.
    apply Imply_I.
    apply And_I.
    eapply Imply_E.
    eauto.
    eauto.
    eapply Imply_E.
    eauto.
    eauto.
  Qed.

  Theorem allR : forall A (p : A -> _),
    (forall x, interp specs (P ---> p x))
    -> interp specs (P ---> (Forall p)).
    intros.
    apply Imply_I.
    apply Forall_I; intro.
    eapply Imply_E.
    eauto.
    eauto.
  Qed.

  Theorem existsR : forall A (p : A -> _) x,
    interp specs (P ---> p x)
    -> interp specs (P ---> (Exists p)).
    intros.
    apply Imply_I.
    apply Exists_I with x.
    eapply Imply_E.
    eauto.
    eauto.
  Qed.

  Theorem existsXR : forall A (p : propX _ _ (A :: nil)) x,
    interp specs (P ---> Subst p x)
    -> interp specs (P ---> (ExistsX p)).
    intros.
    apply Imply_I.
    apply ExistsX_I with x.
    eapply Imply_E.
    eauto.
    eauto.
  Qed.

  Theorem forallXR : forall A (p : propX _ _ (A :: nil)),
    (forall x, interp specs (P ---> PropX.Subst p x))
    -> interp specs (P ---> (ForallX p)).
    intros.
    apply Imply_I.
    apply ForallX_I; intro.
    eapply Imply_E.
    eauto.
    eauto.
  Qed.

  Theorem swap : forall Q R,
    interp specs (R ---> Q ---> P)
    -> interp specs (Q ---> R ---> P).
    intros.
    do 2 apply Imply_I.
    eapply Imply_E.
    eapply Imply_E.
    eauto.
    eauto.
    hyp.
  Qed.
End PropX.

Ltac imply_simp' := match goal with
                      | [ H : ex _ |- _ ] => destruct H
                      | [ H : _ /\ _ |- _ ] => destruct H
                      | [ |- interp _ (Inj _ ---> _) ] => apply injL; intro
                      | [ |- interp _ (Cptr _ _ ---> _) ] => apply cptrL; intro
                      | [ |- interp _ (And _ _ ---> _) ] => apply andL
                      | [ |- interp _ (Exists _ ---> _) ] => apply existsL; intro
                      | [ |- interp _ (_ ---> Inj _) ] => apply injR
                      | [ |- interp _ (_ ---> Cptr _ _) ] => apply cptrR
                      | [ |- interp _ (_ ---> And _ _) ] => apply andR
                      | [ |- interp _ (_ ---> Forall _) ] => apply allR; intro
                      | [ |- interp _ (_ ---> Exists _) ] => eapply existsR
                      | [ |- interp _ (_ ---> ExistsX _) ] => eapply existsXR; unfold Subst; simpl
                      | [ |- interp _ (_ ---> ForallX _) ] => eapply forallXR; unfold Subst; simpl; intro
                    end.

Ltac reduce unf := try (apply simplify_fwd'; simpl); autorewrite with sepFormula; unf; simpl; try congruence.

Ltac imply_simp unf := (imply_simp' || (apply swap; imply_simp')); reduce unf.

Ltac descend := autorewrite with IL in *;
  repeat match goal with
           | [ |- Logic.ex _ ] => eexists
           | [ |- _ /\ _ ] => split
           | [ |- specs _ = _ ] => eassumption
         end; cbv zeta; simpl; intros.

Ltac propxFo' := propxFo; repeat match goal with
                                   | [ H : ?P -> False |- _ ] => change (not P) in H
                                 end.

Ltac ho unf :=
  match goal with
    | [ H : ?X = Some _ |- ?X = Some (fun x => ?g x) ] => apply H
    | [ H : forall x, interp _ (_ ---> ?p _) |- interp _ (?p _) ] => apply (Imply_sound (H _)); propxFo'
    | [ H : forall x, interp _ (_ ---> _ _) |- interp _ (_ ---> _ _) ] => eapply Imply_trans; [ | apply H ]
    | [ |- interp _ _ ] => progress propxFo'
    | [ |- interp _ (_ ---> _) ] => imply_simp unf; repeat imply_simp unf
  end; autorewrite with IL in *.

Ltac withLabel := eexists; split; [ compute; eauto | intros ].

Ltac equate x y := let H := fresh in assert (H : x = y) by reflexivity; clear H.

Ltac safety mok lab := eapply safety; [ exact (refl_equal 0) | exact (refl_equal Datatypes.Lt) | apply mok
  | match goal with
      | [ |- LabelMap.find ?l _ = Some (?u, ?v) ] => equate l lab; simpl;
        match goal with
          | [ |- context[LabelMap.add lab (?u', ?v') _] ] =>
            equate u u'; equate v v'; reflexivity
        end
    end
  | reflexivity
  | propxFo ].


(** * Executing a program *)

Section exec.
  Variable stn : settings.
  Variable prog : program.

  Fixpoint exec (n : nat) (st : state') : option state' :=
    match n with
      | O => Some st
      | S n' => match step stn prog st with
                  | None => None
                  | Some st => exec n' st
                end
    end.
End exec.

Global Opaque natToWord.


(** * Some more notational conveniences *)

Definition B2N (b : bool) : nat :=
  if b then 1 else 0.

Coercion B2N : bool >-> nat.

Definition propToWord (P : Prop) (b : W) :=
  IF P then b = 1 else b = 0.
Infix "\is" := (propToWord) (at level 71, no associativity).

Ltac propToWord := unfold propToWord, IF_then_else; tauto.

Lemma use_propToWord : forall P b, P \is b
  -> forall P', (P' <-> P)
    -> P' \is b.
  propToWord.
Qed.

Lemma propToWord_true : forall (P : Prop) (b : W), b = 1
  -> P
  -> P \is b.
  propToWord.
Qed.

Lemma propToWord_false : forall (P : Prop) (b : W), b = 0
  -> ~P
  -> P \is b.
  propToWord.
Qed.

Hint Resolve propToWord_true propToWord_false.

Hint Extern 5 (_ \is _) => eapply use_propToWord; [ eassumption | ].
