Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith Coq.NArith.NArith Coq.Logic.Eqdep_dec Coq.Lists.List.
Require Import Bedrock.Nomega Bedrock.Word Bedrock.Memory Bedrock.PropX Bedrock.PropXTac Bedrock.IL Bedrock.DepList Bedrock.Heaps Bedrock.SepTheoryXIL.

Set Implicit Arguments.

Fixpoint allWordsUpto (width init : nat) : list (word width) :=
  match init with
    | O => nil
    | S init' => natToWord width init' :: allWordsUpto width init'
  end.

Definition allWords_def (width : nat) :=
  allWordsUpto width (pow2 width).

Fixpoint memoryInUpto (width init : nat) (m : word width -> option B)
  : hlist (fun _ => option B) (allWordsUpto width init) :=
  match init with
    | O => HNil
    | S init' =>
      let w := natToWord width init' in
      let v := m w in
      HCons v (memoryInUpto (width := width) init' m)
  end.

Definition memoryIn_def (width : nat) :=
  memoryInUpto (width := width) (pow2 width).

Theorem fcong : forall A (B : A -> Type) (f g : forall x, B x) x,
  f = g
  -> f x = g x.
  congruence.
Defined.

Module Type ALL_WORDS.
  Parameter allWords : forall width : nat, list (word width).

  Axiom allWords_eq : allWords = allWords_def.

  Parameter memoryIn : forall width, (word width -> option B) -> hlist (fun _ : word width => option B) (allWords width).

  Axiom memoryIn_eq : forall width,
    memoryIn (width := width)
    = match fcong (fun width => list (word width)) width (sym_eq allWords_eq) in _ = L return _ -> hlist _ L with
        | refl_equal => memoryIn_def (width := width)
      end.
End ALL_WORDS.

Module AllWords : ALL_WORDS.
  Definition allWords := allWords_def.

  Theorem allWords_eq : allWords = allWords_def.
    reflexivity.
  Defined.

  Definition memoryIn := memoryIn_def.

  Theorem memoryIn_eq : forall width,
    memoryIn (width := width)
    = match fcong (fun width => list (word width)) width (sym_eq allWords_eq) in _ = L return _ -> hlist _ L with
        | refl_equal => memoryIn_def (width := width)
      end.
    reflexivity.
  Qed.
End AllWords.

Import AllWords.
Export AllWords.

Lemma natToWord_injective : forall width n n',
  (n < pow2 width)%nat
  -> (n' < pow2 width)%nat
  -> natToWord width n = natToWord width n'
  -> n = n'.
  intros.
  destruct (wordToNat_natToWord width n);
    destruct (wordToNat_natToWord width n');
      intuition.
  rewrite H1 in H4.
  rewrite H4 in H2.
  assert (x = 0).
  destruct x; simpl in *.
  omega.
  generalize dependent (x * pow2 width).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; simpl in *.
  omega.
  generalize dependent (x0 * pow2 width).
  intros.
  omega.
  subst.
  omega.
Qed.

Local Hint Constructors NoDup.

Lemma NoDup_allWordsUpto' : forall width init' init,
  init <= init' < pow2 width
  -> ~In (natToWord width init') (allWordsUpto width init).
  induction init; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] => apply natToWord_injective in H; omega
    end.
Qed.

Local Hint Resolve NoDup_allWordsUpto'.

Theorem NoDup_allWordsUpto : forall width init,
  (init <= pow2 width)%nat
  -> NoDup (allWordsUpto width init).
  induction init; simpl; intuition.
Qed.

Theorem NoDup_allWords : forall width,
  NoDup (allWords width).
  rewrite allWords_eq; intros; apply NoDup_allWordsUpto; omega.
Qed.

Module BedrockHeap.
  Definition addr := W.

  Definition mem := mem.

  Definition mem_get := ReadByte.

  Definition mem_set := WriteByte.

  Definition mem_acc (m : mem) (a : addr) :=
    exists v, m a = Some v.

  Theorem mem_get_acc : forall m p,
    mem_acc m p <->
    exists v, mem_get m p = Some v.
  Proof.
    intuition eauto.
  Qed.

  Theorem mem_set_acc : forall m p,
    mem_acc m p <->
    forall v, exists m', mem_set m p v = Some m'.
  Proof.
    intuition. destruct H. unfold mem_set, WriteByte. rewrite H.
    eauto. specialize (H (wzero _)). destruct H. unfold mem_set, mem_acc, WriteByte in *.
    destruct (m p); eauto. congruence.
  Qed.

  Theorem mem_acc_dec : forall m p,
    mem_acc m p \/ ~mem_acc m p.
  Proof.
    unfold mem_acc. intros; destruct (m p); eauto. right.
    intro. destruct H; congruence.
  Qed.

  Theorem mem_get_set_eq : forall m p v' m',
    mem_set m p v' = Some m' ->
    mem_get m' p = Some v'.
  Proof.
    unfold mem_set, mem_get, ReadByte, WriteByte. intros.
    destruct (m p); try congruence.
    inversion H; clear H; subst.
    destruct (weq p p); auto. congruence.
  Qed.

  Theorem mem_get_set_neq : forall m p p' v' m',
    p <> p' ->
    mem_set m p' v' = Some m' ->
    mem_get m' p = mem_get m p.
  Proof.
    unfold mem_set, mem_get, ReadByte, WriteByte; intros.
    destruct (m p'); try congruence.
    inversion H0; clear H0; subst.
    destruct (weq p p'); auto. congruence.
  Qed.

  (** mem writes don't modify permissions **)
  Theorem mem_set_perm : forall m p v m',
    mem_set m p v = Some m' ->
    (forall p, mem_acc m p -> mem_acc m' p).
  Proof.
    unfold mem_set, mem_acc, ReadByte, WriteByte; intros.
    generalize dependent H.
    case_eq (weq p p0); intros; subst.
    destruct (m p0); try congruence.
    inversion H1; subst; auto.
    rewrite H. eauto.

    destruct (m p); try congruence.
    inversion H1; subst.
    destruct (weq p0 p); eauto.
  Qed.

  Definition footprint_w (p : addr) : addr * addr * addr * addr :=
    (p , p ^+ $1 , p ^+ $2 , p ^+ $3).

  Theorem footprint_disjoint : forall p a b c d,
    footprint_w p = (a,b,c,d) ->
    a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d.
  Proof.
    unfold footprint_w. inversion 1. clear.
    repeat split; W_neq.
  Qed.

  Definition addr_dec := @weq 32.

  Definition all_addr := allWords 32.

  Theorem NoDup_all_addr : NoDup all_addr.
    apply NoDup_allWords.
  Qed.
End BedrockHeap.

Module ST := SepTheoryXIL.Make (BedrockHeap).
Import ST.
Export ST.
Import ST.HT.
Export ST.HT.


(** * Define some convenient connectives, etc. for specs *)

Definition memoryIn : mem -> smem := memoryIn.

Definition hpropB := hprop W (settings * state).
Definition HProp := hpropB nil.

Definition empB sos : hpropB sos := emp _ _.
Notation "'Emp'" := (empB _) : Sep_scope.

Definition injB sos (P : Prop) : hpropB sos := inj (Inj P).

Notation "[| P |]" := (injB _ P) : Sep_scope.

Definition injBX sos (P : propX W (settings * state) sos) : hpropB sos := inj P.

Notation "[|| P ||]" := (injBX P) : Sep_scope.

Definition ptsto8 sos : W -> B -> hpropB sos :=
  hptsto W (settings * state) sos.

Notation "a =8> v" := (ptsto8 _ a v) (no associativity, at level 39) : Sep_scope.

(* This breaks the hprop abstraction because it needs access to 'settings' *)
Definition ptsto32 sos (a v : W) : hpropB sos :=
  (fun stn sm => [| ST.HT.smem_get_word (implode stn) a sm = Some v
    /\ forall a', a' <> a /\ a' <> (a ^+ $1) /\ a' <> (a ^+ $2) /\ a' <> (a ^+ $3)
      -> ST.HT.smem_get a' sm = None |])%PropX.

Notation "a =*> v" := (ptsto32 _ a v) (no associativity, at level 39) : Sep_scope.

Definition starB sos : hpropB sos -> hpropB sos -> hpropB sos :=
  @star W (settings * state) sos.

Infix "*" := starB : Sep_scope.

Delimit Scope Sep_scope with Sep.

Fixpoint ptsto32m sos (a : W) (offset : nat) (vs : list W) : hpropB sos :=
  match vs with
    | nil => Emp
    | v :: nil => (match offset with
                     | O => a
                     | _ => a ^+ $ (offset)
                   end) =*> v
    | v :: vs' => (match offset with
                     | O => a
                     | _ => a ^+ $ (offset)
                   end) =*> v * ptsto32m sos a (4 + offset) vs'
  end%Sep.

Notation "a ==*> v1 , .. , vn" := (ptsto32m _ a O (cons v1 .. (cons vn nil) ..)) (no associativity, at level 39) : Sep_scope.

Definition exB sos T (p : T -> hpropB sos) : hpropB sos := ex p.

Notation "'Ex' x , p" := (exB (fun x => p)) : Sep_scope.
Notation "'Ex' x : A , p" := (exB (fun x : A => p)) : Sep_scope.

Definition hvarB sos (x : settings * smem -> propX W (settings * state) sos) : hpropB sos :=
  fun stn sm => x (stn, sm).

Notation "![ x ]" := (hvarB x) : Sep_scope.

Fixpoint arrayOf sos (p : W) (c : list W) : hpropB sos :=
  match c with
    | nil => [| True |]
    | a :: b => p =*> a * arrayOf sos (p ^+ $4) b
  end%Sep.

Notation "#0" := (![ #0%PropX ])%Sep : Sep_scope.
Notation "#1" := (![ #1%PropX ])%Sep : Sep_scope.
Notation "#2" := (![ #2%PropX ])%Sep : Sep_scope.
Notation "#3" := (![ #3%PropX ])%Sep : Sep_scope.
Notation "#4" := (![ #4%PropX ])%Sep : Sep_scope.

Definition lift1 t sos (p : hpropB sos) : hpropB (t :: sos) :=
  fun a b => Lift (p a b).

Fixpoint lift sos (p : HProp) : hpropB sos :=
  match sos with
    | nil => p
    | _ :: sos' => lift1 _ (lift sos' p)
  end.

Notation "^[ p ]" := (lift _ p) : Sep_scope.

Definition Himp (p1 p2 : HProp) : Prop :=
  forall specs, ST.himp specs p1 p2.

Notation "p1 ===> p2" := (Himp p1%Sep p2%Sep) (no associativity, at level 90).

(** * The main injector of separation formulas into PropX *)
Definition sepFormula_def sos (p : hpropB sos) (st : settings * state) : propX W (settings * state) sos :=
  p (fst st) (memoryIn (Mem (snd st))).

Module Type SEP_FORMULA.
  Parameter sepFormula : forall sos, hpropB sos -> settings * state -> propX W (settings * state) sos.

  Axiom sepFormula_eq : sepFormula = sepFormula_def.
End SEP_FORMULA.

Module SepFormula : SEP_FORMULA.
  Definition sepFormula := sepFormula_def.

  Theorem sepFormula_eq : sepFormula = sepFormula_def.
    reflexivity.
  Qed.
End SepFormula.

Import SepFormula.

Require Import Coq.Classes.RelationClasses Coq.Setoids.Setoid.

Global Add Parametric Morphism cs : (@sepFormula nil) with
  signature (@himp W (settings * state) cs ==> @eq (settings * state) ==> @PropXRel.PropX_imply _ _ cs)
as sepFormula_himp_imply.
  unfold himp. rewrite sepFormula_eq.
  unfold sepFormula_def.
  unfold PropXRel.PropX_imply.
  intros. unfold interp.
  eapply PropX.Imply_I.

  specialize (H (fst y0) (memoryIn (Mem (snd y0)))). eapply PropX.Imply_E.
  eapply PropXTac.valid_weaken. eapply H. firstorder.
  PropXRel.propxIntuition.
Qed.
Global Add Parametric Morphism cs : (@sepFormula nil) with
  signature (@heq W (settings * state) cs ==> @eq (settings * state) ==> @PropXRel.PropX_eq _ _ cs)
as sepFormula_himp_eq.
  rewrite sepFormula_eq. unfold heq, himp, sepFormula_def, PropXRel.PropX_eq, PropXRel.PropX_imply.
  intros. unfold interp in *. intuition; PropXRel.propxIntuition; eauto.
Qed.

Export SepFormula.

Definition substH sos (p1 : hpropB sos) (p2 : last sos -> PropX W (settings * state)) : hpropB (eatLast sos) :=
  fun st m => subst (p1 st m) p2.

Theorem subst_sepFormula : forall sos (p1 : hpropB sos) p2 st,
  subst (sepFormula p1 st) p2 = sepFormula (substH p1 p2) st.
  rewrite sepFormula_eq; reflexivity.
Qed.

Hint Rewrite subst_sepFormula : sepFormula.

Theorem substH_inj : forall sos P p,
  substH (injB sos P) p = injB _ P.
  reflexivity.
Qed.

Theorem substH_injX : forall sos P p,
  substH (injBX (sos := sos) P) p = injBX (subst P p).
  reflexivity.
Qed.

Theorem substH_ptsto8 : forall sos a v p,
  substH (ptsto8 sos a v) p = ptsto8 _ a v.
  reflexivity.
Qed.

Theorem substH_ptsto32 : forall sos a v p,
  substH (ptsto32 sos a v) p = ptsto32 _ a v.
  reflexivity.
Qed.

Theorem substH_star : forall sos (p1 p2 : hpropB sos) p3,
  substH (starB p1 p2) p3 = starB (substH p1 p3) (substH p2 p3).
  reflexivity.
Qed.

Theorem substH_ex : forall sos A (p1 : A -> hpropB sos) p2,
  substH (exB p1) p2 = exB (fun x => substH (p1 x) p2).
  reflexivity.
Qed.

Theorem substH_hvar : forall sos (x : settings * smem -> propX W (settings * state) sos) p,
  substH (hvarB x) p = hvarB (fun m => subst (x m) p).
  reflexivity.
Qed.

Definition HProp_extensional (p : HProp) :=
  p = fun st sm => p st sm.

Hint Extern 1 (HProp_extensional _ ) => reflexivity.

Theorem substH_lift1 : forall p' t p,
  HProp_extensional p'
  -> substH (lift (t :: nil) p') p = p'.
  intros; rewrite H; reflexivity.
Qed.

Theorem substH_lift2 : forall p' t1 t2 p,
  substH (lift (t1 :: t2 :: nil) p') p = lift (t1 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift3 : forall p' t1 t2 t3 p,
  substH (lift (t1 :: t2 :: t3 :: nil) p') p = lift (t1 :: t2 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift4 : forall p' t1 t2 t3 t4 p,
  substH (lift (t1 :: t2 :: t3 :: t4 :: nil) p') p = lift (t1 :: t2 :: t3 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift5 : forall p' t1 t2 t3 t4 t5 p,
  substH (lift (t1 :: t2 :: t3 :: t4 :: t5 :: nil) p') p = lift (t1 :: t2 :: t3 :: t4 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift6 : forall p' t1 t2 t3 t4 t5 t6 p,
  substH (lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: nil) p') p = lift (t1 :: t2 :: t3 :: t4 :: t5 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift7 : forall p' t1 t2 t3 t4 t5 t6 t7 p,
  substH (lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: nil) p') p = lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift8 : forall p' t1 t2 t3 t4 t5 t6 t7 t8 p,
  substH (lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: t8 :: nil) p') p = lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift9 : forall p' t1 t2 t3 t4 t5 t6 t7 t8 t9 p,
  substH (lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: t8 :: t9 :: nil) p') p = lift (t1 :: t2 :: t3 :: t4 :: t5 :: t6 :: t7 :: t8 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift1_eatLast : forall T U P p,
  HProp_extensional P ->
  substH (sos := eatLast (T :: U :: nil)) (^[P])%Sep p = P.
Proof.
  intros. simpl eatLast. rewrite substH_lift1; auto.
Qed.

Theorem star_eta1 : forall sos (p1 p2 : hpropB sos),
  starB (fun st m => p1 st m) p2 = starB p1 p2.
  reflexivity.
Qed.

Theorem star_eta2 : forall sos (p1 p2 : hpropB sos),
  starB p1 (fun st m => p2 st m) = starB p1 p2.
  reflexivity.
Qed.


Hint Rewrite substH_inj substH_injX substH_ptsto8 substH_ptsto32 substH_star substH_ex substH_hvar
  substH_lift1 substH_lift2 substH_lift3 substH_lift4 substH_lift5 substH_lift6 substH_lift7 substH_lift8 substH_lift9
  substH_lift1_eatLast star_eta1 star_eta2
  using solve [ auto ] : sepFormula.

Global Opaque lift.

Notation "![ p ]" := (sepFormula p%Sep) : PropX_scope.

Definition natToByte (n : nat) : B := natToWord _ n.

Coercion natToByte : nat >-> B.

(* *)
Require Bedrock.SepExpr Bedrock.SepHeap.
Module SEP := SepExpr.Make ST.
Module SH := SepHeap.Make SEP.

Theorem natToW_plus : forall n m, natToW (n + m) = natToW n ^+ natToW m.
  apply natToWord_plus.
Qed.

Lemma natToW_S : forall n, natToW (S n) = $1 ^+ natToW n.
  apply natToWord_S.
Qed.

Hint Rewrite <- natToW_plus : sepFormula.

Lemma natToW_minus : forall n m, (m <= n)%nat
  -> natToW (n - m) = natToW n ^- natToW m.
  intros; apply wplus_cancel with (natToW m).
  rewrite <- natToWord_plus.
  replace (n - m + m) with n by omega.
  unfold natToW.
  W_eq.
Qed.

Lemma natToW_times4 : forall n, natToW (n * 4) = natToW n ^* natToW 4.
  intros.
  replace (natToW n ^* natToW 4) with (natToW n ^+ (natToW n ^+ (natToW n ^+ (natToW n ^+ natToW 0)))).
  autorewrite with sepFormula.
  intros; rewrite mult_comm; simpl.
  reflexivity.
  W_eq.
Qed.

Lemma Himp_trans : forall p q r,
  p ===> q
  -> q ===> r
  -> p ===> r.
  unfold Himp, himp; eauto using Imply_trans.
Qed.

Lemma himp_star_frame_comm :
  forall (pcType stateType : Type) (cs : codeSpec pcType stateType)
    (P Q R S : hprop pcType stateType nil),
    himp cs P Q -> himp cs R S -> himp cs (star P R) (star S Q).
  intros; eapply Trans_himp; [ | apply himp_star_comm ].
  apply himp_star_frame; auto.
Qed.


(** * [goodSize] *)

Hint Extern 1 (goodSize _) => reflexivity.

Lemma goodSize_plus_l : forall n m sz, (N.of_nat (n + m) < sz)%N -> (N.of_nat n < sz)%N.
  unfold goodSize; intros; nomega.
Qed.
