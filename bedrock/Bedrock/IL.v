Require Import Coq.omega.Omega.
(** Definition of a simple intermediate language *)

Require Import Coq.Arith.Arith Coq.Arith.Div2 Coq.Lists.List Coq.NArith.NArith.
Require Export Bedrock.Labels.

Require Import Bedrock.Nomega Bedrock.Word Bedrock.Memory.

(** * Setting up hidden word constants *)

Fixpoint natToWord' (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord' sz' (div2 n))
  end.

Definition natToW (n : nat) : W := natToWord _ n.

Definition isConstNat (n : nat) := True.

Theorem natToWord_expose : forall n w, isConstNat w -> natToWord n w = natToWord' n w.
  reflexivity.
Qed.

Theorem natToW_expose : forall n, isConstNat n -> natToW n = natToWord' _ n.
  reflexivity.
Qed.

Ltac isConstNat :=
  let rec f n :=
    match n with
      | O => idtac
      | S ?n' => f n'
    end in
    match goal with
      [ |- isConstNat ?n ] => f n; constructor
    end.


(** * Ensuring that natural number sizes are representable in words *)

Definition goodSize (n : nat) := (N_of_nat n < Npow2 32)%N.

Theorem goodSize_danger : forall n, goodSize n
  -> (n < pow2 32)%nat (* Don't evaluate this! :-) *).
  unfold goodSize; intros.
  apply Nlt_out in H.
  rewrite Nat2N.id in H.
  rewrite Npow2_nat in H.
  assumption.
Qed.

Theorem natToW_inj : forall n m, natToW n = natToW m
  -> goodSize n
  -> goodSize m
  -> n = m.
  intros; eapply natToWord_inj; eauto; apply goodSize_danger; auto.
Qed.


(** * Syntax *)

(* Machine registers
 * There aren't many, since we'll use stack-allocated variables in most cases.
 * This is one of many decisions to trade off constant-factor performance for formalism simplicity in this early work. *)
Inductive reg :=
| Sp (* Stack pointer *)
| Rp (* Return pointer *)
| Rv (* Return value *).

(* Basic assignable locations *)
Inductive loc :=
| Reg : reg -> loc
| Imm : W -> loc
| Indir : reg -> W -> loc.

Coercion Reg : reg >-> loc.
Coercion Imm : W >-> loc.

(* Valid targets of assignments *)
Inductive lvalue :=
| LvReg : reg -> lvalue
| LvMem : loc -> lvalue  (* 32-bit read/write *)
| LvMem8 : loc -> lvalue (* 8-bit read/write *) .

Coercion LvReg : reg >-> lvalue.

(* Operands *)
Inductive rvalue :=
| RvLval : lvalue -> rvalue
| RvImm : W -> rvalue
| RvLabel : label -> rvalue.

Coercion RvLval : lvalue >-> rvalue.
Coercion RvImm : W >-> rvalue.
Coercion RvLabel : label >-> rvalue.

(* Binary operations *)
Inductive binop := Plus | Minus | Times.

(* Non-control-flow instructions *)
Inductive instr :=
| Assign : lvalue -> rvalue -> instr
| Binop : lvalue -> rvalue -> binop -> rvalue -> instr.

(* Binary relational operators *)
Inductive test := Eq | Ne | Lt | Le.

(* Jumps *)
Inductive jmp :=
| Uncond : rvalue -> jmp
| Cond : rvalue -> test -> rvalue -> label -> label -> jmp.

(* Basic blocks *)
Definition block := prod (list instr) jmp.


(** Semantics *)

(* Register banks *)
Notation regs := (reg -> W).

Definition reg_eq : forall x y : reg, {x = y} + {x <> y}.
  decide equality.
Defined.

Definition rupd (rs : regs) (r : reg) (v : W) : regs := fun r' =>
  if reg_eq r' r then v else rs r'.

Theorem rupd_eq : forall rs r v, rupd rs r v r = v.
  intros; unfold rupd; destruct (reg_eq r r); tauto.
Qed.

Theorem rupd_ne : forall rs r v r', r' <> r -> rupd rs r v r' = rs r'.
  intros; unfold rupd; destruct (reg_eq r' r); tauto.
Qed.

Hint Rewrite rupd_eq rupd_ne using congruence : IL.

(* Memories *)
Definition mem := W -> option B.

Open Scope word_scope.

Notation "$ n" := (natToWord _ n) (at level 0) : word_scope.

Definition separated (a1 a2 : W) :=
  forall n m, (n < 4)%nat -> (m < 4)%nat
    -> (a1 ^+ $ n) <> (a2 ^+ $ m).

Definition separatedB (a1 a2 : W) :=
  forall n, (n < 4)%nat
    -> a1 <> (a2 ^+ $ n).

(** * A useful principle for separated *)

Ltac wprepare := repeat match goal with
                          | [ |- context[natToWord ?n ?m] ] => rewrite (natToWord_expose n m) by isConstNat
                          | [ |- context[natToW ?n] ] => rewrite (natToW_expose n) by isConstNat
                        end; unfold W in *.

Definition wring32 := wring 32.
Add Ring wring32 : wring32 (decidable (weqb_sound 32), constants [wcst]).

Definition Wring : @ring_theory W _ _ _ _ _ _ _ := wring 32.
Add Ring Wring : Wring (decidable (weqb_sound 32), constants [wcst]).

Lemma cancel : forall u v k : W,
  u ^+ k = v ^+ k
  -> u = v.
  intros.
  apply (f_equal (fun x => x ^+ ^~ k)) in H.
  replace (u ^+ k ^+ ^~ k) with u in H by (wprepare; word_eq).
  replace (v ^+ k ^+ ^~ k) with v in H by (wprepare; word_eq).
  auto.
Qed.

Hint Immediate cancel.

Lemma cancel_contra : forall u v k : W,
  u <> v
  -> u ^+ k <> v ^+ k.
  generalize cancel; firstorder.
Qed.

Hint Immediate cancel_contra.

Lemma natToWordToN : forall n m, (N_of_nat m < Npow2 n)%N
  -> wordToN (natToWord n m) = N_of_nat m.
  intros.
  rewrite wordToN_nat.
  destruct (wordToNat_natToWord n m); intuition.
  rewrite H1; clear H1.
  destruct x.
  nomega.
  elimtype False.
  simpl in *.
  generalize dependent (x * pow2 n).
  rewrite <- Npow2_nat in *.
  intros.
  nomega.
Qed.

Lemma cancel_contra_minus : forall k1 k2 (u v : W),
  u ^+ $ k1 = v ^+ $ k2
  -> (k1 < k2)%nat
  -> (N_of_nat k2 < Npow2 32)%N
  -> u = v ^+ $ (k2 - k1).
  intros.
  apply cancel with ($ k1).
  rewrite H; clear H.
  rewrite <- wplus_assoc.
  f_equal.
  unfold wplus, wordBin.
  repeat rewrite natToWordToN.
  rewrite <- N_of_plus.
  replace (k2 - k1 + k1) with k2 by omega.
  rewrite NToWord_nat.
  autorewrite with N; reflexivity.
  auto.
  generalize dependent (Npow2 32).
  intros.
  nomega.
  generalize dependent (Npow2 32).
  intros.
  nomega.
Qed.

Lemma cancel_contra_minus' : forall k1 k2 (u v : W),
  u <> v ^+ $ (k2 - k1)%nat
  -> (k1 < k2)%nat
  -> (N_of_nat k2 < Npow2 32)%N
  -> u ^+ $ k1 <> v ^+ $ k2.
  intros; intro.
  apply H.
  eapply cancel_contra_minus; eauto.
Qed.

Lemma cancel_contra_minus'' : forall k1 k2 (u v : W),
  v ^+ $ (k2 - k1)%nat <> u
  -> (k1 < k2)%nat
  -> (N_of_nat k2 < Npow2 32)%N
  -> v ^+ $ k2 <> u ^+ $ k1.
  intros; intro.
  apply H.
  symmetry.
  eapply cancel_contra_minus; eauto.
Qed.

Local Hint Extern 1 (_ <> _) => apply cancel_contra_minus'; [ assumption | omega | reflexivity ].
Local Hint Extern 1 (_ <> _) => apply cancel_contra_minus''; [ assumption | omega | reflexivity ].

Theorem const_separated : forall u v,
  u <> v
  -> u <> v ^+ $ 1
  -> u <> v ^+ $ 2
  -> u <> v ^+ $ 3
  -> u ^+ $ 1 <> v
  -> u ^+ $ 2 <> v
  -> u ^+ $ 3 <> v
  -> separated u v.
  red; intros.
  repeat match goal with
           | [ H : (_ < _)%nat |- _ ] => inversion H; clear H; subst
           | [ H : (_ <= _)%nat |- _ ] => inversion H; clear H; subst
         end; auto.
Qed.


(** * Settings *)

(* Execution is parametric in settings that distinguish different platforms.
 * Programs will generally be verified to work in all platforms. *)
Record settings := {
  (* gmm: we can push this into the heap model since it already has
   *      the functionality footprint_w
   *)
  implode : B * B * B * B -> W ;
  explode : W -> B * B * B * B ;
  (* conversion for reading words *)

  implode_explode : forall w,
    implode (explode w) = w ;
  explode_implode : forall b,
    explode (implode b) = b ;

  Labels : label -> option W
  (* Locations of basic blocks *)
}.

Definition ReadByte (m : mem) (a : W) : option B :=
  m a.

Definition footprint_w (a : W) := (a, a ^+ $1, a ^+ $2, a ^+ $3).

Definition ReadWord (s : settings) (m : mem) (a : W) : option W :=
  mem_get_word W mem footprint_w ReadByte (implode s) a m.

Definition WriteByte (m : mem) (p : W) (v : B) : option mem :=
  match m p with
    | None => None
    | Some _ => Some (fun p' => if weq p' p then Some v else m p')
  end.

Definition WriteWord (s : settings) (m : mem) (p v : W) : option mem :=
  mem_set_word W mem footprint_w WriteByte (explode s) p v m.

Ltac W_eq := wprepare; word_eq.
Ltac W_neq := (apply const_separated; word_neq) || (wprepare; word_neq).

Theorem ReadWriteEq : forall stn m m' k v,
  WriteWord stn m k v = Some m' ->
  ReadWord stn m' k = Some v.
Proof.
  unfold ReadWord, WriteWord, mem_get_word, mem_set_word, footprint_w, ReadByte, WriteByte. intros stn m m' k v.
  case_eq (explode stn v). destruct p. destruct p. intros.
  repeat match goal with
           | [ H : match match ?X with
                           | Some _ => _
                           | None => _
                         end
                     with
                     | Some _ => _
                     | None => _
                   end = _ |- _ ] =>
             generalize dependent H; case_eq X; try congruence; intros
         end.
  generalize dependent H3.
  case_eq ((if weq k (k ^+ $ (1))
      then Some b1
      else
       if weq k (k ^+ $ (2))
       then Some b
       else if weq k (k ^+ $ (3)) then Some b2 else m k)); try congruence.
  intros.
  Opaque natToWord.
  inversion H4; clear H4.
  generalize dependent H1; generalize dependent H6; generalize dependent H3; generalize dependent H2.

  repeat rewrite (rewrite_weq (refl_equal _)) in *.
  repeat match goal with
           | [ |- context [ weq ?X ?Y ] ] =>
             let Z := fresh in destruct (weq X Y) as [ Z | ? ]; [ exfalso; generalize Z; W_neq | ]
         end.
  intros. rewrite <- H. rewrite implode_explode. reflexivity.
Qed.

Theorem ReadWriteNe : forall stn m m' k v k',
  separated k' k ->
  WriteWord stn m k v = Some m' ->
  ReadWord stn m' k' = ReadWord stn m k'.
Proof.
  unfold ReadWord, WriteWord, mem_get_word, mem_set_word, footprint_w, ReadByte, WriteByte; intros.
  revert H0.
  case_eq (explode stn v); intros. destruct p. destruct p.
  assert (k' = k' ^+ $0). W_eq.
  assert (k = k ^+ $0). W_eq.
  repeat match goal with
           | [ H : match match ?X with
                           | Some _ => _
                           | None => _
                         end
                     with
                     | Some _ => _
                     | None => _
                   end = _ |- _ ] =>
             generalize dependent H; case_eq X; try congruence; intros
         end.
  generalize dependent H6.
  case_eq ((if weq k (k ^+ $ (1))
      then Some b2
      else
       if weq k (k ^+ $ (2))
       then Some b0
       else if weq k (k ^+ $ (3)) then Some b else m k)); try congruence.
  intro. intros. inversion H7; clear H7.
  revert H4; revert H5; revert H1; revert H9.
  repeat match goal with
    | [ |- context [ weq ?X ?Y ] ] =>
      let Z := fresh in destruct (weq X Y) as [ Z | ? ];
        [ exfalso ; (apply H in Z || (rewrite H2 in Z; apply H in Z) || (rewrite H3 in Z; apply H in Z) || (rewrite H2 in Z; rewrite H3 in Z; apply H in Z)); auto; omega |  ]
  end.
  reflexivity.
Qed.

(* Machine states *)
Record state := {
  Regs : regs;
  Mem : mem
}.

Definition WtoB : W -> B := split1 8 24.
Definition BtoW (b : B) : W := combine b (wzero 24).

Section settings.
  Variable stn : settings.

  Section state.
    Variable st : state.

    Definition evalLoc (l : loc) : W :=
      match l with
        | Reg r => Regs st r
        | Imm w => w
        | Indir r w => let a := Regs st r ^+ w in a
      end.

    Definition evalLvalue (lv : lvalue) (v : W) : option state :=
      match lv with
        | LvReg r => Some {| Regs := rupd (Regs st) r v;
          Mem := Mem st |}
        | LvMem l =>
          let a := evalLoc l in
          match WriteWord stn (Mem st) a v with
            | None => None
            | Some m' => Some {| Regs := Regs st ; Mem := m' |}
          end
        | LvMem8 l =>
          let a := evalLoc l in
          match WriteByte (Mem st) a (WtoB v) with
            | None => None
            | Some m' => Some {| Regs := Regs st ; Mem := m' |}
          end
      end.

    Definition evalRvalue (rv : rvalue) : option W :=
      match rv with
        | LvReg r => Some (Regs st r)
        | LvMem l =>
          let a := evalLoc l in
          ReadWord stn (Mem st) a
        | LvMem8 l =>
          let a := evalLoc l in
          match ReadByte (Mem st) a with
            | None => None
            | Some b => Some (BtoW b)
          end
        | RvImm w => Some w
        | RvLabel l => Labels stn l
      end.

    Definition evalBinop (bo : binop) : W -> W -> W :=
      match bo with
        | Plus => @wplus _
        | Minus => @wminus _
        | Times => @wmult _
      end.

    Definition evalInstr (i : instr) : option state :=
      match i with
        | Assign lv rv => match evalRvalue rv with
                            | None => None
                            | Some w => evalLvalue lv w
                          end
        | Binop lv rv1 bo rv2 => match evalRvalue rv1, evalRvalue rv2 with
                                   | Some w1, Some w2 => evalLvalue lv (evalBinop bo w1 w2)
                                   | _, _ => None
                                 end
      end.

    Definition wltb (w1 w2 : W) : bool :=
      if wlt_dec w1 w2 then true else false.
    Definition weqb (w1 w2 : W) : bool := Word.weqb w1 w2.
    Definition wneb (w1 w2 : W) : bool :=
      if weq w1 w2 then false else true.
    Definition wleb (w1 w2 : W) : bool :=
      if weq w1 w2 then true else if wlt_dec w1 w2 then true else false.

    Definition evalTest (ts : test) : W -> W -> bool :=
      match ts with
        | Lt => wltb
        | Eq => weqb
        | Ne => wneb
        | Le => wleb
      end.

    Definition evalJmp (j : jmp) : option W :=
      match j with
        | Uncond rv => evalRvalue rv
        | Cond rv1 ts rv2 l1 l2 =>
          match evalRvalue rv1, evalRvalue rv2 with
            | Some w1, Some w2 => Labels stn (if evalTest ts w1 w2 then l1 else l2)
            | _, _ => None
          end
      end.
  End state.

  Fixpoint evalInstrs (st : state) (is : list instr) : option state :=
    match is with
      | nil => Some st
      | i :: is' => match evalInstr st i with
                      | None => None
                      | Some st' => evalInstrs st' is'
                    end
    end.

  (* States with program counters *)
  Definition state' := prod W state.

  Definition evalBlock (st : state) (b : block) : option state' :=
    let (is, j) := b in
      match evalInstrs st is with
        | None => None
        | Some st' => match evalJmp st' j with
                        | None => None
                        | Some w => Some (w, st')
                      end
      end.

  (* Program code *)
  Definition program := W -> option block.

  Variable prog : program.

  Definition step (st : state') : option state' :=
    match prog (fst st) with
      | None => None
      | Some b => evalBlock (snd st) b
    end.

  (* To define safety, we characterize reachability of states. *)
  Inductive reachable : state' -> state' -> Prop :=
  | Reachable0 : forall st, reachable st st
  | Reachable1 : forall st st' st'', step st = Some st'
    -> reachable st' st''
    -> reachable st st''.

  (* A state is safe if execution runs forever from it.*)
  Definition safe (st : state') := forall st', reachable st st'
    -> step st' <> None.
End settings.

(*
Export Memory.
*)
