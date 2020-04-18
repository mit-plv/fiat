Require Import Bedrock.Bedrock Bedrock.Platform.PreAutoSep.


(** * Separation logic specifications for system calls *)

Definition abortS := SPEC reserving 0
  PREonly[_] Emp.

Definition printIntS := SPEC("n") reserving 0
  PRE[_] Emp
  POST[_] Emp.

Definition listenS := SPEC("port") reserving 0
  PRE[_] Emp
  POST[stream] Emp.

Definition acceptS := SPEC("stream") reserving 0
  PRE[_] Emp
  POST[stream'] Emp.

Definition buffer (p : W) (size : nat) : HProp :=
  (Ex bs, array8 bs p * [| length bs = size |])%Sep.

Infix "=?>8" := buffer (at level 39) : Sep_scope.
Notation "buf =?>8 size" := (Body (buf =?>8 size)%Sep) : qspec_scope.

Definition connectS := SPEC("address", "size") reserving 0
  PRE[V] V "address" =?>8 wordToNat (V "size")
  POST[bytesRead] V "address" =?>8 wordToNat (V "size").

Definition readS := SPEC("stream", "buffer", "size") reserving 0
  PRE[V] V "buffer" =?>8 wordToNat (V "size")
  POST[bytesRead] V "buffer" =?>8 wordToNat (V "size").

Definition writeS := SPEC("stream", "buffer", "size") reserving 0
  PRE[V] V "buffer" =?>8 wordToNat (V "size")
  POST[bytesWritten] V "buffer" =?>8 wordToNat (V "size").

(* Limited version of epoll_ctl *)
Definition declareS := SPEC("stream", "mode") reserving 0
  PRE[_] Emp
  POST[index] Emp.
(* Mode is either 0 for read or 1 for write. *)

(* Limited version of epoll_wait *)
Definition waitS := SPEC("blocking") reserving 0
  PRE[_] Emp
  POST[index] Emp.

Definition closeS := SPEC("stream") reserving 0
  PRE[_] Emp
  POST[_] Emp.


(** * More primitive operational semantics *)

Definition mapped (base : W) (len : nat) (m : mem) :=
  forall n, (n < len)%nat -> m (base ^+ $ (n)) <> None.

Record onlyChange (base : W) (len : nat) (m m' : mem) : Prop :=
  { Elsewhere : forall p, (forall n, (n < len)%nat -> p <> base ^+ $ (n))
    -> m' p = m p;
    SameMapped : forall p, m p = None <-> m' p = None }.

Hint Constructors onlyChange.

Section OpSem.
  Variable stn : settings.
  Variable prog : program.

  Inductive sys_step : state' -> state' -> Prop :=
  | Normal : forall st st', step stn prog st = Some st'
    -> sys_step st st'
  | Abort : forall st, Labels stn ("sys", Global "abort") = Some (fst st)
    -> sys_step st st
  | PrintInt : forall st st',
    Labels stn ("sys", Global "printInt") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 8 (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> Mem st' = Mem (snd st)
    -> sys_step st (Regs (snd st) Rp, st')
  | Listen : forall st st', Labels stn ("sys", Global "listen") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 8 (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> Mem st' = Mem (snd st)
    -> sys_step st (Regs (snd st) Rp, st')
  | Accept : forall st st',
    Labels stn ("sys", Global "accept") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 8 (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> Mem st' = Mem (snd st)
    -> sys_step st (Regs (snd st) Rp, st')
  | Connect : forall st address size st',
    Labels stn ("sys", Global "connect") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 12 (Mem (snd st))
    -> ReadWord stn (Mem (snd st)) (Regs (snd st) Sp ^+ $4) = Some address
    -> ReadWord stn (Mem (snd st)) (Regs (snd st) Sp ^+ $8) = Some size
    -> mapped address (wordToNat size) (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> onlyChange address (wordToNat size) (Mem (snd st)) (Mem st')
    -> sys_step st (Regs (snd st) Rp, st')
  | Read : forall st buffer size st',
    Labels stn ("sys", Global "read") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 16 (Mem (snd st))
    -> ReadWord stn (Mem (snd st)) (Regs (snd st) Sp ^+ $8) = Some buffer
    -> ReadWord stn (Mem (snd st)) (Regs (snd st) Sp ^+ $12) = Some size
    -> mapped buffer (wordToNat size) (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> onlyChange buffer (wordToNat size) (Mem (snd st)) (Mem st')
    -> sys_step st (Regs (snd st) Rp, st')
  | Write : forall st buffer size st',
    Labels stn ("sys", Global "write") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 16 (Mem (snd st))
    -> ReadWord stn (Mem (snd st)) (Regs (snd st) Sp ^+ $8) = Some buffer
    -> ReadWord stn (Mem (snd st)) (Regs (snd st) Sp ^+ $12) = Some size
    -> mapped buffer (wordToNat size) (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> Mem st' = Mem (snd st)
    -> sys_step st (Regs (snd st) Rp, st')
  | Declare : forall st st',
    Labels stn ("sys", Global "declare") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 12 (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> Mem st' = Mem (snd st)
    -> sys_step st (Regs (snd st) Rp, st')
  | Wait : forall st st',
    Labels stn ("sys", Global "wait") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 8 (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> Mem st' = Mem (snd st)
    -> sys_step st (Regs (snd st) Rp, st')
  | Close : forall st st',
    Labels stn ("sys", Global "close") = Some (fst st)
    -> mapped (Regs (snd st) Sp) 8 (Mem (snd st))
    -> Regs st' Sp = Regs (snd st) Sp
    -> Mem st' = Mem (snd st)
    -> sys_step st (Regs (snd st) Rp, st').

  Inductive sys_reachable : state' -> state' -> Prop :=
  | SR0 : forall st, sys_reachable st st
  | SR1 : forall st st' st'', sys_step st st'
    -> sys_reachable st' st''
    -> sys_reachable st st''.

  Definition sys_safe (st : state') :=
    forall st', sys_reachable st st' -> exists st'', sys_step st' st''.
End OpSem.
