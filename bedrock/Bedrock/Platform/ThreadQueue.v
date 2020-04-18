Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith Bedrock.Platform.AutoSep Bedrock.Platform.Bags Bedrock.Platform.Malloc Bedrock.Platform.Queue Bedrock.Platform.Misc.
Import W_W_Bag.

Set Implicit Arguments.


Record tq_args (world : Type) := {
  World : world;
  Pointer : W;
  Settings : settings;
  Mem : smem
}.

Module Type S.
  Parameter world : Type.

  Parameter evolve : world -> world -> Prop.
  Axiom evolve_refl : forall w, evolve w w.
  Axiom evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.

  Parameter globalInv : world -> W -> hpropB (tq_args world :: nil).
End S.

Definition localsInvariantExit (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (_ : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    [| sp <> 0 |]
    /\ Ex vs, let res := wordToNat (sel vs "ss") - S (length ns) in
      [| freeable sp (wordToNat (sel vs "ss")) |]
      /\ qspecOut (pre (sel vs) st#Rv) (fun pre =>
        ![ locals ("rp" :: ns) vs res sp * pre ] st).

Notation "'PREexit' [ vs ] pre" := (localsInvariantExit (fun vs _ => pre%qspec%Sep))
  (at level 89).

Notation "'PREexit' [ vs , rv ] pre" := (localsInvariantExit (fun vs rv => pre%qspec%Sep))
  (at level 89).

Module Make(M : S).
Import M.

(* What does it mean for a program counter to be valid for a suspended thread? *)

Definition susp (w : world) (sc pc sp : W) : HProp := fun s m =>
  (Ex pc_tq : W, [| s.(Labels) ("threadq"!"ADT")%SP = Some pc_tq |]
    /\ ExX (* tq *) : tq_args world, Cptr pc_tq (_ ~> PropX.Forall #0)
    /\ ExX (* pre *) : settings * state, Cptr pc #0
    /\ ExX (* inv *) : settings * smem, #0 (s, m)
    /\ Al st : state, Al w' : world,
    [| evolve w w' |]
    /\ ![ #0 * (fun x y => Lift (Lift (Var0 {| World := w';
                                               Pointer := sc;
                                               Settings := x;
                                               Mem := y |})))
      * (fun x y => Lift (Lift (globalInv w' sc x y)))
      * ^[mallocHeap 0] ] (s, st)
    /\ [| Regs st Sp = sp |]
    ---> #1 (s, st))%PropX.

Lemma susp_intro : forall specs w sc pc sp P stn st,
  (exists pc_tq, stn.(Labels) ("threadq"!"ADT")%SP = Some pc_tq
    /\ exists tq, specs pc_tq = Some (fun _ => PropX.Forall tq)
      /\ exists pre, specs pc = Some (fun x => pre x)
        /\ exists inv, interp specs (![ inv * P ] (stn, st))
          /\ forall st' w', interp specs ([| evolve w w' |]
            /\ ![ inv
              * (fun x y => tq {| World := w';
                                  Pointer := sc;
                                  Settings := x;
                                  Mem := y |})
              * substH (globalInv w' sc) tq * mallocHeap 0 ] (stn, st')
            /\ [| Regs st' Sp = sp |]
            ---> pre (stn, st'))%PropX)
  -> interp specs (![ susp w sc pc sp * P ] (stn, st)).
  cptr.
Qed.

Lemma susp_elim : forall specs w sc pc sp P stn st,
  interp specs (![ susp w sc pc sp * P ] (stn, st))
  -> (exists pc_tq, stn.(Labels) ("threadq"!"ADT")%SP = Some pc_tq
    /\ exists tq, specs pc_tq = Some (fun _ => PropX.Forall tq)
      /\ exists pre, specs pc = Some (fun x => pre x)
        /\ exists inv, interp specs (![ inv * P ] (stn, st))
          /\ forall st' w', interp specs ([| evolve w w' |]
            /\ ![ inv * (fun x y => tq {| World := w';
                                          Pointer := sc;
                                          Settings := x;
                                          Mem := y |}) * substH (globalInv w' sc) tq * mallocHeap 0 ] (stn, st')
            /\ [| Regs st' Sp = sp |]
            ---> pre (stn, st'))%PropX).
  cptr.
  propxFo; eauto.
  descend; eauto.
  rewrite <- sepFormula_eq; descend.
  step auto_ext.
  eauto.
  make_Himp.
  apply Himp_refl.
Qed.


Inductive mergeSusp : Prop := MS.
Inductive splitSusp : Prop := SS.

Hint Constructors mergeSusp splitSusp.

Module Type TQ.
  Parameter susps : world -> bag -> W -> HProp.
  Parameter tq : world -> W -> HProp.

  Axiom tq_extensional : forall w sc, HProp_extensional (tq w sc).

  Axiom susps_empty_bwd : forall w sc, Emp ===> susps w empty sc.
  Axiom susps_add_bwd : forall w sc b pc sp, pc = pc -> mergeSusp -> susp w sc pc sp * susps w b sc ===> susps w (b %+ (pc, sp)) sc.
  Axiom susps_del_fwd : forall w sc b pc sp, (pc, sp) %in b -> susps w b sc ===> susp w sc pc sp * susps w (b %- (pc, sp)) sc.

  (* Below, the extra [locals] is a temporary stack for the threadq to use during sensitive
   * stack manipulations when the threads' own stacks may not be safe to touch. *)

  Axiom tq_fwd : forall w sc, tq w sc ===> Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps w b sc.

  Axiom tq_bwd : forall w sc, (Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps w b sc) ===> tq w sc.


  Axiom tq_weaken : forall w w' sc,
    evolve w w'
    -> tq w sc ===>* tq w' sc.
End TQ.

Module Tq : TQ.
  Open Scope Sep_scope.

  Definition susps (w : world) (b : bag) (sc : W) : HProp :=
    starB (fun p => susp w sc (fst p) (snd p)) b.

  Theorem susps_empty_bwd : forall w sc, Emp ===> susps w empty sc.
    intros; apply starB_empty_bwd.
  Qed.

  Theorem susps_add_bwd : forall w sc b pc sp, pc = pc -> mergeSusp -> susp w sc pc sp * susps w b sc ===> susps w (b %+ (pc, sp)) sc.
    intros; eapply Himp_trans; [ | apply starB_add_bwd ].
    unfold susps; simpl.
    apply Himp_star_comm.
  Qed.

  Theorem susps_del_fwd : forall w sc b pc sp, (pc, sp) %in b -> susps w b sc ===> susp w sc pc sp * susps w (b %- (pc, sp)) sc.
    intros; eapply Himp_trans; [ apply starB_del_fwd; eauto | apply Himp_refl ].
  Qed.

  Definition tq (w : world) (sc : W) : HProp :=
    Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
      * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
      * queue b p * susps w b sc.

  Theorem tq_extensional : forall w sc, HProp_extensional (tq w sc).
    reflexivity.
  Qed.

  Theorem tq_fwd : forall w sc, tq w sc ===> Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps w b sc.
    unfold tq; sepLemma.
  Qed.

  Theorem tq_bwd : forall w sc, (Ex b, Ex p, Ex sp, Ex vs, (sc ==*> p, sp) * (sc ^+ $8) =?> 2
    * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
    * queue b p * susps w b sc) ===> tq w sc.
    unfold tq; sepLemma.
  Qed.

  Theorem into_ex : forall A (P P' : A -> _),
    (forall x, P x ===>* P' x)
    -> exB P ===>* exB P'.
    unfold HimpWeak; propxFo.
    apply H in H0; eauto.
  Qed.

  Theorem into_star : forall P P' Q Q',
    P ===>* P'
    -> Q ===>* Q'
    -> P * Q ===>* P' * Q'.
    unfold HimpWeak; propxFo.
    apply H in H1; apply H0 in H4; eauto.
  Qed.

  Theorem weak_refl : forall P,
    P ===>* P.
    unfold HimpWeak; auto.
  Qed.

  Theorem tq_weaken : forall w w' sc,
    evolve w w'
    -> tq w sc ===>* tq w' sc.
    unfold tq; intros; repeat match goal with
                                | [ |- exB _ ===>* exB _ ] => apply into_ex; intro
                                | [ |- (_ * _ ===>* _ * _)%Sep ] => apply into_star; try apply weak_refl
                              end.
    apply starB_weaken_weak; intros.
    unfold HimpWeak; propxFo; descend; eauto.
    eapply Imply_trans; [ | apply H5 ]; clear H5.
    descend.
    apply andL; apply injL; intro.
    apply andR; [ apply injR | ].
    eapply evolve_trans; eauto.
    apply Imply_refl.
  Qed.
End Tq.

Import Tq.
Export Tq.
Hint Immediate tq_extensional.

Definition locals_expose ns vs ss sp := locals ns vs ss sp.
Opaque mult.
Require Import Coq.Arith.Arith.
Transparent mult.

Lemma expose_stack : forall ns vs ss sp,
  locals_expose ns vs ss sp ===> sp =?> (length ns + ss).
  unfold locals_expose, locals; intros; eapply Himp_trans; [ | apply allocated_join ].
  instantiate (1 := length ns).
  2: omega.
  Opaque mult.
  sepLemma.
  eapply Himp_trans; [ apply Himp_star_comm | ].
  eapply Himp_star_frame.
  eapply Himp_trans; [ apply ptsto32m_allocated | ].
  rewrite length_toArray; apply Himp_refl.
  apply allocated_shift_base.
  unfold natToW; rewrite mult_comm; words.
  omega.
  Transparent mult.
Qed.

Definition hints : TacPackage.
  prepare (tq_fwd, create_stack, expose_stack) (tq_bwd, susps_empty_bwd, susps_add_bwd).
Defined.

(* What is a valid initial code pointer for a thread, given the requested stack size? *)

Definition ginv w sc := substH (globalInv w sc) (fun x => tq (World x) (Pointer x) (Settings x) (Mem x)).

Definition starting (w : world) (sc pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : state, Al vs, Al w',
      [| evolve w w' |]
      /\ [| Regs st Sp <> 0 /\ freeable (Regs st Sp) (1 + ss) |]
      /\ ![ ^[locals ("rp" :: nil) vs ss (Regs st Sp) * tq w' sc * ginv w' sc * mallocHeap 0] ] (s, st)
      ---> #0 (s, st))%PropX.

Local Hint Resolve split_a_semp_a semp_smem_emp.

Lemma starting_intro : forall specs sc w pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall st' vs w', interp specs ([| evolve w w' |]
      /\ [| Regs st' Sp <> 0 /\ freeable (Regs st' Sp) (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss (Regs st' Sp)
      * tq w' sc * ginv w' sc * mallocHeap 0 ] (stn, st')
    ---> pre (stn, st'))%PropX)
  -> interp specs (![ starting w sc pc ss * P ] (stn, st)).
  cptr.
Qed.

Lemma starting_elim : forall specs w sc pc ss P stn st,
  interp specs (![ starting w sc pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall st' vs w', interp specs ([| evolve w w' |]
      /\ [| Regs st' Sp <> 0 /\ freeable (Regs st' Sp) (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss (Regs st' Sp)
      * tq w' sc * ginv w' sc * mallocHeap 0 ] (stn, st')
    ---> pre (stn, st'))%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  eauto.
  eauto.
  make_Himp.
  apply Himp_refl.
Qed.

Definition susp' (w : world) (sc pc sp : W) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ ExX (* inv *) : settings * smem, #0 (s, m)
    /\ Al st : state, Al w' : world,
    [| evolve w w' |]
    /\ ![ #0 * ^[tq w' sc * ginv w' sc * mallocHeap 0] ] (s, st)
    /\ [| Regs st Sp = sp |]
    ---> #1 (s, st))%PropX.

Lemma susp_convert : forall specs w sc pc sp P stn st pc_tq,
  interp specs (![ susp' w sc pc sp * P ] (stn, st))
  -> Labels stn (labl "threadq" "ADT") = Some pc_tq
  -> specs pc_tq = Some (fun _ => PropX.Forall (fun x => tq (World x) (Pointer x) (Settings x) (Mem x)))
  -> interp specs (![ susp w sc pc sp * P ] (stn, st)).
  cptr.
  descend; step auto_ext.
  eauto.
  step auto_ext.
Qed.

Lemma susp'_intro : forall specs w sc pc sp P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ exists inv, interp specs (![ inv * P ] (stn, st))
      /\ forall st' w', interp specs ([| evolve w w' |]
        /\ ![ inv * tq w' sc * ginv w' sc * mallocHeap 0 ] (stn, st')
        /\ [| Regs st' Sp = sp |]
        ---> pre (stn, st'))%PropX)
  -> interp specs (![ susp' w sc pc sp * P ] (stn, st)).
  cptr.
  descend; step auto_ext.
  eauto.
  descend; step auto_ext.
Qed.

Definition initS : spec := SPEC reserving 12
  Al w,
  PRE[_] mallocHeap 0
  POST[R] tq w R * mallocHeap 0.

Definition isEmptyS : spec := SPEC("sc") reserving 4
  Al w,
  PRE[V] tq w (V "sc") * mallocHeap 0
  POST[_] tq w (V "sc") * mallocHeap 0.

Definition spawnWithStackS : spec := SPEC("sc", "pc", "sp") reserving 14
  Al w,
  PRE[V] tq w (V "sc") * susp' w (V "sc") (V "pc") (V "sp") * mallocHeap 0
  POST[_] tq w (V "sc") * mallocHeap 0.

Definition spawnS : spec := SPEC("sc", "pc", "ss") reserving 18
  Al w,
  PRE[V] [| V "ss" >= $2 |] * tq w (V "sc") * starting w (V "sc") (V "pc") (wordToNat (V "ss") - 1) * mallocHeap 0
  POST[_] tq w (V "sc") * mallocHeap 0.

Definition localsInvariantExit' (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (_ : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    Ex vs, qspecOut (pre (sel vs) st#Rv) (fun pre =>
      ![ locals ("rp" :: ns) vs 14 sp * pre ] st).

Local Notation "'PREexit'' [ vs ] pre" := (localsInvariantExit' (fun vs _ => pre%qspec%Sep))
  (at level 89).

Local Notation "'PREexit'' [ vs , rv ] pre" := (localsInvariantExit' (fun vs rv => pre%qspec%Sep))
  (at level 89).

Definition exitS : spec := SPEC("sc", "ss") reserving 0
  Al w,
  PREexit[V] [| V "ss" >= $3 |] * tq w (V "sc") * ginv w (V "sc") * mallocHeap 0.

Local Notation "'bexit' name ( x1 , .. , xN ) [ p ] b 'end'" :=
  (let p' := p in
   let vars := cons x1 (.. (cons xN nil) ..) in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := b%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Definition yieldS : spec := SPEC("sc") reserving 19
  Al w,
  PRE[V] tq w (V "sc") * ginv w (V "sc") * mallocHeap 0
  POST[_] Ex w', [| evolve w w' |] * tq w' (V "sc") * ginv w' (V "sc") * mallocHeap 0.

(* Next, some hijinks to prevent unnecessary unfolding of distinct memory cells for the threadq's stack. *)

Definition stackSize := 21.

Lemma stackSize_bound : natToW stackSize >= natToW 2.
  unfold stackSize; auto.
Qed.

Hint Immediate stackSize_bound.

Lemma stackSize_split : stackSize = length ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) + 14.
  reflexivity.
Qed.

Opaque stackSize.

Definition yieldInvariantCont (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    Ex vs, qspecOut (pre (sel vs) st#Rv) (fun pre =>
      ![ ^[locals ("rp" :: ns) vs res sp * pre] ] st).

Local Notation "'PREy' [ vs ] pre" := (yieldInvariantCont (fun vs _ => pre%qspec%Sep))
  (at level 89).

Notation "'badt' name p 'end'" :=
  {| FName := name;
    FPrecondition := (fun _ => PropX.Forall p);
    FBody := Diverge;
    FVars := nil;
    FReserved := 0 |}
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
    "queue"!"init" @ [Queue.initS], "queue"!"isEmpty" @ [Queue.isEmptyS],
    "queue"!"enqueue" @ [enqueueS], "queue"!"dequeue" @ [dequeueS] ]]
  bmodule "threadq" {{
    badt "ADT"
      (fun x => tq (World x) (Pointer x) (Settings x) (Mem x))
    end with bfunction "init"("q", "sp", "r") [initS]
      "q" <-- Call "queue"!"init"()
      [PRE[_, R] mallocHeap 0
       POST[R'] Ex sp, Ex vs, (R' ==*> R, sp) * (R' ^+ $8) =?> 2
         * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 sp
         * mallocHeap 0];;

      "sp" <-- Call "malloc"!"malloc"(0, stackSize)
      [PRE[V, R] R =?> stackSize * mallocHeap 0
        POST[R'] Ex vs, (R' ==*> V "q", R) * (R' ^+ $8) =?> 2 * mallocHeap 0
         * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 R];;

      Assert [PRE[V] mallocHeap 0
        POST[R] (R ==*> V "q", V "sp") * (R ^+ $8) =?> 2 * mallocHeap 0];;

      "r" <-- Call "malloc"!"malloc"(0, 4)
      [PRE[V, R] R =?> 4
       POST[R'] [| R' = R |] * (R ==*> V "q", V "sp") * (R ^+ $8) =?> 2 ];;
      "r" *<- "q";;
      "r" + 4 *<- "sp";;
      Return "r"
    end with bfunction "isEmpty"("sc") [isEmptyS]
      "sc" <-* "sc";;
      "sc" <-- Call "queue"!"isEmpty"("sc")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "sc"
    end with bfunction "spawnWithStack"("sc", "pc", "sp") [spawnWithStackS]
      Assert* [("threadq","ADT")] [Al w,
        PRE[V] tq w (V "sc") * susp w (V "sc") (V "pc") (V "sp") * mallocHeap 0
        POST[_] tq w (V "sc") * mallocHeap 0];;

      "sc" <-* "sc";;
      Note [mergeSusp];;
      Call "queue"!"enqueue"("sc", "pc", "sp")
      [Al w, Al b, Al sc,
        PRE[V] susps w (b %+ (V "pc", V "sp")) sc
         POST[_] susps w (b %+ (V "pc", V "sp")) sc];;
      Return 0
    end with bfunction "spawn"("sc", "pc", "ss") [spawnS]
      "ss" <-- Call "malloc"!"malloc"(0, "ss")
      [Al w, Al ss,
        PRE[V, R] tq w (V "sc") * starting w (V "sc") (V "pc") (ss - 1) * mallocHeap 0
          * R =?> ss * [| (ss >= 2)%nat |] * [| R <> 0 |] * [| freeable R ss |]
        POST[_] tq w (V "sc") * mallocHeap 0];;

      Assert [Al w, Al ss, Al vs,
        PRE[V] tq w (V "sc") * starting w (V "sc") (V "pc") ss * mallocHeap 0
          * locals ("rp" :: nil) vs ss (V "ss") * [| V "ss" <> 0 |] * [| freeable (V "ss") (1 + ss) |]
        POST[_] tq w (V "sc") * mallocHeap 0];;

      Assert* [("threadq","ADT")]
      [Al w,
        PRE[V] tq w (V "sc") * susp' w (V "sc") (V "pc") (V "ss") * mallocHeap 0
        POST[_] tq w (V "sc") * mallocHeap 0];;

      Call "threadq"!"spawnWithStack"("sc", "pc", "ss")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end with bexit "exit"("sc", "ss", "curPc", "curSp", "newPc", "newSp") [exitS]
      Rp <-* "sc" + 4;;
      Rp + 4 *<- "sc";;
      Rp + 8 *<- "ss";;
      Rp + 12 *<- Sp;;
      Sp <- Rp;;

      Call "malloc"!"free"(0, "curPc", "ss")
      [Al w, Al q, Al qp, Al tsp,
        PREexit'[V] (V "sc" ==*> qp, tsp) * queue q qp * (V "sc" ^+ $8) =?> 2
          * susps w q (V "sc") * ginv w (V "sc") * mallocHeap 0];;

      "curPc" <-* "sc";;
      "curSp" <-- Call "queue"!"isEmpty"("curPc")
      [Al w, Al q, Al tsp,
        PREexit'[V, R] [| (q %= empty) \is R |]
          * queue q (V "curPc") * (V "sc" ==*> V "curPc", tsp)
          * (V "sc" ^+ $8) =?> 2 * susps w q (V "sc") * ginv w (V "sc") * mallocHeap 0];;

      If ("curSp" = 1) {
        (* No threads left to run.  Let's loop forever! *)
        Diverge
      } else {
        (* Pick a thread to switch to. *)

        "curSp" <- "sc" + 8;;
        Call "queue"!"dequeue"("curPc", "curSp")
        [Al w, Al q, Al tsp, Al pc, Al sp,
          PREexit'[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "curPc")
            * susps w (q %- (pc, sp)) (V "sc") * susp w (V "sc") pc sp
            * (V "sc" ==*> V "curPc", tsp, pc, sp) * ginv w (V "sc") * mallocHeap 0];;

        "sc" + 4 *<- Sp;;
        Rp <-* "sc" + 8;;
        Sp <-* "sc" + 12;;
        IGoto* [("threadq","ADT")] Rp
      }
    end with bfunction "yield"("sc", "ss", "curPc", "curSp", "newPc", "newSp") [yieldS]
      "ss" <-* "sc";;
      (* Using "curPc" as a temporary before getting to its primary use... *)
      "curPc" <-- Call "queue"!"isEmpty"("ss")
      [Al w, Al q, Al tsp, Al vs,
        PRE[V, R] [| (q %= empty) \is R |]
          * queue q (V "ss") * (V "sc" ==*> V "ss", tsp) * (V "sc" ^+ $8) =?> 2 * susps w q (V "sc")
          * ginv w (V "sc") * mallocHeap 0
          * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp
        POST[_] Ex w', [| evolve w w' |] * tq w' (V "sc") * ginv w' (V "sc") * mallocHeap 0];;

      If ("curPc" = 1) {
        (* No other threads to run.  Simply returning to caller acts like a yield. *)
        Rp <- $[Sp+0];;
        IGoto* [("threadq","ADT")] Rp
      } else {
        (* Pick a thread to switch to. *)
        "curPc" <- "sc" + 8;;
        Call "queue"!"dequeue"("ss", "curPc")
        [Al w, Al q, Al tsp, Al vs, Al pc, Al sp,
          PRE[V] [| (pc, sp) %in q |] * queue (q %- (pc, sp)) (V "ss")
            * susps w (q %- (pc, sp)) (V "sc") * susp w (V "sc") pc sp
            * (V "sc" ==*> V "ss", tsp, pc, sp) * ginv w (V "sc") * mallocHeap 0
            * locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil) vs 14 tsp
          POST[_] Ex w', [| evolve w w' |] * tq w' (V "sc") * ginv w' (V "sc") * mallocHeap 0];;
        "newPc" <-* "sc" + 8;;
        "newSp" <-* "sc" + 12;;

        Assert [Al w,
          PRE[V] susp w (V "sc") (V "newPc") (V "newSp") * tq w (V "sc") * ginv w (V "sc") * mallocHeap 0
          POST[_] Ex w', [| evolve w w' |] * tq w' (V "sc") * ginv w' (V "sc") * mallocHeap 0];;

        (* Initialize the temporary stack with data we will need, then switch to using it as our stack. *)
        "curPc" <-* "sc" + 4;;
        "ss" <-* "sc";;
        "curPc" + 4 *<- "sc";;
        "curPc" + 8 *<- "ss";;
        "curPc" + 12 *<- $[Sp+0];;
        "curPc" + 16 *<- Sp;;
        "curPc" + 20 *<- "newPc";;
        "curPc" + 24 *<- "newSp";;
        Sp <- "curPc";;

        Assert* [("threadq","ADT")]
        [PREy[V] Ex w, Ex sp, Ex b, (V "sc" ==*> V "ss", sp) * (V "sc" ^+ $8) =?> 2
          * queue b (V "ss") * susps w b (V "sc") * ginv w (V "sc") * mallocHeap 0
          * susp w (V "sc") (V "newPc") (V "newSp") * susp w (V "sc") (V "curPc") (V "curSp")];;

        Note [mergeSusp];;

        (* Enqueue current thread; note that variable references below resolve in the temporary stack. *)
        Call "queue"!"enqueue"("ss", "curPc", "curSp")
        [PREy[V] Ex w, Ex b, Ex p, Ex sp, (V "sc" ==*> p, sp) * (V "sc" ^+ $8) =?> 2
          * queue b p * susps w b (V "sc") * ginv w (V "sc")
          * mallocHeap 0 * susp w (V "sc") (V "newPc") (V "newSp")];;

        (* Jump to dequeued thread. *)
        "sc" + 4 *<- Sp;;
        Rp <- "newPc";;
        Sp <- "newSp";;
        IGoto* [("threadq","ADT")] Rp
      }
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac t := abstract (sep hints;
  try (apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ]);
    eauto).

Lemma wordBound : forall w : W,
  natToW 2 <= w
  -> (wordToNat w >= 2)%nat.
  intros; pre_nomega;
    rewrite wordToNat_natToWord_idempotent in * by reflexivity; assumption.
Qed.

Local Hint Immediate wordBound.

Hint Rewrite <- minus_n_O : sepFormula.

Transparent evalInstrs.

Theorem evalInstrs_app_fwd_None : forall stn is1 is2 st,
  evalInstrs stn st (is1 ++ is2) = None
  -> evalInstrs stn st is1 = None
  \/ exists st', evalInstrs stn st is1 = Some st' /\ evalInstrs stn st' is2 = None.
  induction is1; simpl; intuition eauto.
  destruct (evalInstr stn st a); eauto.
Qed.

Theorem evalInstrs_app_fwd_Some : forall stn is1 is2 st st',
  evalInstrs stn st (is1 ++ is2) = Some st'
  -> exists st'', evalInstrs stn st is1 = Some st'' /\ evalInstrs stn st'' is2 = Some st'.
  induction is1; simpl; intuition eauto.
  destruct (evalInstr stn st a); eauto.
  discriminate.
Qed.

Opaque evalInstrs.

Require Import Coq.Logic.Eqdep.

Hint Immediate evolve_refl.

Theorem ok : moduleOk m.
  vcgen.

  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  post.
  rewrite stackSize_split in H0.
  assert (NoDup ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)) by NoDup.
  evaluate hints; descend; repeat (step hints; descend); auto.

  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.

  post.
  toFront ltac:(fun P => match P with
                           | susp' _ _ _ _ => idtac
                         end) H0.
  eapply susp_convert in H0; eauto.
  t.

  t.
  t.
  t.
  t.
  t.
  t.
  t.

  t.
  t.
  t.
  t.
  t.
  t.

  post.
  match goal with
    | [ H : context[?X - 1] |- _ ] =>
      replace X with (length ("rp" :: nil) + (X - length ("rp" :: nil))) in H
  end.
  assert (NoDup ("rp" :: nil)) by NoDup.
  evaluate hints; sep hints; auto.
  evaluate hints; simpl; omega.

  post; evaluate auto_ext.
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | starting _ _ _ _ => idtac
                             end) H;
      apply starting_elim in H; post; descend
  end.
  toFront_conc ltac:(fun P => match P with
                                | susp' _ _ _ _ => idtac
                              end);
  apply susp'_intro; descend.
  2: instantiate (5 := locals ("rp" :: nil) x2 x1 (sel x4 "ss")); sep_auto.
  eauto.
  eapply Imply_trans; [ | apply H6 ]; clear H6.
  descend; step auto_ext.
  step auto_ext.
  eauto.
  rewrite H6; auto.
  step auto_ext.
  step auto_ext.
  sep_auto.

  t.
  sep_auto; auto.
  t.
  t.
  t.

  t.

  post.

  Transparent evalInstrs.

  Transparent evalInstrs.

  Transparent evalInstrs.

  Opaque evalInstrs.

  change (evalInstrs stn st
    ((Binop Rv (LvMem (Sp + 4)%loc) Plus 4
      :: Assign Rp (LvMem Rv)
      :: Binop Rv Rp Plus 4
      :: Assign (LvMem Rv) (LvMem (Sp + 4)%loc)
      :: Binop Rv Rp Plus 8
      :: Assign (LvMem Rv) (LvMem (Sp + 8)%loc)
      :: Binop Rv Rp Plus 12
      :: Assign (LvMem Rv) Sp
      :: Assign Sp Rp :: nil)
      ++ (Binop Rv Sp Plus 28
      :: Assign (LvMem (Rv + 4)%loc) 0
      :: Binop Rv Sp Plus 28
      :: Assign (LvMem (Rv + 8)%loc) (LvMem (Sp + 12)%loc)
      :: Binop Rv Sp Plus 28
      :: Assign (LvMem (Rv + 12)%loc) (LvMem (Sp + 8)%loc)
      :: Binop Sp Sp Plus 28 :: nil)) = None) in H0.

  apply evalInstrs_app_fwd_None in H0.
  destruct H0 as [ | [ ? [ ] ] ].
  evaluate hints.
  generalize dependent H0; evaluate hints; intro.

  change (locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
    (upd (upd (upd x4 "sc" (sel x0 "sc")) "ss" (sel x0 "ss")) "curPc" (Regs st Sp))
    14 x5)
    with (locals_call ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
      (upd (upd (upd x4 "sc" (sel x0 "sc")) "ss" (sel x0 "ss")) "curPc" (Regs st Sp))
      14 x5
      ("rp" :: "base" :: "p" :: "n" :: nil) 0 28) in H5.
  assert (ok_call ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
    ("rp" :: "base" :: "p" :: "n" :: nil)
    14 0 28)
  by (split; [ simpl; omega
    | split; [ simpl; omega
      | split; [ NoDup
        | reflexivity ] ] ]).
  evaluate hints.

  propxFo.
  change (evalInstrs stn x
    ((Binop Rv (LvMem (Sp + 4)%loc) Plus 4
      :: Assign Rp (LvMem Rv)
      :: Binop Rv Rp Plus 4
      :: Assign (LvMem Rv) (LvMem (Sp + 4)%loc)
      :: Binop Rv Rp Plus 8
      :: Assign (LvMem Rv) (LvMem (Sp + 8)%loc)
      :: Binop Rv Rp Plus 12
      :: Assign (LvMem Rv) Sp
      :: Assign Sp Rp :: nil)
      ++ (Binop Rv Sp Plus 28
      :: Assign (LvMem (Rv + 4)%loc) 0
      :: Binop Rv Sp Plus 28
      :: Assign (LvMem (Rv + 8)%loc) (LvMem (Sp + 12)%loc)
      :: Binop Rv Sp Plus 28
      :: Assign (LvMem (Rv + 12)%loc) (LvMem (Sp + 8)%loc)
      :: Binop Sp Sp Plus 28 :: nil)) = Some st) in H2.

  apply evalInstrs_app_fwd_Some in H2.
  destruct H2 as [ ? [ ] ].
  generalize dependent H2; evaluate hints; intro.
  change (locals ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
    (upd (upd (upd x5 "sc" (sel x1 "sc")) "ss" (sel x1 "ss")) "curPc" (Regs x Sp))
    14 x6)
    with (locals_call ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
      (upd (upd (upd x5 "sc" (sel x1 "sc")) "ss" (sel x1 "ss")) "curPc" (Regs x Sp))
      14 x6
      ("rp" :: "base" :: "p" :: "n" :: nil) 2 28) in H6.
  assert (ok_call ("rp" :: "sc" :: "ss" :: "curPc" :: "curSp" :: "newPc" :: "newSp" :: nil)
    ("rp" :: "base" :: "p" :: "n" :: nil)
    14 2 28)
  by (split; [ simpl; omega
    | split; [ simpl; omega
      | split; [ NoDup
        | reflexivity ] ] ]).
  change (locals ("rp" :: "sc" :: "ss" :: nil) x1 (wordToNat (sel x1 "ss") - 3) (Regs x Sp))
  with (locals_expose ("rp" :: "sc" :: "ss" :: nil) x1 (wordToNat (sel x1 "ss") - 3) (Regs x Sp)) in H6.
  evaluate hints.
  replace (S (S (S (wordToNat (sel x1 "ss") - 3)))) with (wordToNat (sel x1 "ss")) in H12.
  descend.
  step hints.
  step hints.
  step hints.
  unfold localsInvariantExit'; descend; step hints.
  descend; step hints.
  descend; step hints.
  generalize H9; clear.
  intros; pre_nomega.
  rewrite wordToNat_natToWord_idempotent in H9 by reflexivity; omega.

  t.
  t.
  unfold localsInvariantExit'; t.
  t.
  t.
  t.

  unfold localsInvariantExit'; post; evaluate hints.
  descend.
  step hints.
  2: step hints.
  eauto.
  step hints.
  descend; step hints.
  descend; step hints.
  apply susps_del_fwd; assumption.

  t.
  t.

  post; evaluate hints.
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | susp _ _ _ _ => idtac
                             end) H;
      apply susp_elim in H; post
  end.
  descend.
  step auto_ext.
  match goal with
    | [ H : _ |- _ ] => eapply (Imply_sound (H _ _)); clear H; eauto
  end.
  propxFo.
  unfold labl in H7; rewrite H1 in H7; injection H7; clear H1 H7; intros; subst.
  rewrite H9 in H2; injection H2; clear H2 H9; intros; subst.
  apply (f_equal (fun f => f (stn, st))) in H.
  injection H; clear H; intros; subst.
  do 2 apply inj_pair2 in H; subst; simpl.
  change (fun x y => tq x2 (sel x7 "sc") x y) with (tq x2 (sel x7 "sc")).
  change (fun st m => subst (globalInv x2 (sel x7 "sc") st m)
    (fun x : tq_args world => tq (World x) (Pointer x) (Settings x) (Mem x)))
    with (ginv x2 (sel x7 "sc")).
  step hints.

  t.
  t.
  t.
  t.

  post.
  evaluate hints.
  descend.
  step hints.
  step hints.
  step hints.
  descend; step hints.
  instantiate (2 := x8).
  instantiate (3 := upd x2 "ss" x9).
  descend; cancel hints.
  sep hints.
  sep hints.
  sep hints; auto.

  t.
  t.
  t.

  t.
  t.

  post; evaluate hints; descend.
  step hints.
  2: step hints.
  eauto.
  step hints.
  descend; step hints.
  instantiate (2 := x3).
  instantiate (3 := upd (upd x6 "curPc" (Regs x0 Rv)) "curPc" (sel x6 "sc" ^+ $8)).
  descend; cancel hints.
  step hints.
  apply himp_star_frame; [ reflexivity | apply susps_del_fwd; assumption ].
  step hints.
  sep hints; auto.

  t.
  t.
  t.
  t.

  post; evaluate hints.
  descend.
  instantiate (1 := upd (upd (upd (upd (upd (upd x7 "sc" (sel x3 "sc")) "ss" x9) "curPc"
    (sel x3 "rp")) "curSp" (Regs x0 Sp)) "newPc" (sel x3 "newPc")) "newSp" (sel x3 "newSp")); descend.
  toFront_conc ltac:(fun P => match P with
                                | susp _ _ (sel _ "rp") _ => idtac
                              end).
  apply susp_intro; descend; eauto.
  match goal with
    | [ _ : context[locals ?ns ?v ?a (Regs ?st Sp)] |- interp specs (![?P * _] _) ] =>
      equate P (locals ns v a (Regs st Sp) * (fun x y => x2 (x, y)))%Sep
  end.
  step hints.
  step auto_ext.
  step auto_ext.
  change (fun (x11 : ST.settings) (y : smem) => tq w' (sel x3 "sc") x11 y)
    with (tq w' (sel x3 "sc")).
  change (fun (st : ST.settings) (m0 : smem) =>
    subst (globalInv w' (sel x3 "sc") st m0)
      (fun x11 : tq_args world =>
        tq (World x11) (Pointer x11) (Settings x11) (Mem x11))) with (ginv w' (sel x3 "sc")).
  step auto_ext.

  t.
  t.

  post; evaluate hints; descend.
  instantiate (3 := x3).
  step hints.
  step hints.
  step hints.
  unfold yieldInvariantCont; descend; step hints.
  instantiate (8 := x3 %+ (sel x0 "curPc", sel x0 "curSp")).
  descend; step hints.

  t.
  t.

  post; evaluate hints.
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | susp _ _ _ _ => idtac
                             end) H;
      apply susp_elim in H; post
  end.
  descend.
  step auto_ext.
  match goal with
    | [ H : _ |- _ ] => eapply (Imply_sound (H _ _)); eauto
  end.
  unfold labl in H7; rewrite H1 in H7; injection H7; clear H1 H7; intros; subst.
  rewrite H8 in H2; injection H2; clear H2 H8; intros; subst.
  apply (f_equal (fun f => f (stn, st))) in H1.
  injection H1; clear H1; intros; subst.
  do 2 apply inj_pair2 in H1; subst; simpl.
  instantiate (1 := x3).
  change (fun x y => tq x3 (sel x2 "sc") x y) with (tq x3 (sel x2 "sc")).
  change (fun st m => subst (globalInv x3 (sel x2 "sc") st m)
    (fun x : tq_args world => tq (World x) (Pointer x) (Settings x) (Mem x)))
    with (ginv x3 (sel x2 "sc")).
  propxFo.
  step hints.
Qed.

Transparent stackSize.

End Make.
