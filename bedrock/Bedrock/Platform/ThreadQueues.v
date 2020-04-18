Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Bags Bedrock.Platform.Malloc Bedrock.Platform.ThreadQueue Bedrock.Platform.Misc.
Import W_Bag.

Set Implicit Arguments.


Module Type S.
  Parameter world : Type.

  Parameter evolve : world -> world -> Prop.
  Axiom evolve_refl : forall w, evolve w w.
  Axiom evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.

  Parameter globalInv : bag -> world -> HProp.
End S.

Module Make(M : S).
Import M.

Module M'.
  Open Scope Sep_scope.

  Definition world := (bag * M.world)%type.
  Definition evolve (w1 w2 : world) :=
    fst w1 %<= fst w2
    /\ M.evolve (snd w1) (snd w2).

  Local Hint Resolve M.evolve_refl M.evolve_trans.

  Theorem evolve_refl : forall w, evolve w w.
    unfold evolve; auto.
  Qed.

  Theorem evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.
    unfold evolve; intuition eauto.
  Qed.

  Definition globalInv (w : world) (p : W) : hpropB (tq_args world :: nil) :=
    starB (fun p' stn sm => Var0 {| World := w; Pointer := p'; Settings := stn; Mem := sm |}) (fst w %- p) * ^[M.globalInv (fst w) (snd w)].
End M'.

Module Q := ThreadQueue.Make(M').
Import M' Q.

Module Type TQS.
  Parameter tqs' : world -> bag -> HProp.

  Axiom tqs'_eq : tqs' = fun w => starB (tq w).

  Parameter tqs : bag -> M.world -> HProp.

  Axiom tqs_eq : tqs = fun b w => tqs' (b, w) b.

  Definition tqs'_pick_this_one (_ : W) := tqs'.

  Axiom tqs'_empty_bwd : forall w, Emp ===> tqs' w empty.
  Axiom tqs'_add_bwd : forall w ts t, tqs' w ts * tq w t ===> tqs' w (ts %+ t).
  Axiom tqs'_del_fwd : forall w ts t, t %in ts -> tqs'_pick_this_one t w ts ===> tq w t * tqs' w (ts %- t).
  Axiom tqs'_del_bwd : forall w ts t, t %in ts -> tqs' w (ts %- t) * tq w t ===> tqs' w ts.

  Axiom tqs'_weaken : forall w w' b, evolve w w' -> tqs' w b ===>* tqs' w' b.
End TQS.

Module Tqs : TQS.
  Open Scope Sep_scope.

  Definition tqs' w := starB (tq w).

  Theorem tqs'_eq : tqs' = fun w => starB (tq w).
    auto.
  Qed.

  Definition tqs b w := tqs' (b, w) b.

  Theorem tqs_eq : tqs = fun b w => tqs' (b, w) b.
    auto.
  Qed.

  Definition tqs'_pick_this_one (_ : W) := tqs'.

  Theorem tqs'_empty_bwd : forall w, Emp ===> tqs' w empty.
    intros; apply starB_empty_bwd.
  Qed.

  Theorem tqs'_add_bwd : forall w ts t, tqs' w ts * tq w t ===> tqs' w (ts %+ t).
    intros; apply (starB_add_bwd (tq w)).
  Qed.

  Theorem tqs'_del_fwd : forall w ts t, t %in ts -> tqs'_pick_this_one t w ts ===> tq w t * tqs' w (ts %- t).
    intros; apply (starB_del_fwd (tq w)); auto.
  Qed.

  Theorem tqs'_del_bwd : forall w ts t, t %in ts -> tqs' w (ts %- t) * tq w t ===> tqs' w ts.
    intros; eapply Himp_trans; [ | apply (starB_del_bwd (tq w)); eauto ].
    eapply Himp_trans; [ apply Himp_star_comm | ].
    apply Himp_refl.
  Qed.

  Theorem tqs'_weaken : forall w w' b, evolve w w' -> tqs' w b ===>* tqs' w' b.
    intros; apply starB_weaken_weak; intros.
    apply tq_weaken; unfold evolve in *; simpl in *; intuition.
  Qed.
End Tqs.

Import Tqs.
Export Tqs.

Theorem tqs_empty_bwd : forall w, Emp ===> tqs empty w.
  intros; rewrite tqs_eq; apply tqs'_empty_bwd.
Qed.

Definition exitize_me a b c d := locals a b c d.

Lemma switchedy : forall P Q R S : HProp,
  (P * (Q * R)) * S ===> P * (Q * (R * S)).
  sepLemma.
Qed.

Lemma swatchedy : forall P Q R : HProp,
  P * (Q * R) ===> P * Q * R.
  sepLemma.
Qed.

Lemma exitize_locals : forall xx yy ns vs res sp,
  exitize_me ("rp" :: xx :: yy :: ns) vs res sp ===> Ex vs', locals ("rp" :: "sc" :: "ss" :: nil) (upd vs' "ss" (sel vs yy)) (res + length ns) sp.
  unfold exitize_me, locals; intros.
  simpl; unfold upd; simpl.
  apply Himp_ex_c; exists (fun x => if string_dec x "rp" then vs "rp" else vs xx).
  eapply Himp_trans.
  eapply Himp_star_frame.
  eapply Himp_star_frame.
  apply Himp_refl.
  change (vs "rp" :: vs xx :: vs yy :: toArray ns vs)
    with (toArray (("rp" :: xx :: yy :: nil) ++ ns) vs).
  apply ptsto32m_split.
  apply Himp_refl.
  destruct (string_dec "rp" "rp"); intuition.
  destruct (string_dec "sc" "rp"); intuition.
  unfold array, toArray in *.
  simpl map in *.
  simpl length in *.

  eapply Himp_trans; [ apply switchedy | ].

  eapply Himp_trans; [ | apply swatchedy ].
  apply Himp_star_frame.
  sepLemma; NoDup.
  apply Himp_star_frame.
  apply Himp_refl.
  eapply Himp_trans; [ | apply allocated_join ].
  apply Himp_star_frame.
  eapply Himp_trans; [ | apply allocated_shift_base ].
  apply ptsto32m_allocated.
  simpl.
  words.
  eauto.
  apply allocated_shift_base.
  rewrite map_length.
  repeat rewrite <- wplus_assoc.
  repeat rewrite <- natToW_plus.
  f_equal.
  f_equal.
  omega.
  rewrite map_length; omega.
  rewrite map_length; omega.
Qed.

Definition hints : TacPackage.
  prepare (tqs'_del_fwd, create_stack, exitize_locals) (tqs'_empty_bwd, tqs'_add_bwd).
Defined.

Definition starting (ts : bag) (w : M.world) (pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : state, Al vs, Al ts', Al w',
      [| ts %<= ts' |]
      /\ [| M.evolve w w' |]
      /\ [| Regs st Sp <> 0 /\ freeable (Regs st Sp) (1 + ss) |]
      /\ ![ ^[locals ("rp" :: nil) vs ss (Regs st Sp) * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0] ] (s, st)
      ---> #0 (s, st))%PropX.

Lemma starting_elim : forall specs ts w pc ss P stn st,
  interp specs (![ starting ts w pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall st' vs ts' w', interp specs ([| ts %<= ts' |]
      /\ [| M.evolve w w' |]
      /\ [| Regs st' Sp <> 0 /\ freeable (Regs st' Sp) (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss (Regs st' Sp)
      * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0 ] (stn, st')
    ---> pre (stn, st'))%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  eauto.
  eauto.
  eauto.
  step auto_ext.
Qed.


Definition allocS : spec := SPEC reserving 14
  Al ts, Al w,
  PRE[_] tqs ts w * mallocHeap 0
  POST[R] tqs (ts %+ R) w * mallocHeap 0.

Definition isEmptyS : spec := SPEC("sc") reserving 4
  Al ts, Al w,
  PRE[V] [| V "sc" %in ts |] * tqs ts w * mallocHeap 0
  POST[_] tqs ts w * mallocHeap 0.

Definition spawnS : spec := SPEC("sc", "pc", "ss") reserving 18
  Al ts, Al w, Al w',
  PRE[V] [| V "sc" %in ts |] * [| V "ss" >= $2 |] * [| M.evolve w w' |]
    * tqs ts w * starting ts w' (V "pc") (wordToNat (V "ss") - 1) * mallocHeap 0
  POST[_] tqs ts w' * mallocHeap 0.

Definition exitS : spec := SPEC("sc", "ss") reserving 0
  Al ts, Al w, Al w',
  PREexit[V] [| V "ss" >= $3 |] * [| V "sc" %in ts |] * [| M.evolve w w' |]
    * tqs ts w * M.globalInv ts w' * mallocHeap 0.

Definition yieldS : spec := SPEC("enq", "deq") reserving 22
  Al ts, Al w, Al w',
  PRE[V] [| V "enq" %in ts |] * [| V "deq" %in ts |] * [| M.evolve w w' |]
    * tqs ts w * M.globalInv ts w' * mallocHeap 0
  POST[_] Ex ts', Ex w'', [| ts %<= ts' |] * [| M.evolve w' w'' |]
    * tqs ts' w'' * M.globalInv ts' w'' * mallocHeap 0.

Notation "'balias' name () [ p ] l 'end'" :=
  (let p' := p in
   let vars := nil in
    {| FName := name;
      FPrecondition := Precondition p' None;
      FBody := Goto l%SP;
      FVars := vars;
      FReserved := Reserved p' |})
  (no associativity, at level 95, name at level 0, p at level 0, only parsing) : SPfuncs_scope.

Local Notation "'PREy' [ vs ] pre" := (yieldInvariantCont (fun vs _ => pre%qspec%Sep))
  (at level 89).

Definition stackSize := 25.

Lemma stackSize_bound : natToW stackSize >= natToW 2.
  unfold stackSize; auto.
Qed.

Hint Immediate stackSize_bound.

Lemma stackSize_split : stackSize = length ("rp" :: "enq" :: "deq" :: "sp" :: nil) + 21.
  reflexivity.
Qed.

Opaque stackSize.

Definition localsInvariantYieldy (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    [| sp <> 0 |] /\ [| freeable sp stackSize |]
    /\ Ex vs, qspecOut (pre (sel vs) st#Rv) (fun pre =>
        ![ locals ("rp" :: ns) vs res sp * pre ] st).

Local Notation "'PREyy' [ vs ] pre" := (localsInvariantYieldy (fun vs _ => pre%qspec%Sep))
  (at level 89).

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS],
                           "threadq"!"init" @ [Q.initS], "threadq"!"isEmpty" @ [Q.isEmptyS],
                           "threadq"!"spawn" @ [Q.spawnS], "threadq"!"spawnWithStack" @ [Q.spawnWithStackS],
                           "threadq"!"exit" @ [Q.exitS], "threadq"!"yield" @ [Q.yieldS] ]]
  bmodule "threadqs" {{
    bfunction "alloc"("r") [allocS]
      "r" <-- Call "threadq"!"init"()
      [Al ts, Al w,
        PRE[_, R] tq (ts, w) R * tqs ts w
        POST[R'] tqs (ts %+ R') w ];;
      Return "r"
    end with balias "isEmpty"() [isEmptyS]
      "threadq"!"isEmpty"
    end with balias "spawn"() [spawnS]
      "threadq"!"spawn"
    end with balias "exit"() [exitS]
      "threadq"!"exit"
    end with bfunction "yield"("enq", "deq", "sp") [yieldS]
      If ("enq" = "deq") {
        Call "threadq"!"yield"("enq")
        [PRE[_] Emp
         POST[_] Emp];;
        Return 0
      } else {
        "sp" <-- Call "malloc"!"malloc"(0, stackSize)
        [Al ts, Al w,
          PRE[V, R] [| V "enq" %in ts |] * [| V "deq" %in ts |] * [| V "enq" <> V "deq" |]
            * tqs ts w * M.globalInv ts w * mallocHeap 0
            * R =?> stackSize * [| R <> 0 |] * [| freeable R stackSize |]
          POST[_] Ex ts', Ex w', [| ts %<= ts' |] * [| M.evolve w w' |]
            * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0];;

        Assert [Al ts, Al w,
          PRE[V] [| V "enq" %in ts |] * [| V "deq" %in ts |] * [| V "enq" <> V "deq" |]
            * tqs ts w * M.globalInv ts w * mallocHeap 0
            * Ex vs, locals ("rp" :: "enq" :: "deq" :: "sp" :: nil) vs 21 (V "sp")
            * [| V "sp" <> 0 |] * [| freeable (V "sp") stackSize |]
          POST[_] Ex ts', Ex w', [| ts %<= ts' |] * [| M.evolve w w' |]
            * tqs ts' w' * M.globalInv ts' w' * mallocHeap 0];;

        "sp"+0 *<- $[Sp+0];;
        "sp"+4 *<- "enq";;
        "sp"+8 *<- "deq";;
        "sp"+12 *<- Sp;;
        Sp <- "sp";;
        Call "threadq"!"spawnWithStack"("enq", $[Sp+0], "sp")
        [Al ts, Al w,
          PREyy[V] [| V "deq" %in ts |]
            * tqs ts w * M.globalInv ts w * mallocHeap 0];;

        "enq" <- "deq";;
        "deq" <- 25;;
        Goto "threadq"!"exit"
      }
   end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Ltac t := abstract (sep hints; auto).

Local Hint Immediate M.evolve_refl.

Lemma eq_neq_0 : forall u v : W,
  u <> 0
  -> v = 0
  -> u = v
  -> False.
  congruence.
Qed.

Lemma freeable_cong : forall (u v : W) n,
  freeable v n
  -> v = u
  -> freeable u n.
  congruence.
Qed.

Ltac words_rewr := repeat match goal with
                            | [ H : _ = ?X |- _ ] =>
                              match X with
                                | natToW 0 => fail 1
                                | _ => rewrite H
                              end
                          end; words.

Hint Extern 1 (freeable _ _) => eapply freeable_cong; [ eassumption | words_rewr ].
Hint Extern 1 (_ %in _) => eapply incl_mem; eassumption.
Local Hint Extern 1 (himp _ _ _) => apply tqs'_del_bwd.

Lemma switchy : forall P Q R S T R',
  R ===> R'
  -> P * Q * (R * S) * T ===> P * Q * R' * S * T.
  sepLemma.
Qed.

Lemma swatchy : forall P Q Q' R S,
  Q' ===> Q
  -> P * (Q' * R * S) ===> P * (Q * R * S).
  sepLemma.
Qed.

Lemma swotchy : forall P Q R S T U S',
  S ===> S'
  -> P * star Q (star R (star (S * T) U)) ===> P * Q * R * S' * T * U.
  sepLemma.
Qed.

Theorem ok : moduleOk m.
  vcgen.

  t.
  t.
  t.
  t.
  t.
  t.
  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H6.
  eapply use_HimpWeak in H6; [ | apply (tqs'_weaken (w' := (x1 %+ Regs x0 Rv, x2))); (red; intuition) ].
  toFront ltac:(fun P => match P with
                           | tq _ _ => idtac
                         end) H6.
  eapply use_HimpWeak in H6; [ | apply (tq_weaken (w' := (x1 %+ Regs x0 Rv, x2))); (red; simpl; intuition) ].
  descend.
  step hints.
  step hints.
  descend; step hints.
  rewrite H5; step hints.
  simpl; auto.

  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H4.
  change (tqs' (x, x0) x) with (tqs'_pick_this_one (sel x2 "sc") (x, x0) x) in H4.
  t.

  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H4.
  eapply use_HimpWeak in H4; [ | apply (tqs'_weaken (w' := (x, x1))); (red; intuition) ].
  change (tqs' (x, x1) x) with (tqs'_pick_this_one (sel x3 "sc") (x, x1) x) in H4.
  toFront ltac:(fun P => match P with
                           | starting _ _ _ _ => idtac
                         end) H4; apply starting_elim in H4; post.
  evaluate hints.
  descend.
  toFront_conc ltac:(fun P => match P with
                                | Q.starting _ _ _ _ => idtac
                              end); apply Q.starting_intro; descend.
  2: step hints.
  step hints.
  step hints.
  step hints.
  destruct w'; simpl in *.
  destruct H; simpl in *.
  eapply Imply_trans; [ | eapply (H4 _ _ b0 w) ]; clear H4.
  repeat (apply andR; [ apply injR; assumption | ]).
  repeat (apply andR; [ apply injR; auto | ]).

  make_Himp.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  eapply Himp_trans; [ eapply switchy; apply starB_substH_fwd | ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ * _ * ?P * _ * _ ===> _)%Sep ] =>
      replace P with (tqs' (b0, w) (b0 %- sel x3 "sc")) by (rewrite tqs'_eq; reflexivity)
  end.
  rewrite tqs_eq.

  hnf; intros; step hints.
  step hints.
  t.

  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H4.
  eapply use_HimpWeak in H4; [ | apply (tqs'_weaken (w' := (x, x1))); (red; intuition) ].
  change (tqs' (x, x1) x) with (tqs'_pick_this_one (sel x2 "sc") (x, x1) x) in H4.
  evaluate hints.
  descend.
  eauto.
  step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.

  eapply Himp_trans; [ | apply Himp_star_comm ].
  apply Himp_star_frame; try apply Himp_refl.
  eapply Himp_trans; [ | apply starB_substH_bwd ].
  unfold substH; simpl.
  match goal with
    | [ |- (?P ===> ?Q)%Sep ] =>
      replace P with Q; try apply Himp_refl
  end.
  rewrite tqs'_eq; reflexivity.

  t.
  t.
  t.
  t.
  t.

  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H8.
  eapply use_HimpWeak in H8; [ | apply (tqs'_weaken (w' := (x0, x2))); (red; intuition) ].
  change (tqs' (x0, x2) x0) with (tqs'_pick_this_one (sel x4 "enq") (x0, x2) x0) in H8.
  evaluate hints.
  descend.
  step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.

  eapply Himp_trans; [ | apply swatchy; apply starB_substH_bwd ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ ===> _ * (?P * _ * _))%Sep ] =>
      replace P with (tqs' (x0, x2) (x0 %- sel x4 "enq"))
        by (rewrite tqs'_eq; instantiate (1 := (x0, x2)); reflexivity)
  end.
  sepLemma.
  step hints.
  descend; step hints.
  descend; step hints.
  step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  words.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  instantiate (1 := snd x9).
  instantiate (1 := fst x9).
  make_Himp.

  eapply Himp_trans; [ apply swotchy; apply starB_substH_fwd | ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ * _ * _ * ?P * _ * _ ===> _)%Sep ] =>
      replace P with (tqs' (fst x9, snd x9) (fst x9 %- sel x4 "enq"))
  end.
  sepLemma.
  destruct x9; destruct H19; simpl in *; auto.
  destruct x9; destruct H19; simpl in *; auto.
  destruct x9; destruct H19; simpl in *; auto.
  make_Himp.
  rewrite tqs'_eq.
  apply starB_del_bwd.
  auto.
  rewrite tqs'_eq.
  destruct x9; reflexivity.

  t.
  t.
  t.
  t.

  (* Now the hard part of yield(), with two different queues. *)
  post; evaluate hints.
  rewrite tqs_eq in *.
  toFront ltac:(fun P => match P with
                           | tqs' _ _ => idtac
                         end) H8.
  eapply use_HimpWeak in H8; [ | apply (tqs'_weaken (w' := (x0, x2))); (red; intuition) ].
  t.

  t.

  post; evaluate hints.
  rewrite stackSize_split in *.
  assert (NoDup ("rp" :: "enq" :: "deq" :: "sp" :: nil)) by NoDup.
  evaluate hints.
  t.

  propxFo.
  autorewrite with sepFormula in *; unfold substH in *; simpl in *.
  generalize dependent H0; evaluate hints; intro.
  change (locals ("rp" :: "enq" :: "deq" :: "sp" :: nil) x4 21 (sel x2 "sp"))
    with (locals_call ("rp" :: "enq" :: "deq" :: "sp" :: nil) x4 21 (sel x2 "sp")
      ("rp" :: "sc" :: "pc" :: "sp" :: nil) 0 16) in H4.
  assert (ok_call ("rp" :: "enq" :: "deq" :: "sp" :: nil) ("rp" :: "sc" :: "pc" :: "sp" :: nil) 21 0 16)%nat
    by (split; [ simpl; omega
      | split; [ simpl; omega
        | split; [ NoDup
          | reflexivity ] ] ]).
  evaluate hints.

  propxFo.
  autorewrite with sepFormula in *; unfold substH in *; simpl in *.
  generalize dependent H2; evaluate hints; intro.
  change (locals ("rp" :: "enq" :: "deq" :: "sp" :: nil) x5 21 (sel x3 "sp"))
    with (locals_call ("rp" :: "enq" :: "deq" :: "sp" :: nil) x5 21 (sel x3 "sp")
      ("rp" :: "sc" :: "pc" :: "sp" :: nil) 14 16) in H5.
  assert (ok_call ("rp" :: "enq" :: "deq" :: "sp" :: nil) ("rp" :: "sc" :: "pc" :: "sp" :: nil) 21 14 16)%nat
    by (split; [ simpl; omega
      | split; [ simpl; omega
        | split; [ NoDup
          | reflexivity ] ] ]).
  rewrite tqs_eq in *.
  change (tqs' (x0, x1) x0) with (tqs'_pick_this_one (sel x3 "enq") (x0, x1) x0) in H5.
  evaluate hints.
  descend.
  toFront_conc ltac:(fun P => match P with
                                | susp' _ _ _ _ => idtac
                              end); apply susp'_intro.
  descend.
  2: step hints.
  step hints.
  step hints.
  instantiate (2 := (locals ("rp" :: "enq" :: "deq" :: "sp" :: nil) x3 21 (Regs x Sp)
    * (fun x y => x2 (x, y)))%Sep).
  step hints.
  descend; step hints.
  descend; step hints.
  descend; step hints.
  instantiate (1 := snd w').
  instantiate (1 := fst w').
  destruct w'; destruct H13; simpl in *.
  descend; step hints.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply tqs'_del_bwd ] ].
  step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.
  eapply Himp_trans; [ apply Himp_star_frame; [ apply starB_substH_fwd | apply Himp_refl ] | ].
  unfold substH; simpl.
  match goal with
    | [ |- (star ?P _ ===> _)%Sep ] =>
      replace P with (tqs' (b, w) (b %- sel x3 "enq")) by (rewrite tqs'_eq; reflexivity)
  end.
  sepLemma.
  auto.
  step hints.
  unfold localsInvariantYieldy; descend; step hints.

  descend; step hints.
  intros.
  eapply eq_neq_0; try eassumption.
  words_rewr.
  auto.
  descend; step hints.

  t.
  t.

  post.
  match goal with
    | [ H : context[locals ?a ?b ?c ?d] |- _ ] => change (locals a b c d)
      with (exitize_me a b c d) in H
  end.
  rewrite tqs_eq in H3.
  change (tqs' (x1, x2) x1) with (tqs'_pick_this_one (sel x3 "deq") (x1, x2) x1) in H3.
  evaluate hints.
  descend.
  3: instantiate (1 := upd (upd (upd x4 "ss" (sel x3 "deq")) "sc" (sel x3 "deq")) "ss" 25).
  eapply eq_neq_0; try eassumption; words_rewr.
  descend.
  auto.
  descend; step hints.
  unfold ginv, globalInv.
  autorewrite with sepFormula; simpl.
  make_Himp.
  eapply Himp_trans; [ | apply Himp_star_frame; [ apply starB_substH_bwd | apply Himp_refl ] ].
  unfold substH; simpl.
  match goal with
    | [ |- (_ ===> star ?P _)%Sep ] =>
      replace P with (tqs' (x1, x2) (x1 %- sel x3 "deq")) by (rewrite tqs'_eq; reflexivity)
  end.
  sepLemma.
Qed.

Transparent stackSize.

End Make.
