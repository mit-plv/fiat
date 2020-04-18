Require Import Bedrock.Examples.AutoSep Bedrock.Examples.Malloc.


(* Two definitions based on hiding functions inside a new datatype, to avoid confusing our reification tactics *)
Inductive fn := Fn (f : W -> W).
Definition app (f : fn) (x : W) := let (f) := f in f x.

(* What does it mean for a program counter to implement a mathematical function? *)
Definition goodMemo (f : fn) (pc : W) : HProp := fun s m =>
  (ExX : settings * state, Cptr pc #0
    /\ ExX : settings * smem, #0 (s, m)
    /\ Al st : settings * state, AlX : settings * smem, AlX : settings * state,
    (Ex vs, Cptr st#Rp #0
      /\ ![ ^[locals ("rp" :: "x" :: nil) vs 0 st#Sp] * #1 * #2 ] st
      /\ Al st' : state,
      ([| Regs st' Sp = st#Sp /\ Regs st' Rv = app f (sel vs "x") |]
        /\ Ex vs', ![ ^[locals ("rp" :: "x" :: nil) vs' 0 st#Sp] * #1 * #2 ] (fst st, st'))
      ---> #0 (fst st, st'))
    ---> #3 st)%PropX.

Module Type MEMO.
  Parameter memo : fn -> W -> HProp.
  (* Arguments: mathematical function that is implemented, and pointer to private data *)

  Axiom memo_fwd : forall f p,
    memo f p ===> Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn |] * goodMemo f pc.

  Axiom memo_bwd : forall f p,
    (Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn|] * goodMemo f pc) ===> memo f p.
End MEMO.

Module Memo : MEMO.
  Definition memo (f : fn) (p : W) : HProp :=
    (Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn |] * goodMemo f pc)%Sep.

  Theorem memo_fwd : forall (f : fn) p,
    memo f p ===> Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn |] * goodMemo f pc.
    unfold memo; sepLemma.
  Qed.

  Theorem memo_bwd : forall f p,
    (Ex pc, Ex lastIn, Ex lastOut, (p ==*> pc, lastIn, lastOut) * [| lastOut = app f lastIn|] * goodMemo f pc) ===> memo f p.
    unfold memo; sepLemma.
  Qed.
End Memo.

Import Memo.
Export Memo.

Definition hints : TacPackage.
  prepare memo_fwd memo_bwd.
Defined.

Definition initS : spec := SPEC("f", "in", "out") reserving 7
  Al f,
  PRE[V] goodMemo f (V "f") * [| V "out" = app f (V "in") |] * mallocHeap
  POST[R] memo f R * mallocHeap.

Definition callS : spec := SPEC("m", "x") reserving 4
  Al f,
  PRE[V] memo f (V "m")
  POST[R] [| R = app f (V "x") |] * memo f (V "m").

Definition memoizeM := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "memoize" {{
  bfunction "init"("f", "in", "out", "r") [initS]
    "r" <-- Call "malloc"!"malloc"(1)
    [PRE[V, R] R =?> 3
     POST[R'] [| R' = R |] * R ==*> V "f", V "in", V "out" ];;
    "r" *<- "f";;
    "r" <- "r" + 4;;
    "r" *<- "in";;
    "r" <- "r" + 4;;
    "r" *<- "out";;
    Return "r" - 8
  end with bfunction "call"("m", "x", "tmp", "tmp2") [callS]
    "tmp" <-* "m" + 4;;
    If ("x" = "tmp") {
      (* We're in luck!  This call is cached. *)

      "tmp" <-* "m" + 8;;
      Return "tmp"
    } else {
      (* This is a different argument from last time.  Call the function again. *)

      "tmp" <-* "m";;
      "tmp" <-- ICall "tmp"("x")
      [Al f,
        PRE[V, R] [| R = app f (V "x") |] * memo f (V "m")
        POST[R'] [| R' = R |] * memo f (V "m") ];;

      "tmp2" <- "m" + 4;;
      "tmp2" *<- "x";;
      "tmp2" <- "m" + 8;;
      "tmp2" *<- "tmp";;

      Return "tmp"
    }
  end
}}.

Hint Extern 1 (@eq W _ _) =>
  match goal with
    | [ |- context[app] ] => fail 1
    | _ => words
  end.

Hint Extern 1 (interp ?specs (?U ?x ?y)) =>
  match goal with
    | [ H : interp ?specs (?f (?x, ?y)) |- _ ] =>
      equate U (fun x y => f (x, y)); exact H
  end.

Lemma goodMemo_elim : forall specs f pc P st,
  interp specs (![ goodMemo f pc * P ] st)
  -> exists pre, specs pc = Some pre
    /\ exists inv, interp specs (![ inv * P ] st)
      /\ forall st fr rpre,
        interp specs ((Ex vs, Cptr st#Rp (fun x => rpre x)
          /\ ![ ^[locals ("rp" :: "x" :: nil) vs 0 st#Sp] * fr * inv ] st
          /\ Al st' : state,
          ([| Regs st' Sp = st#Sp /\ Regs st' Rv = app f (sel vs "x") |]
            /\ Ex vs', ![ ^[locals ("rp" :: "x" :: nil) vs' 0 st#Sp] * fr * inv ] (fst st, st'))
          ---> rpre (fst st, st'))
        ---> pre st)%PropX.
  Local Opaque locals.
  rewrite sepFormula_eq; repeat (propxFo; repeat (eauto; esplit)).
  specialize (H4 (a, b) (fun a_b => fr (fst a_b) (snd a_b)) rpre).
  Local Transparent locals lift.
  repeat rewrite sepFormula_eq in *.
  assumption.
  Local Opaque locals lift.
Qed.

Lemma goodMemo_intro : forall specs pre inv f pc,
  specs pc = Some pre
  -> (forall (st : ST.settings * state) (fr : hpropB nil)
    (rpre : settings * state -> propX W (settings * state) nil),
    interp specs
    ((Ex vs : vals,
      Cptr (st) # (Rp) (fun x : settings * state => rpre x) /\
      ![^[locals ("rp" :: "x" :: nil) vs 0 (st) # (Sp)] * fr * inv] st /\
      (Al st' : state,
        [| Regs st' Sp = (st) # (Sp) /\
          Regs st' Rv = app f (sel vs "x")|] /\
        (Ex vs' : vals,
          ![^[locals ("rp" :: "x" :: nil) vs' 0 (st) # (Sp)] * fr * inv]
          (fst st, st')) ---> rpre (fst st, st')))%PropX ---> pre st))
  -> himp specs inv (goodMemo f pc).
  intros.
  unfold goodMemo, himp; propxFo.
  imply_simp unf.
  imply_simp unf.
  imply_simp unf.
  eauto.
  imply_simp unf.
  imply_simp unf.
  instantiate (1 := fun p => inv (fst p) (snd p)); apply Imply_refl.
  apply Imply_I; apply interp_weaken.
  propxFo.
  eapply Imply_trans; [ | apply H0 ].
  rewrite sepFormula_eq.
  instantiate (1 := a1).
  instantiate (1 := fun a b => a0 (a, b)).
  apply Imply_refl.
Qed.

Lemma switchUp : forall specs P Q R,
  himp specs P R
  -> himp specs (P * Q)%Sep (Q * R)%Sep.
  intros; etransitivity; [ apply himp_star_comm | ]; apply himp_star_frame; auto; reflexivity.
Qed.

Hint Extern 1 (himp _ _ _) =>
  apply switchUp; eapply goodMemo_intro; eassumption.

(* Alternate VC post-processor that understands indirect function calls *)
Ltac post :=
  PreAutoSep.post;
  try ((* This appears to be an indirect function call.
        * Put the appropriate marker predicate in [H], to trigger use of a lemma about the
        * point-of-view shift from caller to callee. *)
    icall ("x" :: nil);

    (* Trigger symbolic execution early. *)
    evaluate hints;

    (* Move [goodMemo] to the front of its hypothesis and eliminate it. *)
    match goal with
      | [ H : interp _ _ |- _ ] =>
        toFront ltac:(fun P => match P with goodMemo _ _ => idtac end) H;
        apply goodMemo_elim in H; sep_firstorder
    end;

    (* Find and apply the hypothesis explaining the spec of the function pointer. *)
    match goal with
      | [ H : forall x : ST.settings * state, _ |- _ ] =>
        eapply Imply_sound; [ apply H | ]
    end).

(* Main tactic *)
Ltac sep := post; PreAutoSep.sep hints; auto.

Theorem memoizeMOk : moduleOk memoizeM.
  vcgen; abstract sep.
Qed.
