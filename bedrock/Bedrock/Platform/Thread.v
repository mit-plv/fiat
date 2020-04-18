Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Bedrock.Platform.Scheduler Bedrock.Platform.ThreadQueue.
Export AutoSep Malloc Bags.W_Bag.


Definition localsInvariantMain (pre : vals -> W -> qspec) (rpStashed : bool) (adjustSp : W -> W)
  (ns : list string) (res : nat) : assert :=
  st ~> let sp := adjustSp st#Sp in
    [| sp <> 0 /\ freeable sp (1 + length ns + res) |]
    /\ Ex vs, qspecOut (pre (sel vs) st#Rv) (fun pre =>
        ![ locals ("rp" :: ns) vs res sp * pre ] st).

Notation "'PREmain' [ vs ] pre" := (localsInvariantMain (fun vs _ => pre%qspec%Sep))
  (at level 89).

Notation "'PREmain' [ vs , rv ] pre" := (localsInvariantMain (fun vs rv => pre%qspec%Sep))
  (at level 89).

Definition files := Bags.W_Bag.bag.


Module Make(M : Scheduler.S).
Import M.

Module Q'' := Scheduler.Make(M).
Import Q''.
Export Q''.

Section Recall.
  Variable imps : LabelMap.t assert.
  Variable mn : string.

  Import DefineStructured.
  Transparent evalInstrs.

  Definition Recall_ (mn' l : string) : cmd imps mn.
    red; refine (fun pre => {|
      Postcondition := match LabelMap.find (mn', Global l) imps with
                         | None => (fun _ => [| False |])%PropX
                         | Some pre' => (fun stn_st => Ex st', pre (fst stn_st, st')
                           /\ Ex cp : W, [| evalInstrs (fst stn_st) st' (Assign Rp cp :: nil) = Some (snd stn_st) |]
                             /\ [| (fst stn_st).(Labels) (mn', Global l) = Some cp |]
                             /\ Cptr cp pre')%PropX
                       end;
      VerifCond := match LabelMap.find (mn', Global l) imps with
                     | None => jumpToUnknownLabel (mn', Global l)
                     | Some _ => True
                   end :: nil;
      Generate := fun Base Exit => {|
        Entry := 0;
        Blocks := (pre, (Assign Rp (RvLabel (mn', Global l)) :: nil,
          Uncond (RvLabel (mn, Local Exit)))) :: nil
      |}
    |}); abstract (struct; try congruence; descend; eauto; propxFo; eauto 10).
  Defined.
End Recall.


Definition Init_ (afterCall : list string -> nat -> assert) : chunk :=
  (Call "scheduler"!"init"()
    [fun (_ : bool) (_ : W -> W) => afterCall])%SP.

Local Notation RET := (fun inv ns => inv true (fun w => w ^- $ (4 + 4 * List.length ns)) ns).

Notation "'Init' [ afterCall ]" := (Init_ (RET afterCall)) : SP_scope.

Definition Exit (ss : W) : chunk := ($[Sp+4] <- ss;;
  Goto "scheduler"!"exit")%SP.

Definition Yield_ (afterCall : list string -> nat -> assert) : chunk :=
  (Call "scheduler"!"yield"()
    [fun (_ : bool) (_ : W -> W) => afterCall])%SP.

Notation "'Yield' [ afterCall ]" := (Yield_ (RET afterCall)) : SP_scope.

Definition Recall (mn' l : string) : chunk := fun ns res =>
  Structured nil (fun _ _ _ => Recall_ _ _ mn' l).

Definition Spawn_ (l : label) (ss : W) (afterCall : list string -> nat -> assert) : chunk :=
  match snd l with
    | Global l' =>
      (Recall (fst l) l';;
        Call "scheduler"!"spawn"(Rp, ss)
        [fun (_ : bool) (_ : W -> W) => afterCall])%SP
    | _ => Fail%SP
  end.

Notation "'Spawn' ( l , ss ) [ afterCall ]" := (Spawn_ l ss (RET afterCall)) : SP_scope.

Require Import Coq.Bool.Bool.

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
  Init_ Exit Yield_ Recall Spawn_
].

Ltac vcgen := structured_auto vcgen_simp;
  autorewrite with sepFormula in *; simpl in *;
    unfold starB, hvarB, hpropB in *; fold hprop in *; refold.

Definition exitize_me a b c d := locals a b c d.

Lemma switchedy : forall P Q R S : HProp,
  (P * (Q * R)) * S ===> P * (Q * (R * S)).
  sepLemma.
Qed.

Lemma swatchedy : forall P Q R : HProp,
  P * (Q * R) ===> P * Q * R.
  sepLemma.
Qed.

Lemma exitize_locals : forall xx ns vs res sp,
  exitize_me ("rp" :: xx :: ns) vs res sp ===> Ex vs', locals ("rp" :: "ss" :: nil) (upd vs' "ss" (sel vs xx)) (res + length ns) sp.
  unfold exitize_me, locals; intros.
  simpl; unfold upd; simpl.
  apply Himp_ex_c; exists (fun x => if string_dec x "rp" then vs "rp" else vs xx).
  eapply Himp_trans.
  eapply Himp_star_frame.
  eapply Himp_star_frame.
  apply Himp_refl.
  change (vs "rp" :: vs xx :: toArray ns vs)
    with (toArray (("rp" :: xx :: nil) ++ ns) vs).
  apply ptsto32m_split.
  apply Himp_refl.
  destruct (string_dec "rp" "rp"); intuition.
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

Definition exitize_hints : TacPackage.
  prepare exitize_locals tt.
Defined.

Ltac sep unf hints := unf; unfold localsInvariantMain;
  match goal with
    (* spawn *)
    | [ |- context[starting] ] => post; evaluate hints; descend; [
      toFront_conc ltac:(fun P => match P with
                                    | starting _ _ => idtac
                                  end); apply starting_intro;
      unf; descend; [ | step hints | ] | | ];
    (unfold localsInvariantCont; AutoSep.sep hints)

    (* exit *)
    | [ |- context[localsInvariantExit] ] =>
      post; evaluate hints;
      match goal with
        | [ H : context[locals ?a ?b ?c ?d] |- _ ] =>
          change (locals a b c d) with (exitize_me a b c d) in H
      end;
      evaluate exitize_hints; post; descend;
      try match goal with
            | [ _ : context[locals _ ?vs _ _ ] |- context[locals _ ?vs' _ _] ] =>
              unf; equate vs vs'
          end; AutoSep.sep hints

    | _ => AutoSep.sep hints
  end.

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

Hint Extern 1 False => eapply eq_neq_0; [ match goal with
                                            | [ H : context[Sp] |- _ ] =>
                                              match type of H with
                                                | (_ <> _)%type => apply H
                                              end
                                          end
  | match goal with
      | [ H : context[Sp] |- _ ] =>
        match type of H with
          | _ = _ => apply H
        end
    end | words_rewr ].

Hint Extern 1 (freeable _ _) => eapply freeable_cong; [ eassumption | words_rewr ].

Definition m0 := link Malloc.m Queue.m.
Definition m1 := link Q''.m m0.
Definition m2 := link Q''.Q'.m m1.
Definition m := link Q''.Q'.Q.m m2.

Lemma ok0 : moduleOk m0.
  link Malloc.ok Queue.ok.
Qed.

Lemma ok1 : moduleOk m1.
  link Q''.ok ok0.
Qed.

Lemma ok2 : moduleOk m2.
  link Q''.Q'.ok ok1.
Qed.

Theorem ok : moduleOk m.
  link Q''.Q'.Q.ok ok2.
Qed.

End Make.
