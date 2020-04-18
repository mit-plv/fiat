Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Scheduler Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays Bedrock.Platform.Buffers Bedrock.Platform.StringOps Coq.Strings.Ascii Bedrock.Platform.Io.
Require Import Bedrock.Platform.Http Bedrock.Platform.SinglyLinkedList Bedrock.Platform.Bags Bedrock.Platform.ArrayOps.


Module Type S.
  Parameter buf_size : N.
  Parameters sched globalInv : bag -> HProp.

  Axiom buf_size_lower : (nat_of_N buf_size >= 2)%nat.
  Axiom buf_size_upper : goodSize (4 * nat_of_N buf_size).

  Axiom globalInv_monotone : forall fs fs', fs %<= fs'
    -> globalInv fs ===> globalInv fs'.
End S.

Section specs.
  Variable httpq : W -> HProp.

  Definition saveGS := SPEC("q", "buf", "len") reserving 12
    Al len : W,
    PRE[V] httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |] * mallocHeap 0
    POST[R] httpq R * V "buf" =?>8 wordToNat len * mallocHeap 0.
End specs.

Module Make(Import M : S).

Definition bsize := nat_of_N (buf_size * 4)%N.

Definition onebuf (p : W) := (p =?>8 bsize * [| p <> 0 |] * [| freeable p (nat_of_N buf_size) |])%Sep.
Definition bufs := starL onebuf.

Theorem onebuf_fwd : forall p,
  onebuf p ===> p =?>8 bsize * [| p <> 0 |] * [| freeable p (nat_of_N buf_size) |].
  unfold onebuf; sepLemma.
Qed.

Theorem onebuf_bwd : forall p,
  p =?>8 bsize * [| p <> 0 |] * [| freeable p (nat_of_N buf_size) |] ===> onebuf p.
  unfold onebuf; sepLemma.
Qed.

Module Type HTTPQ.
  Parameter httpq : W -> HProp.

  Axiom httpq_fwd : forall p, httpq p ===> Ex ls, sll ls p * bufs ls.
  Axiom httpq_bwd : forall p, Ex ls, sll ls p * bufs ls ===> httpq p.

  Definition httpqSplitMe := httpq.

  Axiom httpq_split : forall p, (Ex x, Ex ls, sll (x :: ls) p * bufs (x :: ls)) ===> httpqSplitMe p.
End HTTPQ.

Module Httpq : HTTPQ.
  Open Scope Sep_scope.

  Definition httpq (p : W) :=
    Ex ls, sll ls p * bufs ls.

  Theorem httpq_fwd : forall p, httpq p ===> Ex ls, sll ls p * bufs ls.
    unfold httpq; sepLemma.
  Qed.

  Theorem httpq_bwd : forall p, Ex ls, sll ls p * bufs ls ===> httpq p.
    unfold httpq; sepLemma.
  Qed.

  Definition httpqSplitMe := httpq.

  Theorem httpq_split : forall p, (Ex x, Ex ls, sll (x :: ls) p * bufs (x :: ls)) ===> httpqSplitMe p.
    sepLemma.
    etransitivity; [ | apply httpq_bwd ].
    apply himp_ex_c; exists (x0 :: x).
    sepLemma.
  Qed.
End Httpq.

Import Httpq.
Export Httpq.

Definition saveS := saveGS httpq.

Definition sendS := SPEC("q") reserving 56
  Al fs,
  PRE[V] httpq (V "q") * sched fs * globalInv fs * mallocHeap 0
  POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0.

(* This one probably shouldn't be called from other modules. *)
Definition send1S := SPEC("buf") reserving 52
  Al fs,
  PRE[V] onebuf (V "buf") * sched fs * globalInv fs * mallocHeap 0
  POST[_] Ex fs', onebuf (V "buf") * [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0.

Coercion ascii_of_nat : nat >-> ascii.

Module H := Http.Make(M).
Import H.

Definition preRequest := ("POST / HTTP/1.0" ++ nl
  ++ "Content-Type: text/xml" ++ nl
  ++ "User-Agent: Bedrock" ++ nl
  ++ "Content-Length: ")%string.

Definition hints : TacPackage.
  prepare (httpq_fwd, onebuf_fwd, SinglyLinkedList.nil_fwd, SinglyLinkedList.cons_fwd,
  buffer_split_tagged)
  (httpq_bwd, httpq_split, onebuf_bwd, SinglyLinkedList.nil_bwd, SinglyLinkedList.cons_bwd,
  buffer_join_tagged).
Defined.

Definition m := bimport [[ "io"!"writeAll" @ [writeAllGS sched globalInv],
                           "array8"!"copy" @ [ArrayOps.copyS], "buffers"!"contains" @ [containsS],
                           "http"!"itoa" @ [itoaS], "sys"!"abort" @ [abortS],
                           "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "buffers"!"bmalloc" @ [bmallocS], "buffers"!"bfree" @ [bfreeS],
                           "scheduler"!"connect" @ [Scheduler.connectGS sched],
                           "scheduler"!"connected" @ [Scheduler.connectedGS sched globalInv],
                           "scheduler"!"close" @ [Scheduler.closeGS sched] ]]
  bmodule "httpq" {{
    bfunction "save"("q", "buf", "len", "newbuf", "node") [saveS]
      If ("len" >= bsize) {
        (* Well, shucks.  It doesn't fit. *)
        Call "sys"!"abort"()
        [PREonly[_] [| False |] ];;
        Fail
      } else {
        "newbuf" <-- Call "buffers"!"bmalloc"(buf_size)
        [Al len : W,
          PRE[V, R] R =?>8 bsize * [| R <> 0 |] * [| freeable R (nat_of_N buf_size) |]
            * [| V "len" < natToW bsize |]%word
            * httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |]%word * mallocHeap 0
          POST[R'] httpq R' * V "buf" =?>8 wordToNat len * mallocHeap 0];;

        Note [reveal_buffers];;
        (* Copy the input buffer into our new buffer. *)
        Call "array8"!"copy"("newbuf", 0, "buf", 0, "len")
        [Al len : W, Al ls,
          PRE[V] array8 ls (V "newbuf") * [| length ls = bsize |]
            * [| V "newbuf" <> 0 |] * [| freeable (V "newbuf") (nat_of_N buf_size) |]
            * [| V "len" < natToW (length ls) |]%word
            * httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |]%word * mallocHeap 0
          POST[R'] httpq R' * V "buf" =?>8 wordToNat len * mallocHeap 0];;

        (* Write a terminating 0 character. *)
        "newbuf" + "len" *<-8 0;;

        Note [reveal_buffers];;
        "node" <-- Call "malloc"!"malloc"(0, 2)
        [Al len : W,
          PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
            * V "newbuf" =?>8 bsize * [| V "newbuf" <> 0 |] * [| freeable (V "newbuf") (nat_of_N buf_size) |]
            * httpq (V "q") * V "buf" =?>8 wordToNat len * [| V "len" <= len |]%word * mallocHeap 0
          POST[R'] httpqSplitMe R' * V "buf" =?>8 wordToNat len * mallocHeap 0];;

        "node" *<- "newbuf";;
        "node"+4 *<- "q";;

        Return "node"
      }
    end with bfunction "send1"("buf", "pos", "fr", "len", "opos", "overflowed") [send1S]
      "pos" <-- Call "buffers"!"contains"("buf", bsize, 0)
      [Al fs,
        PRE[V] onebuf (V "buf") * sched fs * globalInv fs * mallocHeap 0
        POST[_] onebuf (V "buf") * Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0];;

      If ("pos" >= bsize) {
        (* No '\0' character to separate hostname and payload?  How troubling. :-( *)
        Call "sys"!"abort"()
        [PREonly[_] [| False |] ];;
        Fail
      } else {
        Skip
      };;

      (* Let's rearrange the logical view to expose the hostname and payload separately. *)
      Assert [Al fs,
        PRE[V] [| wordToNat (V "pos") < bsize |]%nat * [| wordToNat (V "pos") <= bsize |]%nat
          * buffer_splitAt (wordToNat (V "pos")) (V "buf") bsize
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] buffer_joinAt (wordToNat (V "pos")) (V "buf") bsize
          * Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0];;

      "fr" <-- Call "scheduler"!"connect"("buf", "pos")
      [Al fs,
        PRE[V, R] [| R %in fs |] * [| 1 <= bsize - wordToNat (V "pos") |]%nat
          * buffer_splitAt 1 (V "buf" ^+ V "pos") (bsize - wordToNat (V "pos"))
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] buffer_joinAt 1 (V "buf" ^+ V "pos") (bsize - wordToNat (V "pos"))
          * Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0];;

      "len" <- "pos" + 1;;
      "buf" <- "buf" + "len";;
      "len" <- bsize - "pos";;
      "len" <- "len" - 1;;

      Call "scheduler"!"connected"("fr")
      [Al fs,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] V "buf" =?>8 wordToNat (V "len")
          * Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0];;

      "pos" <-- Call "buffers"!"contains"("buf", "len", 0)
      [Al fs,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] V "buf" =?>8 wordToNat (V "len")
          * Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0];;

      If ("pos" >= "len") {
        (* No '\0' character to mark end of payload?  How troubling. :-( *)
        Call "sys"!"abort"()
        [PREonly[_] [| False |] ];;
        Fail
      } else {
        Skip
      };;

      "opos" <- "pos";;
      Note [reveal_buffers];;
      StringWrite "buf" "len" "opos" "overflowed" preRequest
      (fun fs V => [| V "fr" %in fs |] * sched fs * globalInv fs * mallocHeap 0
        * [| V "pos" < V "len" |]%word)%Sep
      (fun _ fs V _ => Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
        * sched fs' * globalInv fs' * mallocHeap 0)%Sep;;
      Note [reveal_buffers];;

      "opos" <-- Call "http"!"itoa"("pos", "buf", "opos", "len")
      [Al fs,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs * globalInv fs * mallocHeap 0
          * [| V "pos" < V "len" |]%word
        POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs' * globalInv fs' * mallocHeap 0];;

      If ("opos" > "len") {
        Call "sys"!"abort"()
        [PREonly[_] [| False |] ];;
        Fail
      } else {
        Skip
      };;

      Note [reveal_buffers];;
      StringWrite "buf" "len" "opos" "overflowed" endOfHeaders
      (fun fs V => [| V "fr" %in fs |] * sched fs * globalInv fs * mallocHeap 0
        * [| V "pos" < V "len" |]%word)%Sep
      (fun _ fs V _ => Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
        * sched fs' * globalInv fs' * mallocHeap 0)%Sep;;
      Note [reveal_buffers];;

      If ("overflowed" = 1) {
        Call "sys"!"abort"()
        [PREonly[_] [| False |] ];;
        Fail
      } else {
        (* Write headers. *)
        If ("opos" < "pos") {
          (* Shouldn't be possible. :( *)
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ];;
          Fail
        } else {
          "opos" <- "opos" - "pos";;
          Call "io"!"writeAll"("fr", "buf", "pos", "opos")
          [Al fs,
            PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
              * sched fs * globalInv fs * mallocHeap 0
              * [| V "pos" < V "len" |]%word
            POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
              * sched fs' * globalInv fs' * mallocHeap 0];;

          Call "io"!"writeAll"("fr", "buf", 0, "pos")
          [Al fs,
            PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
              * sched fs * globalInv fs * mallocHeap 0
            POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
              * sched fs' * globalInv fs' * mallocHeap 0];;

          Call "scheduler"!"close"("fr")
          [PRE[_] Emp
           POST[_] Emp];;
          Return 0
        }
      }
    end with bfunction "send"("q", "tmp", "buf") [sendS]
      [Al fs,
        PRE[V] httpq (V "q") * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0]
      While ("q" <> 0) {
        "tmp" <- "q";;
        "buf" <-* "q";;
        "q" <-* "q"+4;;

        Call "httpq"!"send1"("buf")
        [Al fs,
          PRE[V] onebuf (V "buf") * V "tmp" =?> 2 * [| V "tmp" <> 0 |] * [| freeable (V "tmp") 2 |]
            * httpq (V "q") * sched fs * globalInv fs * mallocHeap 0
          POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0];;

        Call "buffers"!"bfree"("buf", buf_size)
        [Al fs,
          PRE[V] V "tmp" =?> 2 * [| V "tmp" <> 0 |] * [| freeable (V "tmp") 2 |]
            * httpq (V "q") * sched fs * globalInv fs * mallocHeap 0
          POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0];;

        Call "malloc"!"free"(0, "tmp", 2)
        [Al fs,
          PRE[V] httpq (V "q") * sched fs * globalInv fs * mallocHeap 0
          POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * globalInv fs' * mallocHeap 0]
      };;

      Return 0
    end
  }}.

Hint Extern 1 (@eq W _ _) => words.

Ltac match_locals :=
  match goal with
    | [ |- interp _ (?P ---> ?Q)%PropX ] =>
      match Q with
        | context[locals ?ns ?vs _ _] =>
          match P with
            | context[locals ns ?vs' _ _] => equate vs' vs; descend
            end
      end;
      try match goal with
            | [ H : sel ?V "len" <= ?X |- context[?Y < sel ?V "len" -> False] ] =>
              equate X Y
          end
    | _ => MoreArrays.match_locals
  end.

Lemma globalInv_wiggle : forall P Q fs fs', fs %<= fs'
  -> P * (globalInv fs * Q) ===> P * (globalInv fs' * Q).
  sepLemma; apply globalInv_monotone; auto.
Qed.

Ltac t' :=
  try match goal with
        | [ |- context[reveal_buffers] ] => post; unfold buffer, httpqSplitMe in *
      end;
  try match goal with
        | [ _ : context[match ?st with pair _ _ => _ end] |- _ ] => destruct st; simpl in *
      end; try solve [ sep hints; eauto ];
  post; evaluate hints; subst; simpl in *; descend;
  repeat (try match_locals; step hints; descend); eauto;
    try (try (etransitivity; [ | apply globalInv_wiggle; eassumption ]; unfold buffer_splitAt);
      descend; step hints).

Ltac t := easy || prove_irrel || t'.

Lemma buf_size_simp : wordToNat (NToW buf_size) = N.to_nat buf_size.
  unfold NToW; rewrite NToWord_nat.
  apply wordToNat_natToWord_idempotent.
  change (goodSize (N.to_nat buf_size)).
  eapply goodSize_weaken.
  apply buf_size_upper.
  auto.
Qed.

Lemma buf_size_lower' : natToW 2 <= NToW buf_size.
  pre_nomega.
  rewrite buf_size_simp.
  apply buf_size_lower.
Qed.

Local Hint Immediate buf_size_lower'.

Lemma freeable_coerce : forall p,
  freeable p (wordToNat (NToW buf_size))
  -> freeable p (N.to_nat buf_size).
  intros.
  rewrite buf_size_simp in *; auto.
Qed.

Local Hint Immediate freeable_coerce.

Lemma make_bsize : wordToNat (NToW buf_size) * 4 = bsize.
  rewrite buf_size_simp.
  unfold bsize.
  rewrite N2Nat.inj_mul.
  change (N.to_nat 4) with 4.
  omega.
Qed.

Hint Rewrite make_bsize : sepFormula.

Lemma bsize_simp : wordToNat (natToW bsize) = bsize.
  intros; apply wordToNat_natToWord_idempotent.
  change (goodSize bsize).
  eapply goodSize_weaken.
  apply buf_size_upper.
  unfold bsize.
  rewrite N2Nat.inj_mul.
  change (N.to_nat 4) with 4.
  omega.
Qed.

Lemma lt_le : forall w n,
  w < natToW bsize
  -> n = bsize
  -> (wordToNat w <= n)%nat.
  intros; subst; pre_nomega; rewrite bsize_simp in *.
  auto.
Qed.

Lemma le_le : forall n (w u : W),
  u <= w
  -> n = wordToNat w
  -> (wordToNat u <= n)%nat.
  intros; subst; nomega.
Qed.

Lemma bsize_wordToNat : forall n,
  n = bsize
  -> n = wordToNat (natToW bsize).
  intros; rewrite bsize_simp; auto.
Qed.

Local Hint Immediate lt_le le_le bsize_wordToNat.

Hint Rewrite bsize_simp natToW_wordToNat : sepFormula.

Lemma bsize_re : forall w : W,
  w < natToW bsize
  -> (wordToNat w < bsize)%nat.
  intros; pre_nomega.
  autorewrite with sepFormula in *.
  auto.
Qed.

Local Hint Immediate bsize_re.

Hint Rewrite bsize_simp : N.

Lemma multisub : forall w,
  (1 <= bsize - wordToNat w)%nat
  -> wordToNat (natToW bsize ^- w ^- natToW 1) = (bsize - wordToNat w - 1).
  intros.
  rewrite wordToNat_wminus.
  rewrite wordToNat_wminus.
  autorewrite with sepFormula; auto.
  nomega.
  pre_nomega.
  rewrite wordToNat_wminus; nomega.
Qed.

Lemma assoc1 : forall u v : W,
  u ^+ (v ^+ natToW 1) = u ^+ v ^+ natToW 1.
  intros; words.
Qed.

Hint Rewrite multisub assoc1 using assumption : sepFormula.

Lemma goodSize_wordToNat' : forall n (w : W),
  n = wordToNat w
  -> goodSize n.
  intros; subst; eauto.
Qed.

Lemma lt_le' : forall u v : W,
  u < v
  -> (wordToNat u <= wordToNat v)%nat.
  intros; nomega.
Qed.

Local Hint Immediate goodSize_wordToNat' lt_le'.

Lemma bsize_unexpand : N.to_nat buf_size * 4 = bsize.
  unfold bsize; rewrite N2Nat.inj_mul; auto.
Qed.

Hint Rewrite buf_size_simp bsize_unexpand : sepFormula.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
