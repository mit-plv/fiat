Require Import Bedrock.Platform.Thread Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays Bedrock.Platform.Buffers Bedrock.Platform.Io Bedrock.Platform.tests.StringDb.
Require Import Coq.Strings.Ascii.

Definition W_of_ascii (ch : ascii) : W := N_of_ascii ch.
Coercion W_of_ascii : ascii >-> W.

Local Hint Extern 1 (@eq W _ _) => words.


Section strings.
  Open Scope Sep_scope.

  Fixpoint strings (n : nat) (p : W) : HProp :=
    Ex len, p =*> len
    * match n with
        | O => [| len = 0 |]
        | S n' => [| len <> 0 |] * (p ^+ $4) =?>8 wordToNat len
          * Ex len', (p ^+ $4 ^+ len) =*> len' * (p ^+ $4 ^+ len ^+ $4) =?>8 wordToNat len'
          * strings n' (p ^+ $4 ^+ len ^+ $4 ^+ len')
      end.

  Definition strings' (n : nat) (p len : W) : HProp :=
    match n with
      | O => [| len = 0 |]
      | S n' => [| len <> 0 |] * (p ^+ $4) =?>8 wordToNat len
        * Ex len', (p ^+ $4 ^+ len) =*> len' * (p ^+ $4 ^+ len ^+ $4) =?>8 wordToNat len'
        * strings n' (p ^+ $4 ^+ len ^+ $4 ^+ len')
    end.

  Theorem strings_fwd : forall n p,
    strings n p ===> Ex len, p =*> len * strings' n p len.
    destruct n; sepLemma.
  Qed.

  Theorem strings_bwd : forall n p,
    Ex len, p =*> len * strings' n p len ===> strings n p.
    destruct n; sepLemma.
  Qed.

  Theorem strings'_fwd_zero : forall n p (len : W), len = 0
    -> strings' n p len ===> Emp.
    destruct n; sepLemma.
  Qed.

  Theorem strings'_fwd_nonzero : forall n p (len : W), len <> 0
    -> strings' n p len ===> Ex n', [| n = S n' |] * [| len <> 0 |] * (p ^+ $4) =?>8 wordToNat len
    * Ex len', (p ^+ $4 ^+ len) =*> len' * (p ^+ $4 ^+ len ^+ $4) =?>8 wordToNat len'
    * strings n' (p ^+ $4 ^+ len ^+ $4 ^+ len').
    destruct n; sepLemma.
  Qed.


  Definition keyValues := starB (fun p => Ex q, Ex len, q =*> len * (q ^+ $4) =?>8 wordToNat len
    * [| p = q ^+ $4 ^+ len |] * Ex len', p =*> len' * (p ^+ $4) =?>8 wordToNat len').

  Theorem keyValues_empty_bwd : Emp ===> keyValues empty.
    apply starB_empty_bwd.
  Qed.

  Theorem keyValues_add_bwd : forall b p, keyValues b * (Ex q, Ex len, q =*> len * (q ^+ $4) =?>8 wordToNat len
    * [| p = q ^+ $4 ^+ len |] * Ex len', p =*> len' * (p ^+ $4) =?>8 wordToNat len')
    ===> keyValues (b %+ p).
    apply starB_add_bwd.
  Qed.

  Definition keyValues_pick (_ : W) := keyValues.

  Ltac keyValues := eauto; simpl;
    match goal with
      | [ |- context[starB ?P ?B] ] => change (starB P B) with (keyValues B)
    end; sepLemma.

  Theorem keyValues_pick_fwd : forall p b, p %in b
    -> keyValues_pick p b ===> keyValues (b %- p)
    * (Ex q, Ex len, q =*> len * (q ^+ $4) =?>8 wordToNat len
      * [| p = q ^+ $4 ^+ len |] * Ex len', p =*> len' * (p ^+ $4) =?>8 wordToNat len').
    intros; eapply Himp_trans; [ apply starB_del_fwd | ]; keyValues.
  Qed.

  Theorem keyValues_pick_bwd : forall p b, p %in b
    -> keyValues (b %- p)
    * (Ex q, Ex len, q =*> len * (q ^+ $4) =?>8 wordToNat len
      * [| p = q ^+ $4 ^+ len |] * Ex len', p =*> len' * (p ^+ $4) =?>8 wordToNat len') ===> keyValues_pick p b.
    intros; eapply Himp_trans; [ | apply starB_del_bwd ]; eauto; keyValues.
  Qed.
End strings.

Module Type S.
  Parameters globalSched globalSock globalTree globalPages : W.

  Parameter inbuf_size : nat.
  Axiom inbuf_size_lower : (inbuf_size >= 2)%nat.
  Axiom inbuf_size_upper : (N_of_nat (inbuf_size * 4) < Npow2 32)%N.

  Parameters port numWorkers : W.
End S.

Module Make(M : S).
Import M.

Module M'''.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv (fs : files) : HProp := Ex fr, Ex b, Ex p, Ex trailer,
    globalSock =*> fr * [| fr %in fs |]
    * globalTree =*> p * tree b p * keyValues b
    * trailer =*> 0.
End M'''.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Module MyM.
  Definition sched := sched.
  Definition globalInv := globalInv.
End MyM.

Ltac unf := unfold MyM.sched, MyM.globalInv, M'''.globalSched, M'''.globalInv in *.

Module MyIo := Io.Make(MyM).


Definition hints : TacPackage.
  prepare (buffer_split_tagged, strings_fwd, strings'_fwd_zero, strings'_fwd_nonzero, keyValues_pick_fwd)
  (buffer_join_tagged, strings_bwd, keyValues_empty_bwd, keyValues_add_bwd, keyValues_pick_bwd).
Defined.

Definition mainS := SPEC reserving 49
  Al n,
  PREmain[_] globalSched =?> 1 * globalSock =?> 1 * globalTree =?> 1 * strings n globalPages * mallocHeap 0.

Definition handlerS := SPEC reserving 99
  Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0.

Definition buildDbS := SPEC("p") reserving 23
  Al n,
  PRE[V] strings n (V "p") * mallocHeap 0
  POST[R] Ex b, Ex trailer, tree b R * keyValues b * trailer =*> 0 * mallocHeap 0.

Definition contentOfS := SPEC("tree", "buf", "len") reserving 11
  Al b,
  PRE[V] tree b (V "tree") * V "buf" =?>8 wordToNat (V "len")
  POST[R] [| R = 0 \/ R %in b |] * tree b (V "tree") * V "buf" =?>8 wordToNat (V "len").

Inductive reveal : Prop := Reveal.
Hint Constructors reveal.

Definition bsize := (inbuf_size * 4)%nat.

Definition m := bimport [[ "stringdb"!"new" @ [StringDb.newS], "stringdb"!"lookup" @ [StringDb.lookupS],
                           "stringdb"!"insert" @ [StringDb.insertS], "sys"!"abort" @ [abortS],
                           "buffers"!"bmalloc" @ [bmallocS], "buffers"!"bfree" @ [bfreeS],
                           "buffers"!"contains" @ [containsS], "buffers"!"copy" @ [copyS],
                           "scheduler"!"init"@ [T.Q''.initS], "scheduler"!"exit" @ [T.Q''.exitS],
                           "scheduler"!"spawn" @ [T.Q''.spawnS], "scheduler"!"listen" @ [T.Q''.listenS],
                           "scheduler"!"accept" @ [T.Q''.acceptS], "scheduler"!"close" @ [T.Q''.closeS],
                           "io"!"readUntil" @ [MyIo.readUntilS], "io"!"writeAll" @ [MyIo.writeAllS] ]]
  bmodule "web" {{
    bfunction "main"("fr", "t") [mainS]
      Init
      [Al n, Al fs, PREmain[_] sched fs * globalSock =?> 1 * globalTree =?> 1
        * strings n globalPages * mallocHeap 0];;

      "fr" <- 0;;
      [Al n, Al fs, PREmain[_] sched fs * globalSock =?> 1 * globalTree =?> 1
        * strings n globalPages * mallocHeap 0]
      While ("fr" < numWorkers) {
        Spawn("web"!"handler", 100)
        [Al n, Al fs, PREmain[_] sched fs * globalSock =?> 1 * globalTree =?> 1
          * strings n globalPages * mallocHeap 0];;
        "fr" <- "fr" + 1
      };;

      "fr" <-- Call "scheduler"!"listen"(port)
      [Al n, Al fs, PREmain[_, R] [| R %in fs |] * sched fs * globalSock =?> 1 * globalTree =?> 1
        * strings n globalPages * mallocHeap 0];;

      "t" <-- Call "web"!"buildDb"(globalPages)
      [Al fs, Al b, Al trailer,
        PREmain[V, R] [| V "fr" %in fs |] * sched fs * globalSock =?> 1 * globalTree =?> 1
          * tree b R * keyValues b * trailer =*> 0 * mallocHeap 0];;

      globalSock *<- "fr";;
      globalTree *<- "t";;
      Exit 50
    end with bfunction "handler"("inbuf", "outbuf", "fr", "n", "p", "len", "len4") [handlerS]
      "inbuf" <-- Call "buffers"!"bmalloc"(inbuf_size)
      [Al fs, PREmain[V, R] R =?>8 bsize * sched fs * globalInv fs * mallocHeap 0];;

      [Al fs, PREmain[V] V "inbuf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0]
      While (0 = 0) {
        "fr" <-- Call "scheduler"!"accept"($[globalSock])
        [Al fs, PREmain[V, R] V "inbuf" =?>8 bsize * [| R %in fs|]
          * sched fs * globalInv fs * mallocHeap 0];;

        "n" <-- Call "io"!"readUntil"("fr", "inbuf", bsize, 13)
        [Al fs, PREmain[V] V "inbuf" =?>8 bsize * [| V "fr" %in fs|]
          * sched fs * globalInv fs * mallocHeap 0];;

        If ("n" = 0) {
          Skip
        } else {
          "p" <-- Call "web"!"contentOf"($[globalTree], "inbuf", bsize)
          [Al fs, Al fr, Al b, Al p, Al trailer,
            PREmain[V, R] V "inbuf" =?>8 bsize
              * [| V "fr" %in fs|]
              * globalSock =*> fr * [| fr %in fs |]
              * globalTree =*> p * tree b p * keyValues b
              * trailer =*> 0
              * [| R = 0 \/ R %in b |]
              * sched fs * mallocHeap 0];;

          If ("p" = 0) {
            Skip
          } else {
            Note [reveal];;

            Assert [Al fs, Al fr, Al b, Al p, Al trailer,
              PREmain[V] V "inbuf" =?>8 bsize * [| V "fr" %in fs|]
                * globalSock =*> fr * [| fr %in fs |]
                * globalTree =*> p * tree b p * keyValues_pick (V "p") b
                * trailer =*> 0
                * [| V "p" %in b |]
                * sched fs * mallocHeap 0];;

            "n" <-* "p";;

            "len" <- 1;;
            "len4" <- 4;;
            [Al fs, Al fr, Al b, Al p, Al trailer, Al q, Al len,
              PREmain[V] V "inbuf" =?>8 bsize * [| V "fr" %in fs|]
                * globalSock =*> fr * [| fr %in fs |]
                * globalTree =*> p * tree b p * keyValues (b %- V "p")
                * q =*> len * (q ^+ $4) =?>8 wordToNat len
                * [| V "p" = q ^+ $4 ^+ len |] * V "p" =*> V "n" * (V "p" ^+ $4) =?>8 wordToNat (V "n")
                * trailer =*> 0
                * [| V "p" %in b |] * [| V "len4" = V "len" ^* $4 |]
                * sched fs * mallocHeap 0]
            While ("len4" < "n") {
              "len" <- "len" * 2;;
              "len4" <- "len" * 4
            };;

            If ("len" < 2) {
              Call "sys"!"abort"()
              [PREonly[_] [| False |] ];;
              Fail
            } else {
              If ("len" >= Npow2 30) {
                Call "sys"!"abort"()
                [PREonly[_] [| False |] ];;
                Fail
              } else {
                "outbuf" <-- Call "buffers"!"bmalloc"("len")
                [Al fs, Al fr, Al b, Al p, Al trailer, Al q, Al len,
                  PREmain[V, R] R =?>8 (wordToNat (V "len") * 4) * [| R <> 0 |]
                    * [| freeable R (wordToNat (V "len")) |] * [| (V "n" <= V "len" ^* $4)%word |]
                    * [| (V "len" < NToW (Npow2 30))%word |]
                    * V "inbuf" =?>8 bsize * [| V "fr" %in fs|]
                    * globalSock =*> fr * [| fr %in fs |]
                    * globalTree =*> p * tree b p * keyValues (b %- V "p")
                    * q =*> len * (q ^+ $4) =?>8 wordToNat len
                    * [| V "p" = q ^+ $4 ^+ len |] * V "p" =*> V "n" * (V "p" ^+ $4) =?>8 wordToNat (V "n")
                    * trailer =*> 0
                    * [| V "p" %in b |]
                    * sched fs * mallocHeap 0];;

                "p" <- "p" + 4;;
                Call "buffers"!"copy"("outbuf", "p", "n")
                [Al fs, Al fr, Al b, Al p, Al trailer, Al Vp,
                  PREmain[V] V "outbuf" =?>8 (wordToNat (V "len") * 4) * [| V "outbuf" <> 0 |]
                    * [| freeable (V "outbuf") (wordToNat (V "len")) |] * [| (V "n" <= V "len" ^* $4)%word |]
                    * [| (V "len" < NToW (Npow2 30))%word |]
                    * V "inbuf" =?>8 bsize * [| V "fr" %in fs|]
                    * globalSock =*> fr * [| fr %in fs |]
                    * globalTree =*> p * tree b p * keyValues_pick Vp b
                    * trailer =*> 0 * [| Vp %in b |]
                    * sched fs * mallocHeap 0];;

                Note [reveal];;

                Call "io"!"writeAll"("fr", "outbuf", 0, "n")
                [Al fs,
                  PREmain[V] V "outbuf" =?>8 (wordToNat (V "len") * 4) * [| V "outbuf" <> 0 |]
                    * [| freeable (V "outbuf") (wordToNat (V "len")) |]
                    * V "inbuf" =?>8 bsize * [| V "fr" %in fs|]
                    * sched fs * globalInv fs * mallocHeap 0];;

                Call "buffers"!"bfree"("outbuf", "len")
                [Al fs,
                  PREmain[V] V "inbuf" =?>8 bsize * [| V "fr" %in fs|]
                    * sched fs * globalInv fs * mallocHeap 0]
              }
            }
          }
        };;

        Call "scheduler"!"close"("fr")
        [Al fs, PREmain[V] V "inbuf" =?>8 bsize
          * sched fs * globalInv fs * mallocHeap 0]
      }
    end with bfunction "buildDb"("p", "len", "db", "key", "value", "vlen") [buildDbS]
      "db" <-- Call "stringdb"!"new"()
      [Al n,
        PRE[V, R] tree empty R * strings n (V "p") * mallocHeap 0
        POST[R'] Ex b, Ex trailer, tree b R' * keyValues b * trailer =*> 0 * mallocHeap 0];;

      "len" <-* "p";;

      [Al n, Al b,
        PRE[V] tree b (V "db") * keyValues b * V "p" =*> V "len" * strings' n (V "p") (V "len") * mallocHeap 0
        POST[R'] Ex b', Ex trailer, tree b' R' * keyValues b' * trailer =*> 0 * mallocHeap 0]
      While ("len" <> 0) {
        "key" <- "p" + 4;;
        "value" <- "key" + "len";;
        "vlen" <-* "value";;
        "p" <- "value" + 4;;
        "p" <- "p" + "vlen";;
        Call "stringdb"!"insert"("db", "key", "len", "value")
        [Al n, Al b,
          PRE[V] tree (b %+ V "value") (V "db") * keyValues (b %+ V "value") * strings n (V "p") * mallocHeap 0
          POST[R'] Ex b', Ex trailer, tree b' R' * keyValues b' * trailer =*> 0 * mallocHeap 0];;

        "len" <-* "p"
      };;

      Return "db"
    end with bfunction "contentOf"("tree", "buf", "len", "newline", "space") [contentOfS]
      If ("len" < 4) {
        (* No "GET " at the beginning. *)
        Return 0
      } else {
        Skip
      };;

      (* Seek forward past "GET ". *)

      Assert [Al b,
        PRE[V] [| (4 <= wordToNat (V "len"))%nat |] * tree b (V "tree")
          * buffer_splitAt 4 (V "buf") (wordToNat (V "len"))
        POST[R] [| R = 0 \/ R %in b |] * tree b (V "tree") * buffer_joinAt 4 (V "buf") (wordToNat (V "len"))];;

      "buf" <- "buf" + 4;;
      "len" <- "len" - 4;;

      (* Find position of line break. *)
      "newline" <-- Call "buffers"!"contains"("buf", "len", 13)
      [Al b,
        PRE[V] tree b (V "tree") * V "buf" =?>8 wordToNat (V "len")
        POST[R] [| R = 0 \/ R %in b |] * tree b (V "tree") * V "buf" =?>8 wordToNat (V "len")];;

      (* Find next position (if any) of a space character, ideally right before "HTTP/1.1". *)
      "space" <-- Call "buffers"!"contains"("buf", "len", " "%char)
      [Al b,
        PRE[V] tree b (V "tree") * V "buf" =?>8 wordToNat (V "len")
        POST[R] [| R = 0 \/ R %in b |] * tree b (V "tree") * V "buf" =?>8 wordToNat (V "len")];;

      If ("space" < "newline") {
        (* OK, this is the space we hoped to find. *)
        Skip
      } else {
        (* Use the newline as the end marker, since no " HTTP/1.1" exists. *)
        "space" <- "newline"
      };;

      If ("space" >= "len") {
        (* Oops, impossible overflow! *)
        Return 0
      } else {
        Skip
      };;

      Assert [Al b,
        PRE[V] [| (wordToNat (V "space") <= wordToNat (V "len"))%nat |] * tree b (V "tree")
          * buffer_splitAt (wordToNat (V "space")) (V "buf") (wordToNat (V "len"))
        POST[R] [| R = 0 \/ R %in b |] * tree b (V "tree")
          * buffer_joinAt (wordToNat (V "space")) (V "buf") (wordToNat (V "len"))];;

      (* Ready to look up in the database. *)
      "newline" <-- Call "stringdb"!"lookup"("tree", "buf", "space")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "newline"
    end
  }}.

Lemma le_bsize : forall w : W,
  w <= natToW bsize
  -> (wordToNat w <= bsize)%nat.
  intros; pre_nomega;
    rewrite wordToNat_natToWord_idempotent in * by apply inbuf_size_upper; assumption.
Qed.

Local Hint Immediate le_bsize.

Lemma inbuf_size_small : (N.of_nat inbuf_size < Npow2 32)%N.
  specialize inbuf_size_upper;  generalize (Npow2 32); intros; nomega.
Qed.

Hint Rewrite Nat2N.inj_mul N2Nat.inj_mul : N.
Lemma le_inbuf_size : natToW 2 <= natToW inbuf_size.
  pre_nomega; rewrite wordToNat_natToWord_idempotent by apply inbuf_size_small;
    rewrite wordToNat_natToWord_idempotent by reflexivity; apply inbuf_size_lower.
Qed.

Local Hint Immediate le_inbuf_size.

Lemma roundTrip_inbuf_size : wordToNat (natToW inbuf_size) = inbuf_size.
  rewrite wordToNat_natToWord_idempotent by apply inbuf_size_small; auto.
Qed.

Lemma roundTrip_bsize : wordToNat (natToW bsize) = bsize.
  rewrite wordToNat_natToWord_idempotent by apply inbuf_size_upper; auto.
Qed.

Hint Rewrite roundTrip_inbuf_size roundTrip_bsize : sepFormula.

Lemma four_in : forall len, len < NToW (Npow2 30)
  -> (wordToNat len * 4)%nat = wordToNat (len ^* $4).
  Transparent goodSize.
  intros; rewrite wordToNat_wmult.
  reflexivity.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  red.
  rewrite Nat2N.inj_mul.
  simpl N.of_nat.
  assert (wordToNat (NToW (Npow2 30)) = N.to_nat (Npow2 30)).
  unfold NToW; rewrite NToWord_nat.
  rewrite wordToNat_natToWord_idempotent.
  reflexivity.
  rewrite N2Nat.id; reflexivity.
  change (Npow2 32) with (Npow2 30 * 4)%N.
  generalize dependent (Npow2 30); intros.
  nomega.
  Opaque goodSize.
Qed.

Hint Rewrite four_in using assumption : sepFormula.

Lemma convert_le : forall u v : W,
  u <= v ^* natToW 4
  -> (wordToNat u <= wordToNat (v ^* natToW 4))%nat.
  intros; nomega.
Qed.

Local Hint Immediate convert_le.

Lemma four_le : forall w : W, (4 <= wordToNat w)%nat
  -> natToW 4 <= w.
  intros; pre_nomega; auto.
Qed.

Local Hint Immediate four_le.

Hint Rewrite wordToNat_wminus using solve [ auto ] : sepFormula.

Lemma wlt_le : forall u v : W, u < v
  -> (wordToNat u <= wordToNat v)%nat.
  intros; nomega.
Qed.

Local Hint Immediate wlt_le.

Ltac t :=
  try match goal with
        | [ |- context[reveal] ] => unfold keyValues_pick
      end;
  try solve [ sep unf hints; auto ];
    unf; unfold localsInvariantMain; post; evaluate hints; descend;
      try (rewrite four_in in * by assumption; match_locals); sep unf hints;
        eauto; try step hints.

Ltac u := solve [ t ].

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
