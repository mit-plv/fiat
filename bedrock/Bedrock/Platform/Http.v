Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Scheduler Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays Bedrock.Platform.Buffers Bedrock.Platform.StringOps Coq.Strings.Ascii Bedrock.Platform.Io.


Definition atoiS := SPEC("buf", "pos", "len") reserving 2
  PRE[V] V "buf" =?>8 wordToNat (V "len")
  POST[R] V "buf" =?>8 wordToNat (V "len").

Definition itoaS := SPEC("n", "buf", "pos", "len") reserving 4
  PRE[V] V "buf" =?>8 wordToNat (V "len")
  POST[R] V "buf" =?>8 wordToNat (V "len").

Section specs.
  Variables sched globalInv : bag -> HProp.

  Definition readRequestGS := SPEC("fr", "buf", "len") reserving 46
    Al fs,
    PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
      * sched fs * globalInv fs * mallocHeap 0
    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
      * sched fs' * globalInv fs' * mallocHeap 0.

  Definition writeResponseGS := SPEC("fr", "buf", "pos", "len") reserving 49
    Al fs,
    PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
      * sched fs * globalInv fs * mallocHeap 0 * [| goodSize (wordToNat (V "len")) |]
    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
      * sched fs' * globalInv fs' * mallocHeap 0.
End specs.

Module Type S.
  Parameters sched globalInv : bag -> HProp.
End S.

Module Make(M : S).
Import M.

Definition readRequestS := readRequestGS sched globalInv.
Definition writeResponseS := writeResponseGS sched globalInv.

Coercion ascii_of_nat : nat >-> ascii.

Definition endOfHeaders := String 13 (String 10 (String 13 (String 10 ""))).
Definition contentLength := "Content-Length: ".
Definition contentLengthLower := "Content-length: ".

Definition nl := String 13 (String 10 "").
Definition preResponse := ("HTTP/1.1 200 OK" ++ nl
  ++ "Connection: close" ++ nl
  ++ "Content-Type: text/xml" ++ nl
  ++ "Server: Bedrock" ++ nl
  ++ "Content-Length: ")%string.

Inductive reveal_buffers : Prop := RevealBuffers.
Local Hint Constructors reveal_buffers.

(* Custom [vcgen] to use StringOps *)
Ltac vcgen_simp :=
  cbv beta iota zeta
   delta [map app imps LabelMap.add Entry Blocks Postcondition VerifCond
         Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_ Structured.If_
         Structured.While_ Goto_ Structured.Call_ IGoto setArgs Reserved
         Formals Precondition importsMap fullImports buildLocals blocks union
         N.add N.succ Datatypes.length N.of_nat fold_left ascii_lt string_lt
         label'_lt LabelKey.compare' LabelKey.compare LabelKey.eq_dec
         LabelMap.find toCmd Seq Instr Diverge Fail Skip Assert_ If_ While_
         Goto Call_ RvImm' Assign' localsInvariant localsInvariantCont regInL
         lvalIn immInR labelIn variableSlot string_eq ascii_eq andb Bool.eqb
         qspecOut ICall_ Structured.ICall_ Assert_ Structured.Assert_
         LabelMap.Raw.find LabelMap.this LabelMap.Raw.add LabelMap.empty
         LabelMap.Raw.empty string_dec ascii_dec string_rec string_rect
         sumbool_rec sumbool_rect ascii_rec ascii_rect Bool.bool_dec bool_rec
         bool_rect eq_rec_r eq_rec eq_rect eq_sym fst snd labl N_of_ascii
         N_of_digits N.compare N.mul Pos.compare Pos.compare_cont Pos.mul
         Pos.add LabelMap.Raw.bal Int.Z_as_Int.gt_le_dec
         Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create ZArith_dec.Z_gt_le_dec
         Int.Z_as_Int.plus Int.Z_as_Int.max LabelMap.Raw.height
         ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add Int.Z_as_Int._0
         Int.Z_as_Int._2 BinInt.Z.max ZArith_dec.Zcompare_rec
         ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
         ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect COperand1 CTest
         COperand2 Pos.succ makeVcs Note_ Note__ IGotoStar_ IGotoStar
         AssertStar_ AssertStar Cond_ Cond
         Wrap.WrapC Wrap.Wrap StringEq StringWrite].

Ltac vcgen :=
  structured_auto vcgen_simp;
  autorewrite with sepFormula in *; simpl in *;
    unfold SepIL.starB, hvarB, hpropB in *; fold hprop in *; refold.

Definition m := bimport [[ "io"!"readSome" @ [readSomeGS sched globalInv],
                           "io"!"writeAll" @ [writeAllGS sched globalInv] ]]
  bmodule "http" {{
    bfunction "atoi"("buf", "pos", "len", "acc", "tmp") [atoiS]
      "acc" <- 0;;

      [PRE[V] V "buf" =?>8 wordToNat (V "len")
       POST[R] V "buf" =?>8 wordToNat (V "len")]
      While ("pos" < "len") {
        Note [reveal_buffers];;
        Assert [Al bs,
          PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
            * [| V "pos" < natToW (length bs) |]%word
          POST[R] V "buf" =?>8 wordToNat (V "len")];;
        "tmp" <-*8 "buf" + "pos";;

        Note [reveal_buffers];;

        If ("tmp" = 13) {
          (* End of header. *)
          Return "acc"
        } else {
          "acc" <- 10 * "acc";;
          "tmp" <- "tmp" - 48;;
          "acc" <- "acc" + "tmp";;
          "pos" <- "pos" + 1
        }
      };;

      Return 0
    end
    with bfunction "itoa"("n", "buf", "pos", "len", "exp", "pow", "i", "j") [itoaS]
      (* Find lowest power of 10 that is > n. *)

      "exp" <- 1;;
      "pow" <- 10;;
      [PRE[V] V "buf" =?>8 wordToNat (V "len")
        POST[R] V "buf" =?>8 wordToNat (V "len")]
      While ("pow" <= "n") {
        "exp" <- "exp" + 1;;
        "pow" <- "pow" * 10
      };;

      (* Loop over outputting digits. *)
      [PRE[V] V "buf" =?>8 wordToNat (V "len")
        POST[R] V "buf" =?>8 wordToNat (V "len")]
      While ("exp" > 0) {
        (* Construct the corresponding power of 10. *)
        "i" <- 1;;
        "pow" <- 1;;
        [PRE[V] V "buf" =?>8 wordToNat (V "len")
          POST[R] V "buf" =?>8 wordToNat (V "len")]
        While ("i" < "exp") {
          "pow" <- "pow" * 10;;
          "i" <- "i" + 1
        };;

        (* Find the highest multiple with [0,9] that is <= n. *)
        "i" <- 9;;
        "j" <- "pow" * 9;;
        [PRE[V] V "buf" =?>8 wordToNat (V "len")
          POST[R] V "buf" =?>8 wordToNat (V "len")]
        While ("j" > "n") {
          "i" <- "i" - 1;;
          "j" <- "pow" * "i"
        };;

        "i" <- "i" + 48;;
        "n" <- "n" - "j";;
        "exp" <- "exp" - 1;;

        Note [reveal_buffers];;
        If ("pos" < "len") {
          Assert [Al bs,
            PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
              * [| V "pos" < natToW (length bs) |]%word
            POST[R] V "buf" =?>8 wordToNat (V "len")];;

          "buf" + "pos" *<-8 "i";;
          "pos" <- "pos" + 1;;
          Note [reveal_buffers]
        } else {
          Skip
        }
      };;

      Return "pos"
    end
    with bfunction "readRequest"("fr", "buf", "len", "pos", "tmp", "endHeaders", "clen", "matched") [readRequestS]
      "pos" <- 0;;

      [Al fs,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs' * globalInv fs' * mallocHeap 0]
      While ("pos" <= "len") {
        (* Check if we yet received the "\r\n\r\n" boundary. *)
        "endHeaders" <- 0;;

        [Al fs,
          PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
            * sched fs * globalInv fs * mallocHeap 0 * [| V "pos" <= V "len" |]%word
          POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
            * sched fs' * globalInv fs' * mallocHeap 0]
        While ("endHeaders" < "pos") {
          Note [reveal_buffers];;

          StringEq "buf" "len" "endHeaders" "matched" endOfHeaders
          (fun fs V => [| V "fr" %in fs |] * sched fs * globalInv fs * mallocHeap 0
            * [| V "pos" <= V "len" |]%word)%Sep
          (fun _ fs V _ => Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
            * sched fs' * globalInv fs' * mallocHeap 0)%Sep;;

          Note [reveal_buffers];;

          If ("matched" = 0) {
            "endHeaders" <- "endHeaders" + 1
          } else {
            (* We have received all the headers.  Now find the Content-Length. *)
            "clen" <- 0;;

            [Al fs,
              PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
                * sched fs * globalInv fs * mallocHeap 0 * [| V "pos" <= V "len" |]%word
              POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                * sched fs' * globalInv fs' * mallocHeap 0]
            While ("clen" < "pos") {
              Note [reveal_buffers];;

              StringEq "buf" "len" "clen" "matched" contentLength
              (fun fs V => [| V "fr" %in fs |] * sched fs * globalInv fs * mallocHeap 0
                * [| V "pos" <= V "len" |]%word)%Sep
              (fun _ fs V _ => Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                * sched fs' * globalInv fs' * mallocHeap 0)%Sep;;

              If ("matched" = 0) {
                Note [reveal_buffers];;

                StringEq "buf" "len" "clen" "matched" contentLengthLower
                (fun fs V => [| V "fr" %in fs |] * sched fs * globalInv fs * mallocHeap 0
                  * [| V "pos" <= V "len" |]%word)%Sep
                (fun _ fs V _ => Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                  * sched fs' * globalInv fs' * mallocHeap 0)%Sep
              } else {
                Skip
              };;

              Note [reveal_buffers];;

              If ("matched" = 0) {
                "clen" <- "clen" + 1
              } else {
                (* Now extract the length and use it to be sure we read all body data. *)
                "clen" <- "clen" + String.length contentLength;;
                "clen" <-- Call "http"!"atoi"("buf", "clen", "len")
                [Al fs,
                  PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
                    * sched fs * globalInv fs * mallocHeap 0
                  POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                    * sched fs' * globalInv fs' * mallocHeap 0];;

                (* Calculate total request length. *)
                "endHeaders" <- "endHeaders" + 4;;
                "clen" <- "clen" + "endHeaders";;

                If ("clen" > "len") {
                  Return 0
                } else {
                  Skip
                };;

                [Al fs,
                  PRE[V] [| V "clen" <= V "len" |]%word
                    * [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
                    * sched fs * globalInv fs * mallocHeap 0
                  POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                    * sched fs' * globalInv fs' * mallocHeap 0]
                While ("pos" < "clen") {
                  "matched" <- "len" - "pos";;
                  "tmp" <-- Call "io"!"readSome"("fr", "buf", "pos", "matched")
                  [Al fs,
                    PRE[V] [| V "clen" <= V "len" |]%word * [| V "matched" = V "len" ^- V "pos" |]
                      * [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
                      * sched fs * globalInv fs * mallocHeap 0
                    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                      * sched fs' * globalInv fs' * mallocHeap 0];;

                  If ("tmp" = 0) {
                    Return 0
                  } else {
                    If ("tmp" <= "matched") {
                      "pos" <- "pos" + "tmp"
                    } else {
                      Skip
                    }
                  }
                };;

                (* Loop filling in spaces for remaining characters. *)
                [Al fs,
                  PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
                    * sched fs * globalInv fs * mallocHeap 0
                  POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                    * sched fs' * globalInv fs' * mallocHeap 0]
                While ("pos" < "len") {
                  Note [reveal_buffers];;

                  Assert [Al fs, Al bs,
                    PRE[V] [| V "fr" %in fs |] * array8 bs (V "buf")
                      * [| length bs = wordToNat (V "len") |]
                      * [| V "pos" < natToW (length bs) |]%word
                      * sched fs * globalInv fs * mallocHeap 0
                    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                      * sched fs' * globalInv fs' * mallocHeap 0];;

                  "buf" + "pos" *<-8 32;;
                  "pos" <- "pos" + 1;;
                  Note [reveal_buffers]
                };;

                Return "endHeaders"
              }
            }
          }
        };;

        (* No match so far.  Read another segment. *)
        "matched" <- "len" - "pos";;
        "endHeaders" <-- Call "io"!"readSome"("fr", "buf", "pos", "matched")
        [Al fs,
          PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
            * sched fs * globalInv fs * mallocHeap 0
          POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
            * sched fs' * globalInv fs' * mallocHeap 0];;

        Note [reveal_buffers];;

        If ("endHeaders" = 0) {
          Return 0
        } else {
          If ("endHeaders" <= "matched") {
            "pos" <- "pos" + "endHeaders"
          } else {
            Skip
          }
        }
      };;

      Return 0
    end
    with bfunction "writeResponse"("fr", "buf", "pos", "len", "opos", "overflowed") [writeResponseS]
      (* We will use the _end_ of the buffer to store the headers, to avoid copying payload. *)

      "opos" <- "pos";;
      If ("opos" > "len") {
        Return 0
      } else {
        Skip
      };;

      Note [reveal_buffers];;
      StringWrite "buf" "len" "opos" "overflowed" preResponse
      (fun fs V => [| V "fr" %in fs |] * sched fs * globalInv fs * mallocHeap 0
        * [| goodSize (wordToNat (V "len")) |])%Sep
      (fun _ fs V _ => Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
        * sched fs' * globalInv fs' * mallocHeap 0)%Sep;;
      Note [reveal_buffers];;

      "opos" <-- Call "http"!"itoa"("pos", "buf", "opos", "len")
      [Al fs,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs * globalInv fs * mallocHeap 0
          * [| goodSize (wordToNat (V "len")) |]
        POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs' * globalInv fs' * mallocHeap 0];;

      If ("opos" > "len") {
        Return 0
      } else {
        Skip
      };;

      Note [reveal_buffers];;
      StringWrite "buf" "len" "opos" "overflowed" endOfHeaders
      (fun fs V => [| V "fr" %in fs |] * sched fs * globalInv fs * mallocHeap 0
        * [| goodSize (wordToNat (V "len")) |])%Sep
      (fun _ fs V _ => Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
        * sched fs' * globalInv fs' * mallocHeap 0)%Sep;;
      Note [reveal_buffers];;

      If ("overflowed" = 1) {
        Return 0
      } else {
        (* Write headers. *)
        If ("opos" < "pos") {
          (* Shouldn't be possible. :( *)
          Return 0
        } else {
          "opos" <- "opos" - "pos";;
          Call "io"!"writeAll"("fr", "buf", "pos", "opos")
          [Al fs,
            PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
              * sched fs * globalInv fs * mallocHeap 0
              * [| goodSize (wordToNat (V "len")) |]
            POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
              * sched fs' * globalInv fs' * mallocHeap 0];;

          If ("len" < "pos") {
            (* Shouldn't be possible. :( *)
            Return 0
          } else {
            Call "io"!"writeAll"("fr", "buf", 0, "pos")
            [Al fs,
              PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
                * sched fs * globalInv fs * mallocHeap 0
                * [| goodSize (wordToNat (V "len")) |]
              POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len")
                * sched fs' * globalInv fs' * mallocHeap 0];;
            Return 0
          }
        }
      }
    end
  }}.

Lemma in_bounds : forall (pos len : W) n,
  pos < len
  -> n = wordToNat len
  -> pos < natToW n.
  intros; subst; rewrite natToW_wordToNat; auto.
Qed.

Local Hint Immediate in_bounds.

Lemma simplify_arith : forall pos len : W,
  (exists clen : W, pos < clen
    /\ clen <= len)
  -> wordToNat pos + wordToNat (len ^- pos) = wordToNat len.
  post; pre_nomega; rewrite wordToNat_wminus; nomega.
Qed.

Hint Rewrite simplify_arith using solve [ eauto 3 ] : sepFormula.

Lemma simplify_arith' : forall pos len : W,
  pos <= len
  -> wordToNat pos + wordToNat (len ^- pos) = wordToNat len.
  post; nomega.
Qed.

Hint Rewrite simplify_arith' using assumption : sepFormula.

Hint Resolve incl_mem.

Lemma size_ok : forall n (opos len : W),
  n = wordToNat len
  -> opos <= len
  -> (wordToNat opos <= n)%nat.
  intros; nomega.
Qed.

Local Hint Immediate size_ok.

Local Hint Extern 1 (goodSize _) => cbv beta; congruence.

Lemma lt_le_trans : forall a b c : W,
  a < b
  -> b <= c
  -> a <= c.
  intros; nomega.
Qed.

Hint Immediate lt_le_trans.

Ltac easy := intuition congruence.

Ltac prove_irrel := intros;
  repeat match goal with
           | [ V : vals |- _ ] =>
             match goal with
               | [ |- context[V ?x] ] => change (V x) with (sel V x)
             end
         end;
  match goal with
    | [ H : forall x : string, _ |- _ ] =>
      match type of H with
        | context[sel] =>
          repeat rewrite H by congruence
      end
  end; reflexivity || apply Himp_refl.

Ltac t' :=
  try match goal with
        | [ |- context[reveal_buffers] ] => post; unfold buffer in *
      end;
  try match goal with
        | [ _ : context[match ?st with pair _ _ => _ end] |- _ ] => destruct st; simpl in *
      end; try abstract (sep_auto; eauto);
  post; evaluate auto_ext; try congruence; descend;
  try match_locals; repeat (step auto_ext; descend); eauto.

Ltac t := easy || prove_irrel || t'.

Local Hint Extern 1 (@eq W _ _) => words.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
