Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Arrays8.


Definition bytes (capacity : W) (bs : list B) (p : W) : HProp :=
  (Ex capacity', Ex junk,
   [| capacity = capacity' ^* $4 |]
   * [| length bs + length junk = wordToNat capacity' * 4 |]%nat
   * (p ==*> capacity', $(length bs))
   * array8 (bs ++ junk) (p ^+ $8)
   * [| p <> 0 |]
   * [| freeable p (2 + wordToNat capacity') |]
   * [| goodSize (2 + wordToNat capacity' * 4) |])%Sep.

Definition newS := SPEC("extra_stack", "capacity") reserving 7
  PRE[V] [| goodSize (2 + wordToNat (V "capacity") * 4) |] * mallocHeap 0
  POST[R] bytes (V "capacity" ^* $4) nil R * mallocHeap 0.

Definition deleteS := SPEC("extra_stack", "self") reserving 6
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * mallocHeap 0
  POST[R] [| R = $0 |] * mallocHeap 0.

Definition pushS := SPEC("extra_stack", "self", "byte") reserving 0
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * [| length bs + 1 <= wordToNat capacity |]%nat * mallocHeap 0
  POST[R] [| R = $0 |] * bytes capacity (bs ++ WtoB (V "byte") :: nil) (V "self") * mallocHeap 0.

Definition putS := SPEC("extra_stack", "self", "index", "byte") reserving 0
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * [| wordToNat (V "index") < length bs |]%nat * mallocHeap 0
  POST[R] [| R = $0 |] * bytes capacity (PutAt bs (wordToNat (V "index")) (WtoB (V "byte"))) (V "self") * mallocHeap 0.

Definition getS := SPEC("extra_stack", "self", "index") reserving 0
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * [| wordToNat (V "index") < length bs |]%nat * mallocHeap 0
  POST[R] [| R = BtoW (nth (wordToNat (V "index")) bs (wzero _)) |] * bytes capacity bs (V "self") * mallocHeap 0.

Definition copyS := SPEC("extra_stack", "self") reserving 13
  Al capacity, Al bs,
  PRE[V] bytes capacity bs (V "self") * mallocHeap 0
  POST[R] bytes capacity bs R * bytes capacity bs (V "self") * mallocHeap 0.

Inductive unfold_bytes := UnfoldBytes.
Hint Constructors unfold_bytes.

Definition array8wc bs p (capacity : W) := array8 bs p.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ByteString" {{
    bfunction "new"("extra_stack", "capacity") [newS]
      "extra_stack" <- 2 + "capacity";;
      "extra_stack" <-- Call "malloc"!"malloc"(0, "extra_stack")
      [PRE[V, R] R =?> (2 + wordToNat (V "capacity")) * [| R <> 0 |] * [| freeable R (2 + wordToNat (V "capacity")) |] * [| goodSize (2 + wordToNat (V "capacity") * 4) |]
       POST[R'] bytes (V "capacity" ^* $4) nil R'];;

      "extra_stack" *<- "capacity";;
      "extra_stack" + 4 *<- 0;;
      Return "extra_stack"
    end

    with bfunction "delete"("extra_stack", "self") [deleteS]
       Note [unfold_bytes];;
       Assert [Al capacity', Al bs, Al junk,
               PRE[V] [| length bs + length junk = wordToNat capacity' * 4 |]%nat
                 * (V "self" ==*> capacity', $(length bs))
                 * array8wc (bs ++ junk) (V "self" ^+ $8) capacity'
                 * [| V "self" <> 0 |]
                 * [| freeable (V "self") (2 + wordToNat capacity') |]
                 * [| goodSize (2 + wordToNat capacity') |]
                 * mallocHeap 0
               POST[R] [| R = $0 |] * mallocHeap 0 ];;
       "extra_stack" <-* "self";;
       "extra_stack" <- 2 + "extra_stack";;
       Call "malloc"!"free"(0, "self", "extra_stack")
       [PRE[_] Emp
        POST[R] [| R = $0 |] ];;
       Return 0
    end

    with bfunction "push"("extra_stack", "self", "byte") [pushS]
       Note [unfold_bytes];;
       "extra_stack" <-* "self" + 4;;
       "self" + 4 *<- "extra_stack" + 1;;

       Assert [Al bs,
               PRE[V] array8 bs (V "self" ^+ $8) * [| V "extra_stack" < natToW (length bs) |]%word
               POST[R] [| R = $0 |] * array8 (Array8.upd bs (V "extra_stack") (WtoB (V "byte"))) (V "self" ^+ $8)];;
       "self" <- "self" + 8;;
       "self" + "extra_stack" *<-8 "byte";;
       Return 0
    end

    with bfunction "put"("extra_stack", "self", "index", "byte") [putS]
       Note [unfold_bytes];;
       Assert [Al bs,
               PRE[V] array8 bs (V "self" ^+ $8) * [| V "index" < natToW (length bs) |]%word
               POST[R] [| R = $0 |] * array8 (Array8.upd bs (V "index") (WtoB (V "byte"))) (V "self" ^+ $8)];;
       "self" <- "self" + 8;;
       "self" + "index" *<-8 "byte";;
       Return 0
    end

    with bfunction "get"("extra_stack", "self", "index") [getS]
       Note [unfold_bytes];;
       Assert [Al bs,
               PRE[V] array8 bs (V "self" ^+ $8) * [| V "index" < natToW (length bs) |]%word
               POST[R] [| R = BtoW (Array8.sel bs (V "index")) |] * array8 bs (V "self" ^+ $8)];;
       "self" <- "self" + 8;;
       "self" <-*8 "self" + "index";;
       Return "self"
    end

    with bfunction "copy"("extra_stack", "self", "capacity", "used", "other") [copyS]
      Note [unfold_bytes];;
      "capacity" <-* "self";;
      "used" <-* "self" + 4;;
      Assert [Al bs,
              PRE[V] bytes (V "capacity" ^* $4) bs (V "self")
                     * [| wordToNat (V "used") = length bs |]
                     * [| length bs <= wordToNat (V "capacity") * 4 |]%nat
                     * [| goodSize (S (S (wordToNat (V "capacity") * 4))) |]
                     * mallocHeap 0
              POST[R] bytes (V "capacity" ^* $4) bs R * bytes (V "capacity" ^* $4) bs (V "self") * mallocHeap 0];;

      "other" <-- Call "ByteString"!"new"("extra_stack", "capacity")
      [Al capacity, Al bs,
       PRE[V, R] bytes capacity nil R * bytes capacity bs (V "self")
                 * [| wordToNat (V "used") = length bs |]
                 * [| length bs <= wordToNat capacity |]%nat
                 * [| goodSize (wordToNat capacity) |]
                 * mallocHeap 0
       POST[R'] bytes capacity bs R' * bytes capacity bs (V "self") * mallocHeap 0];;

      "capacity" <- 0;;

      [Al capacity, Al bs1, Al bs2,
       PRE[V] bytes capacity bs1 (V "other") * bytes capacity (bs1 ++ bs2) (V "self")
                 * [| wordToNat (V "used") = length bs1 + length bs2 |]%nat
                 * [| length bs1 + length bs2 <= wordToNat capacity |]%nat
                 * [| goodSize (wordToNat capacity) |]
                 * [| wordToNat (V "capacity") = length bs1 |]
                 * mallocHeap 0
       POST[R] bytes capacity (bs1 ++ bs2) R * bytes capacity (bs1 ++ bs2) (V "self") * mallocHeap 0]
      While ("capacity" < "used") {
        "extra_stack" <-- Call "ByteString"!"get"("extra_stack", "self", "capacity")
        [Al capacity, Al bs1, Al b, Al bs2,
         PRE[V, R] bytes capacity bs1 (V "other") * bytes capacity (bs1 ++ b :: bs2) (V "self")
                   * [| wordToNat (V "used") = length bs1 + S (length bs2) |]%nat
                   * [| length bs1 + S (length bs2) <= wordToNat capacity |]%nat
                   * [| goodSize (wordToNat capacity) |]
                   * [| R = BtoW b |]
                   * [| wordToNat (V "capacity") = length bs1 |]
                   * mallocHeap 0
         POST[R'] bytes capacity (bs1 ++ b :: bs2) R' * bytes capacity (bs1 ++ b :: bs2) (V "self") * mallocHeap 0];;

        Call "ByteString"!"push"("extra_stack", "other", "extra_stack")
        [Al capacity, Al bs1, Al b, Al bs2,
         PRE[V] bytes capacity (bs1 ++ b :: nil) (V "other") * bytes capacity (bs1 ++ b :: bs2) (V "self")
                   * [| wordToNat (V "used") = length bs1 + S (length bs2) |]%nat
                   * [| length bs1 + S (length bs2) <= wordToNat capacity |]%nat
                   * [| goodSize (wordToNat capacity) |]
                   * [| wordToNat (V "capacity") = length bs1 |]
                   * mallocHeap 0
         POST[R] bytes capacity (bs1 ++ b :: bs2) R * bytes capacity (bs1 ++ b :: bs2) (V "self") * mallocHeap 0];;

        "capacity" <- "capacity" + 1
      };;
      
      Return "other"
    end
  }}.

Lemma goodSize_plus_eq : forall (w : W) (n : nat),
    goodSize (n + wordToNat w)
    -> wordToNat (natToW n ^+ w) = n + wordToNat w.
Proof.
  intros.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent; auto.
  change (goodSize n); eauto.
  rewrite wordToNat_natToWord_idempotent; auto.
  change (goodSize n); eauto.
Qed.

Lemma goodSize1 : forall n,
    goodSize (S (S (n * 4)))
    -> goodSize (S (S n)).
Proof.
  intros.
  eapply goodSize_weaken; eauto.
Qed.

Lemma goodSize1' : forall n,
    goodSize (S (S (n * 4)))
    -> goodSize (2 + n).
Proof.
  intros.
  eapply goodSize_weaken; eauto.
Qed.

Lemma goodSize2 : forall n,
    goodSize (S (S (n * 4)))
    -> goodSize (n * 4).
Proof.
  intros.
  eapply goodSize_weaken; eauto.
Qed.

Hint Immediate goodSize1 goodSize1' goodSize2.

Hint Rewrite goodSize_plus_eq using (assumption || (apply goodSize1; assumption) || (apply goodSize2; assumption)) : sepFormula.

Lemma goodSize_plus_le : forall (w : W) (n : nat),
    goodSize (n + wordToNat w)
    -> natToW n <= natToW n ^+ w.
Proof.
  intros.
  pre_nomega.
  autorewrite with sepFormula.
  rewrite wordToNat_natToWord_idempotent; auto.
  change (goodSize n); eauto.
Qed.

Hint Resolve goodSize_plus_le.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma welcome_bytes : forall (p p' : W) capacity,
    p <> 0
    -> freeable p (2 + wordToNat capacity)
    -> goodSize (2 + wordToNat capacity * 4)
    -> p = p'
    -> allocated p 8 (wordToNat capacity) * (p =*> capacity * (p ^+ $4) =*> 0)
       ===> bytes (capacity ^* $4) nil p'.
Proof.
  intros; subst.
  eapply Himp_trans.
  eapply Himp_star_frame.
  eapply Himp_trans.
  apply allocated_shift_base.
  3: apply materialize_array8.
  instantiate (1 := p' ^+ $8).
  words.
  reflexivity.
  apply Himp_refl.
  unfold bytes.
  sepLemma.
Qed.

Hint Extern 1 (himp _ _ _) => apply welcome_bytes.

Lemma farewell_bytes : forall bs junk p (w : W),
    length bs + length junk = wordToNat w * 4
    -> array8wc (bs ++ junk) (p ^+ $8) w
    ===> allocated p 8 (wordToNat w).
Proof.
  intros.
  eapply Himp_trans.
  apply decomission_array8.
  rewrite app_length.
  eassumption.
  apply allocated_shift_base; auto.
  words.
Qed.

Definition hints : TacPackage.
  prepare farewell_bytes tt.
Defined.

Lemma push_bound : forall (bs junk : list B) n,
    (length bs + 1 <= n)%nat
    -> length bs + length junk = n
    -> goodSize n
    -> natToW (length bs) < natToW (length bs + length junk).
Proof.
  intros.
  apply lt_goodSize.
  omega.
  eapply goodSize_weaken; eauto.
  eapply goodSize_weaken; eauto.
Qed.

Hint Extern 1 (_ < natToW (length _ + length _)) =>
  autorewrite with sepFormula in *; eapply push_bound.

Lemma goodSize_times4 : forall w : W,
    goodSize (wordToNat w * 4)
    -> wordToNat (w ^* $4) = wordToNat w * 4.
Proof.
  intros.
  rewrite wordToNat_wmult; auto.
Qed.

Hint Rewrite goodSize_times4 using (assumption || (apply goodSize2; assumption)) : sepFormula.

Hint Rewrite app_length : sepFormula.

Lemma do_push'' : forall junk b bs,
    (length junk > 0)%nat
    -> Array8.updN (bs ++ junk) (length bs) b
    = ((bs ++ b :: nil) ++ tl junk).
Proof.
  induction bs; simpl; intuition.
  destruct junk; simpl in *; auto.
  omega.
Qed.

Lemma do_push' : forall bs junk b n,
    length bs + length junk = n
    -> (length bs + 1 <= n)%nat
    -> goodSize n
    -> Array8.upd (bs ++ junk) (length bs) b
    = ((bs ++ b :: nil) ++ tl junk).
Proof.
  intros.
  unfold Array8.upd.
  rewrite wordToNat_natToWord_idempotent.
  apply do_push''.
  destruct junk; simpl in *; omega.
  change (goodSize (length bs)).
  eapply goodSize_weaken; eauto.
Qed.

Lemma do_push : forall bs junk b n p,
    length bs + length junk = n
    -> (length bs + 1 <= n)%nat
    -> goodSize n
    -> array8 (Array8.upd (bs ++ junk) (length bs) b) p
       ===> array8 (bs ++ b :: tl junk) p.
Proof.
  intros.
  rewrite <- DepList.pf_list_simpl.
  erewrite do_push'; eauto.
  apply Himp_refl.
Qed.

Hint Extern 1 (himp _ (array8 (Array8.upd (_ ++ _) _ _) _) _) =>
  autorewrite with sepFormula in *; eapply do_push.

Lemma length_tl : forall A (ls : list A),
    (length ls > 0)%nat
    -> length (tl ls) = length ls - 1.
Proof.
  destruct ls; simpl; omega.
Qed.

Hint Rewrite length_tl using omega : sepFormula.

Hint Extern 1 (@eq nat _ _) => repeat autorewrite with sepFormula in *; omega.

Lemma put_bound : forall i (n m : nat) k,
    (wordToNat i < n)%nat
    -> n + m = k
    -> goodSize k
    -> i < natToW (n + m).
Proof.
  intros; subst.
  replace i with (natToW (wordToNat i)) by apply natToWord_wordToNat.
  apply lt_goodSize.
  auto.
  eapply goodSize_weaken; eauto.
  auto.
Qed.

Hint Resolve put_bound.

Lemma length_PutAt : forall A (ls : list A) n v,
    length (PutAt ls n v) = length ls.
Proof.
  induction ls; destruct n; simpl; intuition.
Qed.

Hint Rewrite length_PutAt : sepFormula.

Lemma PutAt_updN : forall junk b bs i,
    (i < length bs)%nat
    -> Array8.updN (bs ++ junk) i b
    = PutAt bs i b ++ junk.
Proof.
  induction bs; simpl; intuition.
  destruct i; simpl; intuition.
  rewrite IHbs; auto.
Qed.

Lemma PutAt_upd : forall i bs junk b,
    (wordToNat i < length bs)%nat
    -> Array8.upd (bs ++ junk) i b
    = PutAt bs (wordToNat i) b ++ junk.
Proof.
  intros.
  apply PutAt_updN; auto.
Qed.

Lemma PutAt_upd_array8 : forall i bs junk b p,
    (wordToNat i < length bs)%nat
    -> array8 (Array8.upd (bs ++ junk) i b) p
       ===> array8 (PutAt bs (wordToNat i) b ++ junk) p.
Proof.
  intros.
  rewrite PutAt_upd; auto.
  apply Himp_refl.
Qed.

Hint Extern 1 (himp _ _ (array8 (PutAt _ _ _ ++ _) _)) => apply PutAt_upd_array8.

Lemma get_okN : forall junk bs i,
    (i < length bs)%nat
    -> Array8.selN (bs ++ junk) i = nth i bs (wzero _).
Proof.
  induction bs; destruct i; simpl; intuition.
Qed.

Lemma get_ok : forall r bs junk i,
    r = BtoW (Array8.sel (bs ++ junk) i)
    -> (wordToNat i < length bs)%nat
    -> r = BtoW (nth (wordToNat i) bs (wzero _)).
Proof.
  intros; subst.
  unfold Array8.sel.
  rewrite get_okN; auto.
Qed.

Hint Immediate get_ok.

Lemma roundtrip_bs : forall n m k,
    n + m = k
    -> goodSize (2 + k)
    -> wordToNat (natToW n) = n.
Proof.
  intros; subst.
  apply wordToNat_natToWord_idempotent.
  change (goodSize n).
  eapply goodSize_weaken; eauto.
Qed.

Hint Immediate roundtrip_bs.

Hint Rewrite DepList.pf_list_simpl : sepFormula.

Lemma copy_bound : forall (c u : W) n,
    c < u
    -> wordToNat u = n
    -> (wordToNat c < n)%nat.
Proof.
  intros; subst.
  nomega.
Qed.

Hint Immediate copy_bound.

Lemma loop_inc : forall (w : W) n m k,
    wordToNat w = n
    -> (n + S m <= k)%nat
    -> goodSize k
    -> wordToNat (w ^+ $1) = n + 1.
Proof.
  intros; subst.
  rewrite wordToNat_wplus; auto.
  eapply goodSize_weaken; eauto.
  change (wordToNat ($ 1)) with 1.
  eauto.
Qed.

Hint Immediate loop_inc.

Lemma copy_loop' : forall bs2 bs1,
    (length bs2 > 0)%nat
    -> bs1 ++ nth (length bs1) (bs1 ++ bs2) (wzero 8) :: tl bs2 = bs1 ++ bs2.
Proof.
  induction bs1; simpl; intuition.
  destruct bs2; simpl in *; auto.
  omega.
Qed.

Lemma copy_loop : forall bs2 bs1 (c u : W),
    c < u
    -> wordToNat u = length bs1 + length bs2
    -> wordToNat c = length bs1
    -> bs1 ++ nth (wordToNat c) (bs1 ++ bs2) (wzero 8) :: tl bs2 = bs1 ++ bs2.
Proof.
  intros.
  rewrite H1.
  apply copy_loop'.
  nomega.
Qed.

Lemma length_tl' : forall (c u : W) A (ls : list A) n,
    c < u
    -> wordToNat c = n
    -> wordToNat u = n + length ls
    -> S (length (tl ls)) = length ls.
Proof.
  intros.
  assert (length ls > 0)%nat by nomega.
  rewrite length_tl; auto.
Qed.

Hint Rewrite length_tl' using assumption : sepFormula.

Hint Extern 1 (@eq nat _ _) => erewrite length_tl' by eassumption.
Hint Extern 1 (_ <= _)%nat => erewrite length_tl' by eassumption.

Lemma BtoW_WtoB : forall w b,
    w = BtoW b
    -> WtoB w = b.
Proof.
  intros; subst.
  unfold WtoB, BtoW.
  apply split1_combine.
Qed.

Lemma copy_final : forall capacity bs1 o bs2 r (u c : W),
    wordToNat c = length bs1
    -> wordToNat u = length bs1 + length bs2
    -> u <= c
    -> o = r
    -> bytes capacity bs1 o ===> bytes capacity (bs1 ++ bs2) r.
Proof.
  intros; subst.
  destruct bs2; simpl in *.
  rewrite <- app_nil_end.
  apply Himp_refl.
  nomega.
Qed.

Hint Extern 1 (himp _ _ _) => eapply copy_final.

Ltac unifyLocals :=
  match goal with
  | [ _ : interp _ (![?P1] ?x) |- interp _ (![?P2] ?x) ] =>
    match P1 with
    | context[locals _ ?vs1 ?y _] =>
      match P2 with
      | context[locals _ ?vs2 y _] => unify vs1 vs2; descend
      end
    end
  | [ |- interp _ (![?P1] ?x ---> ![?P2] ?x)%PropX ] =>
    match P1 with
    | context[locals ?y ?vs1 _ _] =>
      match P2 with
      | context[locals y ?vs2 _ _] => unify vs1 vs2; descend
      end
    end
  end.

Ltac prestep :=
  match goal with
  | [ |- interp _ (![?P] _ ---> ![?Q] _)%PropX ] =>
    match P with
    | context[Regs ?s ?r = ?v] =>
      match Q with
      | context[Regs s r = ?u] => unify u v
      end
    end
  | _ => erewrite copy_loop by eassumption
  | _ => erewrite BtoW_WtoB by eassumption
  end.

Ltac t := try solve [ enterFunction ];
  try match goal with
      | [ |- context[unfold_bytes] ] => unfold bytes, array8wc
      end;
  post; evaluate hints; descend; try unifyLocals; repeat (try prestep; step hints; descend);
  eauto; descend; eauto.

Theorem ok : moduleOk m.
Proof.
  vcgen; abstract t.
Qed.
