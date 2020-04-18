Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.Facade.examples.ArrayTupleF.
Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleSeqF.
Require Import Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.TuplesF.


Section tuples0.
  Open Scope Sep_scope.

  Definition tuples0 (len : W) (ts : tuples) (p : W) :=
    Ex ls, Ex lsp, (p ==*> len, lsp) * lseq ls lsp * [| EnsembleIndexedListEquivalence ts ls |]
      * [| $2 <= len |]
      * [| forall t, IndexedEnsemble_In ts t -> length t = wordToNat len |].
End tuples0.

Theorem tuples0_Equiv : forall len ts1 ts2 p,
  Equiv ts1 ts2
  -> tuples0 len ts1 p ===> tuples0 len ts2 p.
Proof.
  unfold tuples0; sepLemma.
  firstorder idtac.
  firstorder idtac.
Qed.

Definition Empty : tuples := fun _ => False.

Definition newS := SPEC("extra_stack", "len") reserving 11
  PRE[V] [| V "len" >= $2 |] * mallocHeap 0
  POST[R] tuples0 (V "len") Empty R * mallocHeap 0.

Definition insertS := SPEC("extra_stack", "self", "tup") reserving 12
  Al len, Al ts, Al t, Al ts',
  PRE[V] tuples0 len ts (V "self") * tuple t (V "tup") * [| length t = wordToNat len |] * mallocHeap 0
         * [| insert ts t ts' |]
  POST[R] [| R = $0 |] * tuples0 len ts' (V "self") * mallocHeap 0.

Definition enumerateS := SPEC("extra_stack", "self") reserving 22
  Al len, Al ts,
  PRE[V] tuples0 len ts (V "self") * mallocHeap 0
  POST[R] tuples0 len ts (V "self") * Ex ls, lseq ls R * [| EnsembleIndexedListEquivalence ts ls |] * mallocHeap 0.

Definition enumerateIntoS := SPEC("extra_stack", "self", "ls") reserving 23
  Al len, Al ts, Al ls,
  PRE[V] tuples0 len ts (V "self") * lseq ls (V "ls") * mallocHeap 0
  POST[R] [| R = $0 |] * tuples0 len ts (V "self") * Ex ls', lseq (ls' ++ ls) (V "ls") * [| EnsembleIndexedListEquivalence ts ls' |] * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "TupleList"!"new" @ [TupleListF.newS], "TupleList"!"push" @ [TupleListF.pushS],
                           "TupleList"!"copy" @ [TupleListF.copyS], "TupleList"!"copyAppend" @ [TupleListF.copyAppendS] ]]
  bmodule "Tuples0" {{
    bfunction "new"("extra_stack", "len", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0 * [| (V "len" >= $2)%word |]
       POST[R'] tuples0 (V "len") Empty R' * mallocHeap 0];;

      "extra_stack" <-- Call "TupleList"!"new"("extra_stack")
      [PRE[V, R] V "x" =?> 2 * [| V "x" <> 0 |] * [| freeable (V "x") 2 |] * mallocHeap 0 * [| (V "len" >= $2)%word |]
         * lseq nil R
       POST[R'] tuples0 (V "len") Empty R' * mallocHeap 0];;

      "x" *<- "len";;
      "x" + 4 *<- "extra_stack";;
      Return "x"
    end

    with bfunction "insert"("extra_stack", "self", "tup") [insertS]
      "self" <-* "self" + 4;;
      "self" <-- Call "TupleList"!"push"("extra_stack", "self", "tup")
      [PRE[_] Emp
       POST[R] [| R = $0 |] ];;

      Return 0
    end

    with bfunction "enumerate"("extra_stack", "self") [enumerateS]
      "extra_stack" <-* "self";;
      "self" <-* "self" + 4;;
      "self" <-- Call "TupleList"!"copy"("extra_stack", "self", "extra_stack")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;

      Return "self"
    end

    with bfunction "enumerateInto"("extra_stack", "self", "ls") [enumerateIntoS]
      "extra_stack" <-* "self";;
      "self" <-* "self" + 4;;
      "self" <-- Call "TupleList"!"copyAppend"("extra_stack", "self", "ls", "extra_stack")
      [PRE[_] Emp
       POST[R] [| R = $0 |] ];;

      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Local Hint Constructors NoDup.

Lemma Empty_nil : EnsembleIndexedListEquivalence Empty nil.
Proof.
  hnf; intuition.
  exists 0.
  hnf; destruct 1.
  hnf.
  exists nil.
  simpl; intuition.
Qed.

Hint Resolve Empty_nil.

Lemma natToW_wordToNat : forall w : W,
  natToW (wordToNat w) = w.
Proof.
  intros; apply natToWord_wordToNat.
Qed.

Hint Rewrite natToW_wordToNat : sepFormula.

Hint Extern 1 (_ = wordToNat _) =>
  match goal with
  | [ H : IndexedEnsemble_In Empty _ |- _] => destruct H as [ ? [ ] ]
  end.

Lemma fresh_Empty : UnConstrFreshIdx Empty O.
Proof.
  hnf; destruct 1.
Qed.

Hint Resolve fresh_Empty.

Theorem EnsembleIndexedListEquivalence_insert : forall A ts t ls ts',
  EnsembleIndexedListEquivalence ts ls
  -> insert (A := A) ts t ts'
  -> EnsembleIndexedListEquivalence ts' (t :: ls).
Proof.
  unfold insert, EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence, UnConstrFreshIdx, EnsembleInsert, Ensembles.In; simpl; firstorder subst.

  exists (S (max x x1)); unfold EnsembleInsert; intuition (subst; simpl in * ).
  apply H2 in H1; intuition (subst; simpl in * ).
  generalize (Max.max_spec x x1); intuition.
  apply H in H5.
  generalize (Max.max_spec x x1); intuition.
  exists ({| elementIndex := x; indexedElement := t |} :: x0); simpl; intuition.
  apply H2 in H1; intuition (subst; simpl in * ).
  tauto.
  firstorder idtac.
  firstorder idtac.
  subst.
  apply H2; tauto.
  apply H2.
  apply H3 in H5; tauto.
  constructor; intuition.
  apply in_map_iff in H1; destruct H1; intuition subst.
  apply H3 in H6.
  apply H0 in H6.
  omega.
Qed.

Hint Immediate EnsembleIndexedListEquivalence_insert.

Theorem bounded_insert : forall A ts t t' n ts',
  insert (A := A) ts t ts'
  -> (forall t'', IndexedEnsemble_In ts t'' -> length t'' = n)
  -> length t = n
  -> IndexedEnsemble_In ts' t'
  -> length t' = n.
Proof.
  unfold insert, IndexedEnsemble_In, EnsembleInsert, Ensembles.In; simpl; intuition.
  destruct H; intuition subst.
  destruct H2; intuition.
  eauto.
  apply H4 in H; intuition.
  eauto.
Qed.

Hint Immediate bounded_insert.

Lemma allTuplesLen_In : forall A len ls,
  (forall x, In x ls -> length x = len)
  -> allTuplesLen (A := A) len ls.
Proof.
  induction ls; simpl; intuition.
Qed.

Lemma allTuplesLen_setwise : forall A len ts ls,
  EnsembleIndexedListEquivalence ts ls
  -> (forall t, IndexedEnsemble_In ts t
                -> length t = len)
  -> allTuplesLen (A := A) len ls.
Proof.
  unfold EnsembleIndexedListEquivalence, IndexedEnsemble_In; firstorder idtac.
  eapply allTuplesLen_In; intros.
  subst.
  apply in_map_iff in H4; destruct H4; intuition subst.
  apply H2 in H5.
  destruct x2; simpl in *.
  eauto.
Qed.

Hint Immediate allTuplesLen_setwise.

Theorem ok : moduleOk m.
Proof.
  vcgen; abstract (unfold tuples0; sep_auto; eauto).
Qed.
