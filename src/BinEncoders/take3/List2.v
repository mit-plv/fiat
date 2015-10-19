Require Import BigNat Compare_dec Base.

Section List2.

  Context {A : Type}.
  Variable A_record : encode_decode_R A.

  (* terminator *)
  Variable halt : A.
  Variable halt_dec : forall a, {a = halt} + {a <> halt}.

  Definition predicate (xs : list A) :=
    forall x, In x xs -> predicate_R A_record x /\ x <> halt.

  Fixpoint encode (data : list A) :=
    match data with
      | nil => encode_R A_record halt
      | cons s data' => encode_R A_record s ++ encode data'
    end.

  Definition binorder (b1 b2 : bin) := length b1 < length b2.
  Lemma binorder_wf' : forall n, forall b, List.length b <= n -> Acc binorder b.
    unfold binorder; induction n; intuition eauto.
    constructor; intuition; inversion H; rewrite H2 in H0; inversion H0.
    inversion H; [ constructor; rewrite H1; intuition; apply IHn | apply IHn]; eauto.
  Defined.
  Lemma binorder_wf : well_founded binorder.
    unfold well_founded; intro; eapply binorder_wf'; eauto.
  Defined.

  Definition decode : bin -> (list A * bin) :=
    (Fix binorder_wf (fun _ => (list A * bin)%type)
         (fun b rec =>
            let (x, b') := decode_R A_record b in
            if halt_dec x then
              (nil, b)
            else
                match lt_dec (length b') (length b) with
                  | left pf =>
                    let (xs, b'') := rec b' pf in
                    (x :: xs, b'')
                  | right _ =>
                    (nil, b')
                end)).

  Theorem encode_correct : encode_correct predicate encode decode.
  Proof.
    unfold encode_correct, predicate; induction val; simpl; intuition eauto.
    unfold decode.
    admit.
    admit.
  Qed.

  Definition List2_encode_decode :=
    {| predicate_R := predicate;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct |}.
End List2.
