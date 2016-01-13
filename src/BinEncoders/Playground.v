Require Import Coq.Lists.List
               Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Section Specifications.

  Variable (data_t : Type)
           (bin_t  : Type).

  Definition encode_decode_correct
             (predicate : data_t -> Prop)
             (encode : data_t -> bin_t)
             (decode : bin_t -> data_t) :=
    forall data, predicate data -> decode (encode data) = data.

  Class decoder
        (predicate : data_t -> Prop)
        (encode : data_t -> bin_t) :=
  { decode : bin_t -> data_t;
    decode_correct : encode_decode_correct predicate encode decode }.

End Specifications.

Infix "<+>" := (encode_decode_correct (fun _ => True)) (at level 20, no associativity).

Section Lemmas.

  Lemma decode_unpack
         (data_t : Type)
         (bin_t  : Type)
         (proj_t : Type) :
    forall (project : data_t -> proj_t)
           (predicate  : data_t -> Prop)
           (predicate' : proj_t -> Prop)
           (encode1 : proj_t * bin_t -> bin_t)
           (encode2 : data_t -> bin_t)
           (decode1 : bin_t -> proj_t * bin_t)
           (decode2 : proj_t -> bin_t -> data_t),
      (forall data, predicate data -> predicate' (project data)) ->
      (encode_decode_correct
         (fun data => predicate' (fst data)) encode1 decode1) ->
      (forall proj,
          encode_decode_correct
            (fun data => predicate data /\ project data = proj) encode2 (decode2 proj)) ->
      (encode_decode_correct
         predicate
         (fun data => encode1 (project data, encode2 data))
         (fun bin  => let (_proj, _bin) := decode1 bin
                      in  decode2 _proj _bin)).
  Proof.
    unfold encode_decode_correct.
    intros project predicate predicate' encode1 encode2 decode1 decode2
           predicate_pf decode1_pf decode2_pf data pred.
    destruct (decode1 (encode1 (project data, encode2 data))) as [_proj _bin] eqn: eq.
    specialize (decode1_pf (project data, encode2 data)).
    specialize (decode2_pf _proj data).
    rewrite decode1_pf in eq; [ | eapply predicate_pf; eauto ].
    rewrite <- decode2_pf.
    inversion eq. eauto. inversion eq. eauto.
  Qed.

  Lemma decode_degeneralize
        (data_t : Type)
        (bin_t  : Type) :
    forall (encode : data_t -> bin_t)
           (decode : bin_t -> data_t)
           (predicate : data_t -> Prop),
      encode_decode_correct (fun _ => True) encode decode ->
      encode_decode_correct predicate encode decode.
  Proof.
    unfold encode_decode_correct; eauto.
  Qed.

(*
  Lemma decode_finalize
        (data_t : Type)
        (bin_t  : Type)
        (proj_t : Type) :
    forall (project : data_t -> proj_t)
           (predicate  : data_t -> Prop)
           (predicate' : proj_t -> Prop)
           (encode : proj_t -> bin_t)
           (decode : bin_t -> proj_t)
           (build  : proj_t -> data_t),
      (forall data, predicate data -> predicate' (project data)) ->
      (encode_decode_correct
         (fun data => predicate' (fst data)) encode1 decode1) ->
      (forall proj,
          encode_decode_correct
            (fun data => predicate data /\ project data = proj) encode2 (decode2 proj)) ->
      (encode_decode_correct
         predicate
         (fun data => encode1 (project data))
         (fun bin  => ).
  Proof.
    unfold encode_decode_correct.
    intros project predicate predicate' encode1 encode2 decode1 decode2
           predicate_pf decode1_pf decode2_pf data pred.
    destruct (decode1 (encode1 (project data, encode2 data))) as [_proj _bin] eqn: eq.
    specialize (decode1_pf (project data, encode2 data)).
    specialize (decode2_pf _proj data).
    rewrite decode1_pf in eq; [ | eapply predicate_pf; eauto ].
    rewrite <- decode2_pf.
    inversion eq. eauto. inversion eq. eauto.
  Qed.
*)
End Lemmas.


Section Examples.

  Definition bin := list bool.

  Fixpoint exp2 (n : nat) :=
    match n with
    | O => S O
    | S n' => exp2 n' + exp2 n'
    end.

  Variable FixNat_encode : forall size, {n | n < exp2 size} -> bin.
  Variable List1_encode : forall (A : Type) (encode_A : A -> bin) (size : nat), {ls : list A | length ls < exp2 size} -> bin.
  Variable List_encode : forall (A : Type) (encode_A : A -> bin), list A -> bin.
  Variable Nat_encode : nat -> bin.
  Variable Bin_encode : forall (A : Type) (encode_A : A -> bin), A * bin -> bin.

  Global Instance FixNat_decoder
         (size : nat)
    : decoder (fun _ => True) (FixNat_encode size).
  Admitted.

  Global Instance List1_decoder
         (size : nat)
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True) (List1_encode encode_A size).
  Admitted.

  Global Instance List_decoder
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
         (size : nat)
    : decoder (fun data => length data = size) (List_encode encode_A).
  Admitted.

  Global Instance Nat_decoder
    : decoder (fun _ => True) Nat_encode.
  Admitted.

  Global Instance Bin_decoder
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True) (Bin_encode encode_A).
  Admitted.

  Global Instance App_decoder
         (A : Type)
         (encode_A : A -> bin)
         (predicate : A -> Prop)
         (A_Decoder : decoder predicate encode_A)
    : decoder (fun data => predicate (fst data))
              (fun _bundle : A * bin => let (_data, _bin) := _bundle in encode_A _data ++ _bin).
  Admitted.

  Global Instance App_decoder2
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True)
              (fun _bundle : A * bin => let (_data, _bin) := _bundle in encode_A _data ++ _bin).
  Admitted.

  Global Instance App_decoder'
         (A : Type)
         (encode_A : A -> bin)
         (predicate : A -> Prop)
         (A_Decoder : decoder predicate encode_A)
    : decoder (fun data => predicate (fst data))
              (fun _bundle : A * bin => let (_data, _) := _bundle in encode_A _data).
  Admitted.

  Global Instance App_decoder'2
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True)
              (fun _bundle : A * bin => let (_data, _) := _bundle in encode_A _data).
  Admitted.


  Record SSRecord :=
    { field1 : { n | n < exp2 4 };
      field2 : { ls : list { n | n < exp2 3 } | length ls < exp2 2 };
      field3 : { n | n < exp2 2 } }.

  Definition SS_encode (data : SSRecord) :=
   FixNat_encode _ (field1 data) ++
   List1_encode (FixNat_encode _) _ (field2 data) ++
   FixNat_encode _ (field3 data).

  Definition SS_decode :
    { SS_decode | SS_encode <+> SS_decode }.
  Proof.
    unfold SS_encode.
    eexists.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 _proj ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro f1.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 _proj ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro f2.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data)) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _) := _bundle
                       in  e1 _proj)
           (encode2:=fun _ => nil)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro f3.

    unfold encode_decode_correct.
    intros. destruct data.
    instantiate (1:=fun _ _ => Build_SSRecord _ _ _). simpl.
    simpl in *. intuition. subst. reflexivity.
  Defined.

  Definition DepSS_encode (data : list nat) :=
    Nat_encode (length data) ++ (List_encode Nat_encode data).

  Definition DepSS_decode :
    { DepSS_decode | DepSS_encode <+> DepSS_decode }.
  Proof.
    unfold DepSS_encode.
    eexists.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 _proj ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro len.


    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _) := _bundle
                       in  e1 _proj)
           (encode2:=fun _ => nil)
    end.
    instantiate (1:=fun data => length data = len).
    intuition. cbv beta.
    (* eapply decode_correct without the following line does not solve it. *)
    change (fun data : list nat * bin => length (fst data) = len) with
            (fun data : list nat * bin => (fun ls => length ls = len) (fst data)).
    eapply decode_correct. intro ls.

    unfold encode_decode_correct.
    intros.
    instantiate (1:=fun _ _ => _).
    simpl in *. intuition. subst. reflexivity.
  Defined.

End Examples.
