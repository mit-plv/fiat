Load Specs.

Notation "[ data | encode 'with' proj <=> decode 'with' prev ]"
  := (encode_decode_correct_app_curry (fun data => prev) (fun data => proj) encode decode)
       (at level 20, no associativity).

Lemma decode_app_l (data_t proj_t prev_t : Type) :
  forall (prev : data_t -> prev_t)
         (proj : data_t -> proj_t)
         (encode1 : proj_t -> bin)
         (encode2 : data_t -> bin)
         (decode1 : prev_t -> bin -> proj_t * bin)
         (decode2 : prev_t * proj_t -> bin -> data_t * bin),
    [ data | encode1 with proj data <=> decode1 with prev data ] ->
    [ data | encode2 with data      <=> decode2 with (prev data, proj data) ] ->
    [ data | (fun data => encode1 (proj data) ++ encode2 data) with data <=>
             (fun _prev _bin =>
                let (_proj, _ext) := decode1 _prev _bin
                in  decode2 (_prev, _proj) _ext) with prev data ].
Proof.
  intros prev proj encode1 encode2 decode1 decode2 decode1_pf decode2_pf data ext;
  rewrite <- app_assoc; rewrite decode1_pf; rewrite decode2_pf; reflexivity.
Qed.

Lemma decode_resolve_hyp (data_t proj_t prev_t goal_t : Type) :
  forall (prev : data_t -> prev_t)
         (proj : data_t -> proj_t)
         (goal : data_t -> goal_t)
         (encode : proj_t -> bin)
         (constr : prev_t -> proj_t -> goal_t)
         (decode : bin -> proj_t * bin),
  (forall data, constr (prev data) (proj data) = goal data) ->
  encode <++> decode ->
  forall data ext,
    (fun _prev _bin => let (_proj, _ext) := decode _bin
                       in  (constr _prev _proj, _ext)) (prev data) (encode (proj data) ++ ext) = (goal data, ext).
Proof.
  intros prev proj goal encode constr decode constr_pf decode_pf data ext.
  simpl. rewrite decode_pf. rewrite constr_pf. reflexivity.
Qed.

Lemma decode_generalize (data_t : Type) :
  forall (encode : data_t -> bin) (decode : bin -> data_t * bin),
    encode <++> decode ->  encode <+> (fun _bin => fst (decode _bin)).
Proof.
  intros encode decode.
  simpl. intros pf data.
  rewrite <- app_nil_r with (l:=encode data). rewrite pf. reflexivity.
Qed.


Lemma decode_generalize' (data_t : Type) :
  forall (encode : data_t -> bin) (decode : unit -> bin -> data_t * bin),
    [ data | encode with data <=> decode with tt ] ->
    encode <+> (fun _bin => fst (decode tt _bin)).
Proof.
  unfold encode_decode_correct_app_curry.
  intros encode decode.
  simpl. intros pf data.
  rewrite <- app_nil_r with (l:=encode data). rewrite pf. reflexivity.
Qed.


(*
Lemma decode_app_assoc (data_t prev_t : Type) :
  forall (prev : data_t -> prev_t)
         (encode1 : data_t -> bin)
         (encode2 : data_t -> bin),
    { decode : prev_t -> bin -> data_t * bin |
      forall data ext,
        decode (prev data) (encode1 data ++ encode2 data ++ ext) = (data, ext) } ->
    { decode : prev_t -> bin -> data_t * bin |
      forall data ext,
        decode (prev data) ((encode1 data ++ encode2 data) ++ ext) = (data, ext) }.
Proof.
  intros prev encode1 encode2.
  destruct 1 as [ decode decode_pf ].
  eexists. intros data ext.
  instantiate (1:=decode). rewrite <- app_assoc. apply decode_pf.
Defined. *)
