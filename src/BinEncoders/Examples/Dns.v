Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Helpers
               Fiat.BinEncoders.Libraries.Sig
               Fiat.BinEncoders.Libraries.BinCore
               Fiat.BinEncoders.Libraries.FixInt
               Fiat.BinEncoders.Libraries.SteppingList
               Fiat.BinEncoders.Libraries.FixList
               Fiat.BinEncoders.Libraries.FixList2
               Fiat.BinEncoders.Libraries.Char
               Fiat.BinEncoders.Libraries.Bool
               Coq.Strings.Ascii.

Set Implicit Arguments.

Record word_t :=
  { word_attr : { s : list ascii | length s < exp2_nat 8 } }.

Definition halt : word_t.
  refine (Build_word_t (exist _ nil _)).
  rewrite Compare_dec.nat_compare_lt; eauto.
Defined.

Definition halt_dec (a : word_t) : {a = halt} + {a <> halt}.
  unfold halt; destruct a as [word word_pf].
  destruct word as [ w ]. destruct w eqn: eq; subst.
  - left. subst. f_equal. eapply sig_equivalence. eauto.
  - right. intro. inversion H.
Defined.

Record name_t :=
  { name_attr : { s : list word_t | length s <= 255 /\ forall x, In x s -> x <> halt } }.

Definition encode_word (bundle : word_t * bin_t) :=
  FixInt_encode (FixList_getlength (word_attr (fst bundle)),
  FixList_encode Char_encode (word_attr (fst bundle), snd bundle)).

Ltac let's_unfold :=
  unfold SteppingList_predicate,
         FixList_predicate,
         FixList2_predicate,
         FixList.data_t in *.

Ltac solve_predicate :=
  let hdata := fresh
  in  intro hdata; intuition; let's_unfold;
    match goal with
    | |- context[ @fst ?a ?b hdata ] => solve [ pattern (@fst a b hdata); eauto ]
    | |- _ => solve [ intuition eauto ]
    | |- ?func _ =>
      match type of func with
      | ?func_t => solve [ unify ((fun _ => True) : func_t) func; intuition eauto ]
      end
    end.

Global Instance word_decoder
  : decoder (fun _ => True) encode_word.
Proof.
  unfold encode_word.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.
  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eapply FixList_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.
  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eexists. instantiate (1:=fun b => (Build_word_t _, b)).
  intro. intuition. destruct data as [rdata bin]. destruct rdata. simpl in *. subst. eauto.
Defined.

Definition encode_name (bundle : name_t * bin_t) :=
  @SteppingList_encode _ _ halt 255 encode_word (name_attr (fst bundle), snd bundle).

Global Instance name_decoder
  : decoder (fun _ => True) encode_name.
Proof.
  unfold encode_name.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eapply SteppingList_decoder.
  (* special! *) eapply halt_dec.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.

  eexists. instantiate (1:=fun b => (Build_name_t _, b)).
  intro. intuition. destruct data as [rdata bin]. destruct rdata. simpl in *. subst. eauto.
Defined.

Inductive type_t := A | CNAME | NS | MX.
Inductive class_t := IN | CH | HS.

Definition FixInt_of_type (t : type_t) : {n | (n < exp2 16)%N}.
  refine (match t with
          | A     => exist _ (1%N) _
          | CNAME => exist _ (5%N) _
          | NS    => exist _ (2%N) _
          | MX    => exist _ (15%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Definition FixInt_of_class (c : class_t) : {n | (n < exp2 16)%N}.
  refine (match c with
          | IN => exist _ (1%N) _
          | CH => exist _ (3%N) _
          | HS => exist _ (4%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Global Instance type_to_FixInt_decoder
  : decoder (fun _ => True) FixInt_of_type.
Proof.
  eexists.

  intros data _.
  destruct data.

  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    match type of func with
    | ?func_t =>
      let h := fresh
      in  evar (h:func_t);
          unify (fun n => if FixInt_eq_dec n arg then res else h n) func;
          reflexivity
    end
  end.

  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    match type of func with
    | ?func_t =>
      let h := fresh
      in  evar (h:func_t);
          unify (fun n => if FixInt_eq_dec n arg then res else h n) func;
          reflexivity
    end
  end.

  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    match type of func with
    | ?func_t =>
      let h := fresh
      in  evar (h:func_t);
          unify (fun n => if FixInt_eq_dec n arg then res else h n) func;
          reflexivity
    end
  end.

  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    match type of func with
    | ?func_t => unify ((fun _  => res) : func_t) func;
                 reflexivity
    end
  end.
Defined.

Global Instance class_to_FixInt_decoder
  : decoder (fun _ => True) FixInt_of_class.
Proof.
  eexists.

  intros data _.
  destruct data.

  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    match type of func with
    | ?func_t =>
      let h := fresh
      in  evar (h:func_t);
          unify (fun n => if FixInt_eq_dec n arg then res else h n) func;
          reflexivity
    end
  end.

  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    match type of func with
    | ?func_t =>
      let h := fresh
      in  evar (h:func_t);
          unify (fun n => if FixInt_eq_dec n arg then res else h n) func;
          reflexivity
    end
  end.

  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    match type of func with
    | ?func_t => unify ((fun _  => res) : func_t) func;
                 reflexivity
    end
  end.
Defined.

Record question_t :=
  { qname : name_t;
    qtype : type_t;
    qclass : class_t }.

Definition encode_question (bundle : question_t * bin_t) :=
  encode_name (qname (fst bundle),
  FixInt_encode (FixInt_of_type (qtype (fst bundle)),
  FixInt_encode (FixInt_of_class (qclass (fst bundle)), snd bundle))).

Global Instance question_decoder
  : decoder (fun _ => True) encode_question.
Proof.
  unfold encode_question.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=fun bundle => FixInt_encode (FixInt_of_type (fst bundle), snd bundle))
    (encode2:=fun data => FixInt_encode (FixInt_of_class (qclass (fst data)), snd data)).
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=fun bundle => FixInt_encode (FixInt_of_class (fst bundle), snd bundle)).
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eexists. instantiate (1:=fun b => (Build_question_t _ _ _, b)).
  intro. intuition. destruct data as [rdata bin]. destruct rdata. simpl in *. subst. eauto.
Defined.

Record resource_t :=
  { rname : name_t;
    rtype : type_t;
    rclass : class_t;
    rttl : { n : N | (n < exp2 32)%N };
    rdata : { s : list bool |  length s < exp2_nat 16 } }.

Definition encode_resource (bundle : resource_t * bin_t) :=
  encode_name (rname (fst bundle),
  FixInt_encode (FixInt_of_type (rtype (fst bundle)),
  FixInt_encode (FixInt_of_class (rclass (fst bundle)),
  FixInt_encode (rttl (fst bundle),
  FixInt_encode (FixList_getlength (rdata (fst bundle)),
  FixList_encode Bool_encode (rdata (fst bundle), snd bundle)))))).

Global Instance resource_decoder
  : decoder (fun _ => True) encode_resource.
Proof.
  unfold encode_resource.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=fun bundle => FixInt_encode (FixInt_of_type (fst bundle), snd bundle))
    (encode2:=fun data => FixInt_encode (FixInt_of_class (rclass (fst data)),
                          FixInt_encode (rttl (fst data),
                          FixInt_encode (FixList_getlength (rdata (fst data)),
                          FixList_encode Bool_encode (rdata (fst data), snd data))))).
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=fun bundle => FixInt_encode (FixInt_of_class (fst bundle), snd bundle))
    (encode2:=fun data => FixInt_encode (rttl (fst data),
                          FixInt_encode (FixList_getlength (rdata (fst data)),
                          FixList_encode Bool_encode (rdata (fst data), snd data)))).
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eapply FixList_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eexists. instantiate (1:=fun b => (Build_resource_t _ _ _ _ _, b)).
  intro. intuition. destruct data as [rdata bin]. destruct rdata. simpl in *. subst. eauto.
Defined.

Record packet_t :=
  { pid : { s : list bool | length s = 16 };
    pmask : { s : list bool | length s = 16 };
    pquestion : { s : list question_t | length s < exp2_nat 16 };
    panswer : { s : list resource_t | length s < exp2_nat 16 };
    pauthority : { s : list resource_t | length s < exp2_nat 16 };
    padditional : { s : list resource_t | length s < exp2_nat 16 } }.

Definition encode_packet (bundle : packet_t * bin_t) :=
  FixList2_encode Bool_encode (pid (fst bundle),
  FixList2_encode Bool_encode (pmask (fst bundle),
  FixInt_encode (FixList_getlength (pquestion (fst bundle)),
  FixInt_encode (FixList_getlength (panswer (fst bundle)),
  FixInt_encode (FixList_getlength (pauthority (fst bundle)),
  FixInt_encode (FixList_getlength (padditional (fst bundle)),
  FixList_encode encode_question (pquestion (fst bundle),
  FixList_encode encode_resource (panswer (fst bundle),
  FixList_encode encode_resource (pauthority (fst bundle),
  FixList_encode encode_resource (padditional (fst bundle), snd bundle)))))))))).

Global Instance packet_decoder
  : decoder (fun _ => True) encode_packet.
Proof.
  unfold encode_packet.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eapply FixList2_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eapply FixList2_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=FixList_encode encode_question).
  eapply strengthening_decoder.
  eapply FixList_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=FixList_encode encode_resource).
  eapply strengthening_decoder.
  eapply FixList_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=FixList_encode encode_resource).
  eapply strengthening_decoder.
  eapply FixList_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eapply unpacking_decoder with
    (encode1:=FixList_encode encode_resource).
  eapply strengthening_decoder.
  eapply FixList_decoder.
  eapply strengthening_decoder.
  eauto with typeclass_instances.

  solve_predicate.
  solve_predicate.
  solve_predicate.
  intro.

  eexists. instantiate (1:=fun b => (Build_packet_t _ _ _ _ _ _, b)).
  intro. intuition. destruct data as [rdata bin]. destruct rdata. simpl in *. subst. eauto.
Defined.

Section Example.
  Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).
  Definition packet1 := [true; true; false; true; true; false; true; true; false; true;
                         false; false; false; false; true; false; false; false; false; false;
                         false; false; false; true; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; true; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; true; true; false; true; true; true; false; true;
                         true; true; false; true; true; true; false; true; true; true;
                         false; true; true; true; false; true; true; true; false; false;
                         false; false; true; true; false; false; false; true; true; false;
                         true; true; true; false; false; true; true; false; true; true;
                         true; true; false; true; true; true; false; false; true; false;
                         false; true; true; true; false; true; false; false; false; true;
                         true; false; true; false; false; false; false; true; true; false;
                         false; true; false; true; false; true; true; false; false; false;
                         false; true; false; true; true; true; false; false; true; true;
                         false; true; true; true; false; true; false; false; false; true;
                         true; false; false; true; false; true; false; true; true; true;
                         false; false; true; false; false; true; true; false; true; true;
                         true; false; false; false; false; false; false; false; true; true;
                         false; true; true; false; false; true; false; true; false; true;
                         true; false; false; true; false; false; false; true; true; true;
                         false; true; false; true; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; true; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; true].
End Example.


Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive ascii => char [
"(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

(* Extraction "Extracted.ml" packet_decoder packet1. *)
(* #use "Extracted.ml";; *)
(* packet_decoder packet1;; *)




(*

  Focus 2.
  eapply strengthening_decoder.
  eapply FixList2_decoder.
  Focus 2. unfold FixList2_predicate. intros ? ?.

  match goal with
  | |- context[ @fst ?a ?b data ] => pattern (@fst a b data)
  end. eapply H.

unfold data_t. pattern (fst data). eapply H.
  eapply strengthening_decoder.
  eapply Bool_decoder.
  simpl. intros ? ?.  unfold data_t. pattern (fst data). eapply H. simpl. intuition.

  Focus 2. intros. unfold FixList2_predicate. intro. pattern (fst data). eapply H.
  eapply Bool_decoder. *)