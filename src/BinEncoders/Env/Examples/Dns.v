Require Import
        Fiat.BinEncoders.Env.Examples.DnsMap.

Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Automation.Solver.

Require Import
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.BinLib.Char
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Enum
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.Lib.IList
        Fiat.BinEncoders.Env.Lib.SteppingCacheList.

Set Implicit Arguments.
Notation compose := Fiat.BinEncoders.Env.Common.Compose.compose.

Inductive type_t := A | CNAME | NS | MX.
Inductive class_t := IN | CH | HS.

Definition halt : word_t.
  refine (Build_word_t (exist _ nil _)); rewrite Compare_dec.nat_compare_lt; eauto. Defined.
Definition halt_dec (a : word_t) : {a = halt} + {a <> halt}.
  unfold halt; destruct a as [[word word_pf]];
  destruct word eqn: eq; subst.
  - left; f_equal; apply sig_equivalence; eauto.
  - right; inversion 1.
Defined. Hint Resolve halt_dec.

Record name_t :=
  { name : { s : list word_t | length s <= 255 /\ forall x, In x s -> x <> halt } }.

Record question_t :=
  { qname  : name_t;
    qtype  : type_t;
    qclass : class_t }.

Record resource_t :=
  { rname  : name_t;
    rtype  : type_t;
    rclass : class_t;
    rttl   : FixInt 32;
    rdata  : { s : list ascii |  length s < exp2_nat 16 } }.

Record packet_t :=
  { pid         : { s : list bool | length s = 16 };
    pmask       : { s : list bool | length s = 16 };
    pquestion   : { s : list question_t | length s < exp2_nat 16 };
    panswer     : { s : list resource_t | length s < exp2_nat 16 };
    pauthority  : { s : list resource_t | length s < exp2_nat 16 };
    padditional : { s : list resource_t | length s < exp2_nat 16 } }.

Definition FixInt_of_branch (b : CacheBranch) : {n | (n < exp2 2)%N}.
  refine (match b with
          | Yes => exist _ (3%N) _
          | No  => exist _ (0%N) _
          end); rewrite <- N.compare_lt_iff; eauto.  Defined.

Definition FixInt_of_type (t : type_t) : {n | (n < exp2 16)%N}.
  refine (match t with
          | A     => exist _ (1%N) _
          | CNAME => exist _ (5%N) _
          | NS    => exist _ (2%N) _
          | MX    => exist _ (15%N) _
          end); rewrite <- N.compare_lt_iff; eauto.  Defined.

Definition FixInt_of_class (c : class_t) : {n | (n < exp2 16)%N}.
  refine (match c with
          | IN => exist _ (1%N) _
          | CH => exist _ (3%N) _
          | HS => exist _ (4%N) _
          end); rewrite <- N.compare_lt_iff; eauto.  Defined.

Notation "x 'Then' y" := (compose btransformer x y) (at level 100, right associativity).
Notation "x 'Done'"   := (x Then fun e => (nil, e)) (at level 99, right associativity).

Arguments Bool_encode {_ _} _ _.
Arguments Char_encode {_ _} _ _.
Arguments FixInt_encode {_ _ _} _ _.
Arguments Enum_encode {_ _ _ _} _ _ _.
Arguments FixList_encode {_ _ _} _ _ _ _.
Arguments IList_encode {_ _ _} _ _ _ _.
Arguments SteppingList_encode {_ _ _ _ _ _ _} _ {_} _ _ _ _ _.

Definition encode_word (w : word_t) :=
       FixInt_encode (FixList_getlength w.(word))
  Then FixList_encode btransformer Char_encode w.(word)
  Done.

Definition encode_name (n : name_t) :=
       SteppingList_encode btransformer encode_word FixInt_encode
                           (Enum_encode FixInt_of_branch) n.(name)
  Done.

Definition encode_question (q : question_t) :=
       encode_name q.(qname)
  Then Enum_encode FixInt_of_type q.(qtype)
  Then Enum_encode FixInt_of_class q.(qclass)
  Done.

Definition encode_resource (r : resource_t) :=
       encode_name r.(rname)
  Then Enum_encode FixInt_of_type r.(rtype)
  Then Enum_encode FixInt_of_class r.(rclass)
  Then FixInt_encode r.(rttl)
  Then FixInt_encode (FixList_getlength r.(rdata))
  Then FixList_encode btransformer Char_encode r.(rdata)
  Done.

Definition encode_packet (p : packet_t) :=
       IList_encode btransformer Bool_encode p.(pid)
  Then IList_encode btransformer Bool_encode p.(pmask)
  Then FixInt_encode (FixList_getlength p.(pquestion))
  Then FixInt_encode (FixList_getlength p.(panswer))
  Then FixInt_encode (FixList_getlength p.(pauthority))
  Then FixInt_encode (FixList_getlength p.(padditional))
  Then FixList_encode btransformer encode_question p.(pquestion)
  Then FixList_encode btransformer encode_resource p.(panswer)
  Then FixList_encode btransformer encode_resource p.(pauthority)
  Then FixList_encode btransformer encode_resource p.(padditional)
  Done.

Global Instance packet_decoder
  : decoder cache btransformer (fun _ => True) encode_packet.
Proof. solve_decoder.  Defined.

Definition empty :=
  {| eMap := EMap.empty _;
     dMap := DMap.empty _;
     tick := 0;
     extr := 0 |}.

Lemma empty_Equiv : Equiv empty empty.
Proof.
  unfold Equiv.
  simpl. intuition eauto.
  inversion H. inversion H.  Qed.

Definition packet_encode (p : packet_t) : list bool :=
  fst (encode_packet p empty).

Definition packet_decode (b : list bool) : packet_t :=
  fst (fst (decode (decoder:=packet_decoder) b empty)).

Theorem this_is_correct_and_we_know_it :
  forall p, packet_decode (packet_encode p) = p.
Proof.
  intro p.
  unfold packet_encode, packet_decode.
  pose proof (@decode_correct _ cache btransformer _ _ packet_decoder empty empty
                (snd (encode_packet p empty))
                (snd (decode (transform (fst (encode_packet p empty)) transform_id) empty))
                p
                (fst (fst (decode (transform (fst (encode_packet p empty)) transform_id) empty)))
                (fst (encode_packet p empty))
                transform_id
                (snd (fst (decode (transform (fst (encode_packet p empty)) transform_id) empty)))
                empty_Equiv
                I).
  destruct (encode_packet p empty).
  rewrite transform_id_right in H.
  destruct (decode (decoder:=packet_decoder) (fst (b, c)) empty) as [[? ?] ?].
  specialize (H eq_refl eq_refl).
  intuition.  Qed.


Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int"
                           [ "0" "(fun x -> x + 1)" ]
                           "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive ascii => char [
"(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Section Examples.

  Definition packet_uncompressed :=
    true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: false :: false :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: nil.

  Definition packet_compressed :=
    true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: false :: false :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: true :: false :: false :: false :: true :: false :: true :: false :: false :: false :: true :: false :: false :: nil.

End Examples.

(* Extraction "dns.ml" packet_encode packet_decode packet_uncompressed packet_compressed. *)

(*
#use "dns.ml";;
packet_decode packet_uncompressed;;
packet_decode packet_compressed;;
let p = packet_decode packet_uncompressed;;
let q = {pid = pid p; pmask = pmask p; pquestion = pquestion p; panswer = [{rname = qname (List.hd (pquestion p)); rtype = A; rclass = IN; rttl = Npos XH; rdata = []}]; pauthority = []; padditional = []};;
*)

(*
Definition p : packet_t.
  refine ({| pid := exist _ (true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true :: nil) _;
             pmask := exist _ (true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true :: nil) _;
             pquestion := exist _ nil _;
             panswer := exist _ nil _;
             pauthority := exist _ nil _;
             padditional := exist _ nil _ |}); admit.
Defined.

Lemma compose_decoder_decode A A'
      (cache : Cache)
      (transformer : Transformer)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (encode1 : A' -> CacheEncode -> bin * CacheEncode)
      (encode2 : A -> CacheEncode -> bin * CacheEncode)
      (decoder1 : decoder cache transformer predicate' encode1)
      (pred_pf : forall data, predicate data -> predicate' (project data))
      (decoder2 : forall proj,
          decoder cache transformer (fun data => predicate data /\ project data = proj) encode2)
      (b : bin)
      (cd : CacheDecode)
  : decode (decoder:=(compose_decoder project predicate decoder1 pred_pf decoder2)) b cd =
    let (bundle, env') := @decode _ _ _ _ _ decoder1 b cd in
    let (proj, rest) := bundle in
    @decode _ _ _ _ _ (decoder2 proj) rest env'.
Proof. reflexivity.  Qed.

Definition x (Tranformer:=btransformer) (b : bin) : packet_t * bin * CacheDecode.
  pose (decode_packet_i b).
  unfold decode_packet_i in p0.
  cbv beta delta [ packet_decoder ] in p0.

  let p0' := eval unfold p0 in p0 in
  match p0' with
  | context [ compose_decoder ?proj ?pred ?decoder1' ?pred_pf ?decoder2' ] =>
    pose proof (compose_decoder_decode proj pred decoder1' pred_pf decoder2' b
               ({| eMap := EMap.empty position_t;
                   dMap := DMap.empty (list word_t);
                   tick := 0;
                   extr := 0 |})) (*
    rewrite compose_decoder_decode with (decoder1:=decoder1') (decoder2:=decoder2') in p0 *)
  end.
  Set Printing Implicit. idtac.
  unfold encode_packet in p0.
  rewrite H in p0.

  rewrite compose_decoder_decode in p0.

  let p0 := eval unfold p0 in p0 in
  match p0 with
  | context [ compose_decoder ?pid ?pred ?decoder1 _ ?decoder2 ] => set (x:=decoder2) in *
  end.
  unfold compose_decoder in p0.

  cbv beta delta [ decode ] in p0.
  unfold IList_decoder in p0.
  Opaque IList_decode. idtac. Set Printing Implicit. idtac. clearbody x.
  simpl in p0.

Eval vm_compute in (fst (encode_packet_i p)).
(* Eval vm_compute in (decode_packet_i (fst (encode_packet_i p))). *)

(*
Global Instance test_decoder
  : decoder test_cache btransformer (fun _ => True) encode_test.
Proof.
  unfold encode_test.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eexists. unfold encode_decode_correct.
  instantiate (1:=fun b e => (Build_test_t proj proj0 proj1 proj2, b, e)).
  intuition. inversion H1. inversion H2. subst. eauto. inversion H2.
  subst. destruct data. eauto. inversion H1. subst. inversion H2. eauto.
Defined. *)

Section Examples.
End Examples.



Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive ascii => char [
"(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Check DMap.Raw.Proofs.L.find_rect.
Eval vm_compute in (fst (encode_packet_i p)).
(* Extraction "p.ml" encode_packet_i encode_packet'_i p. *)*)


(*
Definition encode_word (w : word_t) :=
  compose btransformer (FixInt_encode _ (FixList_getlength w.(word))) (
  compose btransformer (FixList_encode _ btransformer (Char_encode _) w.(word))
                       (fun e => (nil, e))).

Definition encode_name (n : name_t) :=
  compose btransformer
          (SteppingList_encode _ _ _ btransformer encode_word (FixInt_encode _)
                              (Enum_encode _ FixInt_of_branch) n.(name))
          (fun e => (nil, e)).

Definition encode_question (q : question_t) :=
  compose btransformer (encode_name q.(qname)) (
  compose btransformer (Enum_encode _ FixInt_of_type q.(qtype)) (
  compose btransformer (Enum_encode _ FixInt_of_class q.(qclass))
                       (fun e => (nil, e)))).

Definition encode_resource (r : resource_t) :=
  compose btransformer (encode_name r.(rname)) (
  compose btransformer (Enum_encode _ FixInt_of_type r.(rtype)) (
  compose btransformer (Enum_encode _ FixInt_of_class r.(rclass)) (
  compose btransformer (FixInt_encode _ r.(rttl)) (
  compose btransformer (FixInt_encode _ (FixList_getlength r.(rdata))) (
  compose btransformer (FixList_encode _ btransformer (Bool_encode _) r.(rdata))
                       (fun e => (nil, e))))))).

Definition encode_packet (p : packet_t) :=
  compose btransformer (IList_encode _ btransformer (Bool_encode _) p.(pid)) (
  compose btransformer (IList_encode _ btransformer (Bool_encode _) p.(pmask)) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(pquestion))) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(panswer))) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(pauthority))) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(padditional))) (
  compose btransformer (FixList_encode _ btransformer encode_question p.(pquestion)) (
  compose btransformer (FixList_encode _ btransformer encode_resource p.(panswer)) (
  compose btransformer (FixList_encode _ btransformer encode_resource p.(pauthority)) (
  compose btransformer (FixList_encode _ btransformer encode_resource p.(padditional))
                       (fun e => (nil, e))))))))))). *)
