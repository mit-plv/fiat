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

Section DnsExample.
  Context {cache : Cache}.
  Context {cacheAddN : CacheAdd cache N}.
  Context {cacheAddPair : CacheAdd cache (list word_t * position_t)}.
  Context {cachePeek : CachePeek cache position_t}.
  Context {cacheGet : CacheGet cache (list word_t) position_t}.

  Inductive type_t := A | CNAME | NS | MX.
  Inductive class_t := IN | CH | HS.

  Definition halt : word_t.
    refine (Build_word_t (exist _ nil _));
      abstract (rewrite Compare_dec.nat_compare_lt; eauto). Defined.

  Definition halt_dec (a : word_t) : {a = halt} + {a <> halt}.
    unfold halt; destruct a as [[word word_pf]];
      destruct word eqn: eq; subst.
    - left; abstract (f_equal; apply sig_equivalence; eauto).
    - right; abstract (inversion 1).
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
      rttl   : uint 32;
      rdata  : { s : list ascii |  length s < exp2_nat 16 } }.

  Record packet_t :=
    { pid         : { s : list bool | length s = 16 };
      pmask       : { s : list bool | length s = 16 };
      pquestion   : { s : list question_t | length s < exp2_nat 16 };
      panswer     : { s : list resource_t | length s < exp2_nat 16 };
      pauthority  : { s : list resource_t | length s < exp2_nat 16 };
      padditional : { s : list resource_t | length s < exp2_nat 16 } }.
  
  Open Scope binencoders_scope.
  
  Definition FixInt_of_branch (b : CacheBranch) : {n | (n < exp2 2)%N}.
    refine (match b with
            | Yes => existT _ 3%N _
            | No  => existT _ 0%N _
            end); abstract (rewrite <- N.compare_lt_iff; eauto).  Defined.

  Definition FixInt_of_type (t : type_t) : {n | (n < exp2 16)%N}.
    refine (match t with
            | A     => existT _ 1%N _
            | CNAME => existT _ 5%N _
            | NS    => existT _ 2%N _
            | MX    => existT _ 15%N _
            end%binencoders); abstract (rewrite <- N.compare_lt_iff; eauto).  Defined.

  Definition FixInt_of_class (c : class_t) : {n | (n < exp2 16)%N}.
    refine (match c with
            | IN => existT _ 1%N _
            | CH => existT _ 3%N _
            | HS => existT _ 4%N _
            end); abstract (rewrite <- N.compare_lt_iff; eauto).  Defined.

  Definition encode_word (w : word_t) :=
         FixInt_encode (FixList_getlength w.(word))
    Then FixList_encode Char_encode w.(word)
    Done.

  Definition encode_name (n : name_t) :=
         SteppingList_encode encode_word FixInt_encode (Enum_encode FixInt_of_branch) n.(name)
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
    Then FixList_encode Char_encode r.(rdata)
    Done.

  Definition encode_packet (p : packet_t) :=
         IList_encode Bool_encode p.(pid)
    Then IList_encode Bool_encode p.(pmask)
    Then FixInt_encode (FixList_getlength p.(pquestion))
    Then FixInt_encode (FixList_getlength p.(panswer))
    Then FixInt_encode (FixList_getlength p.(pauthority))
    Then FixInt_encode (FixList_getlength p.(padditional))
    Then FixList_encode encode_question p.(pquestion)
    Then FixList_encode encode_resource p.(panswer)
    Then FixList_encode encode_resource p.(pauthority)
    Then FixList_encode encode_resource p.(padditional)
    Done.

  Definition packet_decoder
    : { decode | encode_decode_correct cache btransformer (fun _ => True) encode_packet decode }.
  Proof.
    eexists.
    Time solve_decoder.
    Grab Existential Variables.
    eauto. eauto. eauto. eauto.
  Defined.

  Definition packet_decoder'
    : list bool -> CacheDecode -> packet_t * list bool * CacheDecode.
  Proof.
    let p' := eval cbv delta [ proj1_sig packet_decoder ] beta iota in (proj1_sig packet_decoder) in
                                                                        pose p' as p.
    exact p.
  Defined.
End DnsExample.

Definition empty :=
  {| eMap := EMap.empty _;
     dMap := DMap.empty _;
     offs := 0 |}.

Lemma empty_Equiv : Equiv empty empty.
Proof.
  unfold Equiv.
  simpl. intuition eauto.
  inversion H. inversion H.  Qed.

Definition packet_encode (p : packet_t) : list bool :=
  fst (encode_packet p empty).

Definition packet_decode (b : list bool) : packet_t :=
  fst (fst (packet_decoder' b empty)).

Theorem this_is_correct_and_we_know_it :
  forall p, packet_decode (packet_encode p) = p.
Proof.
  intro p.
  unfold packet_encode, packet_decode.
  pose proof (proj2_sig packet_decoder empty empty
    (snd (encode_packet p empty))
    (snd (packet_decoder' (transform (fst (encode_packet p empty)) transform_id) empty))
    p
    (fst (fst (packet_decoder' (transform (fst (encode_packet p empty)) transform_id) empty)))
    (fst (encode_packet p empty))
    transform_id
    (snd (fst (packet_decoder' (transform (fst (encode_packet p empty)) transform_id) empty)))
    empty_Equiv
    I).
  destruct (@encode_packet cache cacheAddN cacheAddPair cachePeek cacheGet p empty).
  rewrite transform_id_right in H.
  change (proj1_sig packet_decoder) with packet_decoder' in H.
  destruct (@packet_decoder' cache cacheAddN cacheAddPair cachePeek cacheGet
           (fst (l, c)) empty) as [[? ?] ?].
  specialize (H eq_refl eq_refl).
  intuition.
Qed.

Definition packet_uncompressed :=
  true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: false :: false :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: nil.
Definition packet_compressed :=
  true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: false :: false :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: true :: false :: false :: false :: true :: false :: true :: false :: false :: false :: true :: false :: false :: nil.

Goal True.
  pose (packet_decode packet_uncompressed) as goal.
  unfold packet_decode in goal.
  (* Time vm_compute in goal. (* ~ 100 seconds in 8.5 *) *)
Abort.

Goal True.
  pose (packet_decode packet_compressed) as goal.
  unfold packet_decode in goal.
  (* Time simpl in goal. *)
Abort.

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

(* Extraction "dns.ml" packet_encode packet_decode packet_uncompressed packet_compressed. *)

(*
#use "dns.ml";;
packet_decode packet_uncompressed;;
packet_decode packet_compressed;;
let p = packet_decode packet_uncompressed;;
let q = {pid = pid p; pmask = pmask p; pquestion = pquestion p; panswer = [{rname = qname (List.hd (pquestion p)); rtype = A; rclass = IN; rttl = Npos XH; rdata = []}]; pauthority = []; padditional = []};;
*)
