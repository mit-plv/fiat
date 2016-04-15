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
Notation "x 'Then' y" := (compose btransformer x y) (at level 100, right associativity).
Notation "x 'Done'"   := (x Then fun e => (nil, e)) (at level 99, right associativity).
Notation "[ n ]" := (exist _ n _).

Arguments Bool_encode {_ _} _ _.
Arguments Char_encode {_ _} _ _.
Arguments FixInt_encode {_ _ _} _ _.
Arguments Enum_encode {_ _ _ _} _ _ _.
Arguments FixList_encode {_ _ _} _ _ _ _.
Arguments IList_encode {_ _ _} _ _ _ _.
Arguments SteppingList_encode {_ _ _ _ _ _ _} _ {_} _ _ _ _ _.

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
          | Yes => [3%N]
          | No  => [0%N]
          end); abstract (rewrite <- N.compare_lt_iff; eauto).  Defined.

Definition FixInt_of_type (t : type_t) : {n | (n < exp2 16)%N}.
  refine (match t with
          | A     => [1%N]
          | CNAME => [5%N]
          | NS    => [2%N]
          | MX    => [15%N]
          end); abstract (rewrite <- N.compare_lt_iff; eauto).  Defined.

Definition FixInt_of_class (c : class_t) : {n | (n < exp2 16)%N}.
  refine (match c with
          | IN => [1%N]
          | CH => [3%N]
          | HS => [4%N]
          end); abstract (rewrite <- N.compare_lt_iff; eauto).  Defined.

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
Proof.
  (* solve_decoder -- this one line tactic solves the goal in Coq8.5 but not in 8.4pl6
                      derive manually for now *)
  eapply compose_decoder. eapply IList_decoder. eapply Bool_decoder. solve_predicate. intro.
  eapply compose_decoder. eapply IList_decoder. eapply Bool_decoder. solve_predicate. intro.
  eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
  eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
  eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
  eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
  eapply compose_decoder. eapply FixList_decoder.
  { eapply compose_decoder.
    { eapply compose_decoder. eapply SteppingListCache_decoder. eauto.
      { eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
        eapply compose_decoder. eapply FixList_decoder. eapply Char_decoder. solve_predicate. intro.
        eexists. intro.
        instantiate (1:=fun b e => (Build_word_t proj6, b, e)).
        instantiate (1:=fun _ => True).
        abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                             | inversion H2; destruct data; subst; eauto
                             | inversion H2; inversion H1; subst; eauto ]). }
      eapply FixInt_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
      eexists. intro.
      instantiate (1:=fun b e => (Build_name_t proj5, b, e)).
      instantiate (1:=fun _ => True).
      abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                           | inversion H2; destruct data; subst; eauto
                           | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eexists. intro.
    instantiate (1:=fun b e => (Build_question_t proj5 proj6 proj7, b, e)).
    instantiate (1:=fun _ => True).
    abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                         | inversion H2; destruct data; subst; eauto
                         | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
  eapply compose_decoder. eapply FixList_decoder.
  { eapply compose_decoder.
    { eapply compose_decoder. eapply SteppingListCache_decoder. eauto.
      { eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
        eapply compose_decoder. eapply FixList_decoder. eapply Char_decoder. solve_predicate. intro.
        eexists. intro.
        instantiate (1:=fun b e => (Build_word_t proj7, b, e)).
        instantiate (1:=fun _ => True).
        abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                             | inversion H2; destruct data; subst; eauto
                             | inversion H2; inversion H1; subst; eauto ]). }
      eapply FixInt_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
      eexists. intro.
      instantiate (1:=fun b e => (Build_name_t proj6, b, e)).
      instantiate (1:=fun _ => True).
      abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                           | inversion H2; destruct data; subst; eauto
                           | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
    eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
    eapply compose_decoder. eapply FixList_decoder. eapply Char_decoder. solve_predicate. intro.
    eexists. intro.
    instantiate (1:=fun b e => (Build_resource_t proj6 proj7 proj8 proj9 proj11, b, e)).
    instantiate (1:=fun _ => True).
    abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                         | inversion H2; destruct data; subst; eauto
                         | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
  eapply compose_decoder. eapply FixList_decoder.
  { eapply compose_decoder.
    { eapply compose_decoder. eapply SteppingListCache_decoder. eauto.
      { eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
        eapply compose_decoder. eapply FixList_decoder. eapply Char_decoder. solve_predicate. intro.
        eexists. intro.
        instantiate (1:=fun b e => (Build_word_t proj8, b, e)).
        instantiate (1:=fun _ => True).
        abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                             | inversion H2; destruct data; subst; eauto
                             | inversion H2; inversion H1; subst; eauto ]). }
      eapply FixInt_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
      eexists. intro.
      instantiate (1:=fun b e => (Build_name_t proj7, b, e)).
      instantiate (1:=fun _ => True).
      abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                           | inversion H2; destruct data; subst; eauto
                           | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
    eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
    eapply compose_decoder. eapply FixList_decoder. eapply Char_decoder. solve_predicate. intro.
    eexists. intro.
    instantiate (1:=fun b e => (Build_resource_t proj7 proj8 proj9 proj10 proj12, b, e)).
    instantiate (1:=fun _ => True).
    abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                         | inversion H2; destruct data; subst; eauto
                         | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
  eapply compose_decoder. eapply FixList_decoder.
  { eapply compose_decoder.
    { eapply compose_decoder. eapply SteppingListCache_decoder. eauto.
      { eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
        eapply compose_decoder. eapply FixList_decoder. eapply Char_decoder. solve_predicate. intro.
        eexists. intro.
        instantiate (1:=fun b e => (Build_word_t proj9, b, e)).
        instantiate (1:=fun _ => True).
        abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                             | inversion H2; destruct data; subst; eauto
                             | inversion H2; inversion H1; subst; eauto ]). }
      eapply FixInt_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
      eexists. intro.
      instantiate (1:=fun b e => (Build_name_t proj8, b, e)).
      instantiate (1:=fun _ => True).
      abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                           | inversion H2; destruct data; subst; eauto
                           | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eapply compose_decoder. eapply Enum_decoder. solve_enum. solve_predicate. intro.
    eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
    eapply compose_decoder. eapply FixInt_decoder. solve_predicate. intro.
    eapply compose_decoder. eapply FixList_decoder. eapply Char_decoder. solve_predicate. intro.
    eexists. intro.
    instantiate (1:=fun b e => (Build_resource_t proj8 proj9 proj10 proj11 proj13, b, e)).
    instantiate (1:=fun _ => True).
    abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                         | inversion H2; destruct data; subst; eauto
                         | inversion H2; inversion H1; subst; eauto ]). } solve_predicate. intro.
  eexists. intro.
  instantiate (1:=fun b e => (Build_packet_t proj proj0 proj5 proj6 proj7 proj8, b, e)).
  abstract (intuition; [ inversion H2; inversion H1; subst; eauto
                       | inversion H2; destruct data; subst; eauto
                       | inversion H2; inversion H1; subst; eauto ]).
Defined.

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

Section Examples.
  Definition packet_uncompressed :=
    true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: false :: false :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: nil.
  Definition packet_compressed :=
    true :: true :: false :: true :: true :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: true :: true :: false :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: true :: false :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: false :: false :: true :: false :: true :: true :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: true :: false :: false :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: true :: true :: true :: false :: true :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: true :: true :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: false :: true :: false :: false :: true :: false :: false :: true :: true :: false :: true :: true :: false :: false :: true :: false :: false :: false :: false :: true :: false :: false :: false :: true :: false :: false :: false :: true :: false :: true :: false :: false :: false :: true :: false :: false :: nil.
End Examples.

Goal True.
  pose (packet_decode packet_uncompressed) as goal.
  unfold packet_decode in goal.
  (* Time simpl in goal. (* ~ 100 seconds in 8.5 *) *)
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