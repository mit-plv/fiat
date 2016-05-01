Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.FixList.
Require Export
        Coq.Lists.List.

Section SteppingList.
  Context {A : Type}.
  Context {B : Type}.
  Context {P : Type}.
  Context {cache : Cache}.
  Context {transformer : Transformer B}.

  Variable fuel : nat.
  Variable A_halt : A.
  Variable A_halt_dec : forall a, {a = A_halt} + {~ a = A_halt}.
  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> B * CacheEncode.
  Variable A_decode : B -> CacheDecode -> A * B * CacheDecode.
  Variable A_decode_pf : encode_decode_correct cache transformer A_predicate A_encode A_decode.

  Variable P_predicate : P -> Prop.
  Variable P_predicate_dec : forall p, {P_predicate p} + {~ P_predicate p}.
  Variable P_encode : P -> CacheEncode -> B * CacheEncode.
  Variable P_decode : B -> CacheDecode -> P * B * CacheDecode.
  Variable P_decode_pf : encode_decode_correct cache transformer P_predicate P_encode P_decode.

  Variable X_encode : bool -> CacheEncode -> B * CacheEncode.
  Variable X_decode : B -> CacheDecode -> bool * B * CacheDecode.
  Variable X_decode_pf : encode_decode_correct cache transformer (fun _ => True) X_encode X_decode.

  Variable cacheAdd : CacheAdd cache (list A * P).
  Variable cacheGet : CacheGet cache (list A) P.
  Variable cachePeek : CachePeek cache P.

  Fixpoint encode_list_step (l : list A) (ce : CacheEncode) : B * CacheEncode :=
    match l with
    | nil => let (b1, e1) := X_encode false ce in
             let (b2, e2) := A_encode A_halt e1 in
                 (transform b1 b2, e2)
    | cons x l' =>
      match getE ce l with
      | Some position => let (b1, e1) := X_encode true ce in
                         let (b2, e2) := P_encode position e1 in
                         (transform b1 b2, e2)
      | None => let (b1, e1) := X_encode false ce in
                let (b2, e2) := A_encode x e1 in
                let (b3, e3) := encode_list_step l' e2 in
                    (transform (transform b1 b2) b3, addE e3 (l, peekE ce))
      end
    end.

  Fixpoint decode'_list_step (f : nat) (b : B) (cd : CacheDecode) : list A * B * CacheDecode :=
    let (x1, e1) := X_decode b cd in
    let (br, b1) := x1 in
    match br with
    | true => let (x2, e2) := P_decode b1 e1 in
              let (ps, b2) := x2 in
              match getD cd ps with
              | Some l => (l, b2, e2)
              | None => (nil, b, cd) (* bogus *)
             end
    | false => let (x2, e2) := A_decode b1 e1 in
               let (a, b2) := x2 in
               if A_halt_dec a then
                 (nil, b2, e2)
               else
                 match f with
                 | O => (nil, b, cd) (* bogus *)
                 | S f' => let (x3, e3) := decode'_list_step f' b2 e2 in
                           let (l, b3) := x3 in
                           (a :: l, b3, addD e3 (a :: l, peekD cd))
                 end
    end.

  Definition decode_list_step := decode'_list_step fuel.

  Theorem SteppingList_decode_correct :
    encode_decode_correct
      cache transformer
      (fun ls => A_predicate A_halt /\ |ls| <= fuel /\ (forall x, In x ls -> A_predicate x))
      encode_list_step decode_list_step.
  Proof.
  Admitted.
End SteppingList.