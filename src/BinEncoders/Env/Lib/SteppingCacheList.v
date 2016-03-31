Require Export
        Coq.Lists.List
        Coq.FSets.FMapInterface.
Require Import
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig.

Set Implicit Arguments.

Inductive CacheBranch :=
| Yes
| No.

Section SteppingListCacheEncoder.
  Variable A : Type.
  Variable B : Type.
  Variable fuel : nat.

  Variable cache : Cache.
  Variable cacheAdd : CacheAdd cache (list A * B).
  Variable cacheGet : CacheGet cache (list A) B.
  Variable cachePeek : CachePeek cache B.

  Variable transformer : Transformer.

  Variable A_halt : A.
  Variable A_halt_dec : forall a, {a = A_halt} + {~ a = A_halt}.
  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> bin * CacheEncode.
  Variable A_decoder : decoder cache transformer A_predicate A_encode.

  Variable B_predicate : B -> Prop.
  Variable B_encode : B -> CacheEncode -> bin * CacheEncode.
  Variable B_decoder : decoder cache transformer B_predicate B_encode.

  Variable C_predicate : CacheBranch -> Prop.
  Variable C_encode : CacheBranch -> CacheEncode -> bin * CacheEncode.
  Variable C_decoder : decoder cache transformer C_predicate C_encode.

  Definition SteppingList := { xs : list A | length xs <= fuel /\
                                             forall x, In x xs -> ~ x = A_halt }.

  Definition SteppingList_predicate (l : SteppingList) :=
    A_predicate A_halt /\
    (forall x, In x (proj1_sig l) -> A_predicate x) /\
    (forall x, B_predicate x) /\
    (forall x, C_predicate x).

  Fixpoint SteppingList_encode' (l : list A) (ce : CacheEncode) : bin * CacheEncode :=
    match l with
    | nil => let (b1, e1) := C_encode No ce in
             let (b2, e2) := A_encode A_halt e1 in
                 (transform b1 b2, e2)
    | cons x l' =>
      match getE ce l with
      | Some position => let (b1, e1) := C_encode Yes ce in
                         let (b2, e2) := B_encode position e1 in
                         (transform b1 b2, e2)
      | None => let (b1, e1) := C_encode Yes ce in
                let (b2, e2) := A_encode x e1 in
                let (b3, e3) := SteppingList_encode' l' e2 in
                    (transform (transform b1 b2) b3, addE e3 (l, peekE ce))
      end
    end.

  Definition SteppingList_encode (l : SteppingList) (ce : CacheEncode) : bin * CacheEncode :=
    SteppingList_encode' (proj1_sig l) ce.

  Fixpoint SteppingList_decode' (f : nat) (b : bin) (cd : CacheDecode) : list A * bin * CacheDecode :=
    let (x1, e1) := decode b cd in
    let (br, b1) := x1 in
    match br with
    | Yes => let (x2, e2) := decode b1 e1 in
             let (ps, b2) := x2 in
             match getD cd ps with
             | Some l => (l, b2, e2)
             | None => (nil, b, cd) (* bogus *)
             end
    | No => let (x2, e2) := decode b1 e1 in
            let (a, b2) := x2 in
            if A_halt_dec a then
              (nil, b2, cd)
            else
              match f with
              | O => (nil, b, cd) (* bogus *)
              | S f' => let (x3, e3) := SteppingList_decode' f' b2 e2 in
                        let (l, b3) := x3 in
                        (a :: l, b3, addD e3 (a :: l, peekD cd))
              end
    end.

  Definition SteppingList_decode (b : bin) (cd : CacheDecode) : SteppingList * bin * CacheDecode.
    refine (exist _ (fst (fst (SteppingList_decode' fuel b cd))) _,
            snd (fst (SteppingList_decode' fuel b cd)),
            snd (SteppingList_decode' fuel b cd)).
    admit.
  Defined.

  Theorem SteppingList_encode_correct :
    encode_decode_correct cache transformer SteppingList_predicate SteppingList_encode SteppingList_decode.
  Proof.
  Admitted.
End SteppingListCacheEncoder.

Global Instance SteppingListCache_decoder A B fuel cache cacheAdd cacheGet cachePeek transformer
       (A_halt : A)
       (A_halt_dec : forall a, {a = A_halt} + {~ a = A_halt})
       (A_predicate : A -> Prop)
       (A_encode : A -> CacheEncode -> bin * CacheEncode)
       (A_decoder : decoder cache transformer A_predicate A_encode)
       (B_predicate : B -> Prop)
       (B_encode : B -> CacheEncode -> bin * CacheEncode)
       (B_decoder : decoder cache transformer B_predicate B_encode)
       (C_predicate : CacheBranch -> Prop)
       (C_encode : CacheBranch -> CacheEncode -> bin * CacheEncode)
       (C_decoder : decoder cache transformer C_predicate C_encode)
  : decoder cache transformer
            (SteppingList_predicate A_predicate B_predicate C_predicate)
            (SteppingList_encode cacheAdd cacheGet cachePeek transformer A_encode B_encode C_encode) :=
  { decode := SteppingList_decode fuel cacheAdd cacheGet cachePeek A_halt_dec A_decoder B_decoder C_decoder;
    decode_correct := @SteppingList_encode_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ }.
