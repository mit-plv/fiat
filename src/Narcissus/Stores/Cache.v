Require Import Coq.Lists.List
        Fiat.Computation.

Set Implicit Arguments.

Class Cache :=
  { CacheEncode : Type;
    CacheDecode : Type;
    Equiv : CacheEncode -> CacheDecode -> Prop }.

Class CacheAdd (cache : Cache) (T : Type) :=
  { addE : CacheEncode -> T -> CacheEncode;
    addD : CacheDecode -> T -> CacheDecode;
    add_correct : forall ce cd t, Equiv ce cd -> Equiv (addE ce t) (addD cd t) }.

Class CacheAdd_Guarded (cache : Cache)
      (T : Type)
      (T_OK : T -> CacheEncode -> CacheDecode -> Prop) :=
  { addE_G : CacheEncode -> T -> CacheEncode;
    addD_G : CacheDecode -> T -> CacheDecode;
    add_correct_G : forall ce cd t,
        Equiv ce cd
        -> T_OK t ce cd
        -> Equiv (addE_G ce t) (addD_G cd t) }.

Class CachePeek (cache : Cache) (T : Type):=
  { peekE : CacheEncode -> T;
    peekD : CacheDecode -> T;
    peek_correct : forall ce cd, Equiv ce cd -> peekE ce = peekD cd }.

Class CacheGet (cache : Cache) (P Q : Type) :=
  { getE : CacheEncode -> P -> list Q;
    getD : CacheDecode -> Q -> option P;
    get_correct : forall ce cd p q,
        Equiv ce cd
        -> (getD cd q = Some p <-> In q (getE ce p))
  }.
