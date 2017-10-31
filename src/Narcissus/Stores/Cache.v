Require Import Coq.Lists.List
        Fiat.Computation.

Set Implicit Arguments.

Class Cache :=
  { CacheFormat : Type;
    CacheDecode : Type;
    Equiv : CacheFormat -> CacheDecode -> Prop }.

Class CacheAdd (cache : Cache) (T : Type) :=
  { addE : CacheFormat -> T -> CacheFormat;
    addD : CacheDecode -> T -> CacheDecode;
    add_correct : forall ce cd t, Equiv ce cd -> Equiv (addE ce t) (addD cd t) }.

Class CacheAdd_Guarded (cache : Cache)
      (T : Type)
      (T_OK : T -> CacheFormat -> CacheDecode -> Prop) :=
  { addE_G : CacheFormat -> T -> CacheFormat;
    addD_G : CacheDecode -> T -> CacheDecode;
    add_correct_G : forall ce cd t,
        Equiv ce cd
        -> T_OK t ce cd
        -> Equiv (addE_G ce t) (addD_G cd t) }.

Class CachePeek (cache : Cache) (T : Type):=
  { peekE : CacheFormat -> T;
    peekD : CacheDecode -> T;
    peek_correct : forall ce cd, Equiv ce cd -> peekE ce = peekD cd }.

Class CacheGet (cache : Cache) (P Q : Type) :=
  { getE : CacheFormat -> P -> list Q;
    getD : CacheDecode -> Q -> option P;
    get_correct : forall ce cd p q,
        Equiv ce cd
        -> (getD cd q = Some p <-> In q (getE ce p))
  }.
