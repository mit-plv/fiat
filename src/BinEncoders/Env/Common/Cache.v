Set Implicit Arguments.

Class Cache :=
  { CacheEncode : Type;
    CacheDecode : Type;
    Equiv : CacheEncode -> CacheDecode -> Prop }.

Class CacheAdd (cache : Cache) (T : Type) :=
  { addE : CacheEncode -> T -> CacheEncode;
    addD : CacheDecode -> T -> CacheDecode;
    add_correct : forall ce cd t, Equiv ce cd -> Equiv (addE ce t) (addD cd t) }.

Class CachePeek (cache : Cache) (T : Type):=
  { peekE : CacheEncode -> T;
    peekD : CacheDecode -> T;
    peek_correct : forall ce cd, Equiv ce cd -> peekE ce = peekD cd }.

Class CacheGet (cache : Cache) (P Q : Type) :=
  { getE : CacheEncode -> P -> option Q;
    getD : CacheDecode -> Q -> option P;
    get_correct : forall ce cd p q, Equiv ce cd -> (getE ce p = Some q <-> getD cd q = Some p) }.
