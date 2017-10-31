Require Import  Fiat.Narcissus.Stores.Cache.

Instance test_cache : Cache :=
  {| CacheFormat := unit;
     CacheDecode := unit;
     Equiv := fun _ _ => True |}.

Instance test_cache_add_nat : CacheAdd test_cache nat :=
  {| addE := fun ce _ => ce;
     addD := fun cd _ => cd;
     add_correct := fun _ _ _ eqv => eqv |}.
