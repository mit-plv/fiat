Require Import  Fiat.BinEncoders.Env.Common.Cache.

Instance test_cache : Cache :=
  {| CacheEncode := unit;
     CacheDecode := unit;
     Equiv := fun _ _ => True |}.

Instance test_cache_add_nat : CacheAdd test_cache nat :=
  {| addE := fun ce _ => ce;
     addD := fun cd _ => cd;
     add_correct := fun _ _ _ eqv => eqv |}.
