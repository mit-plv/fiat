Require Import
        Bedrock.Word
        Coq.omega.Omega
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString.

Section AlignedDecodeM.
  
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
    
  Definition AlignedDecodeM
             (A : Set)
             (n : nat):=
    Vector.t char n
    -> nat
    -> CacheDecode
    -> option (A * nat * CacheDecode).
  
  Definition BindAlignedDecodeM
             {A B : Set}
             {n : nat}
             (a : AlignedDecodeM A n)
             (b : A -> AlignedDecodeM B n)
    : AlignedDecodeM B n :=
    fun v idx c => (Ifopt a v n c  as a' Then (b (fst (fst a')) v (snd (fst a')) (snd a')) Else None).
  
  Definition ReturnAlignedDecodeM
             {A : Set}
             {n : nat}
             (a : A)
    : AlignedDecodeM A n :=
    fun v idx c => Some (a, n, c).
 
  Definition ThrowAlignedDecodeM
             {A : Set}
             {n : nat}
    : AlignedDecodeM A n:=
    fun _ _ _ => None.

  Fixpoint nth_opt
    {A : Set}
    {n : nat}
    (v : Vector.t A n)
    (m : nat)
    : option A :=
    match n, v with
    | 0,  Vector.cons a _ _ => Some a
    | S m', Vector.cons _ _ v' => nth_opt v' m'
    | _, _ => None
    end.
  
  Definition GetCurrentByte (* Gets the current byte and increments the current index. *)
             {A : Set}
             {n : nat}
             (m : AlignedDecodeM A n)
    : AlignedDecodeM char n :=
    fun v idx c => Ifopt (nth_opt v idx) as b Then Some (b, S idx, c) Else None.
  
End AlignedDecodeM. 


