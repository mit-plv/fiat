Require Import CertifiedExtraction.Benchmarks.MicrobenchmarksSetup.
(* Require Import BinEncoders.Env.Examples.Dns. *)

Require Import
        CertifiedExtraction.Extraction.BinEncoders.BinEncoders.

Opaque Transformer.transform_id.
Opaque EncodeAndPad. (* FIXME move *)
Require Import Coq.Program.Program.

Definition PacketAsCollectionOfVariables
           {av} vid vmask vquestion vanswer vauthority vadditional (p: packet_t)
  : Telescope av :=
  [[ vid ->> p.(pid) as _ ]]
    :: [[ vmask ->> p.(pmask) as _ ]]
    :: [[ vquestion ->> ` p.(pquestion) as _ ]]
    :: [[ vanswer ->> ` p.(panswer) as _ ]]
    :: [[ vauthority ->> ` p.(pauthority) as _ ]]
    :: [[ vadditional ->> ` p.(padditional) as _ ]]
    :: Nil.

Definition DnsCacheAsCollectionOfVariables
           {av} veMap vdMap voffs (c: DnsMap.CacheT)
  : Telescope av :=
  [[ veMap ->> c.(DnsMap.eMap) as _ ]]
    :: [[ vdMap ->> c.(DnsMap.dMap) as _ ]]
    :: [[ voffs ->> c.(DnsMap.offs) as _ ]]
    :: Nil.

Hint Unfold PacketAsCollectionOfVariables : f2f_binencoders_autorewrite_db.
Hint Unfold DnsCacheAsCollectionOfVariables : f2f_binencoders_autorewrite_db.

Ltac _packet_prepare_cache :=
  may_alloc_head; (* Only create bindings for the cache once. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons (NTSome _) (ret (fst (Compose.compose _ _ _ _))) _ =>
              let veMap := gensym "eMap" in
              let vdMap := gensym "dMap" in
              let voffs := gensym "offs" in
              apply (ProgOk_Add_snd_ret
                       (DnsCacheAsCollectionOfVariables
                          (NTSome veMap) (NTSome vdMap) (NTSome voffs)))
            end).

Ltac packet_start_compiling :=
  repeat match goal with
         | [ p: packet_t |- _ ] => destruct p
         | _ => progress unfold packet_encode, encode_packet; simpl
         end.

Ltac _packet_encode_step :=
  (* try _packet_show_progress; *)
  match goal with
  | _ => _encode_cleanup
  | _ => _packet_prepare_cache
  | _ => _encode_FixInt
  | _ => _encode_IList_compile
  | _ => _packet_encodeType
  | _ => _packet_encodeClass
  | _ => _compile_CallWrite16
  | _ => _compile_Read
  | _ => _compile_ReadConstantN
  | _ => _compile_CallAdd16
  | _ => _compile_CallListLength
  | _ => _compile_CallAllocString
  | _ => _compile_CallAllocEMap
  | _ => _compile_CallAllocDMap
  | _ => _compile_CallAllocOffset
  | _ => _compile_CallDeallocQuestion
  | _ => _compile_CallDeallocResource
  | _ => _compile_compose
  | _ => _compile_step
  end.

Ltac _packet_encode_t :=
  progress (repeat _packet_encode_step).


Lemma DnsCache_addE_is_plus1 :
  forall n (cache: @Cache.CacheEncode DnsMap.cache),
    addE_n n cache =
    {| DnsMap.eMap := DnsMap.eMap cache;
       DnsMap.dMap := DnsMap.dMap cache;
       DnsMap.offs := DnsMap.offs cache + N.of_nat n |}.
Proof.
  Opaque N.of_nat.
  induction n; destruct cache; simpl in *.
  + rewrite N.add_0_r; reflexivity.
  + rewrite IHn; simpl in *.
    rewrite <- N.add_assoc, N.add_1_l, Nat2N.inj_succ; reflexivity.
    Transparent N.of_nat.
Qed.

Example encode :
  ParametricExtraction
    #vars      p
    #program   ret (packet_encode p)
    #arguments (PacketAsCollectionOfVariables
                  (NTSome "id") (NTSome "mask") (NTSome "question")
                  (NTSome "answer") (NTSome "authority") (NTSome "additional")
                  p)
    #env       (GLabelMap.empty (FuncSpec ADTValue)).
Proof.
  start_compiling.
  packet_start_compiling.

  Start Profiling.
  Time repeat _packet_encode_t. (* 411s *)
  Show Profile.

  (* FIXME remove compile_do_use_transitivity_to_handle_head_separately? Or
       add a case with [fun _ => _] as the function for [ProgOk_Transitivity_First] *)

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "answer" ->> ` panswer as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode name") nil); admit. }


  { _packet_encode_t. }

  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode resource name") nil); admit. }

  { _packet_encode_t. }
  
  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode resource ttl") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "authority" ->> ` pauthority as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode length of resource data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode resource data") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority name") nil); admit. }

  { _packet_encode_t. }

  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority ttl") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::[[ ` "additional" ->> ` padditional as _]]::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode length of authority data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode authority data") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional name") nil); admit. }

  { _packet_encode_t. }

  { _packet_encode_t. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                     ::[[ ` "id" ->> pid as _]]
                     ::[[ ` "mask" ->> pmask as _]]
                     ::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional ttl") nil); admit. }

  { instantiate (1 := [[ ` "head" ->> head as _]]
                       ::[[ ` "id" ->> pid as _]]
                       ::[[ ` "mask" ->> pmask as _]]
                       ::Nil).
    instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode length of additional data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Encode additional data") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Deallocate pid and mask") nil); admit. }

  { instantiate (1 := Call (DummyArgument "tmp") ("admitted", "Deallocate cache") nil); admit. }

  Grab Existential Variables.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  exact "AAAAAA".
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
  repeat constructor.
Defined.

Eval lazy in (extract_facade encode).

(*  *)