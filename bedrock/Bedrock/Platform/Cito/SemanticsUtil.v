Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.Semantics.
  Require Import Coq.Lists.List.

  Fixpoint make_triples pairs (outs : list (option ADTValue)) : list (ArgTriple ADTValue) :=
    match pairs, outs with
      | p :: ps, o :: os => {| Word := fst p; ADTIn := snd p; ADTOut := o |} :: make_triples ps os
      | _, _ => nil
    end.

  Require Import Bedrock.Memory.
  Require Import Bedrock.Platform.Cito.WordMap.
  Import WordMap.

  Definition store_pair heap (p : W * Value ADTValue) :=
    match snd p with
      | SCA _ => heap
      | ADT a => add (fst p) a heap
    end.

  Definition make_heap pairs := fold_left store_pair pairs (@empty _).

  Definition word_scalar_match (p : W * Value ADTValue) :=
    let word := fst p in
    let in_ := snd p in
    match in_ with
      | SCA w => word = w
      | _ => True
    end.

  Definition good_scalars pairs := List.Forall word_scalar_match pairs.

End ADTValue.
