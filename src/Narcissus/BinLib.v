Require Import Fiat.Narcissus.Common.Monoid.

Require Import Bedrock.Word.

Require Export
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad.

Global Instance ByteStringQueueMonoid : Monoid ByteString := ByteStringQueueMonoid.

(* Various Constants that clients should never simplify. *)
Global Arguments split1 : simpl never.
Global Arguments split2 : simpl never.
Global Arguments weq : simpl never.
Global Arguments natToWord : simpl never.
Global Arguments Guarded_Vector_split : simpl never.
Global Arguments Core.append_word : simpl never.
Global Arguments split1' : simpl never.
Global Arguments split2' : simpl never.
Global Arguments natToWord : simpl never.
Global Arguments combine : simpl never.
Global Arguments Vector.nth : simpl never.
Global Arguments SetCurrentBytes : simpl never.
