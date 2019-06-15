Require Export ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString ExtrOcamlZInt.

(* Work around the fact that Decimal declares a type "int" *)
Extract Inductive nat => "OCamlNativeInt.t" [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Constant Coq.Init.Nat.ltb => "(<)".
Extract Constant Coq.Init.Nat.leb => "(<=)".

(* ExtrOCamlNatInt uses Pervasives.max, which is slow *)
Extract Constant Nat.sub =>
  "fun (x: OCamlNativeInt.t) (y: OCamlNativeInt.t) ->
if x <= y then 0 else (x - y)".

(** A few additional tweaks *)

Require Import Fiat.Common.String_as_OT.
Require Import Coq.Structures.OrderedTypeEx.

Extraction Inline negb.
Extract Inductive Bool.reflect => bool [ true false ].

Extract Constant Coq.Strings.String.string_dec  => "(=)".
Extract Constant String_as_OT.eq_dec  => "(=)".
Extract Constant Nat_as_OT.eq_dec => "(=)".

Extract Constant String_as_OT.compare => "fun a b -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant Nat_as_OT.compare    => "fun (a: int) (b: int) -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant String_as_OT.string_compare => "fun a b -> let comp = compare a b in
                                                 if comp = 0 then Eq else if comp < 0 then Lt else Gt".

(** * Inline a few functions *)
Require Import
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad.
Extraction Inline fst snd Basics.compose.
Extraction Inline Projection_AlignedEncodeM.
Extraction Inline GetCurrentByte SetCurrentByte.
Extraction Inline BindAlignedDecodeM ReturnAlignedDecodeM ThrowAlignedDecodeM.
Extraction Inline AppendAlignedEncodeM ReturnAlignedEncodeM ThrowAlignedEncodeM.
Extraction Inline Common.If_Opt_Then_Else AlignedByteString.LetIn.

(** * Extract words as int64
      (Only works for words with length < 64) *)

Require Import Word.
Require Import BinLib.AlignWord.

Extract Inductive word =>
"Int64Word.t"
  ["(Int64Word.w0)" "Int64Word.ws"]
  "Int64Word.destruct".

Extract Inlined Constant Core.char => "Int64Word.t".

Extract Inlined Constant whd => "Int64Word.whd".
Extract Inlined Constant wtl => "Int64Word.wtl".
Extract Inlined Constant zext => "Int64Word.zext".
Extract Inlined Constant wplus => "Int64Word.wplus".
Extract Inlined Constant wmult => "Int64Word.wmult".
Extract Inlined Constant wminus => "Int64Word.wminus".
Extract Inlined Constant weq => "Int64Word.weq".
Extract Inlined Constant weqb => "Int64Word.weqb".
Extract Inlined Constant wlt => "Int64Word.wlt".
Extract Inlined Constant wlt_dec => "Int64Word.wlt_dec".
Extract Inlined Constant wand => "Int64Word.wand".
Extract Inlined Constant wor => "Int64Word.wor".
Extract Inlined Constant wnot => "Int64Word.wnot".
Extract Inlined Constant wneg => "Int64Word.wneg".
Extract Inlined Constant wordToNat => "Int64Word.wordToNat".
Extract Inlined Constant natToWord => "Int64Word.natToWord".
Extract Inlined Constant NToWord => "Int64Word.natToWord".
Extract Inlined Constant wordToN => "Int64Word.wordToN".
Extract Inlined Constant wzero => "Int64Word.wzero".
Extract Inlined Constant wzero' => "Int64Word.wzero'".
Extract Inlined Constant wones => "Int64Word.wones".

Extract Inlined Constant WordOpt.word_split_hd => "Int64Word.word_split_hd".
Extract Inlined Constant WordOpt.word_split_tl => "Int64Word.word_split_tl".
Extract Inlined Constant split1' => "Int64Word.split1'".
Extract Inlined Constant split2' => "Int64Word.split2'".
Extract Inlined Constant split1 => "Int64Word.split1".
Extract Inlined Constant split2 => "Int64Word.split2".
Extract Inlined Constant WordOpt.SW_word => "Int64Word.SW_word".
Extract Inlined Constant combine => "Int64Word.combine".
Extract Inlined Constant Core.append_word => "Int64Word.append".

Extract Inlined Constant PeanoNat.Nat.div => "(/)".

Definition word_split_hd_test := WordOpt.word_split_hd (natToWord 5 30).
Definition word_split_tl_test := wordToNat (WordOpt.word_split_tl (natToWord 5 30)).
Definition alignword_split1'_test := wordToNat (AlignWord.split1' 2 3 (natToWord 5 30)).
Definition alignword_split2'_test := wordToNat (AlignWord.split2' 2 3 (natToWord 5 30)).
Definition split1_test := wordToNat (split1 3 2 (natToWord 5 30)).
Definition split2_test := wordToNat (split2 3 2 (natToWord 5 30)).
Definition combine_test := wordToNat (combine (natToWord 5 30) (natToWord 7 14)).
Definition append_word_test := wordToNat (Core.append_word (@natToWord 8 5) (@natToWord 12 126)).

(** * Special case of internet checksum *)
Require Import Narcissus.Formats.InternetChecksum.
Extract Constant InternetChecksum.OneC_plus => "Int64Word.onec_plus".

(** Efficient bytestrings *)

Extract Inductive Fin.t =>
"ArrayVector.idx_t"
  ["ArrayVector.zero" "ArrayVector.succ"]
  "ArrayVector.destruct_idx".

Extract Inlined Constant Fin.L => "(fun _ n p -> p)".
Extract Inlined Constant Fin.R => "(fun _ n p -> n + p)".
Extract Inlined Constant Fin.eqb => "(fun _ _ n p -> n = p)".

Extract Inductive Vector.t =>
"StackVector.t"
  ["StackVector.empty ()" "StackVector.cons"]
  "StackVector.destruct".

Extract Inductive VectorDef.t =>
"StackVector.t"
  ["StackVector.empty ()" "StackVector.cons"]
  "StackVector.destruct".

Extract Inlined Constant Vector.nth => "StackVector.nth".
Extract Inlined Constant VectorDef.nth => "StackVector.nth".
Extract Inlined Constant AlignedDecodeMonad.Vector_nth_opt => "StackVector.nth_opt".
Extract Inlined Constant EnumOpt.word_indexed => "StackVector.index".

(* CPC clean up CstructBytestring.ml to remove unneeded stuff *)

Require Import Fiat.Narcissus.BinLib.AlignedByteString.
Require Import Fiat.Narcissus.BinLib.AlignedByteBuffer.
Extract Constant ByteBuffer.t => "CstructBytestring.storage_t".
Extract Inlined Constant ByteBuffer.t => "CstructBytestring.storage_t".
Extract Inlined Constant ByteBuffer.nil => "CstructBytestring.nil".
Extract Inlined Constant ByteBuffer.cons => "CstructBytestring.cons".
Extract Inlined Constant ByteBuffer.hd => "CstructBytestring.hd".
Extract Inlined Constant ByteBuffer.tl => "CstructBytestring.tl".
Extract Inlined Constant ByteBuffer.to_list => "CstructBytestring.to_list".
Extract Inlined Constant ByteBuffer.of_list => "CstructBytestring.of_list".
Extract Inlined Constant ByteBuffer.of_vector => "CstructBytestring.of_vector".
Extract Inlined Constant ByteBuffer.to_vector => "CstructBytestring.to_vector".
Extract Inlined Constant ByteBuffer.fold_left => "CstructBytestring.fold_left".
Extract Inlined Constant ByteBuffer.append => "CstructBytestring.append".
Extract Inlined Constant ByteBuffer.drop => "CstructBytestring.drop".
Extract Inlined Constant nth_opt => "CstructBytestring.nth_opt".
Extract Inlined Constant set_nth' => "CstructBytestring.set_nth".
Extract Inlined Constant initialize_Aligned_ByteString => "CstructBytestring.create".
Extract Inlined Constant InternetChecksum.ByteBuffer_checksum_bound => "CstructBytestring.checksum_bound".
Extract Inlined Constant AlignedByteBuffer.buffer_blit_buffer => "CstructBytestring.blit_buffer".
Extract Constant AlignedByteBuffer.bytebuffer_of_bytebuffer_range =>
  "(fun sz from len v ->
    let b = CstructBytestring.slice_range sz from len v in
    ExistT (CstructBytestring.length b, b))".
