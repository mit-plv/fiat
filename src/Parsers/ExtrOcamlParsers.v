Require Import Coq.Arith.Compare_dec.
Require Import ADTSynthesis.Common.Equality.
Require Export ExtrOcamlBasic.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlString.
Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Inlined Constant Sumbool.sumbool_of_bool => "(fun x -> x)".
Extract Inlined Constant Equality.ascii_beq => "(=)".
Extract Inlined Constant ascii_eq_dec => "(=)".
