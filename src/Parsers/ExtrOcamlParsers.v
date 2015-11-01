Require Import Coq.Arith.Compare_dec Coq.Strings.String.
Require Import Fiat.Common.Equality Fiat.Parsers.ParserFromParserADT Fiat.Parsers.SplitterFromParserADT Fiat.Parsers.ParserInterface.
Require Import Coq.Arith.Wf_nat.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.NatFacts.
Require Import Coq.ZArith.BinInt.
Require Export Fiat.Parsers.Refinement.Tactics.
Require Export Fiat.ADTNotation.BuildComputationalADT.
Require Export Fiat.Common.NatFacts.
Require Export Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Export Coq.Strings.Ascii.
Require Export Coq.extraction.ExtrOcamlBasic.
Require Export Coq.extraction.ExtrOcamlNatInt.
Require Export Coq.extraction.ExtrOcamlString.
Require Export Coq.extraction.ExtrOcamlIntConv.
Require Export Fiat.Parsers.ExtrOcamlPrimitives.

Import ExtrOcamlPrimitives.Ocaml.

Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Inlined Constant Sumbool.sumbool_of_bool => "(fun x -> x)".
Extract Inlined Constant Equality.ascii_beq => "(=)".
Extract Inlined Constant ascii_eq_dec => "(=)".
Extract Constant minusr => "fun n m -> Pervasives.max 0 (n-m)".

Global Arguments string_dec : simpl never.
Global Arguments Equality.string_beq : simpl never.
Global Arguments SplitterFromParserADT.msplits / .
Global Arguments splits_for / .
Global Arguments Equality.ascii_beq !_ !_ / .
Global Arguments SplitterFromParserADT.mlength / .
Global Arguments SplitterFromParserADT.mis_char / .
Global Arguments SplitterFromParserADT.mtake / .
Global Arguments SplitterFromParserADT.mdrop / .
Global Arguments SplitterFromParserADT.mto_string / .
Global Arguments new_string_of_string / .
Global Arguments ComputationalADT.cRep / .
Global Arguments new_string_of_base_string / .
Global Arguments ComputationalADT.cConstructors / .
Global Arguments Wf.prod_relation / .
Global Arguments Wf_nat.ltof / .
Global Arguments find_first_char_such_that / .
Global Arguments find_first_char_such_that' / .

Module HideProofs.
  Notation hex := (ex _).
  Notation exist' x := (exist _ x _).
  Notation horr := (or_intror _).
  Notation horl := (or_introl _).
End HideProofs.

Definition chan : Pervasives.in_channel
  := match z_of_int (Array.length Sys.argv) with
       | 0%Z | 1%Z => Pervasives.stdin
       | 2%Z => let chan := Pervasives.open_in (Array.get Sys.argv 1) in
                let v := Pervasives.at_exit (fun _ => Pervasives.close_in chan) in
                Ocaml.sequence
                  v
                  chan
       | argc => Pervasives.exit (int_of_z argc)
     end.

Definition line : string := Ocaml.explode (Pervasives.input_line chan).

Definition profile : forall {T}, (unit -> T) -> Ocaml.float * T
  := fun _ f
     => let startt := Sys.time tt in
        let ret := f tt in
        let endt := Sys.time tt in
        ((endt - startt)%ocaml_float, ret).

Fixpoint sum_of_float (ls : list Ocaml.float) : Ocaml.float
  := match ls with
       | nil => Pervasives.float_of_nat 0
       | x::xs => x + sum_of_float xs
     end%ocaml_float.

Local Notation Σ ls := (sum_of_float ls).

Definition mean (ls : list Ocaml.float) : Ocaml.float
  := (Σ ls / List.length ls)%ocaml_float.

Definition sample_variance (ls : list Ocaml.float) : Ocaml.float
  := let avg := mean ls in
     (Σ (List.map (fun x => (x - avg) * (x - avg)) ls)
        / (List.length ls - 1))%ocaml_float.

Definition median (ls : list Ocaml.float) : Ocaml.float
  := let ls' := Ocaml.List.sort Pervasives.compare ls in
     let len := List.length ls in
     ((List.nth (Div2.div2 (len - 1)) ls' 0 + List.nth (Div2.div2 len) ls' 0)
        / 2)%ocaml_float.

Parameter display_info : forall (sum median mean sample_variance : Ocaml.float)
                                (iterations : nat),
                           unit.
Extract Constant display_info
=> "fun sum median mean sample_variance iterations
-> Printf.printf ""total: %f, median: %f, mean: %f, sample variance: %f, iterations: %d\n"" sum median mean sample_variance iterations".

Definition display_info_for_times (ls : list Ocaml.float) : unit
  := let iter := List.length ls in
     let sum := Σ ls in
     let med := median ls in
     let avg := mean ls in
     let var := sample_variance ls in
     display_info sum med avg var iter.

Fixpoint copy {A} (n : nat) (x : A) : list A
  := match n with
       | 0 => nil
       | S n' => x::copy n' x
     end.

Definition profile_parser
           {T}
           (parse : Coq.Strings.String.string -> bool)
           (num_times : nat)
           (all_say_yes : T)
           (all_say_no : T)
           (mixed_answers : forall (yes no : nat), T)
: T * list Ocaml.float
  := let time_results := List.map
                           (fun x : unit => let () := x in @profile bool (fun x => let () := x in parse line))
                           (copy num_times tt) in
     let times := List.map fst time_results in
     let results := List.map snd time_results in
     ((if List.fold_right andb true results
       then all_say_yes
       else if List.fold_right andb true (List.map negb results)
            then all_say_no
            else mixed_answers
                   (List.length (List.filter (fun x => x) results))
                   (List.length (List.filter negb results))),
      times).

Definition display_profile_parser_results
           {T}
           (parse : Coq.Strings.String.string -> bool)
           (num_times : nat)
           (all_say_yes : T)
           (all_say_no : T)
           (mixed_answers : forall (yes no : nat), T)
: unit * T
  := let '(res, times) := profile_parser parse num_times all_say_yes all_say_no mixed_answers in
     let tt_val := display_info_for_times times in
     (tt_val, res).

Definition premain'
           (num_times : nat)
           (parse : Coq.Strings.String.string -> bool)
: unit
  := let '((), exit_code)
         := @display_profile_parser_results
              nat
              parse
              num_times
              0
              1
              (fun _ _ => 2)
     in Pervasives.exit (int_of_nat exit_code).

Definition premain (parse : Coq.Strings.String.string -> bool) : unit
  := premain' 10 parse.
