Require Import Fiat.Common.Equality Fiat.Parsers.ParserFromParserADT.
Require Import Coq.ZArith.BinInt.
Require Export Fiat.Parsers.Refinement.Tactics.
Require Export Fiat.Common.BoolFacts.
Require Export Fiat.ADTNotation.BuildComputationalADT.
Require Export Fiat.Common.NatFacts.
Require Export Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Export Coq.Strings.Ascii.
Require Export Coq.extraction.ExtrOcamlBasic.
Require Export Coq.extraction.ExtrOcamlNatInt.
Require Export Coq.extraction.ExtrOcamlZInt.
Require Export Coq.extraction.ExtrOcamlString.
Require Export Coq.extraction.ExtrOcamlIntConv.
Require Export Fiat.Parsers.ExtrOcamlPrimitives.

Import ExtrOcamlPrimitives.Ocaml.

Extract Inlined Constant Compare_dec.lt_dec => "(<)".
Extract Inlined Constant BinNat.N.ltb => "(<)".
Extract Inlined Constant Sumbool.sumbool_of_bool => "(fun x -> x)".
Extract Inlined Constant Equality.ascii_beq => "(=)".
Extract Inlined Constant ascii_eq_dec => "(=)".
Extract Inlined Constant orbr => "(||)".
Extract Inlined Constant andbr => "(&&)".
Extract Constant minusr => "fun (n : int) (m : int) -> let v = n - m in if v < 0 then 0 else v".
Extract Constant minus => "fun (n : int) (m : int) -> let v = n - m in if v < 0 then 0 else v".
Extract Constant pred => "fun (n : int) -> if n < 1 then 0 else n - 1".
Extract Constant max => "fun (n : int) (m : int) -> if n >= m then n else m".
Extract Constant min => "fun (n : int) (m : int) -> if n <= m then n else m".
Extract Inlined Constant Ascii.N_of_ascii => "Char.code".
Extract Inlined Constant ContextFreeGrammar.Reflective.opt.N_of_ascii => "Char.code".

Global Arguments string_dec : simpl never.
Global Arguments Equality.string_beq : simpl never.
Global Arguments SplitterFromParserADT.msplits / _ _ _ _ _ _ _ _.
Global Arguments splits_for / _ _ _ _ _ _ _.
Global Arguments Equality.ascii_beq !_ !_ / .
Global Arguments SplitterFromParserADT.mlength / _ _ _ _ _.
Global Arguments SplitterFromParserADT.mis_char / _ _ _ _ _ _.
Global Arguments SplitterFromParserADT.mtake / _ _ _ _ _ _.
Global Arguments SplitterFromParserADT.mdrop / _ _ _ _ _ _.
Global Arguments SplitterFromParserADT.mto_string / _ _ _ _ _.
Global Arguments new_string_of_string / _ _ _ _ _ _.
Global Arguments ComputationalADT.cRep / _ _.
Global Arguments new_string_of_base_string / _ _ _ _ _.
Global Arguments ComputationalADT.cConstructors / _ _ _.
Global Arguments Wf.prod_relation / _ _ _ _ _ _.
Global Arguments Wf_nat.ltof / _ _ _ _.
Global Arguments find_first_char_such_that / _ _ _ _ _.
Global Arguments find_first_char_such_that' / _ _ _ _ _ _.

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
                                (iterations : nat) (duplicates_per_iteration : nat),
                           unit.
Extract Constant display_info
=> "fun sum median mean sample_variance iterations duplicates_per_iteration
-> Printf.printf ""total: %f, median: %f, mean: %f, sample variance: %f, iterations: %d (%d on each)\n"" sum median mean sample_variance iterations duplicates_per_iteration".

Definition display_info_for_times (duplicates_per_iteration : nat) (ls : list Ocaml.float) : unit
  := let iter := List.length ls in
     let sum := Σ ls in
     let med := median ls in
     let avg := mean ls in
     let var := sample_variance ls in
     display_info sum med avg var iter duplicates_per_iteration.

Fixpoint copy {A} (n : nat) (x : A) : list A
  := match n with
       | 0 => nil
       | S n' => x::copy n' x
     end.

Definition profile_parser
           {T stringT}
           (line : stringT)
           (parse : stringT -> bool)
           (num_times : nat)
           (duplicates_per_iteration : nat)
           (all_say_yes : T)
           (all_say_no : T)
           (mixed_answers : forall (yes no : nat), T)
: T * list Ocaml.float
  := let parse_once := (fun x : unit => let () := x in parse line) in
     let starters := copy duplicates_per_iteration tt in
     let parse_many := (fun x : unit => let () := x in List.map parse_once starters) in
     let time_results := List.map
                           (fun x : unit => let () := x in @profile (list bool) parse_many)
                           (copy num_times tt) in
     let times := List.map fst time_results in
     let results := List.map snd time_results in
     ((if List.fold_right andb true (flatten1 results)
       then all_say_yes
       else if List.fold_right andb true (List.map negb (flatten1 results))
            then all_say_no
            else mixed_answers
                   (List.length (List.filter (fun x => x) (flatten1 results)))
                   (List.length (List.filter negb (flatten1 results)))),
      times).

Definition display_profile_parser_results
           {T stringT}
           (line : stringT)
           (parse : stringT -> bool)
           (num_times : nat)
           (duplicates_per_iteration : nat)
           (all_say_yes : T)
           (all_say_no : T)
           (mixed_answers : forall (yes no : nat), T)
: unit * T
  := let '(res, times) := profile_parser line parse num_times duplicates_per_iteration all_say_yes all_say_no mixed_answers in
     let tt_val := display_info_for_times duplicates_per_iteration times in
     (tt_val, res).

Definition premain'
           {stringT}
           (line : stringT)
           (num_times : nat)
           (duplicates_per_iteration : nat)
           (parse : stringT -> bool)
: unit
  := let '((), exit_code)
         := @display_profile_parser_results
              nat
              stringT
              line
              parse
              num_times
              duplicates_per_iteration
              0
              1
              (fun _ _ => 2)
     in Pervasives.exit (int_of_nat exit_code).

Definition line_ocaml : Ocaml.string := Pervasives.input_line chan.

Definition line : string := Ocaml.explode line_ocaml.

Definition premain_ocaml (parse : Ocaml.string -> bool) : unit
  := premain' line_ocaml 10 10 parse.

Definition premain (parse : Coq.Strings.String.string -> bool) : unit
  := premain' line 10 10 parse.
