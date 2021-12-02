Require Import
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BinLib.Core.

Set Implicit Arguments.

Record test_t :=
  { f1 : { n : N | (n < exp2 32)%N };
    f2 : { l : list {n : N | (n < exp2 16)%N} | length l < exp2_nat 16} } .

Instance test_cache : Cache :=
  {| CacheFormat := unit;
     CacheDecode := unit;
     Equiv := fun _ _ => True |}.

Instance test_cache_add_nat : CacheAdd test_cache N :=
  {| addE := fun ce _ => ce;
     addD := fun cd _ => cd;
     add_correct := fun _ _ _ => id |}.

Definition format_test (t : test_t) (ce : CacheFormat) :=
  compose bmonoid (FixInt_format (f1 t)) (
  compose bmonoid (FixInt_format (FixList_getlength (f2 t))) (
  compose bmonoid (FixList_format FixInt_format (f2 t)) (
                       (fun e => (nil, e))))) ce.
(* Commenting out until we update for new framework. *)
(*
Definition test_decoder
  : { decode | format_decode_correct test_cache bmonoid (fun _ => True) format_test decode }.
Proof.
  eexists.
  eapply compose_format_correct. eapply FixInt_format_correct. solve_predicate.
  intro.
  eapply compose_format_correct. eapply FixInt_format_correct. solve_predicate.  
  intro.
  eapply compose_format_correct.
  eapply FixList_format_correct.
  eapply FixInt_format_correct.
  solve_predicate.
  intro.
  solve_done.
Defined.

Definition test_decoder'
  : list bool -> CacheDecode -> test_t * list bool * CacheDecode.
Proof.
  let p' := eval cbv delta [ proj1_sig test_decoder ] beta iota in (proj1_sig test_decoder) in
                                                                      pose p' as p.
  exact p.
Defined.
Print test_decoder'. *)
