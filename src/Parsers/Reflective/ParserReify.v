Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.ParserSyntax Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.Reify.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.

Module Export Exports.
   Export Reify.Exports.
   Export StringLike.Core.
End Exports.

Set Implicit Arguments.

Section parser.
  Context {Char}
          {HSLM : StringLikeMin Char}
          {HSL : StringLike Char}
          {HSLP : StringLikeProperties Char}.
  Context (G : pregrammar Char)
          (predata : @parser_computational_predataT Char)
          (splitdata : split_dataT).
  Context (str : String).

  Definition char_at_matches_interp_flip {_ : Reflective.interp_RCharExpr_data Char} str (n : nat)
    := Reflective.char_at_matches_interp n str.
  Definition split_string_for_production_flip str (n : production_carrierT) := @split_string_for_production _ _ _ _ n str.
End parser.

Ltac do_reify_has_parse has_parse cont :=
  idtac;
  let Char := match has_parse with context[@char_at_matches_interp ?Char ?HSLM] => Char end in
  let HSLM := match has_parse with context[@char_at_matches_interp Char ?HSLM] => HSLM end in
  let idata := match has_parse with context[@char_at_matches_interp Char HSLM ?idata] => idata end in
  let predata := match has_parse with context[@split_string_for_production Char HSLM ?predata ?splitdata] => predata end in
  let splitdata := match has_parse with context[@split_string_for_production Char HSLM predata ?splitdata] => splitdata end in
  let str := match has_parse with context[@char_at_matches_interp Char HSLM idata _ ?str] => str end in
  let hp := fresh "hp" in
  pose has_parse as hp;
  progress change (@char_at_matches_interp Char HSLM idata)
  with (fun n str' => @char_at_matches_interp_flip Char HSLM idata str' n) in hp;
  progress change (@split_string_for_production Char HSLM predata splitdata)
  with (fun n str' => @split_string_for_production_flip Char HSLM predata splitdata str' n) in hp;
  let has_parse := (eval cbv beta delta [hp] in hp) in
  clear hp;
  let f := lazymatch has_parse with
           | Wf2.Fix2
               _ _
               (fun len0 valid_len0 parse_nt valids offset len pf nt
                => option_rect
                     (fun _ => ?T)
                     (@?f len0 valid_len0 valids offset len nt)
                     ?default
                     _)
               ?strlen
               ?valid_len
               ?valids'
               0
               ?strlen
               _
               ?nt_idx
             => f
           end in
  let default := lazymatch has_parse with
           | Wf2.Fix2
               _ _
               (fun len0 valid_len0 parse_nt valids offset len pf nt
                => option_rect
                     (fun _ => ?T)
                     (@?f len0 valid_len0 valids offset len nt)
                     ?default
                     _)
               ?strlen
               ?valid_len
               ?valids'
               0
               ?strlen
               _
               ?nt_idx
             => default
           end in
  let f' := constr:(fun len0 valid_len0 parse_nt valids offset len nt
                    => f len0 valid_len0 valids offset len nt parse_nt) in
  let f' := match (eval pattern (@char_at_matches_interp_flip Char HSLM idata str), (@split_string_for_production_flip Char HSLM predata splitdata str) in f') with
            | ?f' _ _ => f'
            end in
  let r := constr:(fun var => (_ : reif_Term_of var f')) in
  let r := (eval cbv [reif_Term_of range_of] in r) in
  let rdefault := constr:(fun var => (_ : reif_Term_of var default)) in
  let rdefault := (eval cbv [reif_Term_of range_of] in rdefault) in
  let rp := lazymatch has_parse with
            | Wf2.Fix2
                _ _ _
                ?strlen
                ?valid_len
                ?valids'
                0
                ?strlen
                _
                ?nt_idx
              => constr:(fun var T fv defaultv => @RFix2 var T valid_len valids' fv defaultv valid_len valids' nt_idx)
            end in
  let rp := constr:(fun var => rp var _ (r var) (rdefault var)) in
  let rp := (eval cbv beta in rp) in
  cont rp.
