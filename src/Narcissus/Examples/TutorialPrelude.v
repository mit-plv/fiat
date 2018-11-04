Require Export
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.
Require Export
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.BaseFormats.

Open Scope nat_scope.
Open Scope type_scope.
Open Scope format_scope.
Open Scope vector_scope.
Arguments Datatypes.length {_}.
Notation "x ⋅ y" := (Core.append_word y x) (left associativity, at level 3, format "x ⋅ y").

Definition encoder_impl' {S P}
           (enc: { encoder : (forall sz : nat, AlignedEncodeM (S:=S) sz) & P encoder })
           {sz} r v :=
  projT1 enc sz v 0 r tt.

Arguments encoder_impl' {_ _} _ [_].

Definition decoder_impl' {A P}
           (dec: {decoder : (forall sz : nat, AlignedDecodeM A sz) & P decoder }) {sz} v :=
  projT1 dec sz v 0 tt.

Arguments decoder_impl' {_ _} _ [_].

Notation simplify x :=
  (ltac:(let x := (eval unfold encoder_impl', decoder_impl' in x) in
         let x := (eval simpl in x) in
         (* let x := (eval unfold SetCurrentBytes in x) in *)
         (* let x := (eval simpl in x) in *)
         exact x)) (only parsing).

Notation encoder_impl x :=
  (simplify (encoder_impl' x)) (only parsing).

Notation decoder_impl x :=
  (simplify (decoder_impl' x)) (only parsing).

Definition must {T} : forall (x: option T),
    match x with
    | Some x0 => T
    | None => True
    end.
  destruct x; auto.
Defined.

Ltac synthesize_aligned_encoder ::=
  start_synthesizing_encoder;
  repeat (progress (decompose_aligned_encoder; eauto) || align_encoder_step). (* !! *)

Ltac synthesize_aligned_decoder ::=
  start_synthesizing_decoder;
    repeat (cbv beta; intros;
            unshelve
              match goal with
              | [ |- CorrectDecoder ?monoid _ _ _ _ _ ] =>
                (normalize_compose monoid) || (repeat decode_step idtac)
              | [ |- cache_inv_Property _ _ ] =>
                synthesize_cache_invariant
              | [ |- _ = ?f _ _ ] =>
                is_evar f; unfold decode_nat; optimize_decoder_impl
              | [ |- DecodeMEquivAlignedDecodeM _ ?f ] =>
                is_evar f; align_decoders
              | [ |- _ = _ ] => reflexivity
              end).

Ltac shelve_inv ::=
  let H' := fresh in
  let data := fresh in
  intros data H';
  repeat (destruct H'; [ idtac ]); (* !! *)
  match goal with
  | H : ?P data |- ?P_inv' =>
    is_evar P;
    let P_inv' := (eval pattern data in P_inv') in
    let P_inv := match P_inv' with ?P_inv data => P_inv end in
    let new_P_T := type of P in
    makeEvar new_P_T
             ltac:(fun new_P =>
                     unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
  end.

Notation "'format_const' x" := (format_word ◦ (fun _ => x)) (at level 50).
