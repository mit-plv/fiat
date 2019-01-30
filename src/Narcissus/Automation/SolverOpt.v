Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.Vector.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

Ltac apply_compose :=
  intros;
  match goal with
    H : cache_inv_Property ?P ?P_inv |- _ =>
    first [eapply (compose_format_correct_no_dep _ H); clear H
          | eapply (compose_format_correct H); clear H
          ]
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac shelve_inv :=
  let H' := fresh in
  let data := fresh in
  intros data H';
  repeat destruct H';
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

Ltac solve_data_inv :=
    first [ simpl; intros; exact I
| shelve_inv ].
