Require Import Narcissus.Examples.Guard.StatefulGuard.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Narcissus.Examples.Guard.Core.
Require Import Narcissus.OCamlExtraction.Extraction.

Open Scope string_scope.

Arguments Fiat.Common.ilist2.ilist2_hd : simpl nomatch.
Arguments Fiat.Common.ilist2.ilist2_tl : simpl nomatch.

Notation simp x :=
  ltac:(let x := (eval red in x) in
        let x := (eval cbn in x) in
        exact x) (only parsing).

Definition guard_init (_: unit) : ComputationalADT.cRep GuardImpl :=
  simp (CallConstructor GuardImpl "Init").

Definition guard_process_packet (rep: ComputationalADT.cRep GuardImpl) (bs: bytes) (chain: IPTables.chain) : (ComputationalADT.cRep GuardImpl * option result) :=
  match IPTables.input_of_bytes chain bs with
  | Some input => simp (CallMethod GuardImpl "Filter" rep input)
  | None => (rep, Some DROP)
  end.

Extract Inductive Vector.t => "ListVector.t" ["(ListVector.empty ())" "ListVector.cons"] "ListVector.destruct".
Extract Inductive VectorDef.t => "ListVector.t" ["(ListVector.empty ())" "ListVector.cons"] "ListVector.destruct".
Extract Inlined Constant Vector.nth => "ListVector.nth".
Extract Inlined Constant AlignedDecodeMonad.Vector_nth_opt => "ListVector.nth_opt".
Extract Inlined Constant ith => "ListVector.ith".
Extract Inlined Constant ith2 => "ListVector.ith2".

Require Import Coq.extraction.ExtrOcamlZInt.

Print ADTImplMethods.
Print guard_init.

Extraction Inline
           StatefulGuard.ADTImplMethod
           StatefulGuard.ADTImplMethod0
           StatefulGuard.ADTImplMethod1
           StatefulGuard.ADTImplMethod2
           StatefulGuard.ADTImplMethod3
           StatefulGuard.ADTImplMethod4
           StatefulGuard.ADTImplMethod5.

Extract Inlined Constant IPTables.N_of_fin => "ArrayVector.idx_to_N".
Extraction Inline If_Then_Else.
Extraction NoInline negb.

Extraction "FiatGuard" guard_init guard_process_packet.
