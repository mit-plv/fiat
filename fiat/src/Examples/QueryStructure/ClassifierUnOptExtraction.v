Require Import Coq.Bool.Bool Coq.Strings.String Fiat.Common.String_as_OT Coq.Structures.OrderedTypeEx.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlNatInt Coq.extraction.ExtrOcamlZInt Coq.extraction.ExtrOcamlString.

Require Import Fiat.QueryStructure.Automation.MasterPlan
        Fiat.Examples.QueryStructure.ClassifierUnOpt.

Extract Inlined Constant fst => fst.
Extract Inlined Constant snd => snd.
Extract Inlined Constant negb => not.
Extract Inlined Constant List.length => "List.length".
Extract Inlined Constant app => "( @ )".
Extract Constant String_as_OT.eq_dec  => "(=)".
Extract Constant Nat_as_OT.eq_dec     => "(=)".

Extract Constant String_as_OT.compare => "fun a b -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant Nat_as_OT.compare    => "fun (a: int) (b: int) -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant String_as_OT.string_compare => "fun a b -> let comp = compare a b in
                                                 if comp = 0 then Eq else if comp < 0 then Lt else Gt".
Extract Inductive reflect            => bool [ true false ].
Extract Inlined Constant iff_reflect => "".

Open Scope string_scope.
Definition InitS := "Init".
Definition AddRuleS := "AddRule".
Definition ContactMessagesS := "ContactMessages".
Definition ClassifyS := "Classify".

Arguments ClassifierImpl /.
Arguments callcADTConstructor / .
Arguments ComputationalADT.cConstructors / .
Arguments ComputationalADT.pcConstructors / .
Arguments callcADTMethod / .
Arguments ComputationalADT.cMethods / .
Arguments ComputationalADT.pcMethods / .
Definition InitClassifier : ComputationalADT.cRep ClassifierImpl :=
  Eval simpl in (CallConstructor ClassifierImpl InitS).
Definition AddRule (priority : nat) (destination : list nat) (policy : Policy Protocol)
           (action : bool)
           (r : ComputationalADT.cRep ClassifierImpl)
  : ComputationalADT.cRep ClassifierImpl * bool :=
  Eval simpl in CallMethod ClassifierImpl AddRuleS r {|prim_fst := priority;
           prim_snd :=
             {| prim_fst := destination;
                prim_snd :=
                  {| prim_fst := policy;
                     prim_snd :=
                       {| prim_fst := action;
                          prim_snd := tt |}
                  |}
             |}
         |}.
Definition Classify (dest : list nat)
           (proto : Protocol)
           (r : ComputationalADT.cRep ClassifierImpl)
  : ComputationalADT.cRep ClassifierImpl * (list RuleRecord) :=
  Eval simpl in CallMethod ClassifierImpl ClassifyS r {| destination := dest;
                                                                protocol := proto |}.

Extraction "classifier_unopt.ml" InitClassifier AddRule Classify.
