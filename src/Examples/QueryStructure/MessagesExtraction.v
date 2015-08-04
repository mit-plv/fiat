Require Import Bool Coq.Strings.String String_as_OT OrderedTypeEx.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt ExtrOcamlString.

Require Import Fiat.QueryStructure.Automation.MasterPlan
        Fiat.Examples.QueryStructure.Messages.

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

Open Scope string.
Definition InitS := "Init".
Definition AddMessageS := "AddMessage".
Definition AddContactS := "AddContact".
Definition ContactMessagesS := "ContactMessages".
Definition RelevantMessagesS := "RelevantMessages".

Arguments MessagesImpl /.
Arguments callcADTConstructor / .
Arguments ComputationalADT.cConstructors / .
Arguments ComputationalADT.pcConstructors / .
Arguments callcADTMethod / .
Arguments ComputationalADT.cMethods / .
Arguments ComputationalADT.pcMethods / .
Definition InitMessages : ComputationalADT.cRep MessagesImpl := Eval simpl in (CallConstructor MessagesImpl InitS tt).
Definition AddMessage (num : nat) (time : nat) (msg : list string)
           (r : ComputationalADT.cRep MessagesImpl)
  : ComputationalADT.cRep MessagesImpl * bool :=
  Eval simpl in CallMethod MessagesImpl AddMessageS r {|prim_fst := num;
           prim_snd :=
             {| prim_fst := time;
                prim_snd :=
                  {| prim_fst := msg;
                     prim_snd := tt |}
             |}
         |}.
Definition AddContact (num : nat) (name : string) (r : ComputationalADT.cRep MessagesImpl)
    : ComputationalADT.cRep MessagesImpl * bool :=
  Eval simpl in CallMethod MessagesImpl AddContactS r
                           {| prim_fst := num;
                              prim_snd :=
                                {| prim_fst := name;
                                   prim_snd := tt |}
                           |}.
Definition ContactMessages (name : string) (r : ComputationalADT.cRep MessagesImpl)
  : ComputationalADT.cRep MessagesImpl * (list (list string)) :=
  Eval simpl in CallMethod MessagesImpl ContactMessagesS r name.
Definition RelevantMessages (keywords : list string) (r : ComputationalADT.cRep MessagesImpl)
  : ComputationalADT.cRep MessagesImpl * (list (list string)) :=
  Eval simpl in CallMethod MessagesImpl RelevantMessagesS r keywords.
Extraction "messages.ml" InitMessages AddMessage AddContact ContactMessages RelevantMessages.
