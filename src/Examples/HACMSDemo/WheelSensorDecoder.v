Require Import Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Structures.OrderedType.

Require Import
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.StringOpt
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import
        Fiat.Common.SumType
        Fiat.Examples.Tutorial.Tutorial
        Fiat.Examples.DnsServer.DecomposeEnumField
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.Examples.HACMSDemo.DuplicateFree
        Fiat.Examples.HACMSDemo.HACMSDemo
        Fiat.Examples.HACMSDemo.WheelSensor.

Definition Sharpened_packet_decoder
  : { decodePlusCacheInv |
      exists P_inv,
      (cache_inv_Property (snd decodePlusCacheInv) P_inv
       -> encode_decode_correct_f cache transformer good_reading encode_SensorData_Spec (fst decodePlusCacheInv) (snd decodePlusCacheInv))
      /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
Proof.
  eexists (_, _); eexists _; split; simpl.
  (* We synthesize the decoder by building decoders for *)
  (* each of the components of the original type. *)
  repeat build_decoder_component.
  (* We have enough information in the context to build *)
  (* the original type. *)
  finalize_decoder good_reading.
  (* We finish by showing the environment doesn't violate any of the *)
  (* assumptions of the decoders used (easy in this case, as we *)
  (* didn't use the environment :) *)
  solve_cache_inv.
Defined.

Definition packet_decoder :=
  Eval simpl in projT1 Sharpened_packet_decoder.

Print packet_decoder.
