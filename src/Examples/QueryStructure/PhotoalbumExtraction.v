Require Import Coq.Bool.Bool Coq.Strings.String Fiat.Common.String_as_OT Coq.Structures.OrderedTypeEx.
Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlNatInt Coq.extraction.ExtrOcamlZInt Coq.extraction.ExtrOcamlString.

Require Import Fiat.QueryStructure.Automation.MasterPlan
        Fiat.Examples.QueryStructure.Photoalbum.

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
Definition AddPhotoS := "AddPhoto".
Definition AddEventS := "AddEvent".
Definition PhotosByDateRangeS := "PhotosByDateRange".
Definition PhotosByPersonsS := "PhotosByPersons".

Arguments AlbumImpl /.
Arguments callcADTConstructor / .
Arguments ComputationalADT.cConstructors / .
Arguments ComputationalADT.pcConstructors / .
Arguments callcADTMethod / .
Arguments ComputationalADT.cMethods / .
Arguments ComputationalADT.pcMethods / .
Definition InitAlbum : ComputationalADT.cRep AlbumImpl := Eval simpl in (CallConstructor AlbumImpl InitS).
Definition AddPhoto (data : list ascii) (persons : list string) (event : string)
           (r : ComputationalADT.cRep AlbumImpl)
  : ComputationalADT.cRep AlbumImpl * bool :=
  Eval simpl in CallMethod AlbumImpl AddPhotoS r {|prim_fst := data;
           prim_snd :=
             {| prim_fst := persons;
                prim_snd :=
                  {| prim_fst := event;
                     prim_snd := tt |}
             |}
         |}.
Definition AddEvent (name : string) (date : nat)
           (r : ComputationalADT.cRep AlbumImpl)
    : ComputationalADT.cRep AlbumImpl * bool :=
  Eval simpl in CallMethod AlbumImpl AddEventS r
                           {| prim_fst := name;
                              prim_snd :=
                                {| prim_fst := date;
                                   prim_snd := tt |}
                           |}.
Definition PhotosByDateRange (startT endT : nat) (r : ComputationalADT.cRep AlbumImpl)
  : ComputationalADT.cRep AlbumImpl * (list (AlbumSchema#PHOTOS)) :=
  Eval simpl in CallMethod AlbumImpl PhotosByDateRangeS r startT endT.
Definition PhotosByPersons (names : list string) (r : ComputationalADT.cRep AlbumImpl)
  : ComputationalADT.cRep AlbumImpl * (list (AlbumSchema#PHOTOS)) :=
  Eval simpl in CallMethod AlbumImpl PhotosByPersonsS r names.

Extraction "photoalbum.ml" InitAlbum AddPhoto AddEvent PhotosByDateRange PhotosByPersons.
