Require Import Fiat.Common.ilist Fiat.Common.BoundedLookup Fiat.ADT.ADTSig.
Require Import Coq.Lists.List Coq.Strings.String.

(* Notation for ADT Signatures. *)

Record methSig :=
  { methID : string ;
    methArity : nat;
    methDom : list Type ;
    methCod : option Type
  }.

Arguments Build_methSig methID%string methArity%nat methDom%type_scope methCod%type_scope.
Bind Scope methSig_scope with methSig.
Delimit Scope methSig_scope with methSig.

(* Notation for ADT Methods. *)

Notation "'Method' id : 'rep' '*' dom1 '*' .. '*' domn '->' 'rep' " :=
  {| methID := id;
     methArity := 1;
     methDom := @cons Type dom1%type .. (@cons Type domn%type (@nil Type)) ..;
     methCod := None |}
    (id at level 0, dom1 at level 0,
     domn at level 0, at level 93)
  : methSig_scope.

Notation "'Method' id : 'rep' '*' dom1 '*' .. '*' domn '->' 'rep' '*' cod " :=
  {| methID := id;
     methArity := 1;
     methDom := @cons Type dom1%type .. (@cons Type domn%type (@nil Type)) ..;
     methCod := Some (cod%type : Type) |}
    (id at level 0, cod at level 0, dom1 at level 0,
     domn at level 0,  at level 93)
  : methSig_scope.

Notation "'Method' id : 'rep' '*' 'rep' " :=
  {| methID := id;
     methArity := 1;
     methDom := (@nil Type);
     methCod := None |}
    (id at level 0, at level 93)
  : methSig_scope.

Notation "'Method' id : 'rep' '->' 'rep' '*' cod " :=
  {| methID := id;
     methArity := 1;
     methDom := @nil Type ;
     methCod := Some (cod%type : Type) |}
    (id at level 0, cod at level 0, at level 93)
  : methSig_scope.


Notation "'Constructor' id ':' 'rep'" :=
  {| methID := id;
     methArity := 0;
     methDom := @nil Type;
     methCod := None;
  |}
    (id at level 0, at level 93)
  : methSig_scope.

Notation "'Constructor' id ':' dom1 '*' .. '*' domn '->' 'rep'" :=
  {| methID := id;
     methArity := 0;
     methDom := @cons Type dom1%type .. (@cons Type domn%type (@nil Type)) .. |}
    (id at level 0, dom1 at level 0, domn at level 0, at level 93)
  : methSig_scope.

(* [BuildADTSig] constructs an ADT signature from a list of
   constructor signatures and a list of method signatures.
   This definition can be formated nicely using notations. *)

Record DecoratedADTSig :=
  { DecADTSig :> ADTSig;
    NumMethods : nat;
    MethodNames : Vector.t string NumMethods }.

Definition BuildADTSig
           {n}
           (methSigs : Vector.t methSig n)
: DecoratedADTSig :=
  {| DecADTSig :=
       {| MethodIndex := Fin.t n;
          MethodDomCod idx :=
            let domcod := (Vector.nth methSigs idx)
            in (methArity domcod, methDom domcod, methCod domcod)
       |};
     NumMethods := n;
     MethodNames := Vector.map methID methSigs |}.

Bind Scope ADTSig_scope with ADTSig.
Delimit Scope ADTSig_scope with ADTSig.

(* Notation for ADT signatures utilizing [BuildADTSig]. *)

Require Import Coq.Vectors.VectorDef.
Import Vectors.VectorDef.VectorNotations.

Delimit Scope vector_scope with vector.

Notation "'ADTsignature' { meth1 , .. , methn }" :=
  (BuildADTSig (meth1%methSig :: .. (methn%methSig :: []) ..))%vector
    (at level 0,
     meth1 at level 93, methn at level 93,
     format "'ADTsignature'  { '[v' '//' meth1 , '//' .. , '//' methn '//'  ']' }") : ADTSig_scope.
