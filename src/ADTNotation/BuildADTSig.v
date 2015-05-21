Require Import Fiat.Common.ilist Fiat.Common.BoundedLookup Fiat.ADT.ADTSig.
Require Import Coq.Lists.List Coq.Strings.String.

(* Notation for ADT Signatures. *)

Record consSig :=
  { consID : string;
    consDom : Type }.

Arguments Build_consSig consID%string consDom%type_scope.
Bind Scope consSig_scope with consSig.
Delimit Scope consSig_scope with consSig.

Record methSig :=
  { methID : string ;
    methDom : Type ;
    methCod : Type
  }.

Arguments Build_methSig methID%string methDom%type_scope methCod%type_scope.
Bind Scope methSig_scope with methSig.
Delimit Scope methSig_scope with methSig.

(* Notation for ADT Methods. *)

Notation "'Method' id : 'rep' 'x' dom '->' 'rep' 'x' cod " :=
  {| methID := id;
     methDom := dom;
     methCod := cod |}
    (id at level 0, dom at level 59, at level 93)
  : methSig_scope.

Notation "'Constructor' id ':' dom '->' 'rep'" :=
  {| consID := id;
     consDom := dom |}
    (id at level 0, dom at level 59, at level 93)
  : consSig_scope.

(* [BuildADTSig] constructs an ADT signature from a list of
   constructor signatures and a list of method signatures.
   This definition can be formated nicely using notations. *)

Print ADTSig.

Record DecoratedADTSig :=
  { DecADTSig :> ADTSig;
    NumConstructors : nat;
    NumMethods : nat;
    ConstructorNames : Vector.t string NumConstructors;
    MethodNames : Vector.t string NumMethods }.

Definition BuildADTSig
           {n n'}
           (consSigs : Vector.t consSig n)
           (methSigs : Vector.t methSig n')
: DecoratedADTSig :=
  {| DecADTSig :=
       {| ConstructorIndex := Fin.t n;
          MethodIndex := Fin.t n';
          ConstructorDom idx :=
            consDom (Vector.nth consSigs idx);
          MethodDomCod idx :=
            let domcod := (Vector.nth methSigs idx)
            in (methDom domcod, methCod domcod)
       |};
     NumConstructors := n;
     NumMethods := n';
     ConstructorNames := Vector.map consID consSigs;
     MethodNames := Vector.map methID methSigs |}.

Bind Scope ADTSig_scope with ADTSig.
Delimit Scope ADTSig_scope with ADTSig.

(* Notation for ADT signatures utilizing [BuildADTSig]. *)

Require Import Coq.Vectors.VectorDef.
Import Coq.Vectors.VectorDef.VectorNotations.

Delimit Scope vector_scope with vector.

Notation "'ADTsignature' { cons1 , meth1 , .. , methn }" :=
  (BuildADTSig (cons1%consSig :: [])%vector
              (meth1%methSig :: .. (methn%methSig :: []) ..))%vector
    (at level 0,
     cons1 at level 93,
     meth1 at level 93, methn at level 93,
     format "'ADTsignature'  { '[v' '//' cons1 , '//' meth1 , '//' .. , '//' methn '//'  ']' }") : ADTSig_scope.
