Require Import Common Computation ADT.ADTSig
        Common.ilist Common.StringBound.
Require Import List String.

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

Notation "id : 'rep' × dom → 'rep' × cod " :=
  {| methID := id;
     methDom := dom;
     methCod := cod |}
    (at level 60)
  : methSig_scope.

Notation "id : dom → 'rep'" :=
  {| consID := id;
     consDom := dom |}
    (at level 60)
  : consSig_scope.

(* [BuildADTSig] constructs an ADT signature from a list of
   constructor signatures and a list of method signatures.
   This definition can be formated nicely using notations. *)

Definition BuildADTSig
           (consSigs : list consSig)
           (methSigs : list methSig)
: ADTSig :=
  {| ConstructorIndex := @BoundedString (map consID consSigs);
     MethodIndex := @BoundedString (map methID methSigs);
     ConstructorDom idx :=
       consDom (nth_Bounded consID consSigs idx) ;
    MethodDomCod idx :=
      let domcod := (nth_Bounded methID methSigs idx)
      in (methDom domcod, methCod domcod)
  |}.

Bind Scope ADTSig_scope with ADTSig.
Delimit Scope ADTSig_scope with ADTSig.

(* Notation for ADT signatures utilizing [BuildADTSig]. *)

Notation "'ADTsignature' { cons1 , meth1 , .. , methn }" :=
  (BuildADTSig (cons1%consSig :: [])
              (meth1%methSig :: .. (methn%methSig :: []) ..))
    (at level 70,
     format "'ADTsignature'  { '[v' '//' cons1 , '//' meth1 , '//' .. , '//' methn '//'  ']' }") : ADTSig_scope.
