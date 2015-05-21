Require Import Coq.Sets.Ensembles
        Coq.Lists.List
        Coq.Strings.String
        Fiat.Common
        Fiat.Computation
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADT.ComputationalADT
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.ADTNotation.BuildADTSig.

(* Notations for ADTs. *)

Bind Scope ADT_Scope with ADT.
Delimit Scope ADT_scope with ADT.

(* This class is used by BuildADT to give a hint
   to help infer the representation type. *)
Class RepHint := {repHint : Type}.

(* This class is used to give a hint to help infer the
   return type. *)

Class CoDHint := {codHint : Type}.

(* Notations for ADT methods. Constructors and methods
   are parameterized by a signature that includes the
   domain (both) and codomain (just methods). *)

Record methDef {Rep : Type} (Sig : methSig) :=
  { methBody :> methodType Rep (methDom Sig) (methCod Sig)}.

Notation "'Def' 'Method' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |} (fun (r : repHint) x => let cod := {| codHint := cod |} in bod%comp))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'Def'  'Method'  id  ( r  :  'rep' ,  x  :  dom )  :  cod  := '/' '[  '   bod ']' " ) :
methDefParsing_scope.

Notation "'Def' 'Method' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |} (fun r x => bod%comp))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0,
     at level 94, format "'Def'  'Method'  id  ( r  :  'rep' ,  x  :  dom )  :  cod  :=  '/' '[  '   bod ']' " ) :
methDef_scope.

Delimit Scope methDefParsing_scope with methDefParsing.
Delimit Scope methDef_scope with methDef.

Record consDef {Rep : Type} (Sig : consSig) :=
  { consBody :> constructorType Rep (consDom Sig) }.

Notation "'Def' 'Constructor' id ( x : dom ) : 'rep' := bod" :=
  (Build_consDef {| consID := id; consDom := dom |} (fun x => bod%comp))
    (no associativity, at level 94, id at level 0,
     x at level 0, dom at level 0,
     format "'Def'  'Constructor'  id  ( x :  dom )  :  'rep'  :=  '/' '[  '   bod ']' " ) :
consDef_scope.

Delimit Scope consDef_scope with consDef.

(* Lookup functions for constructor and method definitions. Because
   these definitions are parameterized on a signature, their
   bodies are contained in an indexed list [ilist] which is
   parameterized on a list of those signatures. *)

Definition getConsDef
           (Rep : Type)
           {n}
           (consSigs : Vector.t consSig n)
           (consDefs : ilist consSigs)
           (idx : Fin.t n)
: constructorType Rep (consDom (Vector.nth consSigs idx)) :=
  consBody (ith consDefs idx).

Definition getMethDef
           (Rep : Type)
           {n}
           (methSigs : Vector.t methSig n)
           (methDefs : ilist (B := @methDef Rep) methSigs)
           (idx : Fin.t n)
: methodType
    Rep
    (methDom (Vector.nth methSigs idx))
    (methCod (Vector.nth methSigs idx)) :=
  methBody (ith methDefs idx).

(* Always simplify method lookup when the index is specified. *)
Arguments getConsDef [_] {n} [_] _ idx%string / _ _ .
Arguments getMethDef [_] {n} [_] _ idx%string / _ _ _ .

(* [BuildADT] constructs an ADT from a single constructor
   definition and a list of method signatures,
   both indexed by their signatures. [BuildADT] uses [BuildADTSig]
   to construct the signature of the ADT from these signatures.
   This definition is formated nicely using notations. *)

Definition DecoratedADT (dSig : DecoratedADTSig) := ADT dSig.

Definition BuildADT
        {Rep : Type}
        {n n'}
        {consSigs : Vector.t consSig n}
        {methSigs : Vector.t methSig n'}
        (consDefs : ilist (B := @consDef Rep) consSigs)
        (methDefs : ilist (B := @methDef Rep) methSigs)
  : DecoratedADT (BuildADTSig consSigs methSigs)
  := @Build_ADT (BuildADTSig consSigs methSigs)
               Rep
               (getConsDef consDefs)
               (getMethDef methDefs).

(* Notation for ADTs built from [BuildADT]. *)

Definition callADTConstructor
           {dSig : DecoratedADTSig}
           (adt : DecoratedADT dSig)
           (idxMap : BoundedIndex (ConstructorNames dSig) -> ConstructorIndex dSig)
           (idx : BoundedIndex (ConstructorNames dSig))
  := Constructors adt (idxMap idx).

Definition callADTMethod
           {dSig : DecoratedADTSig}
           (adt : DecoratedADT dSig)
           (idxMap : BoundedIndex (MethodNames dSig) -> MethodIndex dSig)
           (idx : BoundedIndex (MethodNames dSig))
  := Methods adt (idxMap idx).

Notation "'ADTRep' r { cons1 , meth1 , .. , methn } " :=
  (let _ := {| repHint := r |} in
    @BuildADT r
             _ _
             _ _
             (icons cons1%consDef (inil (@consDef r)))
             (icons meth1%methDefParsing .. (icons methn%methDefParsing (inil (@methDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'ADTRep'  r  '/' '[hv  ' {  cons1 ,  '//' meth1 , '//' .. , '//' methn  ']' }") : ADTParsing_scope.

Notation "'ADTRep' r { cons1 , meth1 , .. , methn } " :=
  (@BuildADT r
             _ _
             _ _
             (icons cons1%consDef (inil (@consDef r)))
             (icons meth1%methDef .. (icons methn%methDef (inil (@methDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'ADTRep'  r  '/' '[hv  ' {  cons1 , '//' meth1 , '//' .. , '//' methn  ']' }") : ADT_scope.

(* Notations for method calls. *)
Notation callMeth adt idx := (callADTMethod adt (fun idx => ibound (indexb idx))
                                             {| bindex := idx |}).
Notation callCons adt idx := (callADTConstructor adt (fun idx => ibound (indexb idx))
                                                  {| bindex := idx |}).
