Require Import Common Computation Ensembles List String
        ADT.ADTSig ADT.Core
        ADTNotation.StringBound ADTNotation.ilist
        ADTNotation.BuildADTSig.

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

Notation "'meth' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |} (fun (r : repHint) x => let cod := {| codHint := cod |} in bod%comp))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'meth'  id  ( r  :  'rep' ,  x  :  dom )  :  cod  := '/' '[  '   bod ']' " ) :
methDefParsing_scope.

Notation "'meth' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |} (fun r x => bod%comp))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0,
     at level 94, format "'meth'  id  ( r  :  'rep' ,  x  :  dom )  :  cod  :=  '/' '[  '   bod ']' " ) :
methDef_scope.

Delimit Scope methDefParsing_scope with methDefParsing.
Delimit Scope methDef_scope with methDef.

Record consDef {Rep : Type} (Sig : consSig) :=
  { consBody :> constructorType Rep (consDom Sig) }.

Notation "'const' id ( x : dom ) : 'rep' := bod" :=
  (Build_consDef {| consID := id; consDom := dom |} (fun x => bod%comp))
    (no associativity, at level 94, id at level 0, r at level 0,
     x at level 0, dom at level 0,
     format "'const'  id  ( x :  dom )  :  'rep'  :=  '/' '[  '   bod ']' " ) :
consDef_scope.

Delimit Scope consDef_scope with consDef.

(* Lookup functions for constructor and method definitions. Because
   these definitions are parameterized on a signature, their
   bodies are contained in an indexed list [ilist] which is
   parameterized on a list of those signatures. *)

Definition getConsDef
        (Rep : Type)
        (consSigs : list consSig)
        (consDefs : ilist (@consDef Rep) consSigs)
        (idx : @BoundedString (map consID consSigs))
: constructorType Rep (consDom (nth_Bounded _ consSigs idx)) :=
  consBody (@ith_Bounded _ _ _ (@consDef Rep) consSigs consDefs idx).

Definition getMethDef
         (Rep : Type)
         (methSigs : list methSig)
         (methDefs : ilist (@methDef Rep) methSigs)
         (idx : @BoundedString (map methID methSigs))
: methodType
    Rep
    (methDom (nth_Bounded _ methSigs idx))
    (methCod (nth_Bounded _ methSigs idx)) :=
  methBody (@ith_Bounded _ _ _ (@methDef Rep) methSigs methDefs idx).

(* Always simplify method lookup when the index is specified. *)
Arguments getConsDef [_] [_] _ idx%string / _ .
Arguments getMethDef [_] [_] _ idx%string / _ _ .

(* [BuildADT] constructs an ADT from a single constructor
   definition and a list of method signatures,
   both indexed by their signatures. [BuildADT] uses [BuildADTSig]
   to construct the signature of the ADT from these signatures.
   This definition is formated nicely using notations. *)

Program Definition BuildADT
        (Rep : Type)
        (consSigs : list consSig)
        (methSigs : list methSig)
        (consDefs : ilist (@consDef Rep) consSigs)
        (methDefs : ilist (@methDef Rep) methSigs)
: ADT (BuildADTSig consSigs methSigs)
      := {|
          Rep := Rep;
          Constructors idx := getConsDef consDefs idx;
          Methods idx := getMethDef methDefs idx
          |}.

(* Notation for ADTs built from [BuildADT]. *)

Notation "'ADTRep' r { cons1 , meth1 , .. , methn } " :=
  (let _ := {| repHint := r |} in
    @BuildADT r
             _
             _
             (icons _ cons1%consDef (inil (@consDef r)))
             (icons _ meth1%methDefParsing .. (icons _ methn%methDefParsing (inil (@methDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'ADTRep'  r  '/' '[hv  ' {  cons1 ,  '//' meth1 , '//' .. , '//' methn  ']' }") : ADTParsing_scope.

Notation "'ADTRep' r { cons1 , meth1 , .. , methn } " :=
  (@BuildADT r
             _
             _
             (icons _ cons1%consDef (inil (@consDef r)))
             (icons _ meth1%methDef .. (icons _ methn%methDef (inil (@methDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'ADTRep'  r  '/' '[hv  ' {  cons1 , '//' meth1 , '//' .. , '//' methn  ']' }") : ADT_scope.

(* Notations for method calls. *)
Notation callMeth adt idx := (Methods adt {| bindex := idx |}).
Notation callCons adt idx := (Constructors adt {| bindex := idx |}).
