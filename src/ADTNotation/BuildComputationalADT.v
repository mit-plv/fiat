Require Import Fiat.Common Fiat.Computation Coq.Sets.Ensembles Coq.Lists.List Coq.Strings.String
        Fiat.ADT.ADTSig Fiat.ADT.Core Fiat.ADT.ComputationalADT
        Fiat.Common.StringBound Fiat.Common.ilist
        Fiat.ADTNotation.BuildADTSig Fiat.ADTNotation.BuildADT.

(* Notations for ADTs. *)

Bind Scope cADT_Scope with cADT.
Delimit Scope cADT_scope with cADT.

(* Notations for computational ADT methods. *)

Record cMethDef {Rep : Type} (Sig : methSig) :=
  { cMethBody :> cMethodType Rep (methDom Sig) (methCod Sig)}.

Notation "'Def' 'Method' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_cMethDef {| methID := id; methDom := dom; methCod := cod |}
                  (fun (r : repHint) x => let cod := {| codHint := cod |} in bod%comp))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'Def'  'Method'  id  ( r  :  'rep' ,  x  :  dom )  :  cod  := '/' '[  '   bod ']' " ) :
cMethDefParsing_scope.

Notation "'Def' 'Method' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_cMethDef {| methID := id; methDom := dom; methCod := cod |} (fun r x => bod%comp))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0,
     at level 94, format "'Def'  'Method'  id  ( r  :  'rep' ,  x  :  dom )  :  cod  :=  '/' '[  '   bod ']' " ) :
cMethDef_scope.

Delimit Scope cMethDefParsing_scope with cMethDefParsing.
Delimit Scope cMethDef_scope with cMethDef.

Record cConsDef {Rep : Type} (Sig : consSig) :=
  { cConsBody :> cConstructorType Rep (consDom Sig) }.

Notation "'Def' 'Constructor' id ( x : dom ) : 'rep' := bod" :=
  (Build_cConsDef {| consID := id; consDom := dom |} (fun x => bod%comp))
    (no associativity, at level 94, id at level 0,
     x at level 0, dom at level 0,
     format "'Def'  'Constructor'  id  ( x :  dom )  :  'rep'  :=  '/' '[  '   bod ']' " ) :
cConsDef_scope.

Delimit Scope cConsDef_scope with cConsDef.

(* Lookup functions for constructor and method definitions. Because
   these definitions are parameterized on a signature, their
   bodies are contained in an indexed list [ilist] which is
   parameterized on a list of those signatures. *)

Definition getcConsDef
        (Rep : Type)
        (consSigs : list consSig)
        (consDefs : ilist (@cConsDef Rep) consSigs)
        (idx : @BoundedString (map consID consSigs))
: cConstructorType Rep (consDom (nth_Bounded _ consSigs idx)) :=
  cConsBody (@ith_Bounded _ _ _ (@cConsDef Rep) consSigs consDefs idx).

Definition getcMethDef
         (Rep : Type)
         (methSigs : list methSig)
         (methDefs : ilist (@cMethDef Rep) methSigs)
         (idx : @BoundedString (map methID methSigs))
: cMethodType
    Rep
    (methDom (nth_Bounded _ methSigs idx))
    (methCod (nth_Bounded _ methSigs idx)) :=
  cMethBody (@ith_Bounded _ _ _ (@cMethDef Rep) methSigs methDefs idx).

(* Always simplify method lookup when the index is specified. *)
Arguments getcConsDef [_] [_] _ idx%string / _ .
Arguments getcMethDef [_] [_] _ idx%string / _ _ .

(* [BuildcADT] constructs an computational ADT from a single constructor
   definition and a list of method signatures,
   both indexed by their signatures. *)

Program Definition BuildcADT
        (Rep : Type)
        (consSigs : list consSig)
        (methSigs : list methSig)
        (consDefs : ilist (@cConsDef Rep) consSigs)
        (methDefs : ilist (@cMethDef Rep) methSigs)
: cADT (BuildADTSig consSigs methSigs)
      := existT _ Rep {|
                  pcConstructors idx := getcConsDef consDefs idx;
                  pcMethods idx := getcMethDef methDefs idx
                |}.

(* Notation for ADTs built from [BuildADT]. *)

Notation "'cADTRep' r { cons1 , meth1 , .. , methn } " :=
  (let _ := {| repHint := r |} in
    @BuildcADT r
             _
             _
             (icons _ cons1%cConsDef (inil (@cConsDef r)))
             (icons _ meth1%cMethDefParsing .. (icons _ methn%cMethDefParsing (inil (@cMethDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'cADTRep'  r  '/' '[hv  ' {  cons1 ,  '//' meth1 , '//' .. , '//' methn  ']' }") :
    ADTParsing_scope.

Notation "'cADTRep' r { cons1 , meth1 , .. , methn } " :=
  (@BuildcADT r
             _
             _
             (icons _ cons1%cConsDef (inil (@cConsDef r)))
             (icons _ meth1%cMethDef .. (icons _ methn%cMethDef (inil (@cMethDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'cADTRep'  r  '/' '[hv  ' {  cons1 , '//' meth1 , '//' .. , '//' methn  ']' }") : ADT_scope.

(* Notations for method calls. *)
Notation CallMethod CompADT idx := (cMethods CompADT {| bindex := idx |}).
Notation CallConstructor CompADT idx := (cConstructors CompADT {| bindex := idx |}).
