Require Import
        Coq.Sets.Ensembles
        Coq.Lists.List
        Coq.Strings.String
        Fiat.Common
        Fiat.Computation
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADT.ComputationalADT
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.ADTNotation.BuildADTSig
        Fiat.ADTNotation.BuildADT.

(* Notations for Computational ADTs. *)

Bind Scope cADT_Scope with cADT.
Delimit Scope cADT_scope with cADT.

(* Notations for computational ADT methods. *)

Record cMethDef {Rep : Type} (Sig : methSig) :=
  { cMethBody :> cMethodType (methArity Sig) Rep (methDom Sig) (methCod Sig)}.

Notation "'Def' 'Method0' id r .. xn : 'rep' '*' cod := bod" :=
  (Build_cMethDef
     {| methID := id; methArity := 1; methDom := [ ] ; methCod := Some (cod : Type) |}
     (fun r => .. (fun xn =>
                     let _ := {| codHint := Some (cod : Type) |} in
                     (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method0'  id  r  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method1' id r .. xn : 'rep' '*' cod := bod" :=
  (Build_cMethDef
     {| methID := id; methArity := 1; methDom := [ _ ] ; methCod := Some (cod : Type) |}
     (fun r => .. (fun xn =>
                     let _ := {| codHint := Some (cod : Type) |} in
                     (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method1'  id  r  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method2' id r .. xn : 'rep' '*' cod := bod" :=
  (Build_cMethDef
     {| methID := id; methArity := 1; methDom := [ _; _ ] ; methCod := Some (cod : Type) |}
     (fun r => .. (fun xn =>
                     let _ := {| codHint := Some (cod : Type) |} in
                     (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method2'  id  r  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method3' id r .. xn : 'rep' '*' cod := bod" :=
  (Build_cMethDef
     {| methID := id; methArity := 1; methDom := [ _; _; _ ] ; methCod := Some (cod : Type) |}
     (fun r => .. (fun xn =>
                     let _ := {| codHint := Some (cod : Type) |} in
                     (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method3'  id  r  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method4' id r .. xn : 'rep' '*' cod := bod" :=
  (Build_cMethDef
     {| methID := id; methArity := 1; methDom := [_; _; _; _ ] ; methCod := Some (cod : Type) |}
     (fun r => .. (fun xn =>
                     let _ := {| codHint := Some (cod : Type) |} in
                     (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method4'  id  r  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method5' id r .. xn : 'rep' '*' cod := bod" :=
  (Build_cMethDef
     {| methID := id; methArity := 1; methDom := [_; _; _; _; _ ] ; methCod := Some (cod : Type) |}
     (fun r => .. (fun xn =>
                     let _ := {| codHint := Some (cod : Type) |} in
                     (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method5'  id  r  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

(* Variant Notations for methods that don't return a value. *)

Notation "'Def' 'Method0' id r .. xn : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [ ] ; methCod := None |} (fun r => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method0'  id  r  ..  xn  :  'rep' :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method1' id r .. xn : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [_ ] ; methCod := None |} (fun r => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method1'  id  r  ..  xn  :  'rep' :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method2' id r .. xn : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [_; _ ] ; methCod := None |} (fun r => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method2'  id  r  ..  xn  :  'rep' :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method3' id r .. xn : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [_; _; _ ] ; methCod := None |} (fun r => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method3'  id  r  ..  xn  :  'rep' :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method4' id r .. xn : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [_; _; _; _] ; methCod := None |} (fun r => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method4'  id  r  ..  xn  :  'rep' :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

Notation "'Def' 'Method5' id r .. xn : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [_; _; _; _; _] ; methCod := None |} (fun r => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : cMethodType' _ [ ] codHint )) ..))
    (no associativity, id at level 0, r closed binder , xn closed binder,
     only parsing,
     at level 94,
     format "'Def'  'Method5'  id  r  ..  xn  :  'rep' :=  '/' '[  '   bod ']' ")
  : cMethDefParsing_scope.

(* Again, pretty printing involves fewer rules. *)
Notation "'Def' 'Method' id ( r : 'rep' ) : 'rep' '*' cod := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [] ; methCod := Some cod |} (fun r => bod%comp ))
    (no associativity, id at level 0, r at level 0,
     cod at level 0,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDef_scope.

Notation "'Def' 'Method' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := _ :: _ ; methCod := Some cod |} (fun r =>
                                                                             (fun x1 => .. (fun xn => (bod%comp )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : cMethDef_scope.

Notation "'Def' 'Method' id ( r : 'rep' ) : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := [] ; methCod := None |} (fun r => bod%comp ))
    (no associativity, id at level 0, r at level 0,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  :  'rep'  :=  '/' '[  '   bod ']' ")
  : cMethDef_scope.

Notation "'Def' 'Method' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef {| methID := id; methArity := 1; methDom := _ :: _ ; methCod := None |} (fun r =>
                                                                         (fun x1 => .. (fun xn => (bod%comp )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : cMethDef_scope.

Delimit Scope cMethDefParsing_scope with cMethDefParsing.
Delimit Scope cMethDef_scope with cMethDef.

(* Notations for parsing Constructors. Including the arity is the simplest way to
 make typechecking work. *)
Notation "'Def' 'Constructor0' id : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := []; methCod := None |} ((bod%comp : cConstructorType rep [ ]) ))
    (no associativity, at level 94, id at level 0,
     format "'Def'  'Constructor0'  id  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor1' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor1'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor2' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor2'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor3' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor3'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor4' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _ ; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor4'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor5' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _; _; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor5'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor6' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _; _;_; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor6'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor7' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _; _; _; _; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor7'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor8' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _; _; _; _; _ ; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor8'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor9' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _; _; _; _; _; _; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor9'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor10' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [_; _; _; _; _; _; _; _;  _; _] ; methCod := None |} ((fun x1 => .. ((fun xn => (bod%comp : cConstructorType rep [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor10'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

(* Once the type infomation is in hand, two rules can handle pretty printing.  *)
Notation "'Def' 'Constructor' id x1 .. xn : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := _ ; methCod := None |} ((fun x1 => .. ((fun xn => bod%comp )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Notation "'Def' 'Constructor' id : 'rep' := bod" :=
  (Build_cMethDef _ {| methID := id; methArity := 1; methDom := [] ; methCod := None |} bod%comp)
    (no associativity, at level 94, id at level 0,
     format "'Def'  'Constructor'  id :  'rep'  :=  '/' '[  '   bod ']' " ) :
    cMethDef_scope.

Delimit Scope cMethDef_scope with cMethDef.

(* Lookup functions for constructor and method definitions. Because
   these definitions are parameterized on a signature, their
   bodies are contained in an indexed list [ilist] which is
   parameterized on a list of those signatures. *)

Definition getcMethDef
           (Rep : Type)
           {n}
           (methSigs : Vector.t methSig n)
           (methDefs : ilist methSigs)
           (idx : Fin.t n)
  : cMethodType
      (methArity (Vector.nth methSigs idx))
      Rep
      (methDom (Vector.nth methSigs idx))
      (methCod (Vector.nth methSigs idx)) :=
  cMethBody (ith methDefs idx).

(* Always simplify method lookup when the index is specified. *)
Arguments getcMethDef [_] {n} [_] _ idx%string / .

(* [BuildcADT] constructs an computational ADT from a single constructor
   definition and a list of method signatures,
   both indexed by their signatures. *)

Definition DecoratedcADT (dSig : DecoratedADTSig) := cADT dSig.

Program Definition BuildcADT
        {Rep : Type}
        {n'}
        {methSigs : Vector.t methSig n'}
        (methDefs : ilist (B:= @cMethDef Rep) methSigs)
: DecoratedcADT (BuildADTSig methSigs)
      := existT _ Rep {|
                  pcMethods idx := getcMethDef methDefs idx
                |}.

Definition callcADTMethod
           {dSig : DecoratedADTSig}
           (adt : DecoratedcADT dSig)
           (idxMap : BoundedIndex (MethodNames dSig) -> MethodIndex dSig)
           (idx : BoundedIndex (MethodNames dSig))
  := cMethods adt (idxMap idx).

(* Notation for ADTs built from [BuildADT]. *)

Notation "'cADTRep' r { meth1 , .. , methn } " :=
  (let _ := {| rep := r |} in
    @BuildcADT r
             _ _
             (icons meth1%cMethDefParsing .. (icons methn%cMethDefParsing (@inil _ (@cMethDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'cADTRep'  r  '/' '[hv  ' {  meth1 , '//' .. , '//' methn  ']' }") :
    ADTParsing_scope.

Notation "'cADTRep' r { meth1 , .. , methn } " :=
  (@BuildcADT r
             _ _
             (icons meth1%cMethDef .. (icons methn%cMethDef (@inil _  (@cMethDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'cADTRep'  r  '/' '[hv  ' {  meth1 , '//' .. , '//' methn  ']' }") : ADT_scope.

(* Notations for method calls. *)
Notation CallMethod CompADT idx := (callcADTMethod CompADT (fun idx => ibound (indexb idx))
                                                  {| bindex := idx |}).
