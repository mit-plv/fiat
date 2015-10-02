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

Class CoDHint := {codHint : option Type}.

(* Notations for ADT methods. Constructors and methods
   are parameterized by a signature that includes the
   domain (both) and codomain (just methods). *)

Record consDef {Rep : Type} (Sig : consSig) :=
  { consBody :> constructorType Rep (consDom Sig) }.

Delimit Scope consDef_scope with consDef.

(* Notations for parsing Constructors. Including the arity is the simplest way to
 make typechecking work. *)
Notation "'Def' 'Constructor0' id : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [] |} ((bod%comp : constructorType repHint [ ]) ))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor0'  id  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor1' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor1'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor2' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor2'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor3' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor3'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor4' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _ ; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor4'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor5' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _; _; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor5'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor6' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _; _;_; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor6'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor7' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _; _; _; _; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor7'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor8' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _; _; _; _; _ ; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor8'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor9' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _; _; _; _; _; _; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor9'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor10' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [_; _; _; _; _; _; _; _;  _; _] |} ((fun x1 => .. ((fun xn => (bod%comp : constructorType repHint [ ]) )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor10'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

(* Once the type infomation is in hand, two rules can handle pretty printing.  *)
Notation "'Def' 'Constructor' id x1 .. xn : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := _ |} ((fun x1 => .. ((fun xn => bod%comp )) ..)))
    (no associativity, at level 94, id at level 0,
     x1 closed binder, xn closed binder,
     format "'Def'  'Constructor'  id  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

Notation "'Def' 'Constructor' id : 'rep' := bod" :=
  (Build_consDef _ {| consID := id; consDom := [] |} bod%comp)
    (no associativity, at level 94, id at level 0,
     format "'Def'  'Constructor'  id :  'rep'  :=  '/' '[  '   bod ']' " ) :
    consDef_scope.

(* Notations for parsing methods. Again, including the arity is the simplest way to
 make typechecking work. *)

Record methDef {Rep : Type} (Sig : methSig) :=
  { methBody :> methodType Rep (methDom Sig) (methCod Sig)}.

Notation "'Def' 'Method0' id ( r : 'rep' ) : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                     (let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint ))))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method0'  id  (  r  :  'rep'  )  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method1' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                      (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     only parsing,
     at level 94,
     format "'Def'  'Method1'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method2' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                         (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method2'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method3' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                            (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method3'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method4' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                               (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method4'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method5' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                                  (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method5'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method6' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                                     (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method6'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method7' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                                        (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method7'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method8' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                                           (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method8'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method9' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                                              (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method9'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method10' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _; _; _; _] ; methCod := Some (cod : Type) |} (fun r =>
                                                                                                                 (fun x1 => .. (fun xn => let _ := {| codHint := Some (cod : Type) |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method10'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method0' id ( r : 'rep' ) : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [] ; methCod := None |} (fun r =>
                                                                        (let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint ))))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method0'  id  (  r  :  'rep'  )  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method1' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_] ; methCod := None |} (fun r =>
                                                                         (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     only parsing,
     at level 94,
     format "'Def'  'Method1'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method2' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _] ; methCod := None |} (fun r =>
                                                                            (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method2'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method3' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _] ; methCod := None |} (fun r =>
                                                                               (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method3'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method4' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _] ; methCod := None |} (fun r =>
                                                                                  (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method4'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method5' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _] ; methCod := None |} (fun r =>
                                                                                     (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method5'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method6' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _] ; methCod := None |} (fun r =>
                                                                                        (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method6'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method7' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _] ; methCod := None |} (fun r =>
                                                                                           (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method7'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method8' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _; _] ; methCod := None |} (fun r =>
                                                                                              (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method8'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method9' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _; _; _] ; methCod := None |} (fun r =>
                                                                                                 (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method9'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

Notation "'Def' 'Method10' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_; _; _; _; _; _; _; _; _; _] ; methCod := None |} (fun r =>
                                                                                                    (fun x1 => .. (fun xn => let _ := {| codHint := None |} in (bod%comp : methodType' _ [] codHint )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method10'  id  (  r  :  'rep'  )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDefParsing_scope.

(* Again, pretty printing involves fewer rules. *)
Notation "'Def' 'Method' id ( r : 'rep' ) : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [] ; methCod := Some cod |} (fun r => bod%comp ))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDef_scope.

Notation "'Def' 'Method' id ( r : 'rep' ) x1 .. xn : 'rep' '*' cod := bod" :=
  (Build_methDef {| methID := id; methDom := [_] ; methCod := Some cod |} (fun r =>
                                                                             (fun x1 => .. (fun xn => (bod%comp )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     only parsing,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  x1  ..  xn  :  'rep'  '*'  cod  :=  '/' '[  '   bod ']' ")
  : methDef_scope.

Notation "'Def' 'Method' id ( r : 'rep' ) : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [] ; methCod := None |} (fun r => bod%comp ))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     cod at level 0, only parsing,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDef_scope.

Notation "'Def' 'Method' id ( r : 'rep' ) x1 .. xn : 'rep' := bod" :=
  (Build_methDef {| methID := id; methDom := [_] ; methCod := None |} (fun r =>
                                                                         (fun x1 => .. (fun xn => (bod%comp )) ..)))
    (no associativity, id at level 0, r at level 0, x1 closed binder , xn closed binder, dom at level 0,
     only parsing,
     at level 94,
     format "'Def'  'Method'  id  ( r  :  'rep' )  x1  ..  xn  :  'rep'  :=  '/' '[  '   bod ']' ")
  : methDef_scope.

Delimit Scope methDefParsing_scope with methDefParsing.
Delimit Scope methDef_scope with methDef.


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
Arguments getConsDef [_] {n} [_] _ idx%string / .
Arguments getMethDef [_] {n} [_] _ idx%string / _ .

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

Delimit Scope ADTParsing_scope with ADTParsing.

Notation "'ADTRep' r { cons1 , meth1 , .. , methn } " :=
  (let _ := {| repHint := r |} in
   @BuildADT r
             _ _
             _ _
             (icons cons1%consDef (@inil _ (@consDef r)))
             (icons meth1%methDefParsing .. (icons methn%methDefParsing (@inil _ (@methDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'ADTRep'  r  '/' '[hv  ' {  cons1 ,  '//' meth1 , '//' .. , '//' methn  ']' }") : ADTParsing_scope.

Notation "'ADTRep' r { cons1 , meth1 , .. , methn } " :=
  (@BuildADT r
             _ _
             _ _
             (icons cons1%consDef (@inil _ (@consDef r)))
             (icons meth1%methDef .. (icons methn%methDef (@inil _ (@methDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'ADTRep'  r  '/' '[hv  ' {  cons1 , '//' meth1 , '//' .. , '//' methn  ']' }") : ADT_scope.

(* Notations for method calls. *)
Notation callMeth adt idx := (callADTMethod adt (fun idx => ibound (indexb idx))
                                            {| bindex := idx |}).
Notation callCons adt idx := (callADTConstructor adt (fun idx => ibound (indexb idx))
                                                 {| bindex := idx |}).

Section NotationExample.

  Variable Key : Type.
  Variable Value : Type.

  Definition EnsembleInsert  {A} (a : A) (ens : Ensemble A) (a' : A)
    : Prop := a' = a \/ ens a'.

  Definition SubEnsembleInsert {A} (a : A) (ens ens' : Ensemble A)
    : Prop :=
    forall (a' : A), ens' a' -> EnsembleInsert a ens a'.

  Definition EnsembleRemove
             (k : Key)
             (ens : Ensemble (Key * Value))
             (k' : Key * Value)
    : Prop := (fst k' <> k /\ ens k').

  Definition EnsembleReplace
             (k : Key * Value)
             (ens : Ensemble (Key * Value))
             (k' : Key * Value)
    : Prop := k' = k \/
              (EnsembleRemove (fst k) ens k').

  Definition EnsembleUpdate
             (k : Key)
             (ens : Ensemble (Key * Value))
             (f : Value -> Value)
             (kv : Key * Value)
    : Prop := ((fst kv) = k /\ exists v, (snd kv) = f v /\ Ensembles.In _ ens (k, v)) \/
              (EnsembleRemove k ens kv).

  Lemma SubEnsembleInsertReplace
    : forall (kv : Key * Value)
             (r : Ensemble (Key * Value)),
      SubEnsembleInsert kv r (EnsembleReplace kv r).
  Proof.
    unfold SubEnsembleInsert, EnsembleInsert,
    EnsembleReplace, EnsembleRemove; intros; intuition.
  Qed.

  Lemma SubEnsembleInsertRefl
    : forall (kv : Key * Value)
             (r : Ensemble (Key * Value)),
      SubEnsembleInsert kv r r.
  Proof.
    unfold SubEnsembleInsert, EnsembleInsert,
    EnsembleReplace, EnsembleRemove; intros; eauto.
  Qed.

  Definition ValidLookup
             (r : Ensemble (Key * Value))
             (k : Key)
             (v : option Value)
    : Prop := forall v', v = Some v' -> r (k, v').

  Definition usedKey
             (r : Ensemble (Key * Value))
             (k : Key)
    : Prop := exists v, r (k, v).

  Definition CacheSig : ADTSig :=
    ADTsignature {
        Constructor "EmptyCache" : rep,
        Method "AddKey" : rep * Key * Value -> rep * bool ,
        Method "UpdateKey" : rep * Key * (Value -> Value) -> rep * bool ,
        Method "LookupKey" :  rep * Key -> rep * (option Value)
      }%ADTSig.

  Definition CacheSpec : ADT CacheSig :=
    (ADTRep (Ensemble (Key * Value)) {
       Def Constructor0 "EmptyCache" : rep :=
         ret (Empty_set _),
       Def Method2 "AddKey" (r : rep) (k : Key) (v : Value) : rep * bool :=
         { r' | (SubEnsembleInsert (k, v) r (fst r')) /\
                ((usedKey r k /\ snd r' = false) \/
                 (~ usedKey r k /\ snd r' = true))},
       Def Method2 "UpdateKey" (r : rep) (k : Key) (v : Value -> Value) : rep * bool :=
           { r' |
             (Same_set _ (fst r') (EnsembleUpdate k r v))
             /\ ((usedKey r k /\ snd r' = true) \/
                 (~ usedKey r k -> snd r' = false))},
           Def Method1 "LookupKey" (r : rep) (k : Key) : rep * option Value :=
             v <- {v | ValidLookup r k v};
       ret (r, v)
     }%ADTParsing) : ADT _.

End NotationExample.
