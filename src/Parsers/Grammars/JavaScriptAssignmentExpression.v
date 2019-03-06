(** * 1. Gramamr for JavaScript AssignmentExpression *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

(** Quoting http://www-archive.mozilla.org/js/language/grammar14.html *)
Section JavaScriptAssignmentExpression.
  Local Open Scope prod_assignment_scope.

  (** ** Expressions *)
  (**
<<
α ∈ {normal, initial}
β ∈ {allowIn, noIn}
>> *)

  (** *** Primary Expressions
<<
PrimaryExpressionnormal ⇒
   SimpleExpression
|  ObjectLiteral
PrimaryExpressioninitial ⇒ SimpleExpression
>> *)
  Let PrimaryExpression_normal :=
    "PrimaryExpression normal"
      ::== "SimpleExpression"
        || "ObjectLiteral".
  Let PrimaryExpression_initial :=
    "PrimaryExpression initial"
      ::== "SimpleExpression".

  (**
<<
SimpleExpression ⇒
   this
|  Number
|  String
|  Identifier
|  ParenthesizedExpression
|  ArrayLiteral
*)
  Let SimpleExpression :=
    "SimpleExpression"
      ::== "'this'"
        || "Number"
        || "String"
        || "Identifier"
        || "ParenthesizedExpression"
        || "ArrayLiteral".
  (**
<<
ParenthesizedExpression ⇒ ( Expressionnormal,allowIn )
>> *)
  Let ParenthesizedExpression :=
    "ParenthesizedExpression"
      ::== "(" "WS*" "Expression normal,allowIn" "WS*" ")".

  (** *** Object Literals
<<
ObjectLiteral ⇒
   { }
|  { FieldList }
FieldList ⇒
   LiteralField
|  FieldList , LiteralField
LiteralField ⇒ Identifier : AssignmentExpressionnormal,allowIn
>> *)
  Let ObjectLiteral :=
    "ObjectLiteral"
      ::== "{" "WS*" "}"
        || "{" "WS*" "FieldList" "WS*" "}".
  Let FieldList :=
    "FieldList"
      ::== "LiteralField"
        || "FieldList" "WS*" "," "WS*" "LiteralField".
  Let LiteralField :=
    "LiteralField"
      ::== "Identifier" "WS*" ":" "WS*" "AssignmentExpression normal,allowIn".

  (** *** Array Literals
<<
ArrayLiteral ⇒
   [ ]
|  [ ElementList ]
ElementList ⇒
   LiteralElement
|  ElementList , LiteralElement
LiteralElement ⇒ AssignmentExpressionnormal,allowIn
>> *)
  Let ArrayLiteral :=
    "ArrayLiteral"
      ::== "[" "WS*" "]"
        || "[" "WS*" "ElementList" "WS*" "]".
  Let ElementList :=
    "ElementList"
      ::== "LiteralElement"
        || "ElementList" "WS*" "," "WS*" "LiteralElement".
  Let LiteralElement :=
    "LiteralElement"
      ::== "AssignmentExpression normal,allowIn".

  (** *** Left-Side Expressions
<<
LeftSideExpressionα ⇒
   CallExpressionα
|  ShortNewExpression
>> *)
  Let LeftSideExpression α :=
    ("LeftSideExpression " ++ α)
      ::== ("CallExpression " ++ α)
        || "ShortNewExpression".
  (**
<<
CallExpressionα ⇒
   PrimaryExpressionα
|  FullNewExpression
|  CallExpressionα MemberOperator
|  CallExpressionα Arguments
FullNewExpression ⇒ new FullNewSubexpression Arguments
ShortNewExpression ⇒ new ShortNewSubexpression
>> *)
  Let CallExpression α :=
    ("CallExpression " ++ α)
      ::== ("PrimaryExpression " ++ α)
        || "FullNewExpression"
        || ("CallExpression " ++ α) "WS*" "MemberOperator"
        || ("CallExpression " ++ α) "WS*" "Arguments".
  Let FullNewExpression :=
    "FullNewExpression"
      ::== "'new'" [\s] "WS*" "FullNewSubexpression" "WS*" "Arguments".
  Let ShortNewExpression :=
    "ShortNewExpression"
      ::== "'new'" [\s] "WS*" "ShortNewSubexpression" "WS*" "Arguments".

  (**
<<
FullNewSubexpression ⇒
   PrimaryExpressionnormal
|  FullNewExpression
|  FullNewSubexpression MemberOperator
>> *)
  Let FullNewSubexpression :=
    "FullNewSubexpression"
      ::== "PrimaryExpression normal"
        || "FullNewExpression"
        ||  "FullNewSubexpression" "WS*" "MemberOperator".

  (**
<<
ShortNewSubexpression ⇒
   FullNewSubexpression
|  ShortNewExpression
>> *)
  Let ShortNewSubexpression :=
    "ShortNewSubexpression"
      ::== "FullNewSubexpression"
        || "ShortNewExpression".

  (**
<<
MemberOperator ⇒
   [ Expressionnormal,allowIn ]
|  . Identifier
>> *)
  Let MemberOperator :=
    "MemberOperator"
      ::== "[" "WS*" "Expression normal,allowIn" "WS*" "]"
        || "." "WS*" "Identifier".
  (**
<<
Arguments ⇒
   ( )
|  ( ArgumentList )
ArgumentList ⇒
   AssignmentExpressionnormal,allowIn
|  ArgumentList , AssignmentExpressionnormal,allowIn
>> *)
  Let Arguments :=
    "Arguments"
      ::== "(" "WS*" ")"
        || "(" "WS*" "ArgumentList" "WS*" ")".
  Let ArgumentList :=
    "ArgumentList"
      ::== "AssignmentExpression normal,allowIn"
        || "ArgumentList" "WS*" "," "WS*" "AssignmentExpression normal,allowIn".

  (** *** Postfix Operators
<<
PostfixExpressionα ⇒
   LeftSideExpressionα
|  LeftSideExpressionα ++
>> *)
  Let PostfixExpression α :=
    ("PostfixExpression " ++ α)
      ::== ("LeftSideExpression " ++ α)
        || "PostfixExpression normal" "WS*" "'++'".

  (** *** Unary Operators
<<
UnaryExpressionα ⇒
   PostfixExpressionα
|  delete LeftSideExpressionnormal
|  ++ LeftSideExpressionnormal
|  - UnaryExpressionnormal
>> *)
  Let UnaryExpression α :=
    ("UnaryExpression " ++ α)
      ::== ("PostfixExpression " ++ α)
        || "'delete'" [\s] "WS*" "LeftSideExpression normal"
        || "'++'" "WS*" "LeftSideExpression normal"
        || "-" "WS*" "UnaryExpression normal".

  (** *** Multiplicative Operators
<<
MultiplicativeExpressionα ⇒
   UnaryExpressionα
|  MultiplicativeExpressionα * UnaryExpressionnormal
>> *)
  Let MultiplicativeExpression α :=
    ("MultiplicativeExpression " ++ α)
      ::== ("UnaryExpression " ++ α)
        || ("MultiplicativeExpression " ++ α) "WS*" "*" "WS*" "UnaryExpression normal".

  (** *** Additive Operators
<<
AdditiveExpressionα ⇒
   MultiplicativeExpressionα
|  AdditiveExpressionα + MultiplicativeExpressionnormal
>> *)
  Let AdditiveExpression α :=
    ("AdditiveExpression " ++ α)
      ::== ("MultiplicativeExpression " ++ α)
        || ("AdditiveExpression " ++ α) "WS*" "+" "WS*" "MultiplicativeExpression normal".

  (** *** Relational Operators
<<
RelationalExpressionα,allowIn ⇒
   AdditiveExpressionα
|  RelationalExpressionα,allowIn < AdditiveExpressionnormal
|  RelationalExpressionα,allowIn instanceof AdditiveExpressionnormal
|  RelationalExpressionα,allowIn in AdditiveExpressionnormal
RelationalExpressionα,noIn ⇒
   AdditiveExpressionα
|  RelationalExpressionα,noIn < AdditiveExpressionnormal
|  RelationalExpressionα,noIn instanceof AdditiveExpressionnormal
>> *)
  Let RelationalExpression α β :=
    match β with
    | "allowIn" =>
      ("RelationalExpression " ++ α ++ "," ++ β)
        ::== ("AdditiveExpression " ++ α)
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "<" "WS*" "AdditiveExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'instanceof'" "WS*" "AdditiveExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'in'" "WS*" "AdditiveExpression normal"
    | "noIn" =>
      ("RelationalExpression " ++ α ++ "," ++ β)
        ::== ("AdditiveExpression " ++ α)
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "<" "WS*" "AdditiveExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'instanceof'" "WS*" "AdditiveExpression normal"
    | _ => "ERROR" ::== "ERROR"
    end.

  (** *** Equality Operators
<<
EqualityExpressionα,β ⇒
   RelationalExpressionα,β
|  EqualityExpressionα,β == RelationalExpressionnormal,β
>> *)
  Let EqualityExpression α β :=
    Eval cbv [append] in
      ("EqualityExpression " ++ α ++ "," ++ β)
        ::== ("RelationalExpression " ++ α ++ "," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "'=='" "WS*" ("RelationalExpression normal," ++ β).

  (** *** Binary Logical Operators
<<
LogicalAndExpressionα,β ⇒
   EqualityExpressionα,β
|  LogicalAndExpressionα,β && EqualityExpressionnormal,β
>> *)
  Let LogicalAndExpression α β :=
    Eval cbv [append] in
      ("LogicalAndExpression " ++ α ++ "," ++ β)
        ::== ("EqualityExpression " ++ α ++ "," ++ β)
          || ("LogicalAndExpression " ++ α ++ "," ++ β) "WS*" "'&&'" "WS*" ("EqualityExpression normal," ++ β).

  (** *** Assignment Operators
<<
AssignmentExpressionα,β ⇒
   LogicalAndExpressionα,β
|  LeftSideExpressionα = AssignmentExpressionnormal,β
|  LeftSideExpressionα CompoundAssignment AssignmentExpressionnormal,β
>> *)
  Let AssignmentExpression α β :=
    Eval cbv [append] in
      ("AssignmentExpression " ++ α ++ "," ++ β)
        ::== ("LogicalAndExpression " ++ α ++ "," ++ β)
          || ("LeftSideExpression " ++ α) "WS*" "=" "WS*" ("AssignmentExpression normal," ++ β)
          || ("LeftSideExpression " ++ α) "WS*" "CompoundAssignment" "WS*" ("AssignmentExpression normal," ++ β).

(**
<<
CompoundAssignment ⇒
   *=
>> *)
  Let CompoundAssignment :=
    "CompoundAssignment"
      ::== "'*='".

  (** *** Expressions
<<
Expressionα,β ⇒
   AssignmentExpressionα,β
|  Expressionα,β , AssignmentExpressionnormal,β
>> *)
  Let Expression α β :=
    Eval cbv [append] in
      ("Expression " ++ α ++ "," ++ β)
        ::== ("AssignmentExpression " ++ α ++ "," ++ β)
          || ("Expression " ++ α ++ "," ++ β) "WS*" "," "WS*" ("AssignmentExpression normal," ++ β).
  (**
<<
OptionalExpression ⇒
   Expressionnormal,allowIn
|  «empty»
>> *)
  Let OptionalExpression :=
      "OptionalExpression"
        ::== "Expression normal,allowIn"
          || "".
  Let SOptionalExpression :=
      "\s OptionalExpression"
        ::== [\s] "WS*" "Expression normal,allowIn"
          || "".

  Definition javascript_assignment_expression_pregrammar' : pregrammar Ascii.ascii :=
    Eval grammar_red in
      [[[
           OptionalExpression;;
           PrimaryExpression_normal;;
           PrimaryExpression_initial;;
           SimpleExpression;;
           ParenthesizedExpression;;
           ObjectLiteral;;
           FieldList;;
           LiteralField;;
           ArrayLiteral;;
           ElementList;;
           LiteralElement;;
           LeftSideExpression "normal";;
           LeftSideExpression "initial";;
           CallExpression "normal";;
           CallExpression "initial";;
           FullNewExpression;;
           ShortNewExpression;;
           FullNewSubexpression;;
           ShortNewSubexpression;;
           MemberOperator;;
           Arguments;;
           ArgumentList;;
           PostfixExpression "normal";;
           PostfixExpression "initial";;
           UnaryExpression "normal";;
           UnaryExpression "initial";;
           MultiplicativeExpression "normal";;
           MultiplicativeExpression "initial";;
           AdditiveExpression "normal";;
           AdditiveExpression "initial";;
           RelationalExpression "normal" "allowIn";;
           RelationalExpression "initial" "allowIn";;
           RelationalExpression "normal" "noIn";;
           RelationalExpression "initial" "noIn";;
           EqualityExpression "normal" "allowIn";;
           EqualityExpression "initial" "allowIn";;
           EqualityExpression "normal" "noIn";;
           EqualityExpression "initial" "noIn";;
           LogicalAndExpression "normal" "allowIn";;
           LogicalAndExpression "initial" "allowIn";;
           LogicalAndExpression "normal" "noIn";;
           LogicalAndExpression "initial" "noIn";;
           AssignmentExpression "normal" "allowIn";;
           AssignmentExpression "initial" "allowIn";;
           AssignmentExpression "normal" "noIn";;
           AssignmentExpression "initial" "noIn";;
           CompoundAssignment;;
           Expression "normal" "allowIn";;
           Expression "initial" "allowIn";;
           Expression "normal" "noIn";;
           Expression "initial" "noIn";;
           SOptionalExpression;;
           ("Number"
              ::== "0");;
           ("String"
              ::== "'""ThisIsNotImplementedYet""'");;
           ("Identifier"
              ::== "x");;
           (**
<<
WS
   : [ \t\n\r] + -> skip
   ;
>> *)
           "WS*"
           ::== "" || [\s] "WS*"

      ]]]%grammar.
End JavaScriptAssignmentExpression.

Definition javascript_assignment_expression_pregrammar
  := Eval cbv [javascript_assignment_expression_pregrammar' append]
    in javascript_assignment_expression_pregrammar'.
(*
(** TODO
  "Number"
    "String"
    "Identifier"
    "RegularExpression"
 *)

Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Goal is_true (grammar_rvalid javascript_assignment_expression_pregrammar).
  cbv [grammar_rvalid is_true Valid_nonterminals grammar_of_pregrammar Lookup pregrammar_nonterminals].
  set (x := List.map fst javascript_assignment_expression_pregrammar).
  set (y := Lookup_string javascript_assignment_expression_pregrammar).
  vm_compute in x; subst x.
  cbv [List.map List.fold_right].
  set (z := productions_rvalid javascript_assignment_expression_pregrammar).
  repeat match goal with
  | [ |- context[y ?k] ]
    => let y' := fresh in
       fast_set' y' (y k)
  end.
  pose z as z'.
  cbv [z] in z'.
  subst y.
  hnf in * |- .
  repeat match goal with
  | [ |- context[z ?H] ]
    => is_var H; subst H
  end.
  cbv [z z' productions_rvalid  List.fold_right List.map list_to_productions list_to_grammar magic_juxta_append_productions productions_of_production    magic_juxta_append_production production_of_string production_rvalid item_rvalid production_of_chartest opt'.substring opt'.pred opt'.length opt'.list_of_string opt'.map].
  repeat (change (andb true) with (fun x : bool => x); cbv beta).
  pose (Valid_nonterminals javascript_assignment_expression_pregrammar) as x.
  vm_compute in x.
  clear z z'.
  set (k := BaseTypes.is_valid_nonterminal BaseTypes.initial_nonterminals_data).
  set (k' := BaseTypes.of_nonterminal).
  let v := (eval cbv [x] in x) in
  repeat match goal with
         | [ |- context[k (k' ?nt)] ]
           => match v with
              | context[nt]
                => change (k (k' nt)) with true
              end
         end.
  repeat (change (andb true) with (fun x : bool => x); cbv beta).
*)
