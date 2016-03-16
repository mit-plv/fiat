(** * 1. Gramamr for JavaScript AssignmentExpression *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

(** Quoting http://www-archive.mozilla.org/js/language/grammar14.html *)
(**
<<
α ∈ {normal, initial}
β ∈ {allowIn, noIn}
>> *)

Section JavaScriptAssignmentExpression.
  Local Open Scope prod_assignment.

  (** ** Primary Expressions
<<
PrimaryExpressionnormal ⇒
   SimpleExpression
|  FunctionExpression
|  ObjectLiteral
PrimaryExpressioninitial ⇒ SimpleExpression
>> *)
  Let PrimaryExpression_normal :=
    "PrimaryExpression normal"
      ::== "SimpleExpression"
        || "FunctionExpression"
        || "ObjectLiteral".
  Let PrimaryExpression_initial :=
    "PrimaryExpression initial"
      ::== "SimpleExpression".

  (**
<<
SimpleExpression ⇒
   this
|  null
|  true
|  false
|  Number
|  String
|  Identifier
|  RegularExpression
|  ParenthesizedExpression
|  ArrayLiteral
*)
  Let SimpleExpression :=
    "SimpleExpression"
      ::== "t" "h" "i" "s"
        || "n" "u" "l" "l"
        || "t" "r" "u" "e"
        || "f" "a" "l" "s" "e"
        || "Number"
        || "String"
        || "Identifier"
        || "RegularExpression"
        || "ParenthesizedExpression"
        || "ArrayLiteral".
  (**
<<
ParenthesizedExpression ⇒ ( Expressionnormal,allowIn )
>> *)
  Let ParenthesizedExpression :=
    "ParenthesizedExpression"
      ::== "(" "WS*" "Expression normal,allowIn" "WS*" ")".

  (** ** Function Expressions
<<
FunctionExpression ⇒
   AnonymousFunction
|  NamedFunction
>> *)
  Let FunctionExpression :=
    "FunctionExpression"
      ::== "AnonymousFunction"
        || "NamedFunction".

  (** ** Object Literals
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

  (** ** Array Literals
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

  (** ** Left-Side Expressions
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
      ::== "n" "e" "w" [\s] "WS*" "FullNewSubexpression" "WS*" "Arguments".
  Let ShortNewExpression :=
    "ShortNewExpression"
      ::== "n" "e" "w" [\s] "WS*" "ShortNewSubexpression" "WS*" "Arguments".

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

  (** ** Postfix Operators
<<
PostfixExpressionα ⇒
   LeftSideExpressionα
|  LeftSideExpressionα ++
|  LeftSideExpressionα --
>> *)
  Let PostfixExpression α :=
    ("PostfixExpression " ++ α)
      ::== ("LeftSideExpression " ++ α)
        || "PostfixExpression normal" "WS*" "+" "+"
        || "PostfixExpression normal" "WS*" "-" "-".

  (** ** Unary Operators
<<
UnaryExpressionα ⇒
   PostfixExpressionα
|  delete LeftSideExpressionnormal
|  void UnaryExpressionnormal
|  typeof UnaryExpressionnormal
|  ++ LeftSideExpressionnormal
|  -- LeftSideExpressionnormal
|  + UnaryExpressionnormal
|  - UnaryExpressionnormal
|  ~ UnaryExpressionnormal
|  ! UnaryExpressionnormal
>> *)
  Let UnaryExpression α :=
    ("UnaryExpression " ++ α)
      ::== ("PostfixExpression " ++ α)
        || "d" "e" "l" "e" "t" "e" [\s] "WS*" "LeftSideExpression normal"
        || "v" "o" "i" "d" [\s] "WS*" "UnaryExpression normal"
        || "t" "y" "p" "e" "o" "f" [\s] "WS*" "UnaryExpression normal"
        || "+" "+" "WS*" "LeftSideExpression normal"
        || "+" "WS*" "UnaryExpression normal"
        || "-" "WS*" "UnaryExpression normal"
        || "~" "WS*" "UnaryExpression normal"
        || "!" "WS*" "UnaryExpression normal".

  (** ** Multiplicative Operators
<<
MultiplicativeExpressionα ⇒
   UnaryExpressionα
|  MultiplicativeExpressionα * UnaryExpressionnormal
|  MultiplicativeExpressionα / UnaryExpressionnormal
|  MultiplicativeExpressionα % UnaryExpressionnormal
>> *)
  Let MultiplicativeExpression α :=
    ("MultiplicativeExpression " ++ α)
      ::== ("UnaryExpression " ++ α)
        || ("MultiplicativeExpression " ++ α) "WS*" "+" "WS*" "UnaryExpression normal"
        || ("MultiplicativeExpression " ++ α) "WS*" "-" "WS*" "UnaryExpression normal".

  (** ** Additive Operators
<<
AdditiveExpressionα ⇒
   MultiplicativeExpressionα
|  AdditiveExpressionα + MultiplicativeExpressionnormal
|  AdditiveExpressionα - MultiplicativeExpressionnormal
>> *)
  Let AdditiveExpression α :=
    ("AdditiveExpression " ++ α)
      ::== ("MultiplicativeExpression " ++ α)
        || ("AdditiveExpression " ++ α) "WS*" "+" "WS*" "MultiplicativeExpression normal"
        || ("AdditiveExpression " ++ α) "WS*" "-" "WS*" "MultiplicativeExpression normal".

  (** ** Bitwise Shift Operators
<<
ShiftExpressionα ⇒
   AdditiveExpressionα
|  ShiftExpressionα << AdditiveExpressionnormal
|  ShiftExpressionα >> AdditiveExpressionnormal
|  ShiftExpressionα >>> AdditiveExpressionnormal
>> *)
  Let ShiftExpression α :=
    ("ShiftExpression " ++ α)
      ::== ("AdditiveExpression " ++ α)
        || ("ShiftExpression " ++ α) "WS*" "<" "<" "WS*" "AdditiveExpression normal"
        || ("ShiftExpression " ++ α) "WS*" ">" ">" "WS*" "AdditiveExpression normal"
        || ("ShiftExpression " ++ α) "WS*" ">" ">" ">" "WS*" "AdditiveExpression normal".

  (** ** Relational Operators
<<
RelationalExpressionα,allowIn ⇒
   ShiftExpressionα
|  RelationalExpressionα,allowIn < ShiftExpressionnormal
|  RelationalExpressionα,allowIn > ShiftExpressionnormal
|  RelationalExpressionα,allowIn <= ShiftExpressionnormal
|  RelationalExpressionα,allowIn >= ShiftExpressionnormal
|  RelationalExpressionα,allowIn instanceof ShiftExpressionnormal
|  RelationalExpressionα,allowIn in ShiftExpressionnormal
RelationalExpressionα,noIn ⇒
   ShiftExpressionα
|  RelationalExpressionα,noIn < ShiftExpressionnormal
|  RelationalExpressionα,noIn > ShiftExpressionnormal
|  RelationalExpressionα,noIn <= ShiftExpressionnormal
|  RelationalExpressionα,noIn >= ShiftExpressionnormal
|  RelationalExpressionα,noIn instanceof ShiftExpressionnormal
>> *)
  Let RelationalExpression α β :=
    match β with
    | "allowIn" =>
      ("RelationalExpression " ++ α ++ "," ++ β)
        ::== ("ShiftExpression " ++ α)
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "<" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" ">" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "<" "=" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" ">" "=" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "i" "n" "s" "t" "a" "n" "c" "e" "o" "f" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "i" "n" "WS*" "ShiftExpression normal"
    | "noIn" =>
      ("RelationalExpression " ++ α ++ "," ++ β)
        ::== ("ShiftExpression " ++ α)
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "<" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" ">" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "<" "=" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" ">" "=" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "i" "n" "s" "t" "a" "n" "c" "e" "o" "f" "WS*" "ShiftExpression normal"
    | _ => "ERROR" ::== "ERROR"
    end.

  (** ** Equality Operators
<<
EqualityExpressionα,β ⇒
   RelationalExpressionα,β
|  EqualityExpressionα,β == RelationalExpressionnormal,β
|  EqualityExpressionα,β != RelationalExpressionnormal,β
|  EqualityExpressionα,β === RelationalExpressionnormal,β
|  EqualityExpressionα,β !== RelationalExpressionnormal,β
>> *)
  Let EqualityExpression α β :=
    Eval cbv [append] in
      ("EqualityExpression " ++ α ++ "," ++ β)
        ::== ("RelationalExpression " ++ α ++ "," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "=" "=" "WS*" ("RelationalExpression normal," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "!" "=" "WS*" ("RelationalExpression normal," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "=" "=" "=" "WS*" ("RelationalExpression normal," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "!" "=" "=" "WS*" ("RelationalExpression normal," ++ β).

  (** ** Binary Bitwise Operators
<<
BitwiseAndExpressionα,β ⇒
   EqualityExpressionα,β
|  BitwiseAndExpressionα,β & EqualityExpressionnormal,β
BitwiseXorExpressionα,β ⇒
   BitwiseAndExpressionα,β
|  BitwiseXorExpressionα,β ^ BitwiseAndExpressionnormal,β
BitwiseOrExpressionα,β ⇒
   BitwiseXorExpressionα,β
|  BitwiseOrExpressionα,β | BitwiseXorExpressionnormal,β
>> *)
  Let BitwiseAndExpression α β :=
    Eval cbv [append] in
      ("BitwiseAndExpression " ++ α ++ "," ++ β)
        ::== ("EqualityExpression " ++ α ++ "," ++ β)
          || ("BitwiseAndExpression " ++ α ++ "," ++ β) "WS*" "&" "WS*" ("EqualityExpression normal," ++ β).
  Let BitwiseXorExpression α β :=
    Eval cbv [append] in
      ("BitwiseXorExpression " ++ α ++ "," ++ β)
        ::== ("BitwiseAndExpression " ++ α ++ "," ++ β)
          || ("BitwiseXorExpression " ++ α ++ "," ++ β) "WS*" "^" "WS*" ("BitwiseAndExpression normal," ++ β).
  Let BitwiseOrExpression α β :=
    Eval cbv [append] in
      ("BitwiseOrExpression " ++ α ++ "," ++ β)
        ::== ("BitwiseXorExpression " ++ α ++ "," ++ β)
          || ("BitwiseOrExpression " ++ α ++ "," ++ β) "WS*" "|" "WS*" ("BitwiseXorExpression normal," ++ β).

  (** ** Binary Logical Operators
<<
LogicalAndExpressionα,β ⇒
   BitwiseOrExpressionα,β
|  LogicalAndExpressionα,β && BitwiseOrExpressionnormal,β
LogicalOrExpressionα,β ⇒
   LogicalAndExpressionα,β
|  LogicalOrExpressionα,β || LogicalAndExpressionnormal,β
>> *)
  Let LogicalAndExpression α β :=
    Eval cbv [append] in
      ("LogicalAndExpression " ++ α ++ "," ++ β)
        ::== ("BitwiseOrExpression " ++ α ++ "," ++ β)
          || ("LogicalAndExpression " ++ α ++ "," ++ β) "WS*" "&" "&" "WS*" ("BitwiseOrExpression normal," ++ β).
  Let LogicalOrExpression α β :=
    Eval cbv [append] in
      ("LogicalOrExpression " ++ α ++ "," ++ β)
        ::== ("LogicalAndExpression " ++ α ++ "," ++ β)
          || ("LogicalOrExpression " ++ α ++ "," ++ β) "WS*" "|" "|" "WS*" ("LogicalAndExpression normal," ++ β).

  (** ** Conditional Operator
<<
ConditionalExpressionα,β ⇒
   LogicalOrExpressionα,β
|  LogicalOrExpressionα,β ? AssignmentExpressionnormal,β : AssignmentExpressionnormal,β
>> *)
  Let ConditionalExpression α β :=
    Eval cbv [append] in
      ("ConditionalExpression " ++ α ++ "," ++ β)
        ::== ("LogicalOrExpression " ++ α ++ "," ++ β)
          || ("LogicalOrExpression " ++ α ++ "," ++ β) "WS*" "?" "WS*" ("AssignmentExpression normal," ++ β) "WS*" ":" "WS*" ("AssignmentExpression normal," ++ β).

  (** ** Assignment Operators
<<
AssignmentExpressionα,β ⇒
   ConditionalExpressionα,β
|  LeftSideExpressionα = AssignmentExpressionnormal,β
|  LeftSideExpressionα CompoundAssignment AssignmentExpressionnormal,β
>> *)
  Let AssignmentExpression α β :=
    Eval cbv [append] in
      ("AssignmentExpression " ++ α ++ "," ++ β)
        ::== ("ConditionalExpression " ++ α ++ "," ++ β)
          || ("LeftSideExpression " ++ α) "WS*" "=" "WS*" ("AssignmentExpression normal," ++ β)
          || ("LeftSideExpression " ++ α) "WS*" "CompoundAssignment" "WS*" ("AssignmentExpression normal," ++ β).

(**
<<
CompoundAssignment ⇒
   *=
|  /=
|  %=
|  +=
|  -=
|  <<=
|  >>=
|  >>>=
|  &=
|  ^=
|  |=
>> *)
  Let CompoundAssignment :=
    "CompoundAssignment"
      ::== "*" "="
        || "/" "="
        || "%" "="
        || "+" "="
        || "-" "="
        || "<" "<" "="
        || ">" ">" "="
        || ">" ">" ">" "="
        || "&" "="
        || "^" "="
        || "|" "=".

(** ** Expressions
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

  Definition javascript_assignment_expression'_pregrammar' : pregrammar ascii :=
    Eval grammar_red in
      [[[
           OptionalExpression;;
           PrimaryExpression_normal;;
           PrimaryExpression_initial;;
           SimpleExpression;;
           ParenthesizedExpression;;
           FunctionExpression;;
           ObjectLiteral;;
           FieldList;;
           LiteralField;;
           ArrayLiteral;;
           ElementList;;
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
           ShiftExpression "normal";;
           ShiftExpression "initial";;
           RelationalExpression "normal" "allowIn";;
           RelationalExpression "initial" "allowIn";;
           RelationalExpression "normal" "noIn";;
           RelationalExpression "initial" "noIn";;
           EqualityExpression "normal" "allowIn";;
           EqualityExpression "initial" "allowIn";;
           EqualityExpression "normal" "noIn";;
           EqualityExpression "initial" "noIn";;
           BitwiseAndExpression "normal" "allowIn";;
           BitwiseAndExpression "initial" "allowIn";;
           BitwiseAndExpression "normal" "noIn";;
           BitwiseAndExpression "initial" "noIn";;
           BitwiseXorExpression "normal" "allowIn";;
           BitwiseXorExpression "initial" "allowIn";;
           BitwiseXorExpression "normal" "noIn";;
           BitwiseXorExpression "initial" "noIn";;
           BitwiseOrExpression "normal" "allowIn";;
           BitwiseOrExpression "initial" "allowIn";;
           BitwiseOrExpression "normal" "noIn";;
           BitwiseOrExpression "initial" "noIn";;
           LogicalAndExpression "normal" "allowIn";;
           LogicalAndExpression "initial" "allowIn";;
           LogicalAndExpression "normal" "noIn";;
           LogicalAndExpression "initial" "noIn";;
           LogicalOrExpression "normal" "allowIn";;
           LogicalOrExpression "initial" "allowIn";;
           LogicalOrExpression "normal" "noIn";;
           LogicalOrExpression "initial" "noIn";;
           ConditionalExpression "normal" "allowIn";;
           ConditionalExpression "initial" "allowIn";;
           ConditionalExpression "normal" "noIn";;
           ConditionalExpression "initial" "noIn";;
           AssignmentExpression "normal" "allowIn";;
           AssignmentExpression "initial" "allowIn";;
           AssignmentExpression "normal" "noIn";;
           AssignmentExpression "initial" "noIn";;
           CompoundAssignment;;
           Expression "normal" "allowIn";;
           Expression "initial" "allowIn";;
           Expression "normal" "noIn";;
           Expression "initial" "noIn";;
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

Definition javascript_assignment_expression'_pregrammar
  := Eval cbv [javascript_assignment_expression'_pregrammar' append]
    in javascript_assignment_expression'_pregrammar'.

(** TODO "AnonymousFunction"
 "NamedFunction"
 "Identifier"
 "LiteralElement"
 "Identifier"

        || "Number"
        || "String"
        || "Identifier"
        || "RegularExpression"
 *)
(*
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Goal is_true (grammar_rvalid javascript_assignment_expression'_pregrammar).
  cbv [grammar_rvalid is_true Valid_nonterminals grammar_of_pregrammar Lookup pregrammar_nonterminals].
  set (x := List.map fst javascript_assignment_expression'_pregrammar).
  set (y := Lookup_string javascript_assignment_expression'_pregrammar).
  set (z := productions_rvalid javascript_assignment_expression'_pregrammar).
  vm_compute in x; subst x.
  cbv [List.map List.fold_right].
  repeat match goal with
  | [ |- appcontext[z (y ?k)] ]
    => let y' := fresh in
       set (y' := (y k));
         hnf in y';
         subst y'
  end;
    subst y.
  cbv [z productions_rvalid  List.fold_right List.map list_to_productions list_to_grammar magic_juxta_append_productions productions_of_production    magic_juxta_append_production production_of_string production_rvalid item_rvalid production_of_chartest].
  repeat (change (andb true) with (fun x : bool => x); cbv beta).
  pose (Valid_nonterminals javascript_assignment_expression'_pregrammar) as x.
  vm_compute in x.
  let v := (eval cbv [x] in x) in
  repeat match goal with
         | [ |- context G[BaseTypes.is_valid_nonterminal ?a (BaseTypes.of_nonterminal ?nt)] ]
           => match v with
              | context[nt]
                => let G' := context G[true] in
                   change G'
              end
         end.
  repeat (change (andb true) with (fun x : bool => x); cbv beta).
  set (x := BaseTypes.initial_nonterminals_data).

  vm_compute in x.
Set Printing Depth 100000.
  repeat match goal with
  | [ |- appcontext[z (y ?k)] ]
    => change (z (y k)) with true
  end.
  change (andb true) with (fun x : bool => x).
  cbv beta.
  repeat match goal with
  | [ |- appcontext[z (y ?k)] ]
    => let y' := fresh in
       set (y' := (y k));
         hnf in y';
         subst y'
  end;
    subst y.
  cbv [productions_rvalid z List.fold_right List.map list_to_productions list_to_grammar magic_juxta_append_productions productions_of_production    magic_juxta_append_production production_of_string].
  repeat match goal with
         | [ |- appcontext[production_rvalid ?x ?y] ]
           => change (production_rvalid x y) with true
         end.
  change (andb true) with (fun x : bool => x).
  cbv beta.
  cbv [production_rvalid List.map List.fold_right item_rvalid].
  repeat match goal with
         | [ |- appcontext G[BaseTypes.is_valid_nonterminal ?x ?y] ]
           => let G' := context G[true] in
              change G'
         end.
  repeat (change (andb true) with (fun x : bool => x); cbv beta).
Set Printing All.


  vm_compute.*)
