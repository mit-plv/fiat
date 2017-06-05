(** * 1. Gramamr for JavaScript 1.4 *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

(** Quoting http://www-archive.mozilla.org/js/language/grammar14.html *)

Section JavaScript.
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
      ::== "'this'"
        || "'null'"
        || "'true'"
        || "'false'"
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

  (** *** Function Expressions
<<
FunctionExpression ⇒
   AnonymousFunction
|  NamedFunction
>> *)
  Let FunctionExpression :=
    "FunctionExpression"
      ::== "AnonymousFunction"
        || "NamedFunction".

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
|  LeftSideExpressionα --
>> *)
  Let PostfixExpression α :=
    ("PostfixExpression " ++ α)
      ::== ("LeftSideExpression " ++ α)
        || "PostfixExpression normal" "WS*" "'++'"
        || "PostfixExpression normal" "WS*" "'--'".

  (** *** Unary Operators
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
        || "'delete'" [\s] "WS*" "LeftSideExpression normal"
        || "'void'" [\s] "WS*" "UnaryExpression normal"
        || "'typeof'" [\s] "WS*" "UnaryExpression normal"
        || "'++'" "WS*" "LeftSideExpression normal"
        || "'--'" "WS*" "LeftSideExpression normal"
        || "+" "WS*" "UnaryExpression normal"
        || "-" "WS*" "UnaryExpression normal"
        || "~" "WS*" "UnaryExpression normal"
        || "!" "WS*" "UnaryExpression normal".

  (** *** Multiplicative Operators
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
        || ("MultiplicativeExpression " ++ α) "WS*" "*" "WS*" "UnaryExpression normal"
        || ("MultiplicativeExpression " ++ α) "WS*" "/" "WS*" "UnaryExpression normal"
        || ("MultiplicativeExpression " ++ α) "WS*" "%" "WS*" "UnaryExpression normal".

  (** *** Additive Operators
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

  (** *** Bitwise Shift Operators
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
        || ("ShiftExpression " ++ α) "WS*" "'<<'" "WS*" "AdditiveExpression normal"
        || ("ShiftExpression " ++ α) "WS*" "'>>'" "WS*" "AdditiveExpression normal"
        || ("ShiftExpression " ++ α) "WS*" "'>>>'" "WS*" "AdditiveExpression normal".

  (** *** Relational Operators
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
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'<='" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'>='" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'instanceof'" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'in'" "WS*" "ShiftExpression normal"
    | "noIn" =>
      ("RelationalExpression " ++ α ++ "," ++ β)
        ::== ("ShiftExpression " ++ α)
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "<" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" ">" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'<='" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'>='" "WS*" "ShiftExpression normal"
          || ("RelationalExpression " ++ α ++ "," ++ β) "WS*" "'instanceof'" "WS*" "ShiftExpression normal"
    | _ => "ERROR" ::== "ERROR"
    end.

  (** *** Equality Operators
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
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "'=='" "WS*" ("RelationalExpression normal," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "'!='" "WS*" ("RelationalExpression normal," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "'==='" "WS*" ("RelationalExpression normal," ++ β)
          || ("EqualityExpression " ++ α ++ "," ++ β) "WS*" "'!=='" "WS*" ("RelationalExpression normal," ++ β).

  (** *** Binary Bitwise Operators
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

  (** *** Binary Logical Operators
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
          || ("LogicalAndExpression " ++ α ++ "," ++ β) "WS*" "'&&'" "WS*" ("BitwiseOrExpression normal," ++ β).
  Let LogicalOrExpression α β :=
    Eval cbv [append] in
      ("LogicalOrExpression " ++ α ++ "," ++ β)
        ::== ("LogicalAndExpression " ++ α ++ "," ++ β)
          || ("LogicalOrExpression " ++ α ++ "," ++ β) "WS*" "'||'" "WS*" ("LogicalAndExpression normal," ++ β).

  (** *** Conditional Operator
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

  (** *** Assignment Operators
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
      ::== "'*='"
        || "'/='"
        || "'%='"
        || "'+='"
        || "'-='"
        || "'<<='"
        || "'>>='"
        || "'>>>='"
        || "'&='"
        || "'^='"
        || "'|='".

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

  (** ** Statements *)
  (**
<<
ω ∈ {noShortIf, full}
>> *)

  (**
<<
Statementω ⇒
   EmptyStatement
|  ExpressionStatement OptionalSemicolon
|  VariableDefinition OptionalSemicolon
|  Block
|  LabeledStatementω
|  IfStatementω
|  SwitchStatement
|  DoStatement OptionalSemicolon
|  WhileStatementω
|  ForStatementω
|  WithStatementω
|  ContinueStatement OptionalSemicolon
|  BreakStatement OptionalSemicolon
|  ReturnStatement OptionalSemicolon
|  ThrowStatement OptionalSemicolon
|  TryStatement
OptionalSemicolon ⇒ ;
>> *)
  Let Statement ω :=
    ("Statement " ++ ω)
      ::== "EmptyStatement"
        || "ExpressionStatement" "WS*" "OptionalSemicolon"
        || "VariableDefinition" "WS*" "OptionalSemicolon"
        || "Block"
        || ("LabeledStatement " ++ ω)
        || ("IfStatement " ++ ω)
        || "SwitchStatement"
        || "DoStatement" "WS*" "OptionalSemicolon"
        || ("WhileStatement " ++ ω)
        || ("ForStatement " ++ ω)
        || ("WithStatement " ++ ω)
        || "ContinueStatement" "WS*" "OptionalSemicolon"
        || "BreakStatement" "WS*" "OptionalSemicolon"
        || "ReturnStatement" "WS*" "OptionalSemicolon"
        || "ThrowStatement" "WS*" "OptionalSemicolon"
        || "TryStatement".
  Let OptionalSemicolon :=
    "OptionalSemicolon" ::== ";".

  (** *** Empty Statement
<<
EmptyStatement ⇒ ;
>> *)
  Let EmptyStatement :=
    "EmptyStatement" ::== ";".

  (** *** Expression Statement
<<
ExpressionStatement ⇒ Expressioninitial,allowIn
>> *)
  Let ExpressionStatement :=
    "ExpressionStatement" ::== "Expression initial,allowIn".

  (** *** Variable Definition
<<
VariableDefinition ⇒ var VariableDeclarationListallowIn
VariableDeclarationListβ ⇒
   VariableDeclarationβ
|  VariableDeclarationListβ , VariableDeclarationβ
VariableDeclarationβ ⇒ Identifier VariableInitializerβ
VariableInitializerβ ⇒
   «empty»
|  = AssignmentExpressionnormal,β
>> *)
  Let VariableDefinition :=
    "VariableDefinition" ::== "'var'" [\s] "WS*" "VariableDeclarationList allowIn".
  Let VariableDeclarationList β :=
    ("VariableDeclarationList " ++ β)
      ::== ("VariableDeclaration " ++ β)
        || ("VariableDeclarationList " ++ β) "WS*" "," "WS*" ("VariableDeclaration " ++ β).
  Let VariableDeclaration β :=
    ("VariableDeclaration " ++ β)
      ::== "Identifier" ("VariableInitializer " ++ β).
  Let VariableInitializer β :=
    ("VariableInitializer " ++ β)
      ::== "WS*"
        || "WS*" "=" "WS*" ("AssignmentExpression normal," ++ β).

  (** *** Block
<<
Block ⇒ { BlockStatements }
BlockStatements ⇒
   «empty»
|  BlockStatementsPrefix
BlockStatementsPrefix ⇒
   Statementfull
|  BlockStatementsPrefix Statementfull
>> *)
  Let Block :=
    "Block"
      ::== "{" "WS*" "BlockStatements" "WS*" "}".
  Let BlockStatements :=
    "BlockStatements"
      ::== ""
        || "BlockStatementsPrefix".
  Let BlockStatementsPrefix :=
    "BlockStatementsPrefix"
      ::== "Statement full"
        || "BlockStatementsPrefix" "Statement full".

  (** *** Labeled Statements
<<
LabeledStatementω ⇒ Identifier : Statementω
>> *)
  Let LabeledStatement ω :=
    ("LabeledStatement " ++ ω)
      ::== "Identifier" "WS*" ":" "WS*" ("Statement " ++ ω).

  (** *** If Statement
<<
IfStatementfull ⇒
   if ParenthesizedExpression Statementfull
|  if ParenthesizedExpression StatementnoShortIf else Statementfull
IfStatementnoShortIf ⇒ if ParenthesizedExpression StatementnoShortIf else StatementnoShortIf
>> *)
  Let IfStatement_full :=
    "IfStatement full"
      ::== "'if'" "WS*" "ParenthesizedExpression" "WS*" "Statement full"
        || "'if'" "WS*" "ParenthesizedExpression" "WS*" "Statement noShortIf" "WS*" "'else'" "WS*" "Statement full".
  Let IfStatement_noShortIf :=
    "IfStatement noShortIf"
      ::== "'if'" "WS*" "ParenthesizedExpression" "WS*" "Statement noShortIf" "WS*" "'else'" "WS*" "Statement noShortIf".

  (** *** Switch Statement
<<
SwitchStatement ⇒
   switch ParenthesizedExpression { }
|  switch ParenthesizedExpression { CaseGroups LastCaseGroup }
CaseGroups ⇒
   «empty»
|  CaseGroups CaseGroup
CaseGroup ⇒ CaseGuards BlockStatementsPrefix
LastCaseGroup ⇒ CaseGuards BlockStatements
CaseGuards ⇒
   CaseGuard
|  CaseGuards CaseGuard
CaseGuard ⇒
   case Expressionnormal,allowIn :
|  default :
>> *)
  Let SwitchStatement :=
    "SwitchStatement"
      ::== "'switch'" "WS*" "ParenthesizedExpression" "WS*" "{" "WS*" "}"
        || "'switch'" "WS*" "ParenthesizedExpression" "WS*" "{" "WS* CaseGroups WS*" "LastCaseGroup" "WS*" "}".
  Let CaseGroups :=
    "WS* CaseGroups WS*"
      ::== "WS*"
        || "WS* CaseGroups WS*" "CaseGroup" "WS*".
  Let CaseGroup :=
    "CaseGroup" ::== "CaseGuards" "WS*" "BlockStatementsPrefix".
  Let LastCaseGroup :=
    "LastCaseGroup" ::== "CaseGuards" "WS*" "BlockStatements".
  Let CaseGuards :=
    "CaseGuards"
      ::== "CaseGuard"
        || "CaseGuards" "WS*" "CaseGuard".
  Let CaseGuard :=
    "CaseGuard"
      ::== "'case'" [\s] "WS*" "Expression normal,allowIn" "WS*" ":"
        || "'default'" "WS*" ":".

  (** *** Do-While Statement
<<
DoStatement ⇒ do Statementfull while ParenthesizedExpression
>> *)
  Let DoStatement :=
    "DoStatement"
      ::== "'do'" [\s] "WS*" "Statement full" "WS*" "'while'" "WS*" "ParenthesizedExpression".

  (** *** While Statement
<<
WhileStatementω ⇒ while ParenthesizedExpression Statementω
>> *)
  Let WhileStatement ω :=
    ("WhileStatement " ++ ω)
      ::== "'while'" "WS*" "ParenthesizedExpression" "WS*" ("Statement " ++ ω).

  (** *** For Statements
<<
ForStatementω ⇒
   for ( ForInitializer ; OptionalExpression ; OptionalExpression ) Statementω
|  for ( ForInBinding in Expressionnormal,allowIn ) Statementω
ForInitializer ⇒
   «empty»
|  Expressionnormal,noIn
|  var VariableDeclarationListnoIn
ForInBinding ⇒
   LeftSideExpressionnormal
|  var VariableDeclarationnoIn
>> *)
  Let ForStatement ω :=
    ("ForStatement " ++ ω)
      ::== "'for'" "WS*" "(" "WS*" "ForInitializer" "WS*" ";" "WS*" "OptionalExpression" "WS*" ";" "WS*" "OptionalExpression" "WS*" ")" "WS*" ("Statement " ++ ω)
        || "'for'" "WS*" "(" "WS*" "ForInBinding" [\s] "WS*" "'in'" [\s] "WS*" "Expression normal,allowIn" "WS*" ")" "WS*" ("Statement " ++ ω).
  Let ForInitializer :=
    "ForInitializer"
      ::== ""
        || "Expression normal,noIn"
        || "'var'" [\s] "WS*" "VariableDeclarationList noIn".
  Let ForInBinding :=
    "ForInBinding"
      ::== "LeftSideExpression normal"
        || "'var'" [\s] "WS*" "VariableDeclaration noIn".

  (** *** With Statement
<<
WithStatementω ⇒ with ParenthesizedExpression Statementω
>> *)
  Let WithStatement ω :=
    ("WithStatement " ++ ω)
      ::== "'with'" "WS*" "ParenthesizedExpression" "WS*" ("Statement " ++ ω).

  (** *** Continue and Break Statements
<<
ContinueStatement ⇒ continue OptionalLabel
BreakStatement ⇒ break OptionalLabel
OptionalLabel ⇒
   «empty»
|  Identifier
>> *)
  Let ContinueStatement :=
    "ContinueStatement" ::== "'continue'" "OptionalLabel".
  Let BreakStatement :=
    "BreakStatement" ::== "'break'" "OptionalLabel".
  Let OptionalLabel :=
    "OptionalLabel"
      ::== ""
        || [\s] "WS*" "Identifier".

  (** *** Return Statement
<<
ReturnStatement ⇒ return OptionalExpression
>> *)
  Let ReturnStatement :=
    "ReturnStatement" ::== "'return'" "\s OptionalExpression".

  (** *** Throw Statement
<<
ThrowStatement ⇒ throw Expressionnormal,allowIn
>> *)
  Let ThrowStatement :=
    "ThrowStatement" ::== "'throw'" [\s] "WS*" "Expression normal,allowIn".

  (** *** Try Statement
<<
TryStatement ⇒
   try Block CatchClauses
|  try Block FinallyClause
|  try Block CatchClauses FinallyClause
CatchClauses ⇒
   CatchClause
|  CatchClauses CatchClause
CatchClause ⇒ catch ( Identifier ) Block
FinallyClause ⇒ finally Block
>> *)
  Let TryStatement :=
    "TryStatement"
      ::== "'try'" "WS*" "Block" "WS*" "CatchClauses"
        || "'try'" "WS*" "Block" "WS*" "FinallyClause"
        || "'try'" "WS*" "Block" "WS*" "CatchClauses" "WS*" "FinallyClause".
  Let CatchClauses :=
    "CatchClauses"
      ::== "CatchClause"
        || "CatchClauses" "WS*" "CatchClause".
  Let CatchClause :=
    "CatchClause" ::== "'catch'" "WS*" "(" "WS*" "Identifier" "WS*" ")" "WS*" "Block".
  Let FinallyClause :=
    "FinallyClause" ::== "'finally'" "WS*" "Block".

  (** *** Function Definition
<<
FunctionDefinition ⇒ NamedFunction
AnonymousFunction ⇒ function FormalParametersAndBody
NamedFunction ⇒ function Identifier FormalParametersAndBody
FormalParametersAndBody ⇒ ( FormalParameters ) { TopStatements }
FormalParameters ⇒
   «empty»
|  FormalParametersPrefix
FormalParametersPrefix ⇒
   FormalParameter
|  FormalParametersPrefix , FormalParameter
FormalParameter ⇒ Identifier
>> *)
  Let FunctionDefinition :=
    "FunctionDefinition" ::== "NamedFunction".
  Let AnonymousFunction :=
    "AnonymousFunction" ::== "'function'" "WS*" "FormalParametersAndBody".
  Let NamedFunction :=
    "NamedFunction" ::== "'function'" [\s] "WS*" "Identifier" "WS*" "FormalParametersAndBody".
  Let FormalParametersAndBody :=
    "FormalParametersAndBody" ::== "(" "WS*" "FormalParameters" "WS*" ")" "WS*" "{" "WS*" "TopStatements" "WS*" "}".
  Let FormalParameters :=
    "FormalParameters"
      ::== ""
        || "FormalParametersPrefix".
  Let FormalParametersPrefix :=
    "FormalParametersPrefix"
      ::== "FormalParameter"
        || "FormalParametersPrefix" "WS*" "," "WS*" "FormalParameter".
  Let FormalParameter :=
    "FormalParameter"
      ::== "Identifier".

  (** ** Programs *)
  (**
<<
Program ⇒ TopStatements
TopStatements ⇒
   «empty»
|  TopStatementsPrefix
TopStatementsPrefix ⇒
   TopStatement
|  TopStatementsPrefix TopStatement
TopStatement ⇒
   Statementfull
|  FunctionDefinition
>> *)
  Let Program :=
    "Program"
      ::== "TopStatements".
  Let TopStatements :=
    "TopStatements"
      ::== ""
        || "TopStatementsPrefix".
  Let TopStatementsPrefix :=
    "TopStatementsPrefix"
      ::== "TopStatement"
        || "TopStatementsPrefix" "WS*" "TopStatement".
  Let TopStatement :=
    "TopStatement"
      ::== "Statement full"
        || "FunctionDefinition".

  Definition javascript'_pregrammar' : pregrammar Ascii.ascii :=
    Eval grammar_red in
      [[[
           Program;;
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
           OptionalExpression;;
           SOptionalExpression;;
           Statement "noShortIf";;
           Statement "full";;
           OptionalSemicolon;;
           EmptyStatement;;
           ExpressionStatement;;
           VariableDefinition;;
           VariableDeclarationList "allowIn";;
           VariableDeclarationList "noIn";;
           VariableDeclaration "allowIn";;
           VariableDeclaration "noIn";;
           VariableInitializer "allowIn";;
           VariableInitializer "noIn";;
           Block;;
           BlockStatements;;
           BlockStatementsPrefix;;
           LabeledStatement "noShortIf";;
           LabeledStatement "full";;
           IfStatement_full;;
           IfStatement_noShortIf;;
           SwitchStatement;;
           CaseGroups;;
           CaseGroup;;
           LastCaseGroup;;
           CaseGuards;;
           CaseGuard;;
           DoStatement;;
           WhileStatement "noShortIf";;
           WhileStatement "full";;
           ForStatement "noShortIf";;
           ForStatement "full";;
           ForInitializer;;
           ForInBinding;;
           WithStatement "noShortIf";;
           WithStatement "full";;
           ContinueStatement;;
           BreakStatement;;
           OptionalLabel;;
           ReturnStatement;;
           ThrowStatement;;
           TryStatement;;
           CatchClauses;;
           CatchClause;;
           FinallyClause;;
           FunctionDefinition;;
           AnonymousFunction;;
           NamedFunction;;
           FormalParametersAndBody;;
           FormalParameters;;
           FormalParametersPrefix;;
           FormalParameter;;
           TopStatements;;
           TopStatementsPrefix;;
           TopStatement;;
           (**
<<
WS
   : [ \t\n\r] + -> skip
   ;
>> *)
           "WS*"
           ::== "" || [\s] "WS*"

      ]]]%grammar.
End JavaScript.

Definition javascript'_pregrammar
  := Eval cbv [javascript'_pregrammar' append]
    in javascript'_pregrammar'.

(** TODO
  "Number"
    "String"
    "Identifier"
    "RegularExpression"
 *)

(*
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Goal is_true (grammar_rvalid javascript'_pregrammar).
  cbv [grammar_rvalid is_true Valid_nonterminals grammar_of_pregrammar Lookup pregrammar_nonterminals].
  set (x := List.map fst javascript'_pregrammar).
  set (y := Lookup_string javascript'_pregrammar).
  vm_compute in x; subst x.
  cbv [List.map List.fold_right].
  set (z := productions_rvalid javascript'_pregrammar).
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
  pose (Valid_nonterminals javascript'_pregrammar) as x.
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
