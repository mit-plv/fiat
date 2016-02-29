(*3
ω ∈ {noShortIf, full}
Statementω ⇒
   EmptyStatement
|  (*ExpressionStatement OptionalSemicolon*)
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
Empty Statement





JavaScript 1.4 Grammar
up
Monday, May 3, 1999

This is an LR(1) grammar written by waldemar that describes the state of ECMAScript as of February 1999. The grammar is complete except for semicolon insertion (the OptionalSemicolon grammar state can sometimes reduce to «empty») and distinguishing RegularExpression from / and /=. Also, there is some controversy about elision in array literals, so this feature has been omitted for now.

Grammar syntax

Grammar productions may expand nonterminals into empty right sides. Such right sides are indicated as «empty».

A number of rules in the grammar occur in groups of analogous rules. Rather than list them individually, these groups have been summarized using the shorthand illustrated by the example below:

Statements such as

α ∈ {normal, initial}
β ∈ {allowIn, noIn}
introduce grammar arguments α and β. If these arguments later parametrize the nonterminal on the left side of a rule, that rule is implicitly replicated into a set of rules in each of which a grammar argument is consistently substituted by one of its variants. For example,

AssignmentExpressionα,β  ⇒
   ConditionalExpressionα,β
|  LeftSideExpressionα = AssignmentExpressionnormal,β
|  LeftSideExpressionα CompoundAssignment AssignmentExpressionnormal,β
expands into the following four rules:

AssignmentExpressionnormal,allowIn  ⇒
   ConditionalExpressionnormal,allowIn
|  LeftSideExpressionnormal = AssignmentExpressionnormal,allowIn
|  LeftSideExpressionnormal CompoundAssignment AssignmentExpressionnormal,allowIn
AssignmentExpressionnormal,noIn  ⇒
   ConditionalExpressionnormal,noIn
|  LeftSideExpressionnormal = AssignmentExpressionnormal,noIn
|  LeftSideExpressionnormal CompoundAssignment AssignmentExpressionnormal,noIn
AssignmentExpressioninitial,allowIn  ⇒
   ConditionalExpressioninitial,allowIn
|  LeftSideExpressioninitial = AssignmentExpressionnormal,allowIn
|  LeftSideExpressioninitial CompoundAssignment AssignmentExpressionnormal,allowIn
AssignmentExpressioninitial,noIn  ⇒
   ConditionalExpressioninitial,noIn
|  LeftSideExpressioninitial = AssignmentExpressionnormal,noIn
|  LeftSideExpressioninitial CompoundAssignment AssignmentExpressionnormal,noIn
AssignmentExpressionnormal,allowIn is now an unparametrized nonterminal and processed normally by the grammar.

Some of the expanded rules (such as the fourth one in the example above) may be unreachable from the starting nonterminal Program; these are ignored.

Expressions

α ∈ {normal, initial}
β ∈ {allowIn, noIn}
Primary Expressions

PrimaryExpressionnormal ⇒
   SimpleExpression
|  FunctionExpression
|  ObjectLiteral
PrimaryExpressioninitial ⇒ SimpleExpression
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
ParenthesizedExpression ⇒ ( Expressionnormal,allowIn )
Function Expressions

FunctionExpression ⇒
   AnonymousFunction
|  NamedFunction
Object Literals

ObjectLiteral ⇒
   { }
|  { FieldList }
FieldList ⇒
   LiteralField
|  FieldList , LiteralField
LiteralField ⇒ Identifier : AssignmentExpressionnormal,allowIn
Array Literals

ArrayLiteral ⇒
   [ ]
|  [ ElementList ]
ElementList ⇒
   LiteralElement
|  ElementList , LiteralElement
LiteralElement ⇒ AssignmentExpressionnormal,allowIn
Left-Side Expressions

LeftSideExpressionα ⇒
   CallExpressionα
|  ShortNewExpression
CallExpressionα ⇒
   PrimaryExpressionα
|  FullNewExpression
|  CallExpressionα MemberOperator
|  CallExpressionα Arguments
FullNewExpression ⇒ new FullNewSubexpression Arguments
ShortNewExpression ⇒ new ShortNewSubexpression
FullNewSubexpression ⇒
   PrimaryExpressionnormal
|  FullNewExpression
|  FullNewSubexpression MemberOperator
ShortNewSubexpression ⇒
   FullNewSubexpression
|  ShortNewExpression
MemberOperator ⇒
   [ Expressionnormal,allowIn ]
|  . Identifier
Arguments ⇒
   ( )
|  ( ArgumentList )
ArgumentList ⇒
   AssignmentExpressionnormal,allowIn
|  ArgumentList , AssignmentExpressionnormal,allowIn
Postfix Operators

PostfixExpressionα ⇒
   LeftSideExpressionα
|  LeftSideExpressionα ++
|  LeftSideExpressionα --
Unary Operators

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
Multiplicative Operators

MultiplicativeExpressionα ⇒
   UnaryExpressionα
|  MultiplicativeExpressionα * UnaryExpressionnormal
|  MultiplicativeExpressionα / UnaryExpressionnormal
|  MultiplicativeExpressionα % UnaryExpressionnormal
Additive Operators

AdditiveExpressionα ⇒
   MultiplicativeExpressionα
|  AdditiveExpressionα + MultiplicativeExpressionnormal
|  AdditiveExpressionα - MultiplicativeExpressionnormal
Bitwise Shift Operators

ShiftExpressionα ⇒
   AdditiveExpressionα
|  ShiftExpressionα << AdditiveExpressionnormal
|  ShiftExpressionα >> AdditiveExpressionnormal
|  ShiftExpressionα >>> AdditiveExpressionnormal
Relational Operators

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
Equality Operators

EqualityExpressionα,β ⇒
   RelationalExpressionα,β
|  EqualityExpressionα,β == RelationalExpressionnormal,β
|  EqualityExpressionα,β != RelationalExpressionnormal,β
|  EqualityExpressionα,β === RelationalExpressionnormal,β
|  EqualityExpressionα,β !== RelationalExpressionnormal,β
Binary Bitwise Operators

BitwiseAndExpressionα,β ⇒
   EqualityExpressionα,β
|  BitwiseAndExpressionα,β & EqualityExpressionnormal,β
BitwiseXorExpressionα,β ⇒
   BitwiseAndExpressionα,β
|  BitwiseXorExpressionα,β ^ BitwiseAndExpressionnormal,β
BitwiseOrExpressionα,β ⇒
   BitwiseXorExpressionα,β
|  BitwiseOrExpressionα,β | BitwiseXorExpressionnormal,β
Binary Logical Operators

LogicalAndExpressionα,β ⇒
   BitwiseOrExpressionα,β
|  LogicalAndExpressionα,β && BitwiseOrExpressionnormal,β
LogicalOrExpressionα,β ⇒
   LogicalAndExpressionα,β
|  LogicalOrExpressionα,β || LogicalAndExpressionnormal,β
Conditional Operator

ConditionalExpressionα,β ⇒
   LogicalOrExpressionα,β
|  LogicalOrExpressionα,β ? AssignmentExpressionnormal,β : AssignmentExpressionnormal,β
Assignment Operators

AssignmentExpressionα,β ⇒
   ConditionalExpressionα,β
|  LeftSideExpressionα = AssignmentExpressionnormal,β
|  LeftSideExpressionα CompoundAssignment AssignmentExpressionnormal,β
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
Expressions

Expressionα,β ⇒
   AssignmentExpressionα,β
|  Expressionα,β , AssignmentExpressionnormal,β
OptionalExpression ⇒
   Expressionnormal,allowIn
|  «empty»
Statements

ω ∈ {noShortIf, full}
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
Empty Statement

EmptyStatement ⇒ ;
Expression Statement

ExpressionStatement ⇒ Expressioninitial,allowIn
Variable Definition

VariableDefinition ⇒ var VariableDeclarationListallowIn
VariableDeclarationListβ ⇒
   VariableDeclarationβ
|  VariableDeclarationListβ , VariableDeclarationβ
VariableDeclarationβ ⇒ Identifier VariableInitializerβ
VariableInitializerβ ⇒
   «empty»
|  = AssignmentExpressionnormal,β
Block

Block ⇒ { BlockStatements }
BlockStatements ⇒
   «empty»
|  BlockStatementsPrefix
BlockStatementsPrefix ⇒
   Statementfull
|  BlockStatementsPrefix Statementfull
Labeled Statements

LabeledStatementω ⇒ Identifier : Statementω
If Statement

IfStatementfull ⇒
   if ParenthesizedExpression Statementfull
|  if ParenthesizedExpression StatementnoShortIf else Statementfull
IfStatementnoShortIf ⇒ if ParenthesizedExpression StatementnoShortIf else StatementnoShortIf
Switch Statement

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
Do-While Statement

DoStatement ⇒ do Statementfull while ParenthesizedExpression
While Statement

WhileStatementω ⇒ while ParenthesizedExpression Statementω
For Statements

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
With Statement

WithStatementω ⇒ with ParenthesizedExpression Statementω
Continue and Break Statements

ContinueStatement ⇒ continue OptionalLabel
BreakStatement ⇒ break OptionalLabel
OptionalLabel ⇒
   «empty»
|  Identifier
Return Statement

ReturnStatement ⇒ return OptionalExpression
Throw Statement

ThrowStatement ⇒ throw Expressionnormal,allowIn
Try Statement

TryStatement ⇒
   try Block CatchClauses
|  try Block FinallyClause
|  try Block CatchClauses FinallyClause
CatchClauses ⇒
   CatchClause
|  CatchClauses CatchClause
CatchClause ⇒ catch ( Identifier ) Block
FinallyClause ⇒ finally Block
Function Definition

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
Programs

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
Waldemar Horwat
Last modified Monday, May 3, 1999
up
*)
