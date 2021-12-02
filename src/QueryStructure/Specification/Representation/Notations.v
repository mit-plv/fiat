Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Global Set Asymmetric Patterns.

Reserved Notation "t ! r"
         (no associativity, at level 2,
          format "t ! r").

Reserved Notation "< col1 , .. , coln >"
         (at level 0, col1, coln at level 60,
          format "< '[v  ' col1 ,  .. ,  coln ']' >").

(*Reserved Notation "tup '!!' attr '<-' v " (no associativity, at level 2,
                                          format "tup '!!' attr  '<-'  v").*)
Reserved Notation "tup ○ attrs"
         (at level 79, no associativity).
Reserved Notation "x !! attr / f"
         (at level 80, attr at level 0, no associativity).

Reserved Notation "attr ::= v"
  (at level 80, no associativity).

Reserved Notation "ro ≃ rn"  (at level 70).

Reserved Notation "'attributes' attrlist1 'depend' 'on' attrlist2 "
         (at level 50).

Reserved Notation "'attribute' attr 'for' rel1 'references' rel2 "
         (at level 50).

Reserved Notation "'relation' name 'has' sch"
  (at level 0, name at level 8).

Reserved Notation "'schema' headings"
  (at level 0, headings at level 0).

Reserved Notation "'schema' headings 'where' constraints"
         (at level 0, headings at level 0, constraints at level 50).

Reserved Notation "'schema' headings 'where' aconstraints 'and' tupconstraints"
         (at level 0, headings at level 0,
          aconstraints at level 50,
          tupconstraints at level 50).

Reserved Notation "'Query' 'Structure' 'Schema' relList "
         (at level 0).

Reserved Notation "'Query' 'Structure' 'Schema' relList 'enforcing' constraints"
         (at level 0, constraints at level 50).

Reserved Notation "( x 'in' r '!' Ridx ) bod"
         (right associativity, at level 0, r at level 0,
          format "( x  'in'  r '!' Ridx ) '//' bod ").

Reserved Notation "'Return' t"
         (right associativity, at level 3,
          format "'Return'  t" ).

Reserved Notation "'Where' p bod"
         (right associativity, at level 3, p at level 3,
          format "'Where'  p '//' bod " ).

Reserved Notation "'For' bod"
         (right associativity, at level 3,
          format "'For'  '[v' bod ']'").

Declare Scope Attribute_scope.
Delimit Scope Attribute_scope with Attribute.
Declare Scope Heading_scope.
Delimit Scope Heading_scope with Heading.
Declare Scope Component_scope.
Delimit Scope Component_scope with Component.
Declare Scope Tuple_scope.
Delimit Scope Tuple_scope with Tuple.
Declare Scope Relation_scope.
Delimit Scope Relation_scope with Relation.
Declare Scope SchemaConstraints_scope.
Delimit Scope SchemaConstraints_scope with SchemaConstraints.
Declare Scope Schema_scope.
Delimit Scope Schema_scope with Schema.
Declare Scope NamedSchema_scope.
Delimit Scope NamedSchema_scope with NamedSchema.
Declare Scope QSSchema_scope.
Delimit Scope QSSchema_scope with QSSchema.
Declare Scope QSSchemaConstraints_scope.
Delimit Scope QSSchemaConstraints_scope with QSSchemaConstraints.
Declare Scope QuerySpec_scope.
Delimit Scope QuerySpec_scope with QuerySpec.
Declare Scope QueryImpl_scope.
Delimit Scope QueryImpl_scope with QueryImpl.
Declare Scope QueryStructure_scope.
Delimit Scope QueryStructure_scope with QueryStructure.
Declare Scope QueryStructureParsing_scope.
Delimit Scope QueryStructureParsing_scope with QueryStructureParsing.
Declare Scope queryDefParsing_scope.
Delimit Scope queryDefParsing_scope with queryDefParsing.
Declare Scope queryDef_scope.
Delimit Scope queryDef_scope with queryDef.
Declare Scope updateDefParsing_scope.
Delimit Scope updateDefParsing_scope with updateDefParsing.
Declare Scope updateDef_scope.
Delimit Scope updateDef_scope with updateDef.
Declare Scope Update_scope.
Delimit Scope Update_scope with Update.
