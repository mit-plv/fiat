Reserved Infix ":"
         (no associativity, at level 60).

Reserved Notation "< col1 , .. , coln >"
         (at level 0, col1, coln at level 60,
          format "< '[v  ' col1 ,  .. ,  coln ']' >").

Reserved Notation "'attributes' attrlist1 'depend' 'on' attrlist2 "
         (at level 50).

Reserved Notation "'attribute' attr 'of' rel1 'references' rel2 "
         (at level 50).

Reserved Notation "'relation' name 'has' sch"
  (at level 0, name at level 8, schema at level 0).

Reserved Notation "'schema' headings"
  (at level 0, headings at level 0, constraints at level 50).

Reserved Notation "'schema' headings 'where' constraints"
  (at level 0, headings at level 0, constraints at level 50).

Reserved Notation "'query' 'structure' relList 'enforcing' constraints"
         (at level 0, constraints at level 50).

Reserved Notation "'query' 'structure' relList "
         (at level 0).

Delimit Scope Attribute_scope with Attribute.
Delimit Scope Heading_scope with Heading.
Delimit Scope Component_scope with Component.
Delimit Scope Tuple_scope with Tuple.
Delimit Scope Relation_scope with Relation.
Delimit Scope SchemaConstraints_scope with SchemaConstraints.
Delimit Scope Schema_scope with Schema.
Delimit Scope NamedSchema_scope with NamedSchema.
Delimit Scope QSSchema_scope with QSSchema.
Delimit Scope QSSchemaConstraints_scope with QSSchemaConstraints.
