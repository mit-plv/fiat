Reserved Notation "x >>= y" (at level 42, right associativity).
(*Reserved Notation "x <- y ; z" (at level 42, right associativity).
Reserved Notation "x ;; z" (at level 42, right associativity).*)
Reserved Notation "'call' f 'from' funcs [[ x ]]" (at level 35).
Reserved Notation "'call' f [[ x ]]" (at level 35).
Reserved Infix "↝" (at level 70).

Reserved Notation "id : 'rep' × dom → cod" (at level 60, format "id  :  'rep'  ×  dom  →  cod" ).
Reserved Notation "id : 'rep' × dom → 'rep'" (at level 60, format "id  :  'rep'  ×  dom  →  'rep'" ).

Delimit Scope comp_scope with comp.
Delimit Scope long_comp_scope with long_comp.
Delimit Scope bundled_comp_scope with bundled_comp.
