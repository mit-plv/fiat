Reserved Notation "x >>= y" (at level 42, right associativity).
(*Reserved Notation "x <- y ; z" (at level 42, right associativity).
Reserved Notation "x ;; z" (at level 42, right associativity).*)
Reserved Infix "↝" (at level 70).
Reserved Notation "⟦ x 'in' xs | P ⟧" (at level 70).

Reserved Notation "x <- y ; z"
         (at level 81, right associativity,
          format "'[v' x  <-  y ; '/' z ']'").

Reserved Notation "`( a , b ) <- c ; k"
         (at level 81, right associativity,
          format "'[v' `( a ,  b )  <-  c ; '/' k ']'").

Reserved Notation "`( a , b , c ) <- d ; k"
         (at level 81, right associativity,
          format "'[v' `( a ,  b ,  c )  <-  d ; '/' k ']'").

Delimit Scope comp_scope with comp.
