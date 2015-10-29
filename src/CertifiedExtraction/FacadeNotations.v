Require Import
        Bedrock.Platform.Facade.Facade
        Bedrock.Platform.Facade.DFacade
        Bedrock.Platform.Cito.StringMap
        Bedrock.Platform.Cito.SyntaxExpr
        Bedrock.Memory.
Require Import Coq.Strings.String.

Notation "A ; B" := (Seq A B) (at level 201,
                               B at level 201,
                               left associativity,
                               format "'[v' A ';' '/' B ']'") : facade_scope.

Delimit Scope facade_scope with facade.

Definition DummyArgument (s: string) := s.
Hint Unfold DummyArgument : MapUtils_unfold_db.

Notation "x <- y" := (Assign x y) (at level 90) : facade_scope.
Notation "y <- f . g ()" := (Call y (f, g) nil)
                             (at level 90, no associativity, format "y  '<-'  f '.' g '()'") : facade_scope.
Notation "y <- f . g ( x1 , .. , xn )" := (Call y (f, g) (cons x1 .. (cons xn nil) ..))
                                       (at level 90, no associativity, format "y  '<-'  f '.' g '(' x1 ','  .. ','  xn ')'") : facade_scope.
Notation "'call' f . g ()" := (Call (DummyArgument _) (f, g) nil)
                             (at level 90, no associativity, format "call  f '.' g '()'") : facade_scope.
Notation "'call' f . g ( x1 , .. , xn )" := (Call (DummyArgument _) (f, g) (cons x1 .. (cons xn nil) ..))
                                              (at level 90, no associativity, format "call  f '.' g '(' x1 ','  .. ','  xn ')'") : facade_scope.

Notation "A < B" := (TestE IL.Lt A B) : facade_scope.
Notation "A <= B" := (TestE IL.Le A B) : facade_scope.
Notation "A <> B" := (TestE IL.Ne A B) : facade_scope.
Notation "A = B" := (TestE IL.Eq A B) : facade_scope.
Notation "! x" := (x = 0)%facade (at level 70, no associativity).

Notation "A * B" := (Binop IL.Times A B) : facade_scope.
Notation "A + B" := (Binop IL.Plus A B) : facade_scope.
Notation "A - B" := (Binop IL.Minus A B) : facade_scope.

Notation "'__'" := (Skip) : facade_scope.

Notation "'While' A B" := (While A B)
                            (at level 200,
                             A at level 0,
                             B at level 1000,
                             format "'[v    ' 'While'  A '/' B ']'")
                          : facade_scope.

Notation "'If' a 'Then' b 'Else' c 'EndIf'" := (DFacade.If a b c)
                                          (at level 200,
                                           a at level 1000,
                                           b at level 1000,
                                           c at level 1000,
                                          format "'[v' '[v  ' 'If'  a  'Then' '/' b ']' '/' '[v  ' 'Else' '/' c ']' '/' 'EndIf' ']'")
                                       : facade_scope.