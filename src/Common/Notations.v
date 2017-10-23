Reserved Notation "# x" (at level 70).
Reserved Infix "@" (left associativity, at level 77).
Reserved Notation "\ x , e" (at level 78).
Reserved Notation "\ ! , e" (at level 78).
Reserved Infix "⊓" (at level 80).
Reserved Infix "⊔" (at level 80).
Reserved Infix "##" (at level 60, right associativity).
Reserved Infix "=s" (at level 70, no associativity).
Reserved Infix "=b" (at level 70, no associativity).
Reserved Notation "s ~= [ ch ]" (at level 70, no associativity).
Reserved Infix "=?" (at level 70).
Reserved Infix "<=?" (at level 70).
Reserved Infix "<?" (at level 70).
Reserved Infix "?=" (at level 70).
Reserved Notation "'⊤'".
Reserved Notation "'⊥'".
Reserved Notation "p <{< act >}>" (at level 30).
Reserved Notation "'plet' x := y 'in' z"
         (at level 200, z at level 200, format "'plet'  x  :=  y  'in' '//' z").
Reserved Notation "'nlet' x := A 'in' b"
         (at level 200, b at level 200, x at level 99, format "'nlet'  x  :=  A  'in' '//' b").
Reserved Notation "'nlet' x : tx := A 'in' b"
         (at level 200, b at level 200, x at level 99, format "'nlet'  x  :  tx  :=  A  'in' '//' b").
Reserved Notation "'slet' x .. y := A 'in' b"
         (at level 200, x binder, y binder, b at level 200, format "'slet'  x .. y  :=  A  'in' '//' b").
Reserved Notation "'llet' x := A 'in' b"
         (at level 200, b at level 200, format "'llet'  x  :=  A  'in' '//' b").
Reserved Notation "'mlet' x := A 'in' b"
         (at level 200, b at level 200, format "'mlet'  x  :=  A  'in' '//' b").
(* Note that making [Let] a keyword breaks the vernacular [Let] in Coq 8.4 *)
Reserved Notation "'dlet_nd' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet_nd'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'dlet' x .. y := v 'in' f"
         (at level 200, x binder, y binder, f at level 200, format "'dlet'  x .. y  :=  v  'in' '//' f").
Reserved Notation "'pflet' x , pf := y 'in' f"
         (at level 200, f at level 200, format "'pflet'  x ,  pf  :=  y  'in' '//' f").
