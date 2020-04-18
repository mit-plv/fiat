Require Import Bedrock.Platform.Thread.
Export Thread.

Module Type S.
  Parameter globalSched : W.
End S.

Module Make(M : S).
Import M.

Module M'.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv (_ : files) : HProp := Emp.
End M'.

Ltac unf := unfold M'.globalInv in *.

Module T := Thread.Make(M').

Import T.
Export T.

Ltac sep := T.sep unf.
Ltac sep_auto := sep auto_ext.

End Make.
