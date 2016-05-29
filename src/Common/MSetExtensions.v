Require Export Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetProperties
        Coq.MSets.MSetFacts.

Module MSetExtensionsOn (E: DecidableType) (Import M: WSetsOn E).
  Module Export BasicFacts := WFactsOn E M.
  Module Export BasicProperties := WPropertiesOn E M.

  Definition of_list (ls : list E.t) : t
    := List.fold_right
         add
         empty
         ls.
End MSetExtensionsOn.

Module MSetExtensions (M: Sets) := MSetExtensionsOn M.E M.
