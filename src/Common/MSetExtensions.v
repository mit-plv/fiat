Require Export Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetProperties
        Coq.MSets.MSetFacts.
Require Import Fiat.Common.Instances.

Local Coercion is_true : bool >-> Sortclass.

Module MSetExtensionsOn (E: DecidableType) (Import M: WSetsOn E).
  Module Export BasicFacts := WFactsOn E M.
  Module Export BasicProperties := WPropertiesOn E M.

  Definition of_list (ls : list E.t) : t
    := List.fold_right
         add
         empty
         ls.

  Global Instance equal_Equivalence : Equivalence equal.
  Proof.
    setoid_rewrite <- equal_iff; exact _.
  Qed.
End MSetExtensionsOn.

Module MSetExtensions (M: Sets) := MSetExtensionsOn M.E M.
