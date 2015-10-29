Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.DeallocSCA.

Ltac compile_dealloc key cmp :=
  debug "Deallocating head binding" key;
  match cmp with
  | _ => apply CompileDeallocSCA; [ solve [eauto with dealloc_db] | ]
  | ret (@ADT _ ?x) => fail
  end.

Hint Resolve AlwaysComputesToSCA_ret_SCA : dealloc_db.
Hint Resolve AlwaysComputesToSCA_WrapComp_W : dealloc_db.
