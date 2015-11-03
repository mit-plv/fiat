Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.DeallocSCA.

Ltac compile_dealloc key cmp :=
  debug "Deallocating head binding" key;
  apply CompileDeallocSCA.

Hint Resolve AlwaysComputesToSCA_ret_SCA : dealloc_db. (* FIXME remove *)

