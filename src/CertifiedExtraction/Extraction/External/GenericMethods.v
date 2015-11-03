Require Import
        Coq.Lists.List
        CertifiedExtraction.Extraction.External.Core.

Definition FacadeImplementationWW av (fWW: W -> W) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x, args = (wrap x) :: nil;
      PostCond := fun args ret => exists x, args = (wrap x, None) :: nil /\ ret = wrap (fWW x)
    |}; spec_t.
Defined.
