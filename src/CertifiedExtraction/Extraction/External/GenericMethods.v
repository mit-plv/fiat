Require Import
        Coq.Lists.List
        CertifiedExtraction.Extraction.External.Core.

Definition FacadeImplementationWW av (fWW: W -> W) : AxiomaticSpec av.
  refine {|
      PreCond := fun args => exists x, args = (SCA av x) :: nil;
      PostCond := fun args ret => exists x, args = (SCA av x, None) :: nil /\ ret = SCA av (fWW x)
    |}; spec_t.
Defined.
