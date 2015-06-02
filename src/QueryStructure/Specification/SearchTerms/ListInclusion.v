Require Import
        Coq.Arith.Peano_dec
        Coq.Structures.OrderedTypeEx
        Coq.Lists.SetoidList
        Fiat.Common
        Fiat.Common.DecideableEnsembles
        Fiat.Common.String_as_OT
        Fiat.Common.List.ListFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.SetEqProperties
        Fiat.Common.FMapExtensions
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations.

Module IncludesClauses (X : DecidableType).

  Definition IncludedIn := inclA X.eq.

  Fixpoint IncludedIn_dec (l l' : list X.t)
  : {IncludedIn l l'} + {~ IncludedIn l l'}.
  refine (match l with
            | nil => left _
            | e :: l =>
              if InA_dec X.eq_dec e l' then
                if IncludedIn_dec l l' then
                  left _
                else right _
              else right _
          end); unfold IncludedIn, inclA in *; intros.
  - inversion H.
  - inversion H; subst; eauto.
    eapply InA_compat; eauto.
    econstructor.
    + intros x'; eapply X.eq_refl.
    + intros x' x''; eapply X.eq_sym.
    + intros x' x'' x'''; eapply X.eq_trans.
    + unfold equivlistA; intros; intuition.
  - unfold not; intros; apply _H0; intros.
    eapply H; econstructor 2; eauto.
  - unfold not; intros; eapply _H.
    apply H; econstructor; eauto.
  Defined.

  Instance DecideableEnsemble_IncludedIn st :
    DecideableEnsemble (IncludedIn st) :=
    {| dec a := ?[IncludedIn_dec st a] |}.
  Proof.
    intros; destruct (IncludedIn_dec st a); intuition eauto.
    discriminate.
  Defined.

  Global Instance DecideableEnsemble_IncludedIn_f
         (A : Type)
         (f : A -> list X.t)
         b :
    DecideableEnsemble (fun a => IncludedIn b (f a) ) :=
    {| dec a := ?[IncludedIn_dec b (f a)]|}.
  Proof.
    intros; destruct (IncludedIn_dec b (f a)); intuition eauto.
    discriminate.
  Defined.

End IncludesClauses.
