Require Import
        Coq.Arith.Peano_dec
        Coq.Structures.OrderedTypeEx
        ADTSynthesis.Common
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.String_as_OT
        ADTSynthesis.Common.List.ListFacts
        ADTSynthesis.Common.List.FlattenList
        ADTSynthesis.Common.SetEqProperties
        ADTSynthesis.Common.FMapExtensions
        ADTSynthesis.Common.List.PermutationFacts
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations.

Section IncludesClauses.

  Context {X : Type}
          {X_eq_dec : Query_eq X}.

  Definition IncludedIn := inclA (@eq X).

  Fixpoint IncludedIn_dec (l l' : list X)
  : {IncludedIn l l'} + {~ IncludedIn l l'}.
  refine (match l with
            | nil => left _
            | e :: l =>
              if InA_dec A_eq_dec e l' then
                if IncludedIn_dec l l' then
                  left _
                else right _
              else right _
          end); unfold IncludedIn, inclA in *; intros.
  - inversion H.
  - inversion H; subst; eauto; rewrite H1; eauto.
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
         (f : A -> list X)
         b :
    DecideableEnsemble (fun a => IncludedIn b (f a) ) :=
    {| dec a := ?[IncludedIn_dec b (f a)]|}.
  Proof.
    intros; destruct (IncludedIn_dec b (f a)); intuition eauto.
    discriminate.
  Defined.

End IncludesClauses.
