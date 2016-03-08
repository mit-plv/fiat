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

Section IncludedInAClauses.

  Context {X : Type}
          (X_eq : X -> X -> Prop)
          {X_eq_dec : forall x x', {X_eq x x'} + {~ X_eq x x'}}
          {X_equiv : Equivalence X_eq}.

  Definition IncludedInA := inclA X_eq.

  Fixpoint IncludedInA_dec (l l' : list X)
  : {IncludedInA l l'} + {~ IncludedInA l l'}.
  refine (match l with
            | nil => left _
            | e :: l =>
              if InA_dec X_eq_dec e l' then
                if IncludedInA_dec l l' then
                  left _
                else right _
              else right _
          end); unfold IncludedInA, inclA in *; intros.
  - inversion H.
  - inversion H; subst; eauto.
    rewrite H1; eauto.
  - unfold not; intros.
    let _H0 := match goal with _H0 : ~ _ |- _ => constr:(_H0) end in
    apply _H0; intros.
    eapply H; econstructor 2; eauto.
  - unfold not; intros.
    let _H := match goal with _H0 : ~ _ |- _ => constr:(_H0) end in
    eapply _H.
    apply H; econstructor; eauto.
    reflexivity.
  Defined.

  Global Instance DecideableEnsemble_IncludedInA st :
    DecideableEnsemble (IncludedInA st) :=
    {| dec a := ?[IncludedInA_dec st a] |}.
  Proof.
    intros; destruct (IncludedInA_dec st a); intuition eauto.
    discriminate.
  Defined.

  Global Instance DecideableEnsemble_IncludedInA_f
         (A : Type)
         (f : A -> list X)
         b :
    DecideableEnsemble (fun a => IncludedInA b (f a) ) :=
    {| dec a := ?[IncludedInA_dec b (f a)]|}.
  Proof.
    intros; destruct (IncludedInA_dec b (f a)); intuition eauto.
    discriminate.
  Defined.

End IncludedInAClauses.

Section IncludedInClauses.

  Context {X : Type}
          {X_eq : Query_eq X}.

  Definition IncludedIn := IncludedInA (@eq X).

  Definition IncludedIn_dec (l l' : list X)
    : {IncludedIn l l'} + {~ IncludedIn l l'} :=
    IncludedInA_dec (X_eq_dec := A_eq_dec) l l'.

  Global Instance DecideableEnsemble_IncludedIn st :
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

End IncludedInClauses.
