Require Import Fiat.QueryStructure.Specification.Representation.QueryStructureNotations.

Open Scope list.

Section PrefixClauses.
  Context {X : Type}
          {X_eq_dec : Query_eq X}.

  Definition IsPrefix (p s : list X) : Prop := exists e, p ++ e = s.

  Fixpoint IsPrefix_dec (p s : list X) : {IsPrefix p s} + {~ IsPrefix p s}.
  refine (match p, s with
            | nil, _ => left _
            | p' :: ps, s' :: ss =>
              if A_eq_dec p' s' then
                if IsPrefix_dec ps ss then
                  left _
                else
                  right _
              else
                right _
            | _, _ => right _
          end); intuition; [
    eexists; intuition |
    inject H; apply app_eq_nil in H0; destruct H0; inversion H |
    destruct _H0; eexists; simpl; subst |
    apply _H0; inject H; inversion H0; eexists |
    inject H; simpl in H0; inversion H0 ]; eauto.
  Defined.

  Ltac prefix_crush := intros; find_if_inside; intuition eauto; discriminate.

  Instance DecideableEnsemble_HasPrefix st :
    DecideableEnsemble (IsPrefix st) :=
    {| dec a := ?[IsPrefix_dec st a] |}. prefix_crush. Defined.

  Global Instance DecideableEnsemble_HasPrefix_f
         (A : Type)
         (f : A -> list X)
         b :
    DecideableEnsemble (fun a => IsPrefix b (f a)) :=
    {| dec a := ?[IsPrefix_dec b (f a)] |}. prefix_crush. Defined.

  Instance DecideableEnsemble_FindPrefix st :
    DecideableEnsemble (fun a => IsPrefix a st) :=
    {| dec a := ?[IsPrefix_dec a st] |}. prefix_crush. Defined.

  Global Instance DecideableEnsemble_FindPrefix_f
         (A : Type)
         (f : A -> list X)
         b :
    DecideableEnsemble (fun a => IsPrefix (f a) b) :=
    {| dec a := ?[IsPrefix_dec (f a) b] |}. prefix_crush. Defined.
End PrefixClauses.

Section SuffixClauses.
  Context {X : Type}
          {X_eq_dec : Query_eq X}.

  Definition IsSuffix (p s : list X) : Prop := IsPrefix s p.

  Definition IsSuffix_dec (p s : list X) : {IsSuffix p s} + {~ IsSuffix p s} := IsPrefix_dec s p.

  Ltac suffix_crush := intros; find_if_inside; intuition eauto;
                       unfold IsSuffix in *; discriminate.

  Instance DecideableEnsemble_HasSuffix st :
    DecideableEnsemble (IsSuffix st) :=
    {| dec a := ?[IsSuffix_dec st a] |}. suffix_crush. Defined.
  
  Global Instance DecideableEnsemble_HasSuffix_f
         (A : Type)
         (f : A -> list X)
         b 
    : DecideableEnsemble (fun a => IsSuffix b (f a)) :=
    {| dec a := ?[IsSuffix_dec b (f a)] |}. suffix_crush. Defined.

  Instance DecideableEnsemble_FindSuffix st :
    DecideableEnsemble (fun a => IsSuffix a st) :=
    {| dec a := ?[IsSuffix_dec a st] |}. suffix_crush. Defined.

  Global Instance DecideableEnsemble_FindSuffix_f
         (A : Type)
         (f : A -> list X)
         b :
    DecideableEnsemble (fun a => IsSuffix (f a) b) :=
    {| dec a := ?[IsSuffix_dec (f a) b] |}. suffix_crush. Defined.
End SuffixClauses.
