Require Import
        Coq.Lists.SetoidList
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations.

Open Scope list_scope.

Section PrefixClauses.
  Context {X : Type}
          {X_Qeq : Query_eq X}.

  Definition Prefix (X_eq : X -> X -> Prop)
             (s s' : list X) :=
    exists s'', eqlistA X_eq (s ++ s'') s'.

  Definition IsPrefix (x st : list X) : Prop := @Prefix eq x st.

  Fixpoint Prefix_dec
           {X_eq : X -> X -> Prop}
           (X_eq_dec : forall x x', {X_eq x x'} + {~ X_eq x x'})
           {X_refl : Reflexive X_eq}
           (p s : list X) : {Prefix X_eq p s} + {~ Prefix X_eq p s}.
  refine (match p, s with
            | nil, _ => left _
            | p' :: ps, s' :: ss =>
              if X_eq_dec p' s' then
                if Prefix_dec X_eq X_eq_dec _ ps ss then
                  left _
                else
                  right _
              else
                right _
            | _, _ => right _
          end);  intuition; [
    eexists; intuition |
    inject H |
    let _H0 := match goal with H : ?R _ _ |- _ => constr:(H) end in
    destruct _H0; eexists; simpl; subst |
    let _H0 := match goal with H : ?R _ _ -> False |- _ => constr:(H) end in
    apply _H0; inject H; inversion H0; eexists |
    inject H; simpl in H0; inversion H0 ]; eauto.
  inversion H0.
  Defined.

  Definition IsPrefix_dec
    : forall (p s : list X), {IsPrefix p s} + {~ IsPrefix p s}
  := @Prefix_dec _ A_eq_dec (fun a => eq_refl a).
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
