Require Import Fiat.Common.FMapExtensions.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.LogicMorphisms.
Require Import Fiat.Common.

Unset Implicit Arguments.

Module FMapExtensionsLiftRelationInstances_fun (E: DecidableType) (Import M: WSfun E).
  Module BasicExtensions := FMapExtensions_fun E M.
  Include BasicExtensions.

    Section rel.
    Context {P} {Q : P -> Prop} {and True'}
            (HTrue' : Q True')
            (Hand : forall x y, Q (and x y) <-> Q x /\ Q y)
            (iffP : P -> P -> Prop)
            (iffP_iff : forall x y, iffP x y <-> (Q x <-> Q y))
            {A} {default : A}.

    Local Coercion Q : P >-> Sortclass.

    Local Notation lift R := (@lift_relation_gen_hetero A A P and True' R default default).

    Local Ltac t :=
      repeat ((rewrite lift_relation_gen_hetero_iff by auto) || intro);
      repeat match goal with
             | [ H : forall k : key, _, k' : key |- _ ] => specialize (H k')
             | [ |- ?R (forall _, _) (forall _, _) ] => apply pull_forall_iffR; intro
             end;
      try solve [ break_match; break_match_hyps; eauto ].

    Section with_R.
      Context {R : A -> A -> P}.
      Local Notation R' := (fun x y => Q (R x y)).
      Local Notation liftR := (lift R).

      Global Instance lift_relation_gen_hetero_Reflexive {HR : @Reflexive A R'} : Reflexive liftR | 5.
      Proof. t. Qed.
      Global Instance lift_relation_gen_hetero_Symmetric {HR : @Symmetric A R'} : Symmetric liftR | 5.
      Proof. t. Qed.
      Global Instance lift_relation_gen_hetero_Transitive {HR : @Transitive A R'} : Transitive liftR | 5.
      Proof. t. Qed.

      Global Instance lift_relation_gen_hetero_Proper_Equal_gen
             {iffR}
             {iffR_Proper : Proper (iff ==> iff ==> flip impl) iffR}
             {iffR_Reflexive : Reflexive iffR}
             {iffR_pull : pull_forall_able iffR}
        : Proper (@Equal A ==> @Equal A ==> iffR) liftR | 2.
      Proof.
        t; setoid_subst_rel (@Equal A); reflexivity.
      Qed.

      Global Instance lift_relation_gen_hetero_Proper_Equal
        : Proper (@Equal A ==> @Equal A ==> iff) liftR | 2 := _.
      Global Instance lift_relation_gen_hetero_Proper_Equal_impl
        : Proper (@Equal A ==> @Equal A ==> impl) liftR | 2 := _.
      Global Instance lift_relation_gen_hetero_Proper_Equal_flip_impl
        : Proper (@Equal A ==> @Equal A ==> flip impl) liftR | 2 := _.

      Global Instance lift_relation_gen_hetero_Proper_Equal_genb
        : Proper (@Equal A ==> @Equal A ==> iffP) (lift R) | 2.
      Proof.
        pose proof lift_relation_gen_hetero_Proper_Equal as H.
        repeat let x := fresh in intro x; specialize (H x).
        apply iffP_iff, H.
      Qed.

      Section lift_relation_gen_hetero_homo_Proper_Proper_subrelation.
        Context {R1 R2 : A -> A -> P}
                {R1_Reflexive : Reflexive R1}
                {R2_Reflexive : Reflexive R2}
                {R1_subrelation : subrelation R1 R}
                {R2_subrelation : subrelation R2 R}.

        Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffR
               {iffR}
               {iffR_Proper : Proper (iff ==> iff ==> flip impl) iffR}
               {iffR_pull : pull_forall_able iffR}
               {R_Proper : Proper (R1 ==> R2 ==> iffR) R}
          : Proper (lift R1 ==> lift R2 ==> iffR) (lift R) | 2.
        Proof.
          pose proof (R1_Reflexive default).
          pose proof (R2_Reflexive default).
          t; compute in * |- ; split_and; break_match; try split;
            try solve [ eauto 3
                      | eapply iffR_Proper; [ | | eauto ]; [ | eauto ]; eauto ].
        Qed.

        Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation
               {R_Proper : Proper (R1 ==> R2 ==> iff) R'}
          : Proper (lift R1 ==> lift R2 ==> iff) (lift R) | 2 := _.
        Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_impl
               {R_Proper : Proper (R1 ==> R2 ==> impl) R'}
          : Proper (lift R1 ==> lift R2 ==> impl) (lift R) | 2 := _.
        Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_flip_impl
               {R_Proper : Proper (R1 ==> R2 ==> flip impl) R'}
          : Proper (lift R1 ==> lift R2 ==> flip impl) (lift R) | 2 := _.
        Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffP
               {R_Proper : Proper (R1 ==> R2 ==> iffP) R}
          : Proper (lift R1 ==> lift R2 ==> iffP) (lift R) | 2.
        Proof.
          pose proof @lift_relation_gen_hetero_homo_Proper_Proper_subrelation as H.
          repeat let x := fresh in intro x; specialize (fun y => H y x).
          apply iffP_iff, H.
          repeat let x := fresh in intro x; specialize (R_Proper x).
          apply iffP_iff, R_Proper.
        Qed.
      End lift_relation_gen_hetero_homo_Proper_Proper_subrelation.

      Global Instance lift_relation_gen_hetero_Proper_Proper_iffR
             {iffR}
             {iffR_Proper : Proper (iff ==> iff ==> flip impl) iffR}
             {iffR_pull : pull_forall_able iffR}
             {R_Proper : Proper (R' ==> R' ==> iffR) R}
             {R_Reflexive : Reflexive R'}
             {R_Proper : Proper (R' ==> R' ==> iffR) R'}
        : Proper (liftR ==> liftR ==> iffR) liftR | 2 := _.

      Global Instance lift_relation_gen_hetero_Proper_Proper
             {R_Reflexive : Reflexive R'}
             {R_Proper : Proper (R' ==> R' ==> iff) R'}
        : Proper (liftR ==> liftR ==> iff) liftR | 2 := _.

      Global Instance lift_relation_gen_hetero_Proper_Proper_impl
             {R_Reflexive : Reflexive R'}
             {R_Proper : Proper (R' ==> R' ==> impl) R'}
        : Proper (liftR ==> liftR ==> impl) liftR | 2 := _.

      Global Instance lift_relation_gen_hetero_Proper_Proper_flip_impl
             {R_Reflexive : Reflexive R'}
             {R_Proper : Proper (R' ==> R' ==> flip impl) R'}
        : Proper (liftR ==> liftR ==> flip impl) liftR | 2 := _.

      Global Instance lift_relation_gen_hetero_Proper_Proper_iffP
             {R_Reflexive : Reflexive R'}
             {R_Proper : Proper (R' ==> R' ==> iffP) R}
        : Proper (liftR ==> liftR ==> iffP) (lift R) | 2.
      Proof.
        pose proof (@lift_relation_gen_hetero_Proper_Proper _) as H.
        repeat let x := fresh in intro x; specialize (fun y => H y x).
        apply iffP_iff, H.
        repeat let x := fresh in intro x; specialize (R_Proper x).
        apply iffP_iff, R_Proper.
      Qed.

      Global Instance lift_relation_gen_hetero_Equivalence
             {R_Equiv : @Equivalence A R'} : Equivalence liftR | 2.
      Proof.
        split; exact _.
      Qed.
    End with_R.

    Global Instance lift_relation_gen_hetero_Antisymmetric
           {R RE : A -> A -> P}
           (R' := fun x y => Q (R x y))
           (RE' := fun x y => Q (RE x y))
           {RE_Equivalence : @Equivalence A RE'}
           {AS : Antisymmetric A RE' R'}
    : Antisymmetric _ (lift RE) (lift R) | 2.
    Proof.
      t; compute in *; break_match; eauto.
    Qed.
  End rel.

  Section rel1.
    Section lift_relation_gen_hetero_Proper_Proper_subrelation_gen.
      Context {P1 P2 P} {Q1 : P1 -> Prop} {Q2 : P2 -> Prop} {Q : P -> Prop}
              {and1 True'1 and2 True'2 and True'}
              (HTrue'1 : Q1 True'1)
              (Hand1 : forall x y, Q1 (and1 x y) <-> Q1 x /\ Q1 y)
              (HTrue'2 : Q2 True'2)
              (Hand2 : forall x y, Q2 (and2 x y) <-> Q2 x /\ Q2 y)
              (HTrue' : Q True')
              (Hand : forall x y, Q (and x y) <-> Q x /\ Q y)
              {iffP}
              (HiffP : forall x y, iffP x y <-> (Q x <-> Q y))
              {A B} {R : A -> B -> P}
              {defaultA : A} {defaultB : B}
              (Rdefault : Q (R defaultA defaultB))
              {R1 : A -> A -> P1}
              {R2 : B -> B -> P2}.
      Local Coercion Q1 : P1 >-> Sortclass.
      Local Coercion Q2 : P2 >-> Sortclass.
      Local Coercion Q : P >-> Sortclass.
      Context {R1_Reflexive : Reflexive R1}
              {R2_Reflexive : Reflexive R2}.

      Local Ltac t' :=
        unfold pull_forall_able in *;
        repeat ((rewrite lift_relation_gen_hetero_iff by auto) || intro);
        repeat match goal with
               | [ H : forall k : key, _, k' : key |- _ ] => specialize (H k')
               | [ |- (forall _, _) <-> (forall _, _) ] => apply pull_forall_iff; intro
               | [ pull_forall_iff : (forall A P Q, (forall x, ?R (P x) (Q x)) -> ?R (forall y, P y) (forall z, Q z))
                   |- ?R (forall _, _) (forall _, _) ] => apply pull_forall_iff; intro
               end;
        compute in * |- ; split_and; break_match_hyps; break_match; try split.

      Local Ltac t := t'; eauto.

      Local Notation lift_relation_gen_hetero_Proper_Proper_subrelation_genT iffR
        := (Proper ((fun x y => Q1 (@lift_relation_gen_hetero A A P1 and1 True'1 R1 defaultA defaultA x y))
                      ==> (fun x y => Q2 (@lift_relation_gen_hetero B B P2 and2 True'2 R2 defaultB defaultB x y))
                      ==> iffR)
                   (@lift_relation_gen_hetero A B P and True' R defaultA defaultB)).
      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffR
             {iffR}
             {iffR_Proper : Proper (iff ==> iff ==> flip impl) iffR}
             {iffR_pull_forall : pull_forall_able iffR}
             {R_Proper : Proper (R1 ==> R2 ==> iffR) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelation_genT iffR | 2.
      Proof. clear dependent iffP; t'; eauto 3; solve [ eapply iffR_Proper; [ | | eauto ]; eauto | eauto ]. Qed.

      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_gen
             {R_Proper : Proper (R1 ==> R2 ==> iff) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelation_genT iff | 2 := _.

      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_gen_impl
             {R_Proper : Proper (R1 ==> R2 ==> impl) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelation_genT impl | 2 := _.

      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_gen_flip_impl
             {R_Proper : Proper (R1 ==> R2 ==> flip impl) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelation_genT (flip impl) | 2 := _.
      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffP
             {R_Proper : Proper (R1 ==> R2 ==> iffP) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelation_genT iffP | 2.
      Proof.
        pose proof @lift_relation_gen_hetero_Proper_Proper_subrelation_gen as H.
        repeat let x := fresh in intro x; specialize (fun y => H y x).
        apply HiffP, H.
        repeat let x := fresh in intro x; specialize (R_Proper x).
        apply HiffP, R_Proper.
      Qed.
    End lift_relation_gen_hetero_Proper_Proper_subrelation_gen.

    Section lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen.
      Context {P1 P2 P} {Q1 : P1 -> Prop} {Q2 : P2 -> Prop} {Q : P -> Prop}
              {and1 True'1 and2 True'2 and True'}
              (HTrue'1 : Q1 True'1)
              (Hand1 : forall x y, Q1 (and1 x y) <-> Q1 x /\ Q1 y)
              (HTrue'2 : Q2 True'2)
              (Hand2 : forall x y, Q2 (and2 x y) <-> Q2 x /\ Q2 y)
              (HTrue' : Q True')
              (Hand : forall x y, Q (and x y) <-> Q x /\ Q y)
              {iffP}
              (HiffP : forall x y, iffP x y <-> (Q x <-> Q y))
              {A} {R : A -> A -> P} {default : A}
              {R1 : A -> A -> P1}
              {R2 : A -> A -> P2}.
      Local Coercion Q1 : P1 >-> Sortclass.
      Local Coercion Q2 : P2 >-> Sortclass.
      Local Coercion Q : P >-> Sortclass.
      Context {R1_Reflexive : Reflexive R1}
              {R2_Reflexive : Reflexive R2}
              {R1_subrelation : subrelation R1 R}
              {R2_subrelation : subrelation R2 R}.

      Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_iffR
             {iffR}
             {iffR_Proper : Proper (iff ==> iff ==> flip impl) iffR}
             {iffR_pull_forall : pull_forall_able iffR}
             {R_Proper : Proper (R1 ==> R2 ==> iffR) R}
        : Proper ((@lift_relation_gen_hetero A A P1 and1 True'1 R1 default default)
                    ==> (@lift_relation_gen_hetero A A P2 and2 True'2 R2 default default)
                    ==> iffR)
                 (@lift_relation_gen_hetero A A P and True' R default default) | 2.
      Proof.
        apply lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffR; auto; apply R1_subrelation; reflexivity.
      Qed.

      Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen
             {R_Proper : Proper (R1 ==> R2 ==> iff) R}
        : Proper ((fun x y => Q1 (@lift_relation_gen_hetero A A P1 and1 True'1 R1 default default x y))
                    ==> (fun x y => Q2 (@lift_relation_gen_hetero A A P2 and2 True'2 R2 default default x y))
                    ==> iff)
                 (fun x y => Q (@lift_relation_gen_hetero A A P and True' R default default x y)) | 2
        := _.

      Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_impl
             {R_Proper : Proper (R1 ==> R2 ==> impl) R}
        : Proper ((fun x y => Q1 (@lift_relation_gen_hetero A A P1 and1 True'1 R1 default default x y))
                    ==> (fun x y => Q2 (@lift_relation_gen_hetero A A P2 and2 True'2 R2 default default x y))
                    ==> impl)
                 (fun x y => Q (@lift_relation_gen_hetero A A P and True' R default default x y)) | 2
        := _.

      Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_flip_impl
             {R_Proper : Proper (R1 ==> R2 ==> flip impl) R}
        : Proper ((fun x y => Q1 (@lift_relation_gen_hetero A A P1 and1 True'1 R1 default default x y))
                    ==> (fun x y => Q2 (@lift_relation_gen_hetero A A P2 and2 True'2 R2 default default x y))
                    ==> flip impl)
                 (fun x y => Q (@lift_relation_gen_hetero A A P and True' R default default x y)) | 2
        := _.
      Global Instance lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_iffP
             {R_Proper : Proper (R1 ==> R2 ==> iffP) R}
        : Proper ((@lift_relation_gen_hetero A A P1 and1 True'1 R1 default default)
                    ==> (@lift_relation_gen_hetero A A P2 and2 True'2 R2 default default)
                    ==> iffP)
                 (@lift_relation_gen_hetero A A P and True' R default default) | 2.
      Proof.
        eapply lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffP; eauto; apply R1_subrelation; reflexivity.
      Qed.
    End lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen.

    Section lift_relation_gen_hetero_Proper_Proper_subrelation.
      Context {P} {Q : P -> Prop} {and True' iffP}
              (HTrue' : Q True')
              (Hand : forall x y, Q (and x y) <-> Q x /\ Q y)
              (HiffP : forall x y, iffP x y <-> (Q x <-> Q y))
              {A B} {R : A -> B -> P}
              {defaultA : A} {defaultB : B}
              (Rdefault : Q (R defaultA defaultB))
              {R1 : A -> A -> P}
              {R2 : B -> B -> P}.
      Local Coercion Q : P >-> Sortclass.
      Context {R1_Reflexive : Reflexive R1}
              {R2_Reflexive : Reflexive R2}.
      Local Notation lift_relation_gen_hetero_Proper_Proper_subrelationT iffR
        := (Proper ((fun x y => Q (@lift_relation_gen_hetero A A P and True' R1 defaultA defaultA x y))
                      ==> (fun x y => Q (@lift_relation_gen_hetero B B P and True' R2 defaultB defaultB x y))
                      ==> iffR)
                   (@lift_relation_gen_hetero A B P and True' R defaultA defaultB)).
      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_iffR
             {iffR}
             {iffR_Proper : Proper (iff ==> iff ==> flip impl) iffR}
             {iffR_pull_forall : pull_forall_able iffR}
             {R_Proper : Proper (R1 ==> R2 ==> iffR) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelationT iffR | 2
        := lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffR
             HTrue' Hand HTrue' Hand HTrue' Hand Rdefault.
      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation
             {R_Proper : Proper (R1 ==> R2 ==> iff) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelationT iff | 2 := _.
      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_impl
             {R_Proper : Proper (R1 ==> R2 ==> impl) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelationT impl | 2 := _.
      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_flip_impl
             {R_Proper : Proper (R1 ==> R2 ==> flip impl) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelationT (flip impl) | 2 := _.
      Global Instance lift_relation_gen_hetero_Proper_Proper_subrelation_iffP
             {R_Proper : Proper (R1 ==> R2 ==> iffP) R}
        : lift_relation_gen_hetero_Proper_Proper_subrelationT iffP | 2
        := lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffP
             HTrue' Hand HTrue' Hand HTrue' Hand HiffP Rdefault.
    End lift_relation_gen_hetero_Proper_Proper_subrelation.
  End rel1.

  Module Type LiftRelationParams.
    Parameter P : Type.
    Parameter Q : P -> Prop.
    Parameter and : P -> P -> P.
    Parameter True : P.
    Parameter iffP : P -> P -> Prop.

    Coercion Q : P >-> Sortclass.

    Axiom HTrue : True.
    Axiom Hand : forall x y, and x y <-> (x /\ y).
    Axiom iffP_iff : forall x y, iffP x y <-> (x <-> y).
  End LiftRelationParams.

  Module LiftRelation (Params : LiftRelationParams).
    Import Params.

    Definition lift_relation_gen_hetero_Reflexive
      := @lift_relation_gen_hetero_Reflexive P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Symmetric
      := @lift_relation_gen_hetero_Symmetric P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Transitive
      := @lift_relation_gen_hetero_Transitive P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Equal_gen
      := @lift_relation_gen_hetero_Proper_Equal_gen P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Equal_genb
      := @lift_relation_gen_hetero_Proper_Equal_genb P Q and True HTrue Hand iffP iffP_iff.
    Definition lift_relation_gen_hetero_Proper_Equal
      := @lift_relation_gen_hetero_Proper_Equal P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Equal_impl
      := @lift_relation_gen_hetero_Proper_Equal_impl P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Equal_flip_impl
      := @lift_relation_gen_hetero_Proper_Equal_flip_impl P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffR
      := @lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffR P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation
      := @lift_relation_gen_hetero_homo_Proper_Proper_subrelation P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_impl
      := @lift_relation_gen_hetero_homo_Proper_Proper_subrelation_impl P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_flip_impl
      := @lift_relation_gen_hetero_homo_Proper_Proper_subrelation_flip_impl P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffP
      := @lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffP P Q and True HTrue Hand iffP iffP_iff.
    Definition lift_relation_gen_hetero_Proper_Proper_iffR
      := @lift_relation_gen_hetero_Proper_Proper_iffR P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Proper
      := @lift_relation_gen_hetero_Proper_Proper P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Proper_impl
      := @lift_relation_gen_hetero_Proper_Proper_impl P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Proper_flip_impl
      := @lift_relation_gen_hetero_Proper_Proper_flip_impl P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Proper_Proper_iffP
      := @lift_relation_gen_hetero_Proper_Proper_iffP P Q and True HTrue Hand iffP iffP_iff.
    Definition lift_relation_gen_hetero_Equivalence
      := @lift_relation_gen_hetero_Equivalence P Q and True HTrue Hand.
    Definition lift_relation_gen_hetero_Antisymmetric
      := @lift_relation_gen_hetero_Antisymmetric P Q and True HTrue Hand.
    Global Existing Instances
           lift_relation_gen_hetero_Reflexive
           lift_relation_gen_hetero_Symmetric
           lift_relation_gen_hetero_Transitive
           lift_relation_gen_hetero_Proper_Equal_gen
           lift_relation_gen_hetero_Proper_Equal_genb
           lift_relation_gen_hetero_Proper_Equal
           lift_relation_gen_hetero_Proper_Equal_impl
           lift_relation_gen_hetero_Proper_Equal_flip_impl
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffR
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_impl
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_flip_impl
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffP
           lift_relation_gen_hetero_Proper_Proper_iffR
           lift_relation_gen_hetero_Proper_Proper
           lift_relation_gen_hetero_Proper_Proper_impl
           lift_relation_gen_hetero_Proper_Proper_flip_impl
           lift_relation_gen_hetero_Equivalence
           lift_relation_gen_hetero_Antisymmetric
    | 5.
  End LiftRelation.

  Module LiftRelation3 (Params1 : LiftRelationParams) (Params2 : LiftRelationParams) (Params3 : LiftRelationParams).
    Local Notation inst lem
      := (lem
            Params1.P Params2.P Params3.P
            Params1.Q Params2.Q Params3.Q
            Params1.and Params1.True
            Params2.and Params2.True
            Params3.and Params3.True
            Params1.HTrue Params1.Hand
            Params2.HTrue Params2.Hand
            Params3.HTrue Params3.Hand).
    Local Notation instP lem
      := (inst lem Params3.iffP Params3.iffP_iff).
    Definition lift_relation_gen_hetero_Proper_Proper_subrelation_iffR
      := inst (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffR).
    Definition lift_relation_gen_hetero_Proper_Proper_subrelation
      := inst (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen).
    Definition lift_relation_gen_hetero_Proper_Proper_subrelation_impl
      := inst (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen_impl).
    Definition lift_relation_gen_hetero_Proper_Proper_subrelation_flip_impl
      := inst (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen_flip_impl).
    Definition lift_relation_gen_hetero_Proper_Proper_subrelation_iffP
      := instP (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen_iffP).
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffR
      := inst (@lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_iffR).
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation
      := inst (@lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen).
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_impl
      := inst (@lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_impl).
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_flip_impl
      := inst (@lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_flip_impl).
    Definition lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffP
      := inst (@lift_relation_gen_hetero_homo_Proper_Proper_subrelation_gen_iffP).
    Global Existing Instances
           lift_relation_gen_hetero_Proper_Proper_subrelation_iffR
           lift_relation_gen_hetero_Proper_Proper_subrelation
           lift_relation_gen_hetero_Proper_Proper_subrelation_impl
           lift_relation_gen_hetero_Proper_Proper_subrelation_flip_impl
           lift_relation_gen_hetero_Proper_Proper_subrelation_iffP
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffR
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_impl
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_flip_impl
           lift_relation_gen_hetero_homo_Proper_Proper_subrelation_iffP
    | 5.
  End LiftRelation3.

  Module LiftRelation2 (Params1 : LiftRelationParams) (Params2 : LiftRelationParams).
    Module Export P1 := LiftRelation Params1.
    Module Export P2 := LiftRelation Params2.
    Module Export P111 := LiftRelation3 Params1 Params1 Params1.
    Module Export P112 := LiftRelation3 Params1 Params1 Params2.
    Module Export P121 := LiftRelation3 Params1 Params2 Params1.
    Module Export P122 := LiftRelation3 Params1 Params2 Params2.
    Module Export P211 := LiftRelation3 Params2 Params1 Params1.
    Module Export P212 := LiftRelation3 Params2 Params1 Params2.
    Module Export P221 := LiftRelation3 Params2 Params2 Params1.
    Module Export P222 := LiftRelation3 Params2 Params2 Params2.
  End LiftRelation2.

  Module LiftRelationParamsProp <: LiftRelationParams.
    Definition P := Prop.
    Definition Q : P -> Prop := fun H => H.
    Definition and : P -> P -> P := and.
    Definition True : P := True.
    Definition iffP : P -> P -> Prop := iff.
    Definition HTrue : Q True := I.
    Definition Hand : forall x y, Q (and x y) <-> (Q x /\ Q y) := fun x y => reflexivity _.
    Definition iffP_iff : forall x y, iffP x y <-> (Q x <-> Q y) := fun x y => reflexivity _.
  End LiftRelationParamsProp.

  Module LiftRelationParamsBool <: LiftRelationParams.
    Definition P := bool.
    Definition Q : P -> Prop := is_true.
    Definition and : P -> P -> P := andb.
    Definition True : P := true.
    Definition iffP : P -> P -> Prop := eq.
    Definition HTrue : Q True := reflexivity _.
    Definition Hand : forall x y, Q (and x y) <-> (Q x /\ Q y) := andb_true_iff.
    Lemma iffP_iff : forall x y, iffP x y <-> (Q x <-> Q y).
    Proof.
      intros [] []; compute; intuition congruence.
    Qed.
  End LiftRelationParamsBool.

  Module Export LiftRelation2PropBool := LiftRelation2 LiftRelationParamsProp LiftRelationParamsBool.

  Global Instance lift_relation_hetero_Reflexive {A R} {HR : @Reflexive A R} {default}
    : Reflexive (lift_relation_hetero R default default) | 5 := _.
  Global Instance lift_relation_hetero_Symmetric {A R} {HR : @Symmetric A R} {default}
    : Symmetric (lift_relation_hetero R default default) | 5 := _.
  Global Instance lift_relation_hetero_Transitive {A R} {HR : @Transitive A R} {default}
    : Transitive (lift_relation_hetero R default default) | 5 := _.

  Global Instance lift_relation_Reflexive {A} {R : A -> A -> bool} {HR : @Reflexive A R} {default}
    : Reflexive (lift_relation R default) | 5 := _.
  Global Instance lift_relation_Symmetric {A} {R : A -> A -> bool} {HR : @Symmetric A R} {default}
    : Symmetric (lift_relation R default) | 5 := _.
  Global Instance lift_relation_Transitive {A} {R : A -> A -> bool} {HR : @Transitive A R} {default}
    : Transitive (lift_relation R default) | 5 := _.

  Global Instance lift_brelation_hetero_Reflexive {A} {R : A -> A -> bool} {HR : @Reflexive A R} {default}
    : Reflexive (lift_brelation_hetero R default default) | 5 := _.
  Global Instance lift_brelation_hetero_Symmetric {A} {R : A -> A -> bool} {HR : @Symmetric A R} {default}
    : Symmetric (lift_brelation_hetero R default default) | 5 := _.
  Global Instance lift_brelation_hetero_Transitive {A} {R : A -> A -> bool} {HR : @Transitive A R} {default}
    : Transitive (lift_brelation_hetero R default default) | 5 := _.

  Global Instance lift_brelation_Reflexive {A} {R : A -> A -> bool} {HR : @Reflexive A R} {default}
    : Reflexive (lift_brelation R default) | 5 := _.
  Global Instance lift_brelation_Symmetric {A} {R : A -> A -> bool} {HR : @Symmetric A R} {default}
    : Symmetric (lift_brelation R default) | 5 := _.
  Global Instance lift_brelation_Transitive {A} {R : A -> A -> bool} {HR : @Transitive A R} {default}
    : Transitive (lift_brelation R default) | 5 := _.

  Global Instance lift_relation_hetero_Proper_Equal {A R default}
    : Proper (@Equal A ==> @Equal A ==> iff) (@lift_relation_hetero A A R default default) | 2 := _.
  Global Instance lift_relation_Proper_Equal {A R default}
    : Proper (@Equal A ==> @Equal A ==> iff) (@lift_relation A R default) | 2 := _.

  Global Instance lift_brelation_hetero_Proper_Equal_iff {A R default}
    : Proper (@Equal A ==> @Equal A ==> iff) (@lift_brelation_hetero A A R default default) | 2 := _.

  Global Instance lift_brelation_Proper_Equal_iff {A R default}
    : Proper (@Equal A ==> @Equal A ==> iff) (@lift_brelation A R default) | 2 := _.

  Global Instance lift_brelation_hetero_Proper_Equal {A R default}
    : Proper (@Equal A ==> @Equal A ==> eq) (@lift_brelation_hetero A A R default default) | 2
    := _.

  Global Instance lift_brelation_Proper_Equal {A R default}
    : Proper (@Equal A ==> @Equal A ==> eq) (@lift_brelation A R default) | 2 := _.

  Global Instance lift_relation_hetero_Proper_Proper_subrelation
         {A B}
         {R1 : A -> A -> Prop} {R2 : B -> B -> Prop}
         {R : A -> B -> Prop}
         {defaultA defaultB}
         (Rdefault : R defaultA defaultB)
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R_Proper : Proper (R1 ==> R2 ==> iff) R}
    : Proper ((lift_relation_hetero R1 defaultA defaultA)
                ==> (lift_relation_hetero R2 defaultB defaultB)
                ==> iff)
             (lift_relation_hetero R defaultA defaultB) | 2
    := FMapExtensionsLiftRelationInstances_fun.lift_relation_gen_hetero_Proper_Proper_subrelation
         (Q:=fun x => x) I (fun x y => reflexivity _) Rdefault.
  Global Instance lift_relation_hetero_homo_Proper_Proper_subrelation
         {A} {R1 R2 R : A -> A -> Prop}
         {default}
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R1_subrelation : subrelation R1 R}
         {R2_subrelation : subrelation R2 R}
         {R_Proper : Proper (R1 ==> R2 ==> iff) R}
    : Proper ((lift_relation_hetero R1 default default)
                ==> (lift_relation_hetero R2 default default)
                ==> iff)
             (lift_relation_hetero R default default) | 2
    := _.

  Global Instance lift_relation_Proper_Proper_subrelation {A} {R1 R2 R : A -> A -> Prop} {default}
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R1_subrelation : subrelation R1 R}
         {R2_subrelation : subrelation R2 R}
         {R_Proper : Proper (R1 ==> R2 ==> iff) R}
    : Proper (lift_relation R1 default ==> lift_relation R2 default ==> iff) (lift_relation R default) | 2
    := _.

    Global Instance lift_brelation_hetero_Proper_Proper_subrelation_iff
         {A B}
         {R1 : A -> A -> bool} {R2 : B -> B -> bool}
         {R : A -> B -> bool}
         {defaultA defaultB}
         (Rdefault : R defaultA defaultB)
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R_Proper : Proper (R1 ==> R2 ==> iff) R}
    : Proper ((lift_brelation_hetero R1 defaultA defaultA)
                ==> (lift_brelation_hetero R2 defaultB defaultB)
                ==> iff)
             (lift_brelation_hetero R defaultA defaultB) | 2
    := FMapExtensionsLiftRelationInstances_fun.lift_relation_gen_hetero_Proper_Proper_subrelation
         (Q:=is_true) (reflexivity _) andb_true_iff Rdefault.
  Global Instance lift_brelation_hetero_homo_Proper_Proper_subrelation_iff
         {A} {R1 R2 R : A -> A -> bool}
         {default}
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R1_subrelation : subrelation R1 R}
         {R2_subrelation : subrelation R2 R}
         {R_Proper : Proper (R1 ==> R2 ==> iff) R}
    : Proper ((lift_brelation_hetero R1 default default)
                ==> (lift_brelation_hetero R2 default default)
                ==> iff)
             (lift_brelation_hetero R default default) | 2
    := _.

  Global Instance lift_brelation_Proper_Proper_subrelation_iff {A} {R1 R2 R : A -> A -> bool} {default}
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R1_subrelation : subrelation R1 R}
         {R2_subrelation : subrelation R2 R}
         {R_Proper : Proper (R1 ==> R2 ==> iff) R}
    : Proper (lift_brelation R1 default ==> lift_brelation R2 default ==> iff) (lift_brelation R default) | 2
    := _.

  Global Instance lift_brelation_hetero_Proper_Proper_subrelation
         {A B}
         {R1 : A -> A -> bool} {R2 : B -> B -> bool}
         {R : A -> B -> bool}
         {defaultA defaultB}
         (Rdefault : R defaultA defaultB)
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R_Proper : Proper (R1 ==> R2 ==> eq) R}
    : Proper ((lift_brelation_hetero R1 defaultA defaultA)
                ==> (lift_brelation_hetero R2 defaultB defaultB)
                ==> eq)
             (lift_brelation_hetero R defaultA defaultB) | 2
    := FMapExtensionsLiftRelationInstances_fun.lift_relation_gen_hetero_Proper_Proper_subrelation_iffP
         (Q:=is_true) (reflexivity _) andb_true_iff
         LiftRelationParamsBool.iffP_iff Rdefault.

  Global Instance lift_brelation_hetero_homo_Proper_Proper_subrelation
         {A} {R1 R2 R : A -> A -> bool}
         {default}
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R1_subrelation : subrelation R1 R}
         {R2_subrelation : subrelation R2 R}
         {R_Proper : Proper (R1 ==> R2 ==> eq) R}
    : Proper ((lift_brelation_hetero R1 default default)
                ==> (lift_brelation_hetero R2 default default)
                ==> eq)
             (lift_brelation_hetero R default default) | 2
    := _.

  Global Instance lift_brelation_Proper_Proper_subrelation {A} {R1 R2 R : A -> A -> bool} {default}
         {R1_Reflexive : Reflexive R1}
         {R2_Reflexive : Reflexive R2}
         {R1_subrelation : subrelation R1 R}
         {R2_subrelation : subrelation R2 R}
         {R_Proper : Proper (R1 ==> R2 ==> eq) R}
    : Proper (lift_brelation R1 default ==> lift_brelation R2 default ==> eq) (lift_brelation R default) | 2
    := _.

  Section lift_relation_hetero_Proper_Proper_lift_brelation_subrelation.
    Context {A B}
            {R1 : A -> A -> bool} {R2 : B -> B -> bool}
            {R : A -> B -> Prop}
            {defaultA defaultB}
            (Rdefault : R defaultA defaultB)
            {R1_Reflexive : Reflexive R1}
            {R2_Reflexive : Reflexive R2}.

    Local Notation lift_relation_hetero_Proper_Proper_lift_brelation_subrelationT iffR
      := (Proper ((lift_brelation_hetero R1 defaultA defaultA)
                    ==> (lift_brelation_hetero R2 defaultB defaultB)
                    ==> iffR)
                 (lift_relation_hetero R defaultA defaultB)).
    Local Notation inst lem :=
      (@lem
         _ _ _
         is_true is_true (fun x => x)
         _ _ _ _ _ _
         (reflexivity _) andb_true_iff (reflexivity _) andb_true_iff
         I (fun x y => reflexivity _) _ _ _ _ _ Rdefault _ _ _ _ _).

    Global Instance lift_relation_hetero_Proper_Proper_lift_brelation_subrelation
           {R_Proper : Proper (R1 ==> R2 ==> iff) R}
      : lift_relation_hetero_Proper_Proper_lift_brelation_subrelationT iff | 2
      := inst (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen).
    Global Instance lift_relation_hetero_Proper_Proper_lift_brelation_subrelation_impl
           {R_Proper : Proper (R1 ==> R2 ==> impl) R}
      : lift_relation_hetero_Proper_Proper_lift_brelation_subrelationT impl | 2
      := inst (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen_impl).
    Global Instance lift_relation_hetero_Proper_Proper_lift_brelation_subrelation_flip_impl
           {R_Proper : Proper (R1 ==> R2 ==> flip impl) R}
      : lift_relation_hetero_Proper_Proper_lift_brelation_subrelationT (flip impl) | 2
      := inst (@lift_relation_gen_hetero_Proper_Proper_subrelation_gen_flip_impl).
  End lift_relation_hetero_Proper_Proper_lift_brelation_subrelation.
  Section lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelation.
    Context {A} {R1 R2 : A -> A -> bool} {R : A -> A -> Prop}
            {default : A}
            {R1_Reflexive : Reflexive R1}
            {R2_Reflexive : Reflexive R2}
            {R1_subrelation : subrelation R1 R}
            {R2_subrelation : subrelation R2 R}.

    Local Notation lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelationT iffR
      := (Proper ((lift_brelation_hetero R1 default default)
                    ==> (lift_brelation_hetero R2 default default)
                    ==> iffR)
                 (lift_relation_hetero R default default)).
    Local Notation lift_relation_Proper_Proper_lift_brelation_subrelationT iffR
      := (Proper (lift_brelation R1 default ==> lift_brelation R2 default ==> iffR)
                 (lift_relation R default)).

    Global Instance lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelation
           {R_Proper : Proper (R1 ==> R2 ==> iff) R}
      : lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelationT iff | 2
      := _.
    Global Instance lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelation_impl
           {R_Proper : Proper (R1 ==> R2 ==> impl) R}
      : lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelationT impl | 2
      := _.
    Global Instance lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelation_flip_impl
           {R_Proper : Proper (R1 ==> R2 ==> flip impl) R}
      : lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelationT (flip impl) | 2
      := _.

    Global Instance lift_relation_Proper_Proper_lift_brelation_subrelation
           {R_Proper : Proper (R1 ==> R2 ==> iff) R}
      : lift_relation_Proper_Proper_lift_brelation_subrelationT iff | 2 := _.
    Global Instance lift_relation_Proper_Proper_lift_brelation_subrelation_impl
           {R_Proper : Proper (R1 ==> R2 ==> impl) R}
      : lift_relation_Proper_Proper_lift_brelation_subrelationT impl | 2 := _.
    Global Instance lift_relation_Proper_Proper_lift_brelation_subrelation_flip_impl
           {R_Proper : Proper (R1 ==> R2 ==> flip impl) R}
      : lift_relation_Proper_Proper_lift_brelation_subrelationT (flip impl) | 2 := _.
  End lift_relation_hetero_homo_Proper_Proper_lift_brelation_subrelation.

  Section lift_relation_hetero_Proper_Proper.
    Context {A} {R : A -> A -> Prop} {default : A}
         {R_Reflexive : Reflexive R}.

    Local Notation lift_relation_hetero_Proper_ProperT iffR
      := (Proper ((lift_relation_hetero R default default)
                    ==> (lift_relation_hetero R default default)
                    ==> iffR)
                 (lift_relation_hetero R default default)).
    Local Notation lift_relation_Proper_ProperT iffR
      := (Proper ((lift_relation R default)
                    ==> (lift_relation R default)
                    ==> iffR)
                 (lift_relation R default)).
    Global Instance lift_relation_hetero_Proper_Proper
           {R_Proper : Proper (R ==> R ==> iff) R}
      : lift_relation_hetero_Proper_ProperT iff | 2 := _.
    Global Instance lift_relation_hetero_Proper_Proper_impl
           {R_Proper : Proper (R ==> R ==> impl) R}
      : lift_relation_hetero_Proper_ProperT impl | 2 := _.
    Global Instance lift_relation_hetero_Proper_Proper_flip_impl
           {R_Proper : Proper (R ==> R ==> flip impl) R}
      : lift_relation_hetero_Proper_ProperT (flip impl) | 2 := _.
    Global Instance lift_relation_Proper_Proper
           {R_Proper : Proper (R ==> R ==> iff) R}
      : lift_relation_Proper_ProperT iff | 2 := _.
    Global Instance lift_relation_Proper_Proper_impl
           {R_Proper : Proper (R ==> R ==> impl) R}
      : lift_relation_Proper_ProperT impl | 2 := _.
    Global Instance lift_relation_Proper_Proper_flip_impl
           {R_Proper : Proper (R ==> R ==> flip impl) R}
      : lift_relation_Proper_ProperT (flip impl) | 2 := _.
  End lift_relation_hetero_Proper_Proper.

  Global Instance lift_brelation_hetero_Proper_Proper_iff {A} {R : A -> A -> bool} {default}
         {R_Reflexive : Reflexive R}
         {R_Proper : Proper (R ==> R ==> iff) R}
    : Proper (lift_brelation_hetero R default default ==> lift_brelation_hetero R default default ==> iff) (lift_brelation_hetero R default default) | 2
    := _.

  Global Instance lift_brelation_Proper_Proper_iff {A} {R : A -> A -> bool} {default}
         {R_Reflexive : Reflexive R}
         {R_Proper : Proper (R ==> R ==> iff) R}
    : Proper (lift_brelation R default ==> lift_brelation R default ==> iff) (lift_brelation R default) | 2
    := _.

  Global Instance lift_brelation_Proper_Proper {A} {R : A -> A -> bool} {default}
         {R_Reflexive : Reflexive R}
         {R_Proper : Proper (R ==> R ==> eq) R}
    : Proper (lift_brelation R default ==> lift_brelation R default ==> eq) (lift_brelation R default) | 2
    := _.

  Global Instance lift_relation_hetero_Proper_Proper_lift_brelation {A} {R : A -> A -> bool} {default}
         {R_Reflexive : Reflexive R}
         {R_Proper : Proper (R ==> R ==> iff) R}
    : Proper (lift_brelation_hetero R default default ==> lift_brelation_hetero R default default ==> iff) (lift_relation_hetero R default default) | 2
    := _.

  Global Instance lift_relation_Proper_Proper_lift_brelation {A} {R : A -> A -> bool} {default}
         {R_Reflexive : Reflexive R}
         {R_Proper : Proper (R ==> R ==> iff) R}
    : Proper (lift_brelation R default ==> lift_brelation R default ==> iff) (lift_relation R default) | 2
    := _.

  Global Instance lift_relation_hetero_Equivalence
         {A} {R : A -> A -> Prop}
         {R_Equiv : @Equivalence A R}
         {default}
    : Equivalence (lift_relation_hetero R default default) | 2
    := _.

  Global Instance lift_relation_Equivalence
         {A} {R : A -> A -> Prop}
         {R_Equiv : @Equivalence A R}
         {default}
    : Equivalence (lift_relation R default) | 2 := _.

  Global Instance lift_brelation_hetero_Equivalence
         {A} {R : A -> A -> bool}
         {R_Equiv : @Equivalence A R}
         {default}
    : Equivalence (lift_brelation_hetero R default default) | 2 := _.
  Global Instance lift_brelation_Equivalence
         {A} {R : A -> A -> bool}
         {R_Equiv : @Equivalence A R}
         {default}
    : Equivalence (lift_brelation R default) | 2 := _.

  Global Instance lift_relation_hetero_Antisymmetric
         {A} {R RE : A -> A -> Prop}
         {RE_Equivalence : @Equivalence A RE}
         {AS : Antisymmetric A RE R}
         {default}
    : Antisymmetric _ (lift_relation_hetero RE default default) (lift_relation_hetero R default default) | 2 := _.

  Global Instance lift_relation_Antisymmetric
         {A} {R RE : A -> A -> Prop}
         {RE_Equivalence : @Equivalence A RE}
         {AS : Antisymmetric A RE R}
         {default}
    : Antisymmetric _ (lift_relation RE default) (lift_relation R default) | 2
    := _.

  Global Instance lift_brelation_hetero_Antisymmetric
         {A} {R RE : A -> A -> bool}
         {RE_Equivalence : @Equivalence A RE}
         {AS : Antisymmetric A RE R}
         {default}
    : Antisymmetric _ (lift_brelation_hetero RE default default) (lift_brelation_hetero R default default) | 2 := _.

  Global Instance lift_brelation_Antisymmetric
         {A} {R RE : A -> A -> bool}
         {RE_Equivalence : @Equivalence A RE}
         {AS : Antisymmetric A RE R}
         {default}
    : Antisymmetric _ (lift_brelation RE default) (lift_brelation R default) | 2
    := _.

  Global Existing Instance eq_Reflexive. (* make [Reflexive _] resolve to [eq_Reflexive] *)
End FMapExtensionsLiftRelationInstances_fun.

Module FMapExtensionsLiftRelationInstances (M: WS) := FMapExtensionsLiftRelationInstances_fun M.E M.
