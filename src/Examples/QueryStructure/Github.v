Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition MEMBERS := "Members".
Definition REPOSITORIES := "Repositories".
Definition COMMITS := "Commits".

Definition USERNAME := "Username".
Definition STAR := "Star".
Definition PROJECT_NAME := "ProjectName".
Definition HASH := "Hash".
Definition CREATED_AT := "CreatedAt".

Definition hash := list ascii.

Definition GithubSchema :=
  Query Structure Schema
        [ relation REPOSITORIES has
                   schema <PROJECT_NAME :: string,
                           STAR :: nat>;
          relation COMMITS has
                   schema <PROJECT_NAME :: string,
                           HASH :: hash,
                           CREATED_AT :: nat> ]
        enforcing [ attribute PROJECT_NAME for COMMITS references REPOSITORIES ].

Definition GithubSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure GithubSchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "AddRepository" (r : rep) (repository : GithubSchema#REPOSITORIES) : rep * bool :=
      Insert repository into r!REPOSITORIES,

    Def Method1 "AddCommit" (r : rep) (commit : GithubSchema#COMMITS) : rep * bool :=
      Insert commit into r!COMMITS,

    Def Method1 "PopularProjects" (r : rep) (star_threshold : nat) : rep * (list string) :=
        res <- For (repository in r!REPOSITORIES)
          Where (repository!STAR >= star_threshold)
          Return repository!PROJECT_NAME;
    ret (r, res),

    Def Method1 "ProjectCommits" (r : rep) (project : string) : rep * list hash :=
      res <- For (commit in r!COMMITS)
          Where (commit!PROJECT_NAME = project)
          Return commit!HASH;
    ret (r, res),

    Def Method1 "RecentProjects" (r : rep) (date_threshold : nat) : rep * list string :=
      res <- For (repository in r!REPOSITORIES) (
          c <- Count (For (commit in r!COMMITS)
                            Where (commit!PROJECT_NAME = repository!PROJECT_NAME)
                            Where (commit!CREATED_AT >= date_threshold)
                            Return ());
          If (c == 0) Then ret [ ]
          Else ret [repository!PROJECT_NAME]);
          ret (r, res)
}%methDefParsing.

Definition SharpenedGithub :
  FullySharpened GithubSpec.
Proof.
  start sharpening ADT.
  pose_string_hyps.
  eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl | ]
                          ])]
    end | ].
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone representation using (@FiniteTables_AbsR GithubSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
    + simpl.
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).

    + simpl.

  master_plan
    ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics).
Time Defined.

Time Definition GithubImpl : ComputationalADT.cADT GithubSig :=
  Eval simpl in projT1 SharpenedGithub.

Print GithubImpl.
