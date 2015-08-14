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

Definition GithubSig : ADTSig :=
  ADTsignature {
      Constructor "Init"
             : unit -> rep,
      Method "AddRepository"
             : rep x (GithubSchema#REPOSITORIES) -> rep x bool,
      Method "AddCommit"
             : rep x (GithubSchema#COMMITS) -> rep x bool,
      Method "PopularProjects"
             : rep x nat -> rep x list string,
      Method "ProjectCommits"
             : rep x string -> rep x list hash (*,
      Method "RecentProjects"
             : rep x nat -> rep x list string *)
    }.

Definition GithubSpec : ADT GithubSig :=
  QueryADTRep GithubSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddRepository" (r : rep, repository : GithubSchema#REPOSITORIES) : bool :=
      Insert repository into r!REPOSITORIES,

    update "AddCommit" (r : rep, commit : GithubSchema#COMMITS) : bool :=
      Insert commit into r!COMMITS,

    query "PopularProjects" (r : rep, star_threshold : nat) : list string :=
      For (repository in r!REPOSITORIES)
          Where (repository!STAR >= star_threshold)
          Return repository!PROJECT_NAME,

    query "ProjectCommits" (r : rep, project : string) : list hash :=
      For (commit in r!COMMITS)
          Where (commit!PROJECT_NAME = project)
          Return commit!HASH (*,

    query "RecentProjects" (r : rep, date_threshold : nat) : list string :=
      For (repository in r!REPOSITORIES) (
          c <- Count (For (commit in r!COMMITS)
                            Where (commit!PROJECT_NAME = repository!PROJECT_NAME)
                            Where (commit!CREATED_AT >= date_threshold)
                            Return ());
          Where (c > 0)
          Return repository!PROJECT_NAME) *)
}.

Definition SharpenedGithub :
  FullySharpened GithubSpec.
Proof.
  master_plan
    ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics).
Time Defined.

Time Definition GithubImpl : ComputationalADT.cADT GithubSig :=
  Eval simpl in projT1 SharpenedGithub.

Print GithubImpl.