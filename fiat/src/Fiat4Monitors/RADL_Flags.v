Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Arith.Arith
        Coq.Program.Program
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Flag
        Bedrock.Memory.

Section Flags.

  Open Scope ADT_scope.
  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope ADTSig_scope.

  Context {n : nat}.
  Variable TopicTypes : Vector.t Type n. (* List of Topics in the Network. *)
  Variable TopicNames : Vector.t string n. (* List of Topics IDs in the Network. *)
  Let TopicID := @TopicID n.

  Definition RADL_Flag := cRep RADL_FlagADT.

  Definition Flags {n'} (subtopics : Vector.t (Fin.t n) n') :=
    Vector.t RADL_Flag n'.

  Definition GetFlag
             {n'}
             {subtopics : Vector.t (Fin.t n) n'}
             (flags : Flags subtopics)
             (topic : Fin.t n')
    : RADL_Flag := Vector.nth flags topic.

  Definition SetFlag
             {n'}
             {subtopics : Vector.t (Fin.t n) n'}
             (flags : Flags subtopics)
             (topic : Fin.t n')
             (val : RADL_Flag)
    : Flags subtopics := Vector.replace flags topic val.

  Section RADL_FlagsADT.

    Open Scope methSig_scope.
    Open Scope consSig_scope.
    Open Scope cMethDef_scope.
    Open Scope cConsDef_scope.

    (* Message Initialization *)
    Definition Flags_Init := "Init".

    Definition InitFlagsDom {n'} (subtopics : Vector.t (Fin.t n) n') :=
      Vector.t RADL_Flag n'.

    Definition InitFlagsSig {n'} (subtopics : Vector.t (Fin.t n) n') : consSig :=
      Constructor Flags_Init : InitFlagsDom subtopics -> rep.

    Definition InitFlags {n'}
             (subtopics : Vector.t (Fin.t n) n')
             (flags : InitFlagsDom subtopics)
      : Flags subtopics := flags.

    Definition InitFlagsDef
               {n'}
               (subtopics : Vector.t (Fin.t n) n') :=
      Def Constructor Flags_Init (flags : InitFlagsDom subtopics) : rep :=
      @InitFlags _ subtopics flags.

    (* Getters and Setters for Flags *)

    Definition GetFlagSig (topic : Fin.t n) :=
      Method ("Get" ++ (Vector.nth TopicNames topic))
      : rep x unit -> rep x RADL_Flag.

    Definition SetFlagSig (topic : Fin.t n) :=
      Method ("Set" ++ (Vector.nth TopicNames topic)) : rep x RADL_Flag -> rep x unit.

    Fixpoint FlagsSigs
             {n'}
             (subtopics : Vector.t (Fin.t n) n')
      : Vector.t methSig (n' * 2) :=
      match subtopics in Vector.t _ n'
            return Vector.t methSig (n' * 2) with
        | Vector.nil => Vector.nil _
        | Vector.cons topic _ topics' =>
          Vector.cons _ (GetFlagSig topic) _
                      (Vector.cons _ (SetFlagSig topic) _ (FlagsSigs topics'))
      end.

    Definition GetFlagDef
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               (topic : Fin.t n') :
      cMethDef (Rep := Flags subtopics) (GetFlagSig (Vector.nth subtopics topic)) :=
      Def Method _ (msg : rep, g : unit) : RADL_Flag :=
        (msg, GetFlag msg topic).

    Definition SetFlagDef
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               (topic : Fin.t n') :
      cMethDef (Rep := Flags subtopics) (SetFlagSig (Vector.nth subtopics topic)) :=
      Def Method _ (msg : rep, val : RADL_Flag) : unit :=
      (SetFlag msg topic val, tt).

    Fixpoint FlagsDefs'
             {m}
             (subtopics'' : Vector.t (Fin.t n) m)
             {n''}
             (subtopics' : Vector.t (Fin.t n) n'')
      : (forall (topic : Fin.t n''),
            cMethDef (Rep := Flags subtopics'')
                     (GetFlagSig (Vector.nth subtopics' topic)))
        -> (forall (topic : Fin.t n''),
               cMethDef
                 (Rep := Flags subtopics'')
                 (SetFlagSig (Vector.nth subtopics' topic)))
        -> ilist (B := cMethDef (Rep := Flags subtopics''))
              (FlagsSigs subtopics')
        :=
          match subtopics' in Vector.t _ n'' return
                (forall (topic : Fin.t n''),
                    cMethDef (Rep := Flags subtopics'')
                             (GetFlagSig (Vector.nth subtopics' topic)))
                -> (forall (topic : Fin.t n''),
                       cMethDef
                     (Rep := Flags subtopics'')
                     (SetFlagSig (Vector.nth subtopics' topic)))
                -> ilist (B := cMethDef (Rep := Flags subtopics''))
                         (FlagsSigs subtopics') with
          | Vector.nil => fun _ _ => tt
          | Vector.cons _ n0 subtopics' =>
            fun GetFlagDef SetFlagDef =>
              Build_prim_prod (GetFlagDef Fin.F1)
                              (Build_prim_prod (SetFlagDef Fin.F1)
                                               (@FlagsDefs' _ subtopics'' _ subtopics'
                                                              (fun t => GetFlagDef (Fin.FS t))
                                                              (fun t => SetFlagDef (Fin.FS t))))
          end.

    Definition FlagsDefs
               {n''}
               (subtopics' : Vector.t (Fin.t n) n'') :=
      FlagsDefs' subtopics' (GetFlagDef subtopics') (SetFlagDef subtopics').

    (* Flag ADT Definitions *)

    Definition FlagsADTSig
               {n'}
               (subtopics : Vector.t (Fin.t n) n') 
      : ADTSig :=
      BuildADTSig (Vector.cons _ (InitFlagsSig subtopics) _ (Vector.nil _))
                  (FlagsSigs subtopics).

    Definition FlagsADT
               {n'}
               (subtopics : Vector.t (Fin.t n) n') 
      : cADT (FlagsADTSig subtopics) :=
      BuildcADT (icons (InitFlagsDef subtopics) inil)
                (FlagsDefs subtopics).

    (* Support for building messages. *)

    Definition ConstructFlags
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               flags :=
      CallConstructor (FlagsADT subtopics) Flags_Init flags.

    (* Support for calling message getters. *)
        Lemma BuildGetFlagsMethodID_ibound
              {n'}
              (subtopics : Vector.t (Fin.t n) n')
          : forall (idx : Fin.t n'),
        Vector.nth (Vector.map methID (FlagsSigs subtopics))
                   (Fin.depair idx Fin.F1) =
        ("Get" ++ Vector.nth TopicNames (Vector.nth subtopics idx))%string.
    Proof.
      induction subtopics.
      - intro; inversion idx.
      - intro; revert subtopics IHsubtopics; pattern n0, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildGetFlagsMethodID'
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               (idx : Fin.t n')
    : BoundedString (Vector.map methID (FlagsSigs subtopics)) :=
      {| bindex := ("Get" ++ (Vector.nth TopicNames (Vector.nth subtopics idx)))%string;
         indexb := {| ibound := Fin.depair idx (@Fin.F1 1);
                      boundi := BuildGetFlagsMethodID_ibound subtopics idx |}
      |}.

    Definition BuildGetFlagsMethodID
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               (idx : Fin.t n')
      : BoundedString (Vector.map methID (FlagsSigs subtopics))
      := BuildGetFlagsMethodID' _ idx.

    Definition CallFlagsGetMethod
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               (r : Flags subtopics)
               idx
      := cMethods (FlagsADT subtopics) (ibound (indexb (BuildGetFlagsMethodID subtopics idx))) r.

    (* Support for calling message setters. *)
    Lemma BuildSetFlagsMethodID_ibound
          {n'}
          (subtopics : Vector.t (Fin.t n) n')
      : forall (idx : Fin.t n'),
        Vector.nth (Vector.map methID (FlagsSigs subtopics))
                   (Fin.depair idx (Fin.FS Fin.F1)) =
        ("Set" ++ Vector.nth TopicNames (Vector.nth subtopics idx))%string.
    Proof.
      induction subtopics.
      - intro; inversion idx.
      - intro; revert subtopics IHsubtopics; pattern n0, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildSetFlagsMethodID'
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               (idx : Fin.t n')
    : BoundedString (Vector.map methID (FlagsSigs subtopics)) :=
      {| bindex := ("Set" ++ (Vector.nth TopicNames (Vector.nth subtopics idx)))%string;
         indexb := {| ibound := Fin.depair idx (Fin.FS Fin.F1);
                      boundi := BuildSetFlagsMethodID_ibound subtopics idx |}
      |}.

    Definition BuildSetFlagsMethodID
               {n'}
               (subtopics : Vector.t (Fin.t n) n')
               (idx : Fin.t n')
      : BoundedString (Vector.map methID (FlagsSigs subtopics))
      := BuildSetFlagsMethodID' _ idx.

    Definition CallFlagsSetMethod
               {n'}
               {subtopics : Vector.t (Fin.t n) n'}
               (r : Flags subtopics)
               idx
      := cMethods (FlagsADT subtopics) (ibound (indexb (BuildSetFlagsMethodID subtopics idx))) r.

  End RADL_FlagsADT.

End Flags.
