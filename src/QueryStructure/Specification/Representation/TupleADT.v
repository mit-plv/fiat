Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Coq.omega.Omega
        Fiat.Common.ilist2
        Fiat.Common.StringBound
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple.

(* Computational ADT definitions for Tuples. *)
Section TupleADT.

  Open Scope string_scope.
  Open Scope methSig_scope.
  Open Scope consSig_scope.
  Open Scope cMethDef_scope.
  Open Scope cMethDefParsing_scope.
  Open Scope cConsDef_scope.

  Variable heading : Heading.   (* The heading of the tuple. *)

  (* Tuple Initialization *)
  Definition Tuple_Init := "Init".

  Definition InitTupleDom := @Tuple heading.

  Definition InitTupleSig : consSig :=
    {| consID := Tuple_Init;
       consDom := Vector.to_list (AttrList (HeadingRaw heading)) |}.

  (*Fixpoint InitTuple heading' :
    constructorType (@Tuple heading') (Vector.to_list (AttrList (HeadingRaw heading'))).
      refine (match heading' return
                    constructorType (@Tuple heading') (Vector.to_list (AttrList (HeadingRaw heading'))) with
              |
              |

  Definition InitTupleDef :=
    Def Constructor Tuple_Init (inits : InitTupleDom) : rep :=
      InitTuple inits. *)

  (* Getters and Setters for Tuples *)

  Definition GetTupleSig id aType :=
    Method ("Get" ++ id) : rep -> rep * aType.

  Definition SetTupleSig id aType :=
    Method ("Set" ++ id) : rep * aType -> rep.

  Definition TupleSigs'
             {n'}
             (HeadingTypes : Vector.t Type n')
             (HeadingNames : Vector.t string n')
    : Vector.t methSig (n' * 2) :=
    Vector.rect2
      (fun (n : nat) (_ : Vector.t Type n) (_ : Vector.t string n) =>
         Vector.t methSig (n * 2)) (Vector.nil methSig)
      (fun (n : nat) (_ : Vector.t Type n) (_ : Vector.t string n)
           (TupleSigs' : Vector.t methSig (n * 2)) (aType : Type)
           (id : string) =>
         Vector.cons methSig (GetTupleSig id aType) (S (n * 2))
                     (Vector.cons methSig (SetTupleSig id aType) (n * 2) TupleSigs'))
      HeadingTypes HeadingNames.

  Definition TupleSigs :=
    TupleSigs' (AttrList heading)
               (HeadingNames heading).

  Definition GetTupleDef
             (attr : Fin.t (NumAttr heading)) :
    cMethDef (Rep := @Tuple heading) (GetTupleSig (Vector.nth (HeadingNames heading) attr)
                                                  (Vector.nth (AttrList heading) attr)) :=
    Def Method _ (msg : rep) 
    : rep * (Vector.nth (AttrList heading) attr) :=
      (msg, ith2 msg attr).
  
  Definition SetTupleDef
             (attr : Fin.t (NumAttr heading)) :
    cMethDef (Rep := @Tuple heading) (SetTupleSig (Vector.nth (HeadingNames heading) attr)
                                                  (Vector.nth (AttrList heading) attr)) :=
    (Def Method1 _ (msg : @Tuple heading) (val : Vector.nth (AttrList heading) attr) : rep :=
      replace_Index2 _ msg attr val)%cMethDefParsing.

  Definition TupleDefs'
           {n'}
           (HeadingTypes : Vector.t Type n')
           (HeadingNames : Vector.t string n')
    : (forall (attr : Fin.t n'),
          cMethDef (Rep := @Tuple heading) (GetTupleSig (Vector.nth HeadingNames attr)
                                                        (Vector.nth HeadingTypes attr)))
      -> (forall (attr : Fin.t n'),
             cMethDef (Rep := @Tuple heading) (SetTupleSig (Vector.nth HeadingNames attr)
                                                           (Vector.nth HeadingTypes attr)))
      -> ilist (B := cMethDef (Rep := @Tuple heading))
            (TupleSigs' HeadingTypes HeadingNames) :=
    Vector.rect2
      (fun n HeadingTypes HeadingNames =>
         (forall (attr : Fin.t n),
             cMethDef (Rep := @Tuple heading) (GetTupleSig (Vector.nth HeadingNames attr)
                                                           (Vector.nth HeadingTypes attr)))
         -> (forall (attr : Fin.t n),
                cMethDef (Rep := @Tuple heading) (SetTupleSig (Vector.nth HeadingNames attr)
                                                              (Vector.nth HeadingTypes attr)))
         -> ilist (n := n * 2) (B := cMethDef (Rep := @Tuple heading))
                  (TupleSigs' HeadingTypes HeadingNames)) (fun _ _ => ())
      (fun n HeadingTypes HeadingNames
           TupleDefs' aType id
           GetTupleDef' SetTupleDef' =>
         icons (GetTupleDef' Fin.F1)
               (icons (SetTupleDef' Fin.F1)
                      (TupleDefs' (fun n => GetTupleDef' (Fin.FS n))
                                  (fun n => SetTupleDef' (Fin.FS n)))))
      HeadingTypes HeadingNames.

    Definition TupleDefs :=
      TupleDefs' (AttrList heading) (HeadingNames heading)
                 GetTupleDef SetTupleDef.

    (* Tuple ADT Definitions *)
    Definition TupleADTSig : ADTSig :=
      BuildADTSig (Vector.cons _ InitTupleSig _ (Vector.nil _))
                  TupleSigs.

    (*Definition TupleADT : cADT TupleADTSig :=
      BuildcADT (icons InitTupleDef inil) TupleDefs. *)

    (* Support for building messages. *)

    (*Definition ConstructTuple subtopics :=
      CallConstructor TupleADT Tuple_Init subtopics. *)

    (* Support for calling message getters. *)
    Lemma BuildGetTupleMethodID_ibound'
          {n'}
          (HeadingTypes : Vector.t Type n')
          (HeadingNames : Vector.t string n')
      : forall (idx : Fin.t n'),
        Vector.nth (Vector.map methID (TupleSigs' HeadingTypes HeadingNames))
                   (Fin.depair idx Fin.F1) =
        ("Get" ++ Vector.nth HeadingNames idx)%string.
    Proof.
      pattern n', HeadingTypes, HeadingNames.
      eapply Vector.rect2.
      - intro; inversion idx.
      - intros; generalize dependent idx; intro; revert v1 v2 H.
        pattern n, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildGetTupleMethodID
               (idx : Fin.t (NumAttr heading))
    : BoundedString (Vector.map methID TupleSigs) :=
      {| bindex := ("Get" ++ (Vector.nth (HeadingNames heading) idx))%string;
         indexb := {| ibound := Fin.depair idx (@Fin.F1 1);
                      boundi := BuildGetTupleMethodID_ibound' _ _ idx |}
      |}.

    (*Definition CallTupleGetMethod
               (r : Tuple)
               idx
      := cMethods TupleADT (ibound (indexb (BuildGetTupleMethodID idx))) r. *)

    (* Support for calling message setters. *)
    Lemma BuildSetTupleMethodID_ibound
          {n'}
          (HeadingTypes : Vector.t Type n')
          (HeadingNames : Vector.t string n')
      : forall (idx : Fin.t n'),
        Vector.nth (Vector.map methID (TupleSigs' HeadingTypes HeadingNames))
                   (Fin.depair idx (Fin.FS Fin.F1)) =
        ("Set" ++ Vector.nth HeadingNames idx)%string.
    Proof.
      pattern n', HeadingTypes, HeadingNames.
      eapply Vector.rect2.
      - intro; inversion idx.
      - intros; generalize dependent idx; intro; revert v1 v2 H.
        pattern n, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildSetTupleMethodID
               (idx : Fin.t (NumAttr heading))
    : BoundedString (Vector.map methID TupleSigs) :=
      {| bindex := ("Set" ++ (Vector.nth (HeadingNames heading) idx))%string;
         indexb := {| ibound := Fin.depair idx (Fin.FS Fin.F1);
                      boundi := BuildSetTupleMethodID_ibound _ _ idx |}
      |}.

    (*Definition CallTupleSetMethod
               (r : Tuple)
               idx
      := cMethods TupleADT (ibound (indexb (BuildSetTupleMethodID idx))) r. *)

End TupleADT.
