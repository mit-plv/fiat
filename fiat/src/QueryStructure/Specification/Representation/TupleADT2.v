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
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading2
        Fiat.QueryStructure.Specification.Representation.Tuple2.

(* Computational ADT definitions for Tuples. *)
Section TupleADT2.

  Open Scope string_scope.
  Open Scope methSig_scope.
  Open Scope consSig_scope.
  Open Scope cMethDefParsing_scope.
  Open Scope cConsDef_scope.

  Variable heading : Heading2.   (* The heading of the tuple. *)

  (* Tuple2 Initialization *)
  Definition Tuple2_Init := "Init".

  Definition InitTuple2Dom := @Tuple2 heading.

  Definition InitTuple2Sig : consSig :=
      Constructor Tuple2_Init : InitTuple2Dom -> rep.

  Definition InitTuple2 : InitTuple2Dom -> Tuple2 := id.

  Definition InitTuple2Def :=
    let _ := {| rep := Tuple2 |} in
    Def Constructor1 Tuple2_Init (inits : InitTuple2Dom) : rep :=
      InitTuple2 inits.

  (* Getters and Setters for Tuple2s *)

  Definition GetTuple2Sig id aType :=
    Method ("Get" ++ id) : rep -> rep * aType.

  Definition SetTuple2Sig id aType :=
    Method ("Set" ++ id) : rep * aType -> rep.

  Definition Tuple2Sigs'
             {n'}
             (HeadingTypes : Vector.t Type n')
             (HeadingNames : Vector.t string n')
    : Vector.t methSig (n' * 2) :=
    Vector.rect2
      (fun (n : nat) (_ : Vector.t Type n) (_ : Vector.t string n) =>
         Vector.t methSig (n * 2)) (Vector.nil methSig)
      (fun (n : nat) (_ : Vector.t Type n) (_ : Vector.t string n)
           (Tuple2Sigs' : Vector.t methSig (n * 2)) (aType : Type)
           (id : string) =>
         Vector.cons methSig (GetTuple2Sig id aType) (S (n * 2))
                     (Vector.cons methSig (SetTuple2Sig id aType) (n * 2) Tuple2Sigs'))
      HeadingTypes HeadingNames.

  Definition Tuple2Sigs :=
    Tuple2Sigs' (AttrList2 heading)
               (HeadingNames2 heading).

  Definition GetTuple2Def
             (attr : Fin.t (NumAttr2 heading)) :
    cMethDef (Rep := @Tuple2 heading) (GetTuple2Sig (Vector.nth (HeadingNames2 heading) attr)
                                                  (Vector.nth (AttrList2 heading) attr)) :=
    Def Method0 _ (msg : @Tuple2 heading)
    : rep * (Vector.nth (AttrList2 heading) attr) :=
      (msg, ith2 msg attr).

  Definition SetTuple2Def
             (attr : Fin.t (NumAttr2 heading)) :
    cMethDef (Rep := @Tuple2 heading) (SetTuple2Sig (Vector.nth (HeadingNames2 heading) attr)
                                                  (Vector.nth (AttrList2 heading) attr)) :=
    Def Method1 _ (msg : @Tuple2 heading) (val : Vector.nth (AttrList2 heading) attr) : rep :=
      replace_Index2 _ msg attr val.

  Definition Tuple2Defs'
           {n'}
           (HeadingTypes : Vector.t Type n')
           (HeadingNames2 : Vector.t string n')
    : (forall (attr : Fin.t n'),
          cMethDef (Rep := @Tuple2 heading) (GetTuple2Sig (Vector.nth HeadingNames2 attr)
                                                        (Vector.nth HeadingTypes attr)))
      -> (forall (attr : Fin.t n'),
             cMethDef (Rep := @Tuple2 heading) (SetTuple2Sig (Vector.nth HeadingNames2 attr)
                                                           (Vector.nth HeadingTypes attr)))
      -> ilist (B := cMethDef (Rep := @Tuple2 heading))
            (Tuple2Sigs' HeadingTypes HeadingNames2) :=
    Vector.rect2
      (fun n HeadingTypes HeadingNames2 =>
         (forall (attr : Fin.t n),
             cMethDef (Rep := @Tuple2 heading) (GetTuple2Sig (Vector.nth HeadingNames2 attr)
                                                           (Vector.nth HeadingTypes attr)))
         -> (forall (attr : Fin.t n),
                cMethDef (Rep := @Tuple2 heading) (SetTuple2Sig (Vector.nth HeadingNames2 attr)
                                                              (Vector.nth HeadingTypes attr)))
         -> ilist (n := n * 2) (B := cMethDef (Rep := @Tuple2 heading))
                  (Tuple2Sigs' HeadingTypes HeadingNames2)) (fun _ _ => ())
      (fun n HeadingTypes HeadingNames2
           Tuple2Defs' aType id
           GetTuple2Def' SetTuple2Def' =>
         icons (GetTuple2Def' Fin.F1)
               (icons (SetTuple2Def' Fin.F1)
                      (Tuple2Defs' (fun n => GetTuple2Def' (Fin.FS n))
                                  (fun n => SetTuple2Def' (Fin.FS n)))))
      HeadingTypes HeadingNames2.

    Definition Tuple2Defs :=
      Tuple2Defs' (AttrList2 heading) (HeadingNames2 heading)
                 GetTuple2Def SetTuple2Def.

    (* Tuple2 ADT Definitions *)
    Definition Tuple2ADTSig : ADTSig :=
      BuildADTSig (Vector.cons _ InitTuple2Sig _ (Vector.nil _))
                  Tuple2Sigs.

    (*Definition Tuple2ADT : cADT Tuple2ADTSig :=
      BuildcADT (icons InitTuple2Def inil) Tuple2Defs. *)

    (* Support for building messages. *)


    (*Definition ConstructTuple2 subtopics :=
      CallConstructor Tuple2ADT Tuple2_Init subtopics. *)

    (* Support for calling message getters. *)
    Lemma BuildGetTuple2MethodID_ibound'
          {n'}
          (HeadingTypes : Vector.t Type n')
          (HeadingNames2 : Vector.t string n')
      : forall (idx : Fin.t n'),
        Vector.nth (Vector.map methID (Tuple2Sigs' HeadingTypes HeadingNames2))
                   (Fin.depair idx Fin.F1) =
        ("Get" ++ Vector.nth HeadingNames2 idx)%string.
    Proof.
      pattern n', HeadingTypes, HeadingNames2.
      eapply Vector.rect2.
      - intro; inversion idx.
      - intros; generalize dependent idx; intro; revert v1 v2 H.
        pattern n, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildGetTuple2MethodID
               (idx : Fin.t (NumAttr2 heading))
    : BoundedString (Vector.map methID Tuple2Sigs) :=
      {| bindex := ("Get" ++ (Vector.nth (HeadingNames2 heading) idx))%string;
         indexb := {| ibound := Fin.depair idx (@Fin.F1 1);
                      boundi := BuildGetTuple2MethodID_ibound' _ _ idx |}
      |}.

    (*Definition CallTuple2GetMethod
               (r : Tuple2)
               idx
      := cMethods Tuple2ADT (ibound (indexb (BuildGetTuple2MethodID idx))) r. *)

    (* Support for calling message setters. *)
    Lemma BuildSetTuple2MethodID_ibound
          {n'}
          (HeadingTypes : Vector.t Type n')
          (HeadingNames2 : Vector.t string n')
      : forall (idx : Fin.t n'),
        Vector.nth (Vector.map methID (Tuple2Sigs' HeadingTypes HeadingNames2))
                   (Fin.depair idx (Fin.FS Fin.F1)) =
        ("Set" ++ Vector.nth HeadingNames2 idx)%string.
    Proof.
      pattern n', HeadingTypes, HeadingNames2.
      eapply Vector.rect2.
      - intro; inversion idx.
      - intros; generalize dependent idx; intro; revert v1 v2 H.
        pattern n, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildSetTuple2MethodID
               (idx : Fin.t (NumAttr2 heading))
    : BoundedString (Vector.map methID Tuple2Sigs) :=
      {| bindex := ("Set" ++ (Vector.nth (HeadingNames2 heading) idx))%string;
         indexb := {| ibound := Fin.depair idx (Fin.FS Fin.F1);
                      boundi := BuildSetTuple2MethodID_ibound _ _ idx |}
      |}.

    (*Definition CallTuple2SetMethod
               (r : Tuple2)
               idx
      := cMethods Tuple2ADT (ibound (indexb (BuildSetTuple2MethodID idx))) r. *)

End TupleADT2.

(*Definition CallDecTuple2GetMethod
           {n attrs}
           (r : @DecTuple2 n attrs)
           idx
  := cMethods (Tuple2ADT _) (ibound (indexb (BuildGetTuple2MethodID _ idx))) r. *)

(* Notation "t ! R" :=
  (@CallDecTuple2GetMethod _ _ t%Tuple2 (ibound (indexb ((@Build_BoundedIndex _ _ _ R%string _)))) ())
  : Tuple2_scope. *)
