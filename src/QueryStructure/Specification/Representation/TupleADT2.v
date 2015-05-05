Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Coq.omega.Omega
        Fiat.Common.ilist
        Fiat.Common.StringBound
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.Heading2
        Fiat.QueryStructure.Specification.Representation.Tuple2.

(* Duplicate Computational ADT definitions for Tuples to avoid Universe Inconsistencies . *)
Section TupleADT2.

  Open Scope string.
  Open Scope methSig.
  Open Scope consSig.
  Open Scope cMethDef.
  Open Scope cConsDef.

  Variable heading : Heading2.   (* The heading of the tuple. *)

  (* Tuple Initialization *)
  Definition Tuple2_Init := "Init".

  Fixpoint InitTupleDom2 (topics : list Attribute2) :=
    match topics return Type with
      | [ ] => unit
      | topic :: topics' => prod (attrType2 topic) (InitTupleDom2 topics')
    end.

  Definition InitTupleSig (topics : list Attribute2) : consSig :=
    Constructor Tuple2_Init : InitTupleDom2 topics -> rep.

  Fixpoint InitTuple (topics : list Attribute2)
  : InitTupleDom2 topics -> ilist attrType2 topics :=
    match topics return
          InitTupleDom2 topics -> ilist attrType2 topics with
      | [ ] =>
        fun inits => inil _
      | topic :: topics' =>
        fun inits => icons _ (fst inits) (InitTuple topics' (snd inits))
    end.

    Definition InitTupleDef2' (topics : list Attribute2) :=
      Def Constructor Tuple2_Init (inits : InitTupleDom2 topics) : rep :=
      InitTuple topics inits.

    Definition InitTupleDef2 := InitTupleDef2' (AttrList2 heading).

    (* Getters and Setters for Tuples *)

    Definition attrID2 := Attributes2 heading.
    Definition attrType2' (attr : attrID2) := attrType2 (nth_Bounded _ (AttrList2 heading) attr).

    Definition GetTupleSig2 (attr : attrID2) :=
      Method ("Get" ++ bindex attr) : rep x unit -> rep x attrType2' attr.

    Definition SetTupleSig2 (attr : attrID2) :=
      Method ("Set" ++ bindex attr) : rep x attrType2' attr -> rep x unit.

    Fixpoint TupleMethSigs2' (attrs : list attrID2) : list methSig :=
      match attrs with
        | [ ] => [ ]
        | topic :: topics' =>
          GetTupleSig2 topic :: SetTupleSig2 topic :: TupleMethSigs2' topics'
      end.

    Definition GetTupleDef2 (attr : attrID2) :
      cMethDef (Rep := @Tuple2 heading) (GetTupleSig2 attr) :=
      Def Method _ (msg : rep, _ : _) : attrType2' attr :=
      (msg, GetAttribute2 msg attr).

    Definition SetTupleDef2 (attr : attrID2) :
      cMethDef (Rep := @Tuple2 heading) (SetTupleSig2 attr) :=
      Def Method _ (msg : rep, val : attrType2' attr) : unit :=
      (SetAttribute2 msg _ val, tt).

    Fixpoint TupleMeths2'
             (attrs : list attrID2)
    : ilist (cMethDef (Rep := @Tuple2 heading )) (TupleMethSigs2' attrs) :=
      match attrs return
            ilist (cMethDef (Rep := @Tuple2 heading)) (TupleMethSigs2' attrs) with
        | [ ] => inil _
        | attr :: attrs' =>
          icons _ (GetTupleDef2 attr) (icons _ (SetTupleDef2 attr) (TupleMeths2' attrs'))
      end.

    Definition LiftAttributes2 : list attrID2 :=
      (fix LiftAttributes (attributes : list Attribute2)
       : list (@BoundedString (map attrName2 attributes)) :=
         match attributes return list (@BoundedString (map attrName2 attributes)) with
           | [ ] => [ ]
           | attribute :: attributes' =>
             {| bindex := _; indexb := IndexBound_head _ _ |}
               :: (map (fun idx : BoundedString =>
                          {| bindex := bindex idx;
                             indexb := @IndexBound_tail _ _ (attrName2 attribute) _ (indexb idx) |})
                       (LiftAttributes attributes'))
         end) (AttrList2 heading).

    Definition TupleMethSigs2 := TupleMethSigs2' LiftAttributes2.

    Definition TupleMeths2
    : ilist (cMethDef (Rep := @Tuple2 heading )) TupleMethSigs2
      := TupleMeths2' LiftAttributes2.

    (* Tuple2 ADT Definitions *)
    Definition TupleADTSig2 : ADTSig :=
      BuildADTSig [InitTupleSig (AttrList2 heading)] TupleMethSigs2.

    Definition TupleADT2 : cADT TupleADTSig2 :=
      BuildcADT (icons _ InitTupleDef2 (inil _)) TupleMeths2.

    (* Support for building messages. *)

    Definition ConstructTuple2 attr_list :=
      CallConstructor TupleADT2 Tuple2_Init attr_list.

    (* Support for calling message getters. *)

    Lemma BuildGetMethodID2'
    : forall (attrs : list attrID2)
             (idx : BoundedIndex (map (fun id => bindex id) attrs)),
        nth_error (map methID (TupleMethSigs2' attrs)) (2 * ibound idx) =
        Some ("Get" ++ bindex idx).
    Proof.
      destruct idx as [idx [n nth_n]].
      revert idx n nth_n; induction attrs; intros.
      destruct n; simpl in *; discriminate.
      destruct n; simpl in *.
      - unfold Specif.value in *; repeat f_equal.
        destruct a as [b [m nth_m]]; simpl in *; subst.
        injections; eauto.
      - rewrite plus_comm; simpl; rewrite plus_comm.
        eauto.
    Qed.

    Definition BuildGetMethodID2
               (idx : BoundedIndex (map (fun id => bindex id) LiftAttributes2))
    : @BoundedString (map methID TupleMethSigs2) :=
      {| bindex := ("Get" ++ (bindex idx))%string;
         indexb := {| ibound := 2 * ibound idx;
                      boundi := BuildGetMethodID2' LiftAttributes2 idx |}
      |}.

    Definition CallTupleGetMethod2 (r : Tuple2) idx
      := cMethods TupleADT2 (BuildGetMethodID2 idx) r.

    (* Support for calling message setters. *)
    Definition BuildSetMethodID2'
    : forall (attrs : list attrID2)
             (idx : BoundedIndex (map (fun id => bindex id) attrs)),
        nth_error (map methID (TupleMethSigs2' attrs)) (2 * ibound idx + 1) =
        Some ("Set" ++ bindex idx).
    Proof.
      destruct idx as [idx [n nth_n]].
      revert idx n nth_n; induction attrs; intros.
      destruct n; simpl in *; discriminate.
      destruct n; simpl in *.
      - unfold Specif.value; repeat f_equal.
        destruct a as [b [m nth_m]]; simpl in *; subst.
        injections; eauto.
      - rewrite plus_comm; simpl.
        rewrite <- (IHattrs idx n nth_n); f_equal.
        omega.
    Qed.

    Definition BuildSetMethodID2
               (idx : BoundedIndex (map (fun id => bindex id) LiftAttributes2))
    : @BoundedString (map methID (TupleMethSigs2 ))
      :=  {| bindex := ("Set" ++ (bindex idx))%string;
             indexb := {| ibound := 2 * ibound idx + 1;
                          boundi := BuildSetMethodID2' LiftAttributes2 idx |} |}.

    Definition CallTupleSetMethod2 (r : Tuple2) idx :=
      cMethods TupleADT2 (BuildSetMethodID2 idx) r.

End TupleADT2.
