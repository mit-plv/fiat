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
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple.

(* Computational ADT definitions for Tuples. *)
Section TupleADT.

  Open Scope string.
  Open Scope methSig.
  Open Scope consSig.
  Open Scope cMethDef.
  Open Scope cConsDef.

  Variable heading : Heading.   (* The heading of the tuple. *)

  (* Tuple Initialization *)
  Definition Tuple_Init := "Init".

  Fixpoint InitTupleDom (topics : list Attribute) :=
    match topics return Type with
      | [ ] => unit
      | topic :: topics' => prod (attrType topic) (InitTupleDom topics')
    end.

  Definition InitTupleSig (topics : list Attribute) : consSig :=
    Constructor Tuple_Init : InitTupleDom topics -> rep.

  Fixpoint InitTuple (topics : list Attribute)
  : InitTupleDom topics -> ilist attrType topics :=
    match topics return
          InitTupleDom topics -> ilist attrType topics with
      | [ ] =>
        fun inits => inil _
      | topic :: topics' =>
        fun inits => icons _ (fst inits) (InitTuple topics' (snd inits))
    end.

    Definition InitTupleDef' (topics : list Attribute) :=
      Def Constructor Tuple_Init (inits : InitTupleDom topics) : rep :=
      InitTuple topics inits.

    Definition InitTupleDef := InitTupleDef' (AttrList heading).

    (* Getters and Setters for Tuples *)

    Definition attrID := Attributes heading.
    Definition attrType' (attr : attrID) := attrType (nth_Bounded _ (AttrList heading) attr).

    Definition GetTupleSig (attr : attrID) :=
      Method ("Get" ++ bindex attr) : rep x unit -> rep x attrType' attr.

    Definition SetTupleSig (attr : attrID) :=
      Method ("Set" ++ bindex attr) : rep x attrType' attr -> rep x unit.

    Fixpoint TupleMethSigs' (attrs : list attrID) : list methSig :=
      match attrs with
        | [ ] => [ ]
        | topic :: topics' =>
          GetTupleSig topic :: SetTupleSig topic :: TupleMethSigs' topics'
      end.

    Definition GetTupleDef (attr : attrID) :
      cMethDef (Rep := @Tuple heading) (GetTupleSig attr) :=
      Def Method _ (msg : rep, _ : _) : attrType' attr :=
      (msg, GetAttribute msg attr).

    Definition SetTupleDef (attr : attrID) :
      cMethDef (Rep := @Tuple heading) (SetTupleSig attr) :=
      Def Method _ (msg : rep, val : attrType' attr) : unit :=
      (SetAttribute msg _ val, tt).

    Fixpoint TupleMeths'
             (attrs : list attrID)
    : ilist (cMethDef (Rep := @Tuple heading )) (TupleMethSigs' attrs) :=
      match attrs return
            ilist (cMethDef (Rep := @Tuple heading)) (TupleMethSigs' attrs) with
        | [ ] => inil _
        | attr :: attrs' =>
          icons _ (GetTupleDef attr) (icons _ (SetTupleDef attr) (TupleMeths' attrs'))
      end.

    Definition LiftAttributes : list attrID :=
      (fix LiftAttributes (attributes : list Attribute)
       : list (@BoundedString (map attrName attributes)) :=
         match attributes return list (@BoundedString (map attrName attributes)) with
           | [ ] => [ ]
           | attribute :: attributes' =>
             {| bindex := _; indexb := IndexBound_head _ _ |}
               :: (map (fun idx : BoundedString =>
                          {| bindex := bindex idx;
                             indexb := @IndexBound_tail _ _ (attrName attribute) _ (indexb idx) |})
                       (LiftAttributes attributes'))
         end) (AttrList heading).

    Definition TupleMethSigs := TupleMethSigs' LiftAttributes.

    Definition TupleMeths
    : ilist (cMethDef (Rep := @Tuple heading )) TupleMethSigs
      := TupleMeths' LiftAttributes.

    (* Tuple ADT Definitions *)
    Definition TupleADTSig : ADTSig :=
      BuildADTSig [InitTupleSig (AttrList heading)] TupleMethSigs.

    Definition TupleADT : cADT TupleADTSig :=
      BuildcADT (icons _ InitTupleDef (inil _)) TupleMeths.

    (* Support for building messages. *)

    Definition ConstructTuple attr_list :=
      CallConstructor TupleADT Tuple_Init attr_list.

    (* Support for calling message getters. *)

    Lemma BuildGetMethodID'
    : forall (attrs : list attrID)
             (idx : BoundedIndex (map (fun id => bindex id) attrs)),
        nth_error (map methID (TupleMethSigs' attrs)) (2 * ibound idx) =
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

    Definition BuildGetMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftAttributes))
    : @BoundedString (map methID TupleMethSigs) :=
      {| bindex := ("Get" ++ (bindex idx))%string;
         indexb := {| ibound := 2 * ibound idx;
                      boundi := BuildGetMethodID' LiftAttributes idx |}
      |}.

    Definition CallTupleGetMethod (r : Tuple) idx
      := cMethods TupleADT (BuildGetMethodID idx) r.

    (* Support for calling message setters. *)
    Definition BuildSetMethodID'
    : forall (attrs : list attrID)
             (idx : BoundedIndex (map (fun id => bindex id) attrs)),
        nth_error (map methID (TupleMethSigs' attrs)) (2 * ibound idx + 1) =
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

    Definition BuildSetMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftAttributes))
    : @BoundedString (map methID (TupleMethSigs ))
      :=  {| bindex := ("Set" ++ (bindex idx))%string;
             indexb := {| ibound := 2 * ibound idx + 1;
                          boundi := BuildSetMethodID' LiftAttributes idx |} |}.

    Definition CallTupleSetMethod (r : Tuple) idx :=
      cMethods TupleADT (BuildSetMethodID idx) r.

End TupleADT.
