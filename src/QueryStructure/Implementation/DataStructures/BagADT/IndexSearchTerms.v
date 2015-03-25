Require Import
        Coq.Lists.List
        Coq.Program.Program
        Coq.Bool.Bool
        Coq.Strings.String
        ADTSynthesis.Common.ilist
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.StringBound
        ADTSynthesis.ADTNotation
        ADTSynthesis.ADTRefinement
        ADTSynthesis.QueryStructure.Specification.Representation.Notations
        ADTSynthesis.QueryStructure.Specification.Representation.Heading
        ADTSynthesis.QueryStructure.Specification.Representation.Tuple
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation
        ADTSynthesis.ADTRefinement.BuildADTRefinements.HoneRepresentation.
(* Definitions for building BagADT search terms using decideable equalities
   over named attributes.*)

(* Implements a Search Term for heading as a list of optional key
   values given a list of attributes. *)

Class IndexDenotation
      (A : string)
      (heading : Heading)
      (index : Attributes heading)
  := { DenoteIndex : Type;
       MatchIndex : DenoteIndex -> @Tuple heading -> bool
  }.

Open Scope string.
Definition EqualityIndex : string := "Eq".

Global Instance EqualityIndexDenotation
       (heading : Heading)
       (index : Attributes heading)
       (_ : Query_eq (Domain heading index))
: @IndexDenotation EqualityIndex heading index :=
  {| DenoteIndex :=
       option (Domain heading index);
     MatchIndex search_term tup :=
       match search_term with
         | Some val => if A_eq_dec (GetAttribute tup index) val then
                         true
                       else false
         | _ => true
       end
  |}.

Definition UnIndex : string := "unIndex".
Global Instance UnIndexDenotation
       (heading : Heading)
       (index : Attributes heading)
: @IndexDenotation UnIndex heading index :=
  {| DenoteIndex := @Tuple heading -> bool;
     MatchIndex search_term tup := search_term tup
  |}.

Ltac BuildIndexSearchTerm'
     attrs heading indices k :=
  match indices with
    | [(?kind, ?idx)] =>
      k (@DenoteIndex kind heading (@Build_BoundedIndex _ attrs idx _) _)
    | (?kind, ?idx) :: ?indices' =>
      BuildIndexSearchTerm' attrs heading indices'
                           ltac:(fun st' =>
                                   k (prod (@DenoteIndex kind heading
                                                         (@Build_BoundedIndex _ attrs idx _)  _) st'))
  end.

Ltac BuildIndexMatcher'
     attrs heading indices k :=
  match indices with
    | [(?kind, ?idx)] =>
      let idx' := constr:(@Build_BoundedIndex _ attrs idx _) in
      k (@MatchIndex kind heading idx' _)
    | (?kind, ?idx) :: ?indices' =>
      let idx' := constr:(@Build_BoundedIndex _ attrs idx _) in
      BuildIndexMatcher' attrs
        heading indices'
        ltac:(fun matcher' =>
                k (fun st tup => (@MatchIndex kind heading idx' _ (fst st) tup)
                               && matcher' (snd st) tup))
  end.

Record KindIndex
       {heading : Heading}
  := { KindIndexKind : Set;
       KindIndexIndex : @Attributes heading }.

Ltac BuildIndexes
     attrs heading indices k :=
  match indices with
    | [(?kind, ?idx)] =>
      let idx' := constr:(@Build_BoundedIndex _ attrs idx _) in
      k ([@Build_KindIndex heading kind idx'])
    | (?kind, ?idx) :: ?indices' =>
      let idx' := constr:(@Build_BoundedIndex _ attrs idx _) in
      BuildIndexes attrs
                   heading indices'
                   ltac:(fun indices'' =>
                           k ((@Build_KindIndex heading kind idx') :: indices''))
  end.

(* Aliases to make existing automation happy. *)
Definition BuildIndexSearchTerm
           {heading : Heading}
           (indices : list (@KindIndex heading))
           {BuildIndexSearchTermT : Type}
: Type := BuildIndexSearchTermT.

Definition MatchIndexSearchTerm
           {heading : Heading}
           {indices : list (@KindIndex heading)}
           {IndexSearchTermT : Type}
           {matcher : IndexSearchTermT -> @Tuple heading -> bool} :
  @BuildIndexSearchTerm heading indices IndexSearchTermT
  -> @Tuple heading -> bool := matcher.

(*Fixpoint BuildIndexSearchTerm {heading : Heading}
         (indices : list (@Attributes heading))
: Type :=
  match indices with
    | [] => (@Tuple heading -> bool)
    | idx :: indices' => prod (option (Domain heading idx)) (BuildIndexSearchTerm indices')
  end. *)

(* Implements a matcher function for a search term built using [BuildSearchTerm].
Fixpoint MatchIndexSearchTerm {heading}
         {indices : list (@Attributes heading)}
         {eq_dec_indices : ilist (fun attr => Query_eq (Domain heading attr)) indices}
: BuildIndexSearchTerm indices -> @Tuple heading -> bool :=
  match indices return
        ilist (fun attr => Query_eq (Domain heading attr)) indices
        -> BuildIndexSearchTerm indices -> @Tuple heading -> bool
  with
    | nil => fun _ f tup => f tup
    | index :: indices' =>
      fun (eq_dec_indices : ilist (fun attr => Query_eq (Domain heading attr))
                                  (index :: indices')) =>
         (fun (H : BuildIndexSearchTerm indices' -> @Tuple heading -> bool)
              (f : prod (option (Domain heading index))
                        (BuildIndexSearchTerm indices'))
              (tup : @Tuple heading) =>
            match f with
              | (Some k, index') =>
                (if (A_eq_dec (Query_eq := ilist_hd eq_dec_indices) k (GetAttribute tup index))
                 then true else false)
                  && (H index' tup)
              | (None, index') => H index' tup
            end) (@MatchIndexSearchTerm _ _ (ilist_tl eq_dec_indices))
  end eq_dec_indices. *)

Tactic Notation "build" "single" "index":=
repeat match goal with
         | [ |- ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns))) []] =>
           econstructor 2
         | [ |- ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
                      (?sch :: ?sch') ]=> econstructor 1; [ econstructor | ]
         | [ |- ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns))) ?sch] =>
           simpl sch
       end.

(* Ltac build_index_list heading As k :=
  match As with
    | nil => k (inil (fun attr : Attributes heading => Query_eq (Domain heading attr)))
    | cons ?a ?As' =>
      build_index_list heading As'
                       ltac:(fun Bs' =>
                               k (let a : Attributes heading := {| bindex := a; indexb := _ |} in
                                   icons
                                    (B := (fun attr : Attributes heading => Query_eq (Domain heading attr)))
                                    a
                                    (_ : Query_eq (Domain heading a))
                                    Bs'))
  end. *)

Ltac makeIndex' NamedSchemas IndexKeys k :=
  match NamedSchemas  with
    | nil => k (inil (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))))
    | cons ?ns ?NamedSchemas' =>
      match IndexKeys with
        | cons ?ik ?IndexKeys' =>
          let attrs := eval simpl in (map attrName (AttrList (schemaHeading (relSchema ns)))) in
              BuildIndexes attrs (schemaHeading (relSchema ns)) ik
                           ltac:(fun attrs' =>
                                   BuildIndexMatcher' attrs (schemaHeading (relSchema ns)) ik
                                                      ltac:(fun matcher' =>
                                                              makeIndex' NamedSchemas' IndexKeys'
                                                                         ltac:(fun Bs' => k (icons ns
                                                                                                   {| BagMatchSearchTerm := @MatchIndexSearchTerm
                                                                                                                              (schemaHeading (relSchema ns)) attrs' _
                                                                                                                              matcher';
                                                                                                      BagApplyUpdateTerm := fun z => z |} Bs'))))
                                 end
                                 end.

Tactic Notation "make" "simple" "indexes" "using" constr(attrlist) :=
  match goal with
    | [ |- Sharpened (@BuildADT (UnConstrQueryStructure ?sch) _ _ _ _ )] =>
      let sch' := eval simpl in (qschemaSchemas sch) in
          makeIndex' sch' attrlist
                     ltac:(fun l =>
                             let index := fresh "Index" in
                             pose l as index;
                           eapply SharpenStep;
                           [eapply refineADT_BuildADT_Rep_default
                            with (AbsR := @DelegateToBag_AbsR sch index) |
                            compute [imap absConsDef absMethDef]; simpl ])
  end.
