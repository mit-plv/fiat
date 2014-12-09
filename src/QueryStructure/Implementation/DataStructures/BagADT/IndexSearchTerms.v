Require Import
        Coq.Lists.List Coq.Program.Program Coq.Bool.Bool
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
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

(* Definitions for building BagADT search terms using decideable equalities
   over named attributes.*)

(* Implements a Search Term for heading as a list of optional key
   values given a list of attributes. *)
Fixpoint BuildIndexSearchTerm {heading : Heading}
         (indices : list (@Attributes heading))
: Type :=
  match indices with
    | [] => (@Tuple heading -> bool)
    | idx :: indices' => prod (option (Domain heading idx)) (BuildIndexSearchTerm indices')
  end.

(* Implements a matcher function for a search term built using [BuildSearchTerm]. *)
Fixpoint MatchIndexSearchTerm {heading}
         (indices : list (@Attributes heading))
         (eq_dec_indices : ilist (fun attr => Query_eq (Domain heading attr)) indices)
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
                (if (A_eq_dec (Query_eq := ilist_hd eq_dec_indices) k (tup index))
                 then true else false)
                  && (H index' tup)
              | (None, index') => H index' tup
            end) (MatchIndexSearchTerm (ilist_tl eq_dec_indices))
  end eq_dec_indices.

Tactic Notation "build" "single" "index":=
repeat match goal with
         | [ |- ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns))) []] =>
           econstructor 2
         | [ |- ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
                      (?sch :: ?sch') ]=> econstructor 1; [ econstructor | ]
         | [ |- ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns))) ?sch] =>
           simpl sch
       end.

Ltac build_index_list heading As k :=
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
  end.

Ltac makeIndex' NamedSchemas IndexKeys k :=
  match NamedSchemas  with
    | nil => k (inil (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))))
    | cons ?ns ?NamedSchemas' =>
      match IndexKeys with
          | cons ?ik ?IndexKeys' =>
            build_index_list (schemaHeading (relSchema ns)) ik
                             ltac:(fun st =>
                                     makeIndex' NamedSchemas' IndexKeys'
                                                   ltac:(fun Bs' => k (icons ns
                                                                             {| BagMatchSearchTerm := MatchIndexSearchTerm st;
                                                                                BagApplyUpdateTerm := fun z => z |} Bs')))
      end
  end.

Require Import   ADTSynthesis.ADTRefinement.BuildADTRefinements.HoneRepresentation.
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
