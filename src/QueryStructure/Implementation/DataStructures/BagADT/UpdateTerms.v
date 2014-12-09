Require Import
        Coq.Lists.List Coq.Program.Program Coq.Bool.Bool
        ADTSynthesis.Common.ilist
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.QueryStructure.Specification.Representation.Heading
        ADTSynthesis.QueryStructure.Specification.Representation.Tuple
        ADTSynthesis.QueryStructure.Specification.Representation.Notations.

(* Definitions for building BagADT update terms.*)

(* Implements a update term for [heading] as a list of
   values given a list of attributes. *)
Fixpoint BuildUpdateTerm {heading : Heading}
         (indices : list (@Attributes heading))
: Type :=
  match indices with
    | [] => unit
    | idx :: indices' => prod (@Tuple heading -> Domain heading idx)
                              (BuildIndexSearchTerm indices')
  end.

(* Implements a matcher function for a search term built using [BuildSearchTerm]. *)
Fixpoint MatchIndexSearchTerm {heading}
         (indices : list (@Attributes heading))
: BuildIndexSearchTerm indices  -> @Tuple heading -> @Tuple heading :=
  match indices return
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
