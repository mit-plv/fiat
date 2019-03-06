Require Export
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.
Require Export
        CertifiedExtraction.Benchmarks.Any.
Require Export
        Coq.NArith.NArith
        Coq.Program.Basics.

Global Opaque DummyArgument.
Global Opaque Word.wordToNat.
Global Opaque Word.natToWord.
Global Opaque nat_as_constant nat_as_word string_as_var.

Global Arguments wrap : simpl never.
Global Opaque Word.weqb Word.NToWord.

Global Arguments map : simpl nomatch.
Global Arguments Word.NToWord {sz} n.

Global Open Scope list_scope.

Definition extract_facade := proj1_sig.

Notation "'ParametricExtraction' '#vars' x .. y '#program' post '#arguments' pre '#env' env '#carrier' carrier" :=
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [[`"out" ~~> post as _]]::Nil }} ∪ {{ ∅ }} // (env: Env carrier)) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'    '#env'        env '//'    '#carrier'    carrier") : microbenchmarks_scope.

Notation "'ParametricExtraction' '#vars' x .. y '#program' post '#arguments' pre '#env' env" :=
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [[`"out" ~~> post as _]]::Nil }} ∪ {{ ∅ }} // env) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'    '#env'         env") : microbenchmarks_scope.

Notation "'ParametricExtraction' '#program' post '#env' env" :=
  (sigT (fun prog => {{ Nil }} prog {{ [[`"out" ~~> post as _]]::Nil }} ∪ {{ ∅ }} // env))
    (at level 200,
     format "'ParametricExtraction' '//'    '#program'  post '//'    '#env'      env") : microbenchmarks_scope.

(* Notation "'FacadeMethod' '#prog' prog '#requires' pre '#ensures' post '#ext' ext '#env' env" := *)
(*   ({{ pre }} prog {{ post }} ∪ {{ ext }} // env) *)
(*     (at level 200, *)
(*      format "'FacadeMethod' '//'    '#prog'      prog '//'    '#requires'  pre '//'    '#ensures'   post '//'    '#ext'       ext '//'    '#env'       env"). *)

Lemma List_rev_as_fold_generalized :
  forall A l init,
    @List.rev A l ++ init = fold_left (fun acc x => x :: acc) l init.
Proof.
  induction l; simpl; intros; [ | rewrite <- IHl, <- app_assoc ]; reflexivity.
Qed.

Lemma List_rev_as_fold :
  forall A l, @List.rev A l = fold_left (fun acc x => x :: acc) l nil.
Proof.
  intros; rewrite <- (List_rev_as_fold_generalized _ nil), app_nil_r; reflexivity.
Qed.

Fixpoint Inb {sz} (w: @Word.word sz) seq :=
  match seq with
  | nil => false
  | cons w' tl => if Word.weqb w w' then true else Inb w tl
  end.

Definition Microbenchmarks_Carrier : Type := sum (list W) (list (list W)).
Notation W0 := (Word.natToWord 32 0).
Notation W1 := (Word.natToWord 32 1).
Notation W7 := (Word.natToWord 32 7).
Notation "x ≺ y" := (Word.wlt_dec x y) (at level 10).
Notation "x ⊕ y" := (Word.wplus x y) (at level 10).
Notation "x ⊖ y" := (Word.wminus x y) (at level 10).
Notation "x ⊗ y" := (Word.wmult x y) (at level 10).
Notation "x == y" := (Word.weqb x y) (at level 10).

Definition Microbenchmarks_Env : Env Microbenchmarks_Carrier :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FAny)
    ### ("list[W]", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("list[W]", "push") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("list[W]", "pop") ->> (Axiomatic (List_pop W))
    ### ("list[W]", "delete") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("list[W]", "empty?") ->> (Axiomatic (List_empty W))
    ### ("list[list[W]]", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list (list W)) nil))
    ### ("list[list[W]]", "push") ->> (Axiomatic (FacadeImplementationOfMutation_ADT (list W) (list (list W)) cons))
    ### ("list[list[W]]", "pop") ->> (Axiomatic (List_pop (list W)))
    ### ("list[list[W]]", "delete") ->> (Axiomatic (FacadeImplementationOfDestructor (list (list W))))
    ### ("list[list[W]]", "empty?") ->> (Axiomatic (List_empty (list W))).

Global Open Scope microbenchmarks_scope.