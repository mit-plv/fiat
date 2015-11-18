Require Export
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.
Require Export
        CertifiedExtraction.Random.
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
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [[`"out" <~~ post as _]]::Nil }} ∪ {{ ∅ }} // (env: Env carrier)) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'    '#env'        env '//'    '#carrier'    carrier").

Notation "'ParametricExtraction' '#vars' x .. y '#program' post '#arguments' pre '#env' env" :=
  (sigT (fun prog => (forall x, .. (forall y, {{ pre }} prog {{ [[`"out" <~~ post as _]]::Nil }} ∪ {{ ∅ }} // env) ..)))
    (at level 200,
     x binder,
     y binder,
     format "'ParametricExtraction' '//'    '#vars'       x .. y '//'    '#program'     post '//'    '#arguments'  pre '//'    '#env'         env").

Notation "'ParametricExtraction' '#program' post '#env' env" :=
  (sigT (fun prog => {{ Nil }} prog {{ [[`"out" <~~ post as _]]::Nil }} ∪ {{ ∅ }} // env))
    (at level 200,
     format "'ParametricExtraction' '//'    '#program'  post '//'    '#env'      env").

Notation "'FacadeMethod' '#prog' prog '#requires' pre '#ensures' post '#ext' ext '#env' env" :=
  ({{ pre }} prog {{ post }} ∪ {{ ext }} // env)
    (at level 200,
     format "'FacadeMethod' '//'    '#prog'      prog '//'    '#requires'  pre '//'    '#ensures'   post '//'    '#ext'       ext '//'    '#env'       env").

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