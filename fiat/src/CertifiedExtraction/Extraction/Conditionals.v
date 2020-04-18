Require Import
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.Basics.

Lemma isTrueExpr_is_true:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (wrap (bool2w true)) st' -> is_true st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma isTrueExpr_is_false:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (wrap (bool2w false)) st' -> is_false st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma is_true_isTrueExpr:
  forall {av} {gallinaTest : bool} {tmp : StringMap.key} (st' : State av),
    is_true st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (wrap (bool2w gallinaTest)) st' ->
    gallinaTest = true.
Proof.
  unfold isTrueExpr, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Lemma is_false_isTrueExpr:
  forall {av} {gallinaTest : bool} {tmp : StringMap.key} (st' : State av),
    is_false st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (wrap (bool2w gallinaTest)) st' ->
    gallinaTest = false.
Proof.
  unfold isTrueExpr, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Ltac facade_if_helper :=
  match goal with
  | [ H: is_true ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st |- _ ] => learn (is_true_isTrueExpr H H')
  | [ H: is_false ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st |- _ ] => learn (is_false_isTrueExpr H H')
  | _ => solve [eauto 3 using isTrueExpr_is_false, isTrueExpr_is_true with SameValues_db]
  | _ => solve [eauto using isTrueExpr_is_false, isTrueExpr_is_true with SameValues_db]
  end.

Lemma CompileIf :
  forall {av A} k tmp (gallinaTest: bool) (gallinaT gallinaF: Comp A) facadeTest facadeT facadeF
    env (ext: StringMap.t (Value av)) tenv tenv',
    tmp ∉ ext ->
    NotInTelescope tmp tenv ->
    {{ tenv }}
      facadeTest
    {{ [[`tmp ->> (bool2w gallinaTest) as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[`tmp ->> (bool2w gallinaTest) as _]]::tenv }}
      facadeT
    {{ [[`tmp ->> (bool2w gallinaTest) as _]]::[[k ~~> gallinaT as v]]::tenv' v }} ∪ {{ ext }} // env ->
    {{ [[`tmp ->> (bool2w gallinaTest) as _]]::tenv }}
      facadeF
    {{ [[`tmp ->> (bool2w gallinaTest) as _]]::[[k ~~> gallinaF as v]]::tenv' v }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq facadeTest (DFacade.If (isTrueExpr tmp) facadeT facadeF))
    {{ [[k ~~> if gallinaTest then gallinaT else gallinaF as v]]::tenv' v }} ∪ {{ ext }} // env.
Proof.
  intros; hoare.
  repeat (SameValues_Facade_t_step || facade_if_helper).
Qed.
