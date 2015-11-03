Require Import
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.ExtendedLemmas.

Lemma isTrueExpr_is_true:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (bool2val true) st' -> is_true st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, bool2val, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma isTrueExpr_is_false:
  forall {av} (tmp : string) (st' : State av),
    StringMap.MapsTo tmp (bool2val false) st' -> is_false st' (isTrueExpr tmp).
Proof.
  unfold isTrueExpr, bool2val, is_true, is_false, eval_bool; simpl;
  SameValues_Facade_t.
Qed.

Lemma is_true_isTrueExpr:
  forall {av} (gallinaTest : bool) (tmp : StringMap.key) (st' : State av),
    is_true st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (bool2val gallinaTest) st' ->
    gallinaTest = true.
Proof.
  unfold isTrueExpr, bool2val, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Lemma is_false_isTrueExpr:
  forall {av} (gallinaTest : bool) (tmp : StringMap.key) (st' : State av),
    is_false st' (isTrueExpr tmp) ->
    StringMap.MapsTo tmp (bool2val gallinaTest) st' ->
    gallinaTest = false.
Proof.
  unfold isTrueExpr, bool2val, bool2w, is_true, is_false, eval_bool; simpl;
  destruct gallinaTest; SameValues_Facade_t.
Qed.

Ltac facade_if_helper :=
  match goal with
  | [ H: is_true ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (bool2val ?test) ?st |- _ ] => learn (is_true_isTrueExpr H H')
  | [ H: is_false ?st (isTrueExpr ?k), H': StringMap.MapsTo ?k (bool2val ?test) ?st |- _ ] => learn (is_false_isTrueExpr H H')
  | _ => solve [eauto using isTrueExpr_is_false, isTrueExpr_is_true with SameValues_db]
  end.

Lemma CompileIf :
  forall {av} k (gallinaTest: bool) gallinaT gallinaF tmp facadeTest facadeT facadeF env (ext: StringMap.t (Value av)) tenv,
    tmp ∉ ext ->
    NotInTelescope tmp tenv ->
    {{ tenv }}
      facadeTest
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::tenv }}
      facadeT
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaT as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::tenv }}
      facadeF
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaF as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq facadeTest (If (isTrueExpr tmp) facadeT facadeF))
    {{ [[`k <~~ if gallinaTest then gallinaT else gallinaF as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_if_helper).
Qed.

Lemma CompileIf_InPlace :
  forall {av} k (gallinaTest: bool) oldK gallinaT gallinaF tmp facadeTest facadeT facadeF env (ext: StringMap.t (Value av)) tenv,
    tmp ∉ ext ->
    NotInTelescope tmp tenv ->
    {{ [[`k <~~ oldK as kk]] :: tenv }}
      facadeTest
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ oldK as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ oldK as _]] :: tenv }}
      facadeT
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaT as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ oldK as _]] :: tenv }}
      facadeF
    {{ [[tmp <-- (bool2val gallinaTest) as _]]::[[`k <~~ gallinaF as _]]::tenv }} ∪ {{ ext }} // env ->
    {{ [[`k <~~ oldK as _]] :: tenv }}
      (Seq facadeTest (DFacade.If (isTrueExpr tmp) facadeT facadeF))
    {{ [[`k <~~ if gallinaTest then gallinaT else gallinaF as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat match goal with
         | _ => SameValues_Facade_t_step
         | _ => facade_if_helper
         end.
Qed.
