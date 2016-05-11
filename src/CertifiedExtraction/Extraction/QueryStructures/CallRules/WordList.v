Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.

Lemma CompileWordList_pop:
  forall (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) tenv ext
    (fpop : GLabelMap.key) head (tail : list W),
    vlst <> vhead ->
    vhead ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) (head :: tail)) ->
    Lifted_not_mapsto_adt ext tenv vhead ->
    GLabelMap.MapsTo fpop (Axiomatic QsADTs.WordListADTSpec.Pop) env ->
    {{ tenv }}
      Call vhead fpop (vlst :: nil)
    {{ [[`vhead ->> head as _]]::[[(NTSome vlst (H := WrapInstance (H := QS_WrapWordList))) ->> tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileWordList_new:
  forall (vlst : StringMap.key) (env : GLabelMap.t (FuncSpec QsADTs.ADTValue)) tenv ext
    (fnew : GLabelMap.key),
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    GLabelMap.MapsTo fnew (Axiomatic QsADTs.WordListADTSpec.New) env ->
    {{ tenv }}
      Call vlst fnew (nil)
    {{ [[(NTSome vlst (H := WrapInstance (H := QS_WrapWordList))) ->> @nil W as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
  change (ADT (QsADTs.WordList [])) with (wrap (FacadeWrapper := WrapInstance (H := @QS_WrapWordList)) []).
  facade_eauto.
Qed.


Lemma CompileWordList_push :
  forall vret vhd vlst fpointer (env: Env QsADTs.ADTValue) ext tenv
    h (t: list W),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.WordListADTSpec.Push) env ->
    Lifted_MapsTo ext tenv vhd (wrap h) ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) t) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    vret <> vlst ->
    vret <> vhd ->
    vhd <> vlst ->
    vhd ∉ ext ->
    vlst ∉ ext ->
    vret ∉ ext ->
    {{ tenv }}
      Call vret fpointer (vlst :: vhd :: nil)
    {{ [[ `vret ->> (Word.natToWord 32 0) as _ ]] :: [[ NTSome (H := WrapInstance (H := QS_WrapWordList)) vlst ->> h :: t as _ ]] :: DropName vlst (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; congruence.
Qed.

Lemma CompileWordList_push_spec :
  forall vtmp vhd vlst fpointer (env: Env QsADTs.ADTValue) ext tenv
    h (t: list W),
    GLabelMap.MapsTo fpointer (Axiomatic QsADTs.WordListADTSpec.Push) env ->
    PreconditionSet tenv ext [[[vtmp;vhd;vlst]]] ->
    {{ [[ NTSome (H := WrapInstance (H := QS_WrapWordList)) vlst ->> t as _ ]] :: [[ `vhd ->> h as _ ]] :: tenv }}
      Call vtmp fpointer (vlst :: vhd :: nil)
    {{ [[ NTSome (H := WrapInstance (H := QS_WrapWordList)) vlst ->> h :: t as _ ]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R. hoare. PreconditionSet_t.
  apply generalized CompileWordList_push; repeat (compile_do_side_conditions || Lifted_t).
  apply CompileDeallocW_discretely; try compile_do_side_conditions; apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  move_to_front vhd; apply CompileDeallocW_discretely; try compile_do_side_conditions; apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.
Qed.
