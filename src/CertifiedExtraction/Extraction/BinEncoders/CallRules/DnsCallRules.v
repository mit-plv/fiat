Require Export
        Fiat.CertifiedExtraction.Extraction.Extraction.

Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties.

Require Import
        Coq.Program.Program
        Coq.Lists.List.

Unset Implicit Arguments.

Lemma CompileCallAllocEMap:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap ->> DnsMap.EMap.empty DnsMap.position_t as _]]::tenv }}
      pNext
    {{ [[ ` veMap ->> DnsMap.EMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap ->> DnsMap.EMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallAllocDMap:
  forall (vtmp veMap: string) (tenv tenv' : Telescope ADTValue)
    ext env pNext fAllocCache,
    {{ [[ ` veMap ->> DnsMap.DMap.empty (list DnsMap.word_t) as _]]::tenv }}
      pNext
    {{ [[ ` veMap ->> DnsMap.DMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      Seq (Call vtmp fAllocCache [veMap]) pNext
    {{ [[ ` veMap ->> DnsMap.DMap.empty _ as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare.
Admitted.

Lemma CompileCallListResourceLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : FixList.FixList 16 resource_t)
    flength tenv',
    TelEq ext tenv ([[`vlst ->> `lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg flength [vlst]
    {{ [[ ` varg ->> FixList.FixList_getlength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Lemma CompileCallListQuestionLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : FixList.FixList 16 question_t)
    flength tenv',
    TelEq ext tenv ([[`vlst ->> `lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg flength [vlst]
    {{ [[ ` varg ->> FixList.FixList_getlength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Lemma CompileCallGetResourceType:
  forall (vtmp vresource vtype : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (resource : resource_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vresource ->> resource as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 1)) (Call vtype fget [vtmp; vresource])
    {{ [[ ` vtype ->> FixInt_of_type (rtype resource) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Lemma CompileCallGetQuestionType:
  forall (vtmp vquestion vtype : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (question : question_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vquestion ->> question as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 1)) (Call vtype fget [vtmp; vquestion])
    {{ [[ ` vtype ->> FixInt_of_type (qtype question) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Ltac _packet_encodeType :=
  may_alloc_head;
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | Cons _ (ret (FixInt_of_type (_ ?question))) _ =>
              let vtmp := gensym "tmp" in
              let vquestion := find_name_in_precondition question in
              compile_do_use_transitivity_to_handle_head_separately;
              [ (eapply (CompileCallGetQuestionType vtmp vquestion) ||
                 eapply (CompileCallGetResourceType vtmp vquestion))
              | ]
            end).

Lemma CompileCallGetQuestionClass: (* FIXME merge into a single lemma once encoding of questions and answers is decided upon *)
  forall (vtmp vquestion vclass : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (question : question_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vquestion ->> question as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 2)) (Call vclass fget [vtmp; vquestion])
    {{ [[ ` vclass ->> FixInt_of_class (qclass question) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Lemma CompileCallGetResourceClass: (* FIXME merge into a single lemma once encoding of questions and answers is decided upon *)
  forall (vtmp vresource vclass : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (resource : resource_t)
    fget tenv',
    vtmp ∉ ext ->
    NotInTelescope vtmp tenv ->
    TelEq ext tenv ([[`vresource ->> resource as _]]::tenv') ->
    {{ tenv }}
      Seq (Assign vtmp (Const 2)) (Call vclass fget [vtmp; vresource])
    {{ [[ ` vclass ->> FixInt_of_class (rclass resource) as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? Teq.
  hoare; eauto using CompileConstant.
  setoid_rewrite Teq.
Admitted.

Ltac _packet_encodeClass :=
  may_alloc_head;
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | Cons _ (ret (FixInt_of_class (_ ?question))) _ =>
              let vtmp := gensym "tmp" in
              let vquestion := find_name_in_precondition question in
              compile_do_use_transitivity_to_handle_head_separately;
              [ ( eapply (CompileCallGetQuestionClass vtmp vquestion) ||
                  eapply (CompileCallGetResourceClass vtmp vquestion) )
              | ]
            end).

Lemma CompileCallDeallocQuestion: (* FIXME merge with other lemmas regarding deallocation of tuple-encoded structures *)
  forall (vtmp vquestion: string) (q: question_t) (tenv: Telescope ADTValue)
    ext env fDealloc,
    NotInTelescope vquestion tenv ->
    {{ [[ ` vquestion ->> q as _]]::tenv }}
      (Call vtmp fDealloc [vquestion])
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Ltac _compile_CallDeallocQuestion :=
  let vtmp := gensym "tmp" in
  eapply (CompileCallDeallocQuestion vtmp).

Lemma CompileCallDeallocResource: (* FIXME merge with other lemmas regarding deallocation of tuple-encoded structures *)
  forall (vtmp vresource: string) (q: resource_t) (tenv: Telescope ADTValue)
    ext env fDealloc,
    NotInTelescope vresource tenv ->
    {{ [[ ` vresource ->> q as _]]::tenv }}
      (Call vtmp fDealloc [vresource])
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
Admitted.

Ltac _compile_CallDeallocResource :=
  let vtmp := gensym "tmp" in
  eapply (CompileCallDeallocResource vtmp).

Ltac _compile_CallAllocEMap :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocEMap vtmp).

Ltac _compile_CallAllocDMap :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocDMap vtmp).
