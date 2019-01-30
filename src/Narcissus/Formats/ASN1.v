Require Import Coq.Lists.List.
Inductive ty : Set :=
| base : ty
| arr : list ty -> ty -> ty.

Fixpoint ty_Prop (t : ty) : Prop :=
  match t with
  | base => False
  | arr ts t' =>
    (fix tys_Prop (ts : list ty) :=
       match ts with
       | nil => True
       | t'' :: ts' => ty_Prop t'' /\ tys_Prop ts'
       end) ts /\ ty_Prop t'
  end.

Inductive ty_Prop' : ty -> Prop :=
| base_Prop : ty_Prop' base
| arr_Prop : forall ts t,
    Forall ty_Prop' ts -> ty_Prop' t ->
    ty_Prop' (arr ts t).

Require Import
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Numbers.BinNums
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts.

Inductive ASN1_Simple : Set :=
| ASN_Boolean : ASN1_Simple (* Universal 1 *)
| ASN_Null : ASN1_Simple (* Universal 5 *)
| ASN_Integer : ASN1_Simple (* Universal 2 *)
| ASN_Enum : (* Universal 10 *)
    list nat (* Codes *)
    -> ASN1_Simple
| ASN_BitString : ASN1_Simple (* Universal 3 *)
| ASN_OctetString : ASN1_Simple (* Universal 4 *)
| ASN_NumericString : ASN1_Simple (* Universal 18*)
| ASN_PrintableString : ASN1_Simple (* Universal 19 *)
| ASN_IA5String : ASN1_Simple. (* Universal 22 *)

Inductive ASN1_Simple_Modifier : Set :=
| ASN_Size_Fixed : nat -> ASN1_Simple_Modifier
| ASN_Size_Range : nat -> nat -> ASN1_Simple_Modifier
| ASN_None : ASN1_Simple_Modifier.

Definition ASN1_Simple_denote (desc : ASN1_Simple) : Set :=
  match desc with
  | ASN_Boolean => bool
  | ASN_Null => unit
  | ASN_Integer => Z
  | ASN_Enum n => Fin.t (List.length n)
  | ASN_BitString => list bool
  | ASN_OctetString => list (word 8)
  | ASN_NumericString => string
  | ASN_PrintableString => string
  | ASN_IA5String => string
  end.

Inductive ASN1_Structured : Set :=
| ASN_Sequence : list ASN1_Sequence_Element -> ASN1_Structured
| ASN_Choice : list ASN1_Type -> ASN1_Structured
| ASN_Sequence_Of : ASN1_Type -> ASN1_Structured

with ASN1_Sequence_Element : Set :=
     | Normal_Sequence_Element :
         ASN1_Type -> ASN1_Sequence_Element
     | Optional_Sequence_Element :
         ASN1_Type -> ASN1_Sequence_Element
     | Default_Sequence_Element :
         forall (desc : ASN1_Simple),
           ASN1_Simple_Modifier
           -> ASN1_Simple_denote desc
           -> ASN1_Sequence_Element

with ASN1_Type : Set :=
     | ASN_Simple : ASN1_Simple -> ASN1_Simple_Modifier -> ASN1_Type
     | ASN_Structured : ASN1_Structured -> ASN1_Type.

Coercion ASN_Structured : ASN1_Structured >-> ASN1_Type.

Definition ASN_Simple_UnModified (desc : ASN1_Simple) : ASN1_Type :=
  ASN_Simple desc ASN_None.
Coercion ASN_Simple_UnModified : ASN1_Simple >-> ASN1_Type.

Fixpoint ASN1_Structured_denote (desc : ASN1_Structured) : Set :=
  match desc with
  | ASN_Sequence l =>
    (fix ASN1_Sequence_denote (descs : list ASN1_Sequence_Element) {struct descs} : Set :=
       match descs with
       | Normal_Sequence_Element desc :: descs' =>
         (ASN1_Type_denote desc) * (ASN1_Sequence_denote descs')
       | Optional_Sequence_Element desc :: descs' =>
         option (ASN1_Type_denote desc) * (ASN1_Sequence_denote descs')
       | Default_Sequence_Element desc _ _ :: descs' =>
         (ASN1_Simple_denote desc) * (ASN1_Sequence_denote descs')
       | [ ] => unit
       end)%type l
  | ASN_Choice l =>
    (fix ASN1_Choice_denote (descs : list ASN1_Type) {struct descs} : Set :=
       match descs with
       | desc :: descs' => (ASN1_Type_denote desc) + (ASN1_Choice_denote descs')
       | [ ] => unit
       end)%type l
  | ASN_Sequence_Of desc' => list (ASN1_Type_denote desc')
  end

with ASN1_Type_denote (desc : ASN1_Type) : Set :=
       match desc with
       | ASN_Simple desc' mod => ASN1_Simple_denote desc'
       | ASN_Structured desc' => ASN1_Structured_denote desc'
       end.

Section ASN1_Format.

  Require Import
          Bedrock.Word.

  Require Import
          Fiat.Common.EnumType
          Fiat.Common.BoundedLookup
          Fiat.Narcissus.Formats.WordOpt
          Fiat.Narcissus.Formats.EnumOpt
          Fiat.Narcissus.Formats.Bool
          Fiat.Narcissus.Formats.NatOpt
          Fiat.Narcissus.Formats.FixStringOpt
          Fiat.Narcissus.Common.ComposeOpt.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Import Coq.Vectors.Vector.VectorNotations.

  Definition Tag_Classes :=
    ["Universal"; "Application"; "Context-Specific"; "Private"]%string.

  Definition Tag_Class_Codes :=
    [WO~0~0; WO~0~1; WO~1~0; WO~1~1].

  Definition Tag_Class := EnumType Tag_Classes.

  Definition ASN1_Format_Tag
           (tag : BoundedString Tag_Classes)
           (primitive : bool)
           (identifier : nat)
    : CacheFormat -> Comp (B * CacheFormat) :=
          format_enum Tag_Class_Codes (ibound (indexb tag))
    ThenC format_word (WS primitive WO)
    ThenC (If (NPeano.ltb identifier 31) Then
              format_nat 5 identifier
              Else (format_nat 31 identifier
              ThenC (* TODO: Put actual high-tag formating rule here. *)
              format_nat 5 identifier))
    DoneC.

  Definition ASN1_Format_Definite_Length
             (length : nat)
    : CacheFormat -> Comp (B * CacheFormat) :=
    If (NPeano.ltb length 127) Then
       format_nat 8 length
    Else
       (format_word WO~1 (* Set highest bit to 1 *)
       ThenC format_nat (S (NPeano.div (NPeano.log2 length) 8)) 7
       ThenC format_nat length (S (NPeano.div (NPeano.log2 length) 8) * 8))
       DoneC.

  Fixpoint ASN1_Format_Simple_DER
         (desc : ASN1_Simple)
  : ASN1_Simple_denote desc -> CacheFormat -> Comp (B * CacheFormat) :=
  match desc return
        ASN1_Simple_denote desc
        -> CacheFormat
        -> Comp (B * CacheFormat) with

  | ASN_Boolean =>
    fun data =>
          ASN1_Format_Tag ``"Universal" false 1
    ThenC ASN1_Format_Definite_Length 1
    ThenC format_word (if data then natToWord 8 255 else natToWord 8 0)
    DoneC

  | ASN_Null =>
    fun data =>
          ASN1_Format_Tag ``"Universal" false 5
    ThenC ASN1_Format_Definite_Length 0
    DoneC

  | ASN_Integer => fun data => format_word (natToWord 1 10) (* TODO *)
  | ASN_Enum n => fun data => format_word (natToWord 1 10) (* TODO *)
  | ASN_BitString => fun data => format_word (natToWord 1 10) (* TODO *)
  | ASN_OctetString => fun data => format_word (natToWord 1 10) (* TODO *)
  | ASN_NumericString => fun data => format_word (natToWord 1 10) (* TODO *)
  | ASN_PrintableString => fun data => format_word (natToWord 1 10) (* TODO *)
  | ASN_IA5String =>
    fun data =>
          ASN1_Format_Tag ``"Universal" false 22
    ThenC ASN1_Format_Definite_Length (String.length data)
    ThenC format_string data
    DoneC
  end.

End ASN1_Format.

Arguments ASN1_Format_Definite_Length _ _ / . (* Always simplify this format*)
Arguments ASN1_Format_Tag _ _ / . (* Always simplify this format*)

Section ASN1_Decoder_Example.

  Require Import
          Fiat.Narcissus.Stores.EmptyStore
          Fiat.Narcissus.Automation.Solver
          Fiat.Narcissus.BinLib.AlignedByteString
          Fiat.Narcissus.BinLib.AlignWord
          Fiat.Narcissus.BinLib.AlignedDecoders.

  Instance ByteStringQueueMonoid : Monoid ByteString :=
    ByteStringQueueMonoid.

  Example Simple_Format : ASN1_Simple :=
    ASN_IA5String.

  Ltac normalize_Compose Monoid :=
    eapply SetoidMorphisms.refine_refineEquiv_Proper;
    [ unfold flip;
      repeat first
             [ etransitivity; [ apply refineEquiv_compose_compose with (monoid := Monoid) | idtac ]
             | etransitivity; [ apply refineEquiv_compose_Done with (monoid := Monoid) | idtac ]
             | apply refineEquiv_under_compose with (monoid := Monoid) ];
      intros; first [reflexivity | higher_order_reflexivity]
    | reflexivity | ].

  Add Parametric Morphism
      (E B : Type) (monoid : Monoid B)
    : (@compose E B monoid)
      with signature
      (pointwise_relation _ (@refine (B * E)))
        ==> (pointwise_relation _ (@refine (B * E)))
        ==> (@eq E)
        ==> (@refine (B * E))
        as refine_compose.
  Proof.
    unfold pointwise_relation, compose, Bind2; intros.
    setoid_rewrite H; setoid_rewrite H0; reflexivity.
  Qed.

  Lemma refine_compose_compose
     : forall (E B : Type) (monoid : Monoid B) (format1 format2 format3 : E -> Comp (B * E)) (ctx : E),
      refine (((format1 ThenC format2) ThenC format3) ctx)
             ((format1 ThenC format2 ThenC format3) ctx).
  Proof.
    unfold pointwise_relation; intros.
    apply refineEquiv_compose_compose.
  Qed.

  Lemma refine_ThenC_beta_reduce
    : forall (E B : Type) (monoid : Monoid B) (format1 format2 : E -> Comp (B * E)) (ctx : E),
      refine ((format1 ThenC (fun ctx' => format2 ctx')) ctx)
             ((format1 ThenC format2) ctx).
  Proof.
    intros; reflexivity.
  Qed.

  Lemma refine_If_Then_Else_beta_reduce
    : forall (E B : Type) (monoid : Monoid B) (format1 format2 : E -> Comp (B * E)) (ctx : E) b,
      refine ((If b Then format1 Else format2) ctx)
             (If b Then format1 ctx Else format2 ctx).
  Proof.
    intros; destruct b; reflexivity.
  Qed.

  Corollary AlignedFormatNat
            {numBytes}
    : forall (n : nat) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 8)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_nat 8 (monoidUnit := ByteString_QueueMonoidOpt) n)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons _ (natToWord 8 n) _ v), ce')).
  Proof.
    unfold format_nat; cbv beta; intros.
    rewrite <- AlignedFormatChar; eauto.
    reflexivity.
  Qed.

  Definition Variational_Vector
             {numBytesT numBytesE}
             (b : bool)
             (vT : Vector.t Core.char numBytesT)
             (vE : Vector.t Core.char numBytesE)
    : Vector.t Core.char (If b Then numBytesT Else numBytesE) :=
    match b return
          Vector.t Core.char (If b Then numBytesT Else numBytesE)
    with
    | true => vT
    | false => vE
    end.

  Lemma AlignedFormat_If_Then_Else
            {numBytesT numBytesE}
    : forall (b : bool) ctx ctxT ctxE
             (vT : Vector.t Core.char numBytesT)
             (vE : Vector.t Core.char numBytesE)
             (format1 format2 : CacheFormat -> Comp (_ * CacheFormat)),
      (b = true
       -> refine (format1 ctx) (ret (build_aligned_ByteString vT, ctxT)))
      -> (b = false
          -> refine (format2 ctx) (ret (build_aligned_ByteString vE, ctxE)))
      -> refine (If b Then (format1 ctx) Else (format2 ctx))
                (ret (build_aligned_ByteString (Variational_Vector b vT vE)

                      , If b Then ctxT Else ctxE)).
  Proof.
    destruct b; simpl; intros; eauto.
  Qed.

  Lemma build_aligned_ByteString_id {B}
    : forall ctx : B,
      refine (ret (ByteString_id, ctx))
             (ret (build_aligned_ByteString (Vector.nil _), ctx)).
  Proof.
    intros; replace ByteString_id
             with (build_aligned_ByteString (Vector.nil _)).
    reflexivity.
    eapply ByteString_f_equal;
      instantiate (1 := eq_refl _); reflexivity.
  Qed.

  (* We'll restrict this example to strings with fewer than 127 bytes. *)
  Definition Simple_Format_OK
             (t : ASN1_Simple_denote Simple_Format)
    := NPeano.Nat.ltb (String.length t) 127 = true.

  Lemma If_Then_Else_format_correct
      {A B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P))
      (monoid : Monoid B)
      (predicate predicateT predicateE : A -> Prop)
      (predicate_rest : A -> B -> Prop)
      (proj : A -> bool)
      (ICompb : B -> bool)
      (formatT : A -> CacheFormat -> Comp (B * CacheFormat))
      (decodeT : B -> CacheDecode -> option (A * B * CacheDecode))
      (formatE : A -> CacheFormat -> Comp (B * CacheFormat))
      (decodeE : B -> CacheDecode -> option (A * B * CacheDecode))
      (decodeT_pf :
         cache_inv_Property P P_invT
         -> CorrectDecoder
              cache monoid predicateT predicate_rest
              formatT decodeT P)
      (decodeE_pf :
         cache_inv_Property P P_invE
         -> CorrectDecoder
              cache monoid predicateE predicate_rest
              formatE decodeE P)
      (ICompb_OKT : forall data bin env xenv ext,
          predicateT data
          -> formatT data env ↝ (bin, xenv)
          -> ICompb (mappend bin ext) = true)
      (ICompb_OKT' : forall data bin env xenv ext,
          ICompb bin = true
          -> decodeT bin env = Some (data, ext, xenv)
          -> proj data = true)
      (ICompb_OKE : forall data bin env xenv ext,
          predicateE data
          -> formatE data env ↝ (bin, xenv)
          -> ICompb (mappend bin ext) = false)
      (ICompb_OKE' : forall data bin env xenv ext,
          ICompb bin = false
          -> decodeE bin env = Some (data, ext, xenv)
          -> proj data = false)
      (predicateT_OK : forall a, proj a = true
                                 -> (predicate a
                                     <-> predicateT a))
      (predicateE_OK : forall a, proj a = false
                                 -> (predicate a
                                 <-> predicateE a))
  : CorrectDecoder
      cache monoid
      (fun a => predicate a)
      predicate_rest
      (fun (data : A) (ctx : CacheFormat) =>
         (If (proj data)
            Then (formatT data ctx)
            Else (formatE data ctx))
      )%comp
      (fun (b' : B) (env : CacheDecode) =>
         If ICompb b' Then
            decodeT b' env
            Else
            decodeE b' env
      ) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    specialize (predicateT_OK data).
    specialize (predicateE_OK data).
    destruct (proj data); simpl in com_pf.
    - erewrite ICompb_OKT; eauto.
      simpl; eapply decodeT_pf; intuition eauto.
      intuition eauto.
    - erewrite ICompb_OKE; eauto.
      simpl; eapply decodeE_pf; intuition eauto.
      intuition eauto.
  }
  { intros.
    destruct (ICompb bin) eqn : IComp_v ; simpl in *.
    - rewrite (ICompb_OKT' _ _ _ _ _ IComp_v H1).
      pose proof H1.
      eapply decodeT_pf in H1; simpl in *; intuition eauto.
      destruct_ex; eexists _, _; intuition eauto.
      eapply predicateT_OK; try eassumption.
      erewrite ICompb_OKT'; eauto.
    - rewrite (ICompb_OKE' _ _ _ _ _ IComp_v H1).
      pose proof H1.
      eapply decodeE_pf in H1; intuition eauto.
      destruct_ex; eexists _, _; intuition eauto.
      eapply predicateE_OK; try eassumption.
      erewrite ICompb_OKE'; eauto.

  }
Qed.

  Definition Correct_simple_formatr
    : { simple_formatr : _ &
                         forall (t : ASN1_Simple_denote Simple_Format),
                           Simple_Format_OK t
                           -> refine (ASN1_Format_Simple_DER Simple_Format t ())
                     (ret (simple_formatr t)) }.
  Proof.
    simpl; eexists; intros.
    unfold format_nat at 1, format_enum; simpl.
    eapply SetoidMorphisms.refine_refineEquiv_Proper;
      [ unfold flip;
        repeat first
               [ etransitivity; [ apply refineEquiv_compose_compose with (monoid := ByteStringQueueMonoid) | idtac ]
               | etransitivity; [ apply refineEquiv_compose_Done with (monoid := ByteStringQueueMonoid) | idtac ]
               | apply refineEquiv_under_compose with (monoid := ByteStringQueueMonoid) ];
        intros; higher_order_reflexivity
      | reflexivity | ];
      rewrite refine_ThenC_beta_reduce.
    rewrite (@CollapseFormatWord _ test_cache); simpl; eauto.
    rewrite !refine_ThenC_beta_reduce.
    rewrite (@CollapseFormatWord _ test_cache); simpl; eauto.
    rewrite !refine_ThenC_beta_reduce.
    eapply (@AlignedFormatChar test_cache); eauto.
    rewrite refine_If_Then_Else_ThenC.
    eapply AlignedFormat_If_Then_Else; intros.
    eapply (@AlignedFormatNat _).
    eapply (@format_string_aligned_ByteString test_cache); eauto.
    apply build_aligned_ByteString_id.
    congruence.
    Grab Existential Variables.
    exact ().
    apply Vector.nil.
  Defined.

  Arguments natToWord : simpl never.

  Definition byte_aligned_simple_formatr
             (t :  ASN1_Simple_denote Simple_Format)
    := Eval simpl in (projT1 Correct_simple_formatr t).

  Print byte_aligned_simple_formatr.

  Definition Simple_Format_decoder
    : CorrectDecoderFor Simple_Format_OK (ASN1_Format_Simple_DER Simple_Format).
  Proof.
    start_synthesizing_decoder.
    normalize_compose ByteStringQueueMonoid.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    simpl; omega.
    decode_step idtac.
    intros; eapply If_Then_Else_format_correct.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    intros; eapply String_decode_correct.
  Abort.
  (*intros.

    decode_step idtac.
    decode_step idtac.
    eauto.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    auto with arith.
    auto with arith.
    simpl.
    decode_step idtac.

    auto with arith.
    auto with arith.
    intros. setoid_rewrite refine_If_Then_Else_ThenC.
    intros.


    intros; eauto using FixedList_predicate_rest_True.
    synthesize_cache_invariant.
    cbv beta; optimize_decoder_impl.
  Defined.

Definition SimpleDecoderImpl
    := Eval simpl in (projT1 Simple_Format_decoder).

  Ltac rewrite_DecodeOpt2_fmap :=
    set_refine_evar;
    progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
    ?DecodeOpt2_fmap_if_bool;
    subst_refine_evar.

Definition ByteAligned_SimpleDecoderImpl {A}
           (f : _ -> A)
           n
  : {impl : _ & forall (v : Vector.t _ (3 + n)),
         f (fst SimpleDecoderImpl (build_aligned_ByteString v) ()) =
         impl v () }.
Proof.
  eexists _; intros.
  etransitivity.
  set_refine_evar; simpl.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  rewrite (@AlignedDecodeNat NoCache.test_cache).
  subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  rewrite (@AlignedDecode2Char NoCache.test_cache).
  subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  erewrite optimize_align_decode_list.
  rewrite Ifopt_Ifopt; simpl.
  etransitivity.
  eapply optimize_under_if_opt; simpl; intros.
  higher_order_reflexivity.
  reflexivity.
  Focus 2.
  clear H; intros.
  etransitivity.
  match goal with
    |- ?b = _ =>
    let b' := (eval pattern (build_aligned_ByteString v0) in b) in
    let b' := match b' with ?f _ => f end in
      eapply (@optimize_Guarded_Decode n0 _ 1 b')
  end.
  destruct n0 as [ | [ | ?] ]; intros; try omega.
  apply (@decode_word_aligned_ByteString_overflow NoCache.test_cache) with (sz := 1); auto.
  destruct n0 as [ | ?]; intros; try omega.
  higher_order_reflexivity.
  instantiate (1 := fun n1 v1 (cd0 : CacheDecode) =>
                      If NPeano.leb 1 n1 Then (Some ((Vector.hd (Guarded_Vector_split 1 n1 v1), @existT _ (Vector.t _) _ (Vector.tl (Guarded_Vector_split 1 n1 v1))), cd0)) Else None).
  simpl; find_if_inside; simpl; try reflexivity.
  pattern n0, v0; apply Vector.caseS; simpl; intros.
  unfold decode_word, WordOpt.decode_word.
  rewrite aligned_decode_char_eq; reflexivity.
  subst_refine_evar; higher_order_reflexivity.
  higher_order_reflexivity.
Defined.

Definition ByteAligned_SimpleDecoderImpl' n :=
  Eval simpl in (projT1 (ByteAligned_SimpleDecoderImpl id n)). *)

End ASN1_Decoder_Example.

Section ASN1_Example.
  (* Suppose a company owns several sales outlets linked to a central *)
  (* warehouse where stocks are maintained and deliveries start from. The *)
  (* company requires that its protocol have the following features: *)
  (* 1) the orders are collected locally at the sales outlets ; *)
  (* 2) they are transmitted to the warehouse, where the delivery *)
  (*    procedure should be managed ; *)
  (* 3) an account of the delivery must be sent back to the sales outlets *)
  (*    for following through the client's order. *)
  (* Example taken from: http://www.itu.int/en/ITU-T/asn1/Pages/introduction.aspx. *)


  (* Item-code ::= NumericString(SIZE (7)) *)
  Definition ItemCode : ASN1_Type :=
    ASN_Simple ASN_NumericString (ASN_Size_Fixed 7).

  (* Label ::= PrintableString(SIZE (1..30)) *)
  Definition Label : ASN1_Type :=
    ASN_Simple ASN_PrintableString (ASN_Size_Range 1 30).

  (* Quantity ::= CHOICE {
   unites        INTEGER,
   millimetres   INTEGER,
   milligrammes  INTEGER
} *)

  Definition Quantity : ASN1_Type :=
    ASN_Choice [ASN_Simple_UnModified ASN_Integer;
                  ASN_Simple_UnModified ASN_Integer;
                  ASN_Simple_UnModified ASN_Integer].

  (* Cents ::= INTEGER *)
  Definition Cents : ASN1_Type := ASN_Integer.

  (* Order-number ::= NumericString(SIZE (12)) *)
  Definition Order_Number : ASN1_Type :=
    ASN_Simple ASN_NumericString (ASN_Size_Fixed 12).

  (* Delivery-line ::= SEQUENCE {item      Item-code,
                            quantity  Quantity *)
  Definition Delivery_Line : ASN1_Type :=
    ASN_Sequence [Normal_Sequence_Element ItemCode;
                    Normal_Sequence_Element Quantity].

  (*Delivery-report ::= SEQUENCE {
  order-code  Order-number,
  delivery    SEQUENCE OF Delivery-line
} *)

  Definition Delivery_Report : ASN1_Type :=
    ASN_Sequence [Normal_Sequence_Element Order_Number;
                    Normal_Sequence_Element (ASN_Structured (ASN_Sequence_Of Delivery_Line))].

  (* Date ::= NumericString(SIZE (8)) -- MMDDYYYY *)
  Definition Date : ASN1_Type  :=
    ASN_Simple ASN_NumericString (ASN_Size_Fixed 8).

  (* default-country PrintableString ::= "France" *)
  Definition Default_Country : ASN1_Type_denote ASN_PrintableString := "France"%string.


  (* Client ::= SEQUENCE {
  name      PrintableString(SIZE (1..20)),
  street    PrintableString(SIZE (1..50)) OPTIONAL,
  postcode  NumericString(SIZE (5)),
  town      PrintableString(SIZE (1..30)),
  country   PrintableString(SIZE (1..20)) DEFAULT default-country
  } *)
  Definition Client : ASN1_Type :=
    ASN_Sequence [Normal_Sequence_Element (ASN_Simple ASN_PrintableString (ASN_Size_Range 1 20));
                    Optional_Sequence_Element (ASN_Simple ASN_PrintableString (ASN_Size_Range 1 50));
                    Normal_Sequence_Element (ASN_Simple ASN_NumericString (ASN_Size_Fixed 5));
                    Normal_Sequence_Element (ASN_Simple ASN_PrintableString (ASN_Size_Range 1 30));
                    Default_Sequence_Element ASN_PrintableString (ASN_Size_Range 1 20) Default_Country].

  (* Card-type ::= ENUMERATED {
  cb(0), visa(1), eurocard(2), diners(3), american-express(4)} *)
  Definition Card_Type : ASN1_Type :=
    ASN_Enum [ 0; 1; 2; 3; 4].

  (* Credit-card ::= SEQUENCE {
  type         Card-type,
  number       NumericString(SIZE (20)),
  expiry-date  NumericString(SIZE (6))-- MMYYYY --
  }*)
  Definition Credit_Card : ASN1_Type :=
    ASN_Sequence [Normal_Sequence_Element Card_Type;
                    Normal_Sequence_Element (ASN_Simple ASN_NumericString (ASN_Size_Fixed 20));
                    Normal_Sequence_Element (ASN_Simple ASN_NumericString (ASN_Size_Fixed 6))
                 ].

  (* Payment-method ::= CHOICE {
  check        NumericString(SIZE (15)),
  credit-card Credit-card,
  cash         NULL
} *)
  Definition Payment_Method : ASN1_Type :=
    ASN_Choice [ASN_Simple ASN_NumericString (ASN_Size_Fixed 8);
                  Credit_Card;
                  ASN_Simple ASN_Null ASN_None].

  (* Order-header ::= SEQUENCE {
  number   Order-number,
  date     Date,
  client   Client,
  payment  Payment-method
} *)
  Definition Order_Header : ASN1_Type :=
    ASN_Sequence [Normal_Sequence_Element Order_Number;
                    Normal_Sequence_Element Date;
                    Normal_Sequence_Element Client;
                    Normal_Sequence_Element Payment_Method].

  (* Item-code ::= NumericString(SIZE (7)) *)
  Definition Item_Code : ASN1_Type  :=
    ASN_Simple ASN_NumericString (ASN_Size_Fixed 7).

  (* Order-line ::= SEQUENCE {
  item-code  Item-code,
  label      Label,
  quantity   Quantity,
  price      Cents
} *)
  Definition Order_Line : ASN1_Type :=
    ASN_Sequence [Normal_Sequence_Element Item_Code;
                    Normal_Sequence_Element Label;
                    Normal_Sequence_Element Quantity;
                    Normal_Sequence_Element Cents].


  (* Order ::= SEQUENCE {header  Order-header,
                    items   SEQUENCE OF Order-line
} *)
  Definition Order : ASN1_Type :=
    ASN_Sequence [Normal_Sequence_Element Order_Header;
                    Normal_Sequence_Element (ASN_Sequence_Of Order_Line)].

  (*
PDU ::= CHOICE {
  question
    CHOICE {question1  Order,
            question2  Item-code,
            question3  Order-number,
            ...},
  answer
    CHOICE {answer1  Delivery-report,
            answer2  Quantity,
            answer3  Delivery-report,
            ...}
} *)

  Definition PDU : ASN1_Type :=
    ASN_Choice [ASN_Structured (ASN_Choice [Order; Item_Code; Order_Number]);
                  ASN_Structured (ASN_Choice [Delivery_Report; Quantity; Delivery_Report])
               ].

End ASN1_Example.
