Require Import
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Numbers.BinNums
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts.

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
  | ASN_Enum n => Fin.t (length n)
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
          Fiat.BinEncoders.Env.Lib2.WordOpt
          Fiat.BinEncoders.Env.Lib2.EnumOpt
          Fiat.BinEncoders.Env.Lib2.Bool
          Fiat.BinEncoders.Env.Lib2.NatOpt
          Fiat.BinEncoders.Env.Lib2.FixStringOpt
          Fiat.BinEncoders.Env.Common.ComposeOpt.
  
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : QueueTransformerOpt transformer bool}.

  Import Coq.Vectors.VectorDef.VectorNotations.
  
  Definition Tag_Classes :=
    ["Universal"; "Application"; "Context-Specific"; "Private"]%string.
  
  Definition Tag_Class_Codes :=
    [WO~0~0; WO~0~1; WO~1~0; WO~1~1].

  Definition Tag_Class := EnumType Tag_Classes.
  
  Definition ASN1_Format_Tag
           (tag : Tag_Class)
           (primitive : bool)
           (identifier : nat)
    : CacheEncode -> Comp (B * CacheEncode) :=
          encode_enum_Spec Tag_Class_Codes tag
    ThenC encode_word_Spec (WS primitive WO) 
    ThenC (If (NPeano.ltb identifier 31) Then
              encode_nat_Spec 5 identifier
              Else (encode_nat_Spec 31 identifier
              ThenC (* TODO: Put actual high-tag formating rule here. *)
              encode_nat_Spec 5 identifier))
    DoneC. 
  
  Definition ASN1_Format_Definite_Length
             (length : nat)
    : CacheEncode -> Comp (B * CacheEncode) :=
    If (NPeano.ltb length 127) Then
       encode_nat_Spec 8 length
    Else
       (encode_word_Spec WO~1 (* Set highest bit to 1 *)
       ThenC encode_nat_Spec (S (NPeano.div (NPeano.log2 length) 8)) 7
       ThenC encode_nat_Spec length (S (NPeano.div (NPeano.log2 length) 8) * 8))
       DoneC.
  
  Fixpoint ASN1_Format_Simple_DER
         (desc : ASN1_Simple)
  : ASN1_Simple_denote desc -> CacheEncode -> Comp (B * CacheEncode) :=
  match desc return
        ASN1_Simple_denote desc
        -> CacheEncode
        -> Comp (B * CacheEncode) with
  | ASN_Boolean =>
    fun data =>
      ASN1_Format_Tag Fin.F1 false 1
    ThenC ASN1_Format_Definite_Length 1
    ThenC encode_word_Spec (if data then natToWord 8 255 else natToWord 8 0)
    DoneC

  | ASN_Null =>
    fun data =>
      ASN1_Format_Tag Fin.F1 false 5
    ThenC ASN1_Format_Definite_Length 0
    DoneC
    
  | ASN_Integer => fun data => encode_word_Spec (natToWord 1 10) (* TODO *)
  | ASN_Enum n => fun data => encode_word_Spec (natToWord 1 10) (* TODO *)
  | ASN_BitString => fun data => encode_word_Spec (natToWord 1 10) (* TODO *)
  | ASN_OctetString => fun data => encode_word_Spec (natToWord 1 10) (* TODO *)
  | ASN_NumericString => fun data => encode_word_Spec (natToWord 1 10) (* TODO *)
  | ASN_PrintableString => fun data => encode_word_Spec (natToWord 1 10) (* TODO *)
  | ASN_IA5String =>
    fun data => 
      ASN1_Format_Tag Fin.F1 false 22
    ThenC ASN1_Format_Definite_Length (String.length data)
    ThenC encode_string_Spec data                   
    DoneC
  end.

End ASN1_Format.

Arguments ASN1_Format_Definite_Length _ _ / . (* Always simplify this format*)
Arguments ASN1_Format_Tag _ _ / . (* Always simplify this format*)

Section ASN1_Decoder_Example.

  Require Import
          Fiat.BinEncoders.Env.Lib2.NoCache
          Fiat.BinEncoders.Env.Automation.Solver
          Fiat.BinEncoders.Env.BinLib.AlignedByteString
          Fiat.BinEncoders.Env.BinLib.AlignWord
          Fiat.BinEncoders.Env.BinLib.AlignedDecoders.
  
  Instance ByteStringQueueTransformer : Transformer ByteString :=
    ByteStringQueueTransformer.
  
  Example Simple_Format : ASN1_Simple :=
    ASN_IA5String.

  Ltac normalize_Compose Transformer :=
    eapply SetoidMorphisms.refine_refineEquiv_Proper;
    [ unfold flip;
      repeat first
             [ etransitivity; [ apply refineEquiv_compose_compose with (transformer := Transformer) | idtac ]
             | etransitivity; [ apply refineEquiv_compose_Done with (transformer := Transformer) | idtac ]
             | apply refineEquiv_under_compose with (transformer := Transformer) ];
      intros; first [reflexivity | higher_order_reflexivity]
    | reflexivity | ].
  
  Add Parametric Morphism
      (E B : Type) (transformer : Transformer B)
    : (@compose E B transformer)
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
     : forall (E B : Type) (transformer : Transformer B) (encode1 encode2 encode3 : E -> Comp (B * E)) (ctx : E),
      refine (((encode1 ThenC encode2) ThenC encode3) ctx) ((encode1 ThenC encode2 ThenC encode3) ctx).
  Proof.
    unfold pointwise_relation; intros.
    apply refineEquiv_compose_compose.
  Qed.

  Lemma refine_ThenC_beta_reduce
    : forall (E B : Type) (transformer : Transformer B) (encode1 encode2 : E -> Comp (B * E)) (ctx : E),
      refine ((encode1 ThenC (fun ctx' => encode2 ctx')) ctx)
             ((encode1 ThenC encode2) ctx).
  Proof.
    intros; reflexivity.
  Qed.

  Lemma refine_If_Then_Else_beta_reduce
    : forall (E B : Type) (transformer : Transformer B) (encode1 encode2 : E -> Comp (B * E)) (ctx : E) b,
      refine ((If b Then encode1 Else encode2) ctx)
             (If b Then encode1 ctx Else encode2 ctx).
  Proof.
    intros; destruct b; reflexivity.
  Qed.

  Lemma refine_If_Then_Else_ThenC
    : forall (E B : Type) (transformer : Transformer B) (encode1 encode2 encode3 : E -> Comp (B * E)) (ctx : E) b,
      refine (((If b Then encode1 Else encode2) ThenC encode3) ctx)
             (If b Then ((encode1 ThenC encode3) ctx) Else ((encode2 ThenC encode3) ctx)).
  Proof.
    intros; destruct b; reflexivity.
  Qed.

  Corollary AlignedEncodeNat
            {numBytes}
    : forall (n : nat) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 8)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((encode_nat_Spec 8 (transformerUnit := ByteString_QueueTransformerOpt) n)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons _ (natToWord 8 n) _ v), ce')).
  Proof.
    unfold encode_nat_Spec; cbv beta; intros.
    rewrite <- AlignedEncodeChar; eauto.
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
      
  Lemma AlignedEncode_If_Then_Else
            {numBytesT numBytesE}
    : forall (b : bool) ctx ctxT ctxE
             (vT : Vector.t Core.char numBytesT)
             (vE : Vector.t Core.char numBytesE)
             (encode1 encode2 : CacheEncode -> Comp (_ * CacheEncode)),
      (b = true
       -> refine (encode1 ctx) (ret (build_aligned_ByteString vT, ctxT)))
      -> (b = false
          -> refine (encode2 ctx) (ret (build_aligned_ByteString vE, ctxE)))
      -> refine (If b Then (encode1 ctx) Else (encode2 ctx))
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
  
  Definition Correct_simple_encoder
    : { simple_encoder : _ &
                         forall (t : ASN1_Simple_denote Simple_Format),
                           NPeano.Nat.ltb (String.length t) 127 = true
                           -> refine (ASN1_Format_Simple_DER Simple_Format t ())
                     (ret (simple_encoder t)) }.
  Proof.
    simpl; eexists; intros.
    unfold encode_nat_Spec at 1, encode_enum_Spec; simpl.
    eapply SetoidMorphisms.refine_refineEquiv_Proper;
      [ unfold flip;
        repeat first
               [ etransitivity; [ apply refineEquiv_compose_compose with (transformer := ByteStringQueueTransformer) | idtac ]
               | etransitivity; [ apply refineEquiv_compose_Done with (transformer := ByteStringQueueTransformer) | idtac ]
               | apply refineEquiv_under_compose with (transformer := ByteStringQueueTransformer) ];
        intros; higher_order_reflexivity
      | reflexivity | ];
      rewrite refine_ThenC_beta_reduce.
    rewrite (@CollapseEncodeWord _ test_cache); simpl; eauto.
    rewrite !refine_ThenC_beta_reduce.
    rewrite (@CollapseEncodeWord _ test_cache); simpl; eauto.
    rewrite !refine_ThenC_beta_reduce.
    eapply (@AlignedEncodeChar test_cache); eauto.
    rewrite refine_If_Then_Else_ThenC.
    eapply AlignedEncode_If_Then_Else; intros.
    eapply (@AlignedEncodeNat _).
    eapply (@encode_string_aligned_ByteString test_cache); eauto.
    apply build_aligned_ByteString_id.
    congruence.
    Grab Existential Variables.
    exact ().
    apply Vector.nil.
  Defined.

  Arguments natToWord : simpl never.
  
  Definition byte_aligned_simple_encoder
             (t :  ASN1_Simple_denote Simple_Format)
    := Eval simpl in (projT1 Correct_simple_encoder t).

  Print byte_aligned_simple_encoder.

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
