Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory.
Require Import Coq.Sets.Ensembles.

Require Import Bedrock.Bedrock.

Require Import Bedrock.Platform.Facade.examples.TuplesF.

Notation byte := (Word.word 8).
Notation byteString := (list byte).

Inductive WS :=
| WSWord (w: W)
| WSBytes (capacity: W) (s: byteString).

Definition WSTupl := GenericTuple WS.
Definition WSTuplSet := GenericTuples WS.

Inductive ADTValue :=
| WTuple (t : tupl)
| WordList (ws : list W)
| WTupleList (ts : list tupl)
| WBagOfTuples0 (len : W) (ts : tuples)
| WBagOfTuples1 (len key : W) (ts : tuples)
| WBagOfTuples2 (len key1 key2 : W) (ts : tuples)
| WSTuple (t : WSTupl)
| WSTupleList (ts : list WSTupl)
| ByteString (capacity: W) (bs: byteString)
| WSTrie (len keyIndex : W) (tuples : WSTuplSet).

Require Import Bedrock.Platform.Cito.ADT.

Module Adt <: ADT.
  Definition ADTValue := ADTValue.
End Adt.

Require Import Coq.Lists.List Coq.Program.Program.

Definition SCAZero {t} := SCA t (Word.natToWord 32 0).
Definition SCAOne  {t} := SCA t (Word.natToWord 32 1).

Create HintDb crush_types_db.

Ltac crush_types :=
  (unfold type_conforming, same_types, same_type; intros;
   repeat match goal with
          | [ H: exists t, _ |- _ ] => destruct H
          end;
   repeat progress (subst; intuition);
   try (compute; autorewrite with crush_types_db; reflexivity)).

Definition Injective {A B} (f: A -> B) :=
  forall x y, f x = f y -> x = y.

Definition Injective2 {A B C} (f: C -> A -> B) :=
  forall c x y, f c x = f c y -> x = y.

Definition Injective3 {A B C1 C2} (f: C1 -> C2 -> A -> B) :=
  forall c1 c2 x y, f c1 c2 x = f c1 c2 y -> x = y.

Definition Injective4 {A B C1 C2 C3} (f: C1 -> C2 -> C3 -> A -> B) :=
  forall c1 c2 c3 x y, f c1 c2 c3 x = f c1 c2 c3 y -> x = y.

Module Type TupleADTSpecParams.
  Parameter FieldType : Type.
  Parameter ValueConstructor : forall (t: option FieldType), Value ADTValue.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Axiom TupleConstructor_inj : (Injective TupleConstructor).
End TupleADTSpecParams.

Module TupleADTSpec (Params: TupleADTSpecParams).
  Export Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len, args = [SCA _ len]
                                           /\ len >= $2;
        PostCond := fun args ret => exists len ls, args = [(SCA _ len, None)]
                                                   /\ ret = ADT (TupleConstructor ls)
                                                   /\ length ls = wordToNat len
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls len, args = [ADT (TupleConstructor ls); SCA _ len]
                                              /\ length ls = wordToNat len;
        PostCond := fun args ret => exists ls len, args = [(ADT (TupleConstructor ls), None); (SCA _ len, None)]
                                                   /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists ls len,
                       args = [ADT (TupleConstructor ls); SCA _ len]
                       /\ length ls = wordToNat len
                       /\ natToW (length ls) >= $2;
        PostCond := fun args ret => exists ls len,
                        args = [(ADT (TupleConstructor ls), Some (TupleConstructor ls)); (SCA _ len, None)]
                        /\ ret = ADT (TupleConstructor ls)
      |}; crush_types.
  Defined.

  Definition Get : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos,
                       args = [ADT (TupleConstructor ls); SCA _ pos]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos,
                        args = [(ADT (TupleConstructor ls), Some (TupleConstructor ls)); (SCA _ pos, None)]
                        /\ ret = ValueConstructor (List.nth_error ls (Word.wordToNat pos))
      |}; crush_types.
  Defined.
End TupleADTSpec.

Ltac autoinj := inversion 1; intuition congruence.

Module WTupleADTSpecParams <: TupleADTSpecParams.
  Definition FieldType := W.
  Definition TupleConstructor := WTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition ValueConstructor (x: option FieldType) :=
    SCA ADTValue (match x with
                  | Some w => w
                  | _ => wzero _
                  end).
End WTupleADTSpecParams.

Module WTupleADTSpec.
  Include (TupleADTSpec WTupleADTSpecParams).

  Definition Put : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos val,
                       args = [ADT (TupleConstructor ls); SCA _ pos; SCA _ val]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos val,
                        args = [(ADT (TupleConstructor ls), Some (TupleConstructor (Array.upd ls pos val)));
                                (SCA _ pos, None); (SCA _ val, None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.
End WTupleADTSpec.

Module WSTupleADTSpecParams <: TupleADTSpecParams.
  Definition FieldType := WS.
  Definition TupleConstructor := WSTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition ValueConstructor (x: option FieldType) :=
    match x with
    | Some (WSWord w) => SCA ADTValue w
    | Some (WSBytes c s) => ADT (ByteString c s)
    | _ => SCA ADTValue (wzero _)
    end.
End WSTupleADTSpecParams.

Fixpoint PutAt {A} seq offset (val: A) :=
  match seq, offset with
  | nil, _ => nil
  | _ :: t, 0 => val :: t
  | h :: t, S offset' => h :: (PutAt t offset' val)
  end.

Module WSTupleADTSpec.
  Include (TupleADTSpec WSTupleADTSpecParams).

  Definition PutW : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos val,
                       args = [ADT (TupleConstructor ls); SCA _ pos; SCA _ val]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos val,
                        args = [(ADT (TupleConstructor ls),
                                 Some (TupleConstructor (PutAt ls pos (WSWord val))));
                                (SCA _ pos, None); (SCA _ val, None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition PutString : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists ls pos capacity string,
                       args = [ADT (TupleConstructor ls); SCA _ pos; ADT (ByteString capacity string)]
                       /\ pos < natToW (length ls);
        PostCond := fun args ret =>
                      exists ls pos capacity string,
                        args = [(ADT (TupleConstructor ls),
                                 Some (TupleConstructor (PutAt ls pos (WSBytes capacity string))));
                                (SCA _ pos, None); (ADT (ByteString capacity string), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.
End WSTupleADTSpec.

Module WordListADTSpec.
  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (WordList [])
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists l, args = [ADT (WordList l)];
        PostCond := fun args ret => exists l, args = [(ADT (WordList l), None)] /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (WordList (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (WordList (h :: t)), Some (WordList t)) ]
                        /\ ret = SCA ADTValue h
      |}; crush_types.
  Defined.

  Definition Empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (WordList l), Some (WordList l))]
                        /\ exists w, ret = SCA _ w /\ Bedrock.Programming.propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition Push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l w,
                       args = [ADT (WordList l); SCA _ w];
        PostCond := fun args ret =>
                      exists l w,
                        args = [ (ADT (WordList l), Some (WordList (w :: l))); (SCA _ w, None) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList l)) ]
                        /\ ret = ADT (WordList l)
      |}; crush_types.
  Defined.

  Definition Rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList (rev l))) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (WordList l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (WordList l), Some (WordList l)) ]
                        /\ ret = SCA _ (Word.natToWord _ (length l))
      |}; crush_types.
  Defined.
End WordListADTSpec.

Module Type ADTListADTSpecParams.
  Parameter ElemType : Type.
  Parameter ElemConstructor : forall (t: ElemType), ADTValue.
  Axiom ElemConstructor_inj : (Injective ElemConstructor).
  Parameter ListConstructor : forall (ls: list ElemType), ADTValue.
  Axiom ListConstructor_inj : (Injective ListConstructor).
End ADTListADTSpecParams.

Module ADTListADTSpec (Params: ADTListADTSpecParams).
  Import Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [];
        PostCond := fun args ret => args = [] /\ ret = ADT (ListConstructor [])
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => args = [ADT (ListConstructor nil)];
        PostCond := fun args ret => args = [ (ADT (ListConstructor nil), None) ]
                                    /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Pop : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists h t,
                       args = [ADT (ListConstructor (h :: t))];
        PostCond := fun args ret =>
                      exists h t,
                        args = [ (ADT (ListConstructor (h :: t)), Some (ListConstructor t)) ]
                        /\ ret = ADT (ElemConstructor h)
      |}; crush_types.
  Defined.

  Definition Empty : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [(ADT (ListConstructor l), Some (ListConstructor l))]
                        /\ exists w, ret = SCA _ w /\ propToWord (l = nil) w
      |}; crush_types.
  Defined.

  Definition Push : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l t,
                       args = [ADT (ListConstructor l); ADT (ElemConstructor t)];
        PostCond := fun args ret =>
                      exists l t,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor (t :: l)));
                                 (ADT (ElemConstructor t), None) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Rev : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor (rev l))) ]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Length : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l,
                       args = [ADT (ListConstructor l)];
        PostCond := fun args ret =>
                      exists l,
                        args = [ (ADT (ListConstructor l), Some (ListConstructor l)) ]
                        /\ ret = SCA _ (natToWord _ (length l))
      |}; crush_types.
  Defined.
End ADTListADTSpec.

Module Type TupleListADTSpecParams.
  Parameter FieldType : Type.
  Parameter TupleConstructor : forall (t: (GenericTuple FieldType)), ADTValue.
  Axiom TupleConstructor_inj : (Injective TupleConstructor).
  Parameter ListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
  Axiom ListConstructor_inj : (Injective ListConstructor).
End TupleListADTSpecParams.

Module ADTListADTSpecParamsFromTupleOnes (Import Param: TupleListADTSpecParams) <: ADTListADTSpecParams.
  Definition ElemType := (GenericTuple FieldType).
  Definition ElemConstructor := TupleConstructor.
  Definition ElemConstructor_inj := TupleConstructor_inj.
  Definition ListConstructor := ListConstructor.
  Definition ListConstructor_inj := ListConstructor_inj.
End ADTListADTSpecParamsFromTupleOnes.

Module TupleListADTSpec (TupleParams: TupleListADTSpecParams).
  Module Import Params := (ADTListADTSpecParamsFromTupleOnes TupleParams).
  Include (ADTListADTSpec Params).

  Definition Copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists l len,
                       args = [ADT (ListConstructor l); SCA _ len]
                       /\ allTuplesLen (wordToNat len) l
                       /\ $2 <= len;
        PostCond := fun args ret =>
                      exists l len,
                        args = [ (ADT (ListConstructor l),
                                  Some (ListConstructor l)); (SCA _ len, None) ]
                        /\ ret = ADT (ListConstructor l)
      |}; crush_types.
  Defined.
End TupleListADTSpec.

Module WTupleListADTSpecParams <: TupleListADTSpecParams.
  Definition FieldType := W.
  Definition TupleConstructor := WTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition ListConstructor := WTupleList.
  Lemma ListConstructor_inj : Injective ListConstructor. autoinj. Qed.
End WTupleListADTSpecParams.

Module WTupleListADTSpec := TupleListADTSpec WTupleListADTSpecParams.

Module WSTupleListADTSpecParams <: TupleListADTSpecParams.
  Definition FieldType := WS.
  Definition TupleConstructor := WSTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition ListConstructor := WSTupleList.
  Lemma ListConstructor_inj : Injective ListConstructor. autoinj. Qed.
End WSTupleListADTSpecParams.

Module WSTupleListSpec := TupleListADTSpec (WSTupleListADTSpecParams).

Print Module WTupleListADTSpec.
Print Module WSTupleListSpec.

Module Type BagOfTuples0ADTSpecParams.
  Parameter FieldType : Type.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Axiom TupleConstructor_inj : (Injective TupleConstructor).
  Parameter TupleListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
  Axiom TupleListConstructor_inj : (Injective TupleListConstructor).
  Parameter TreeConstructor : forall (len: W) (elems: GenericTuples FieldType), ADTValue.
  Axiom TreeConstructor_inj : (Injective2 TreeConstructor).
End BagOfTuples0ADTSpecParams.

Module BagOfTuples0ADTSpec (Params : BagOfTuples0ADTSpecParams).
  Export Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len, args = [SCA _ len]
                                           /\ len >= $2;
        PostCond := fun args ret => exists len, args = [(SCA _ len, None)]
                                                /\ ret = ADT (TreeConstructor len Empty)
      |}; crush_types.
  Defined.

  Definition Insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len ts t idx,
                       args = [ADT (TreeConstructor len ts); ADT (TupleConstructor t)]
                       /\ minFreshIndex ts idx
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len ts t idx,
                        args = [ (ADT (TreeConstructor len ts),
                                  Some (TreeConstructor len (insertAt ts idx t)));
                                 (ADT (TupleConstructor t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len ts,
                       args = [ADT (TreeConstructor len ts)];
        PostCond := fun args ret =>
                      exists len ts l,
                        args = [ (ADT (TreeConstructor len ts), Some (TreeConstructor len ts)) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.
End BagOfTuples0ADTSpec.

Module WBagOfTuples0ADTSpecParams <: BagOfTuples0ADTSpecParams.
  Definition FieldType := W.
  Definition TupleConstructor := WTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition TupleListConstructor := WTupleList.
  Lemma TupleListConstructor_inj : Injective TupleListConstructor. autoinj. Qed.
  Definition TreeConstructor := WBagOfTuples0.
  Lemma TreeConstructor_inj : Injective2 TreeConstructor. autoinj. Qed.
End WBagOfTuples0ADTSpecParams.

Module WBagOfTuples0ADTSpec := BagOfTuples0ADTSpec WBagOfTuples0ADTSpecParams.
Print Module WBagOfTuples0ADTSpec.

Module Type BagOfTuples1ADTSpecParams.
  Parameter KeyType : Type.
  Parameter FieldType : Type.
  Parameter DefaultField : FieldType.
  Parameter KeyConstructor : forall (k: KeyType), Value ADTValue.
  Axiom KeyConstructor_inj : (Injective KeyConstructor).
  Parameter KeyConstructor_SameTypes : forall x y, is_same_type (KeyConstructor x) (KeyConstructor y) = true.
  Parameter MatchingFunction : forall (f: FieldType) (k: KeyType), Prop.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Axiom TupleConstructor_inj : (Injective TupleConstructor).
  Parameter TupleListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
  Axiom TupleListConstructor_inj : (Injective TupleListConstructor).
  Parameter BagConstructor : forall (len keyIndex : W) (tuples : GenericTuples FieldType), ADTValue.
  Axiom BagConstructor_inj : (Injective3 BagConstructor).
End BagOfTuples1ADTSpecParams.

Module BagOfTuples1ADTSpec (Params : BagOfTuples1ADTSpecParams).
  Export Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len key, args = [SCA _ len; SCA _ key]
                                               /\ len >= $2
                                               /\ key < len;
        PostCond := fun args ret => exists len key, args = [(SCA _ len, None); (SCA _ key, None)]
                                                    /\ ret = ADT (BagConstructor len key Empty)
      |}; crush_types.
  Defined.

  Definition Insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts t idx,
                       args = [ADT (BagConstructor len key ts); ADT (TupleConstructor t)]
                       /\ minFreshIndex ts idx
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len key ts t idx,
                        args = [ (ADT (BagConstructor len key ts),
                                  Some (BagConstructor len key (insertAt ts idx t)));
                                 (ADT (TupleConstructor t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts,
                       args = [ADT (BagConstructor len key ts)]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key ts l,
                        args = [ (ADT (BagConstructor len key ts), Some (BagConstructor len key ts)) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.

  Hint Rewrite KeyConstructor_SameTypes : crush_types_db.
  Definition Find : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts k,
                       args = [ADT (BagConstructor len key ts); KeyConstructor k];
        PostCond := fun args ret =>
                      exists len keyIndex ts k l,
                        args = [ (ADT (BagConstructor len keyIndex ts), Some (BagConstructor len keyIndex ts));
                                 (KeyConstructor k, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence (keepEq MatchingFunction DefaultField ts keyIndex k) l
      |}; crush_types.
  Defined.
End BagOfTuples1ADTSpec.

Module WBagOfTuples1ADTSpecParams <: BagOfTuples1ADTSpecParams.
  Definition KeyType := W.
  Definition FieldType := W.
  Definition DefaultField : W := 0.
  Definition KeyConstructor := SCA ADTValue.
  Lemma KeyConstructor_inj : Injective KeyConstructor. autoinj. Qed.
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction := @eq W.
  Definition TupleConstructor := WTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition TupleListConstructor := WTupleList.
  Lemma TupleListConstructor_inj : Injective TupleListConstructor. autoinj. Qed.
  Definition BagConstructor := WBagOfTuples1.
  Lemma BagConstructor_inj : Injective3 BagConstructor. autoinj. Qed.
End WBagOfTuples1ADTSpecParams.

Module WBagOfTuples1ADTSpec := BagOfTuples1ADTSpec WBagOfTuples1ADTSpecParams.
 
Definition ByteToAscii (w8: byte) : Ascii.ascii :=
  match w8 with
  | Word.WO => Ascii.zero
  | Word.WS b7 _ w7 =>
    match w7 with
    | Word.WO => Ascii.zero
    | Word.WS b6 _ w6 =>
      match w6 with
      | Word.WO => Ascii.zero
      | Word.WS b5 _ w5 =>
        match w5 with
        | Word.WO => Ascii.zero
        | Word.WS b4 _ w4 =>
          match w4 with
          | Word.WO => Ascii.zero
          | Word.WS b3 _ w3 =>
            match w3 with
            | Word.WO => Ascii.zero
            | Word.WS b2 _ w2 =>
              match w2 with
              | Word.WO => Ascii.zero
              | Word.WS b1 _ w1 =>
                match w1 with
                | Word.WO => Ascii.zero
                | Word.WS b0 _ w0 =>
                  Ascii.Ascii b7 b6 b5 b4 b3 b2 b1 b0
                end
              end
            end
          end
        end
      end
    end
  end.

Lemma ByteToAscii_correct_wrt_nat :
  forall n: nat, (n <= 255)%nat -> Ascii.nat_of_ascii (ByteToAscii (Word.natToWord 8 n)) = n.
Proof.
  intros; repeat (destruct n; [ reflexivity | ]).
  apply (Minus.minus_le_compat_r _ _ 255) in H; inversion H.
Qed.

Fixpoint BytesToString bytes :=
  match bytes with
  | nil => ""%string
  | cons a bb => String (ByteToAscii a) (BytesToString bb)
  end.

Definition WS_StringPrefixB ws key :=
  match ws with
  | WSBytes c s => prefix (BytesToString key) (BytesToString s)
  | _ => false
  end.

Definition WS_WordEqB ws key :=
  match ws with
  | WSWord w => Word.weqb w key
  | _ => false
  end.

Module WSTrieADTSpecParams <: BagOfTuples1ADTSpecParams.
  Definition KeyType := (W * byteString)%type.
  Definition FieldType := WS.
  Definition DefaultField := WSWord 0.
  Definition KeyConstructor := (fun cbs: KeyType => ADT (let (c, bs) := cbs in ByteString c bs)).
  Lemma KeyConstructor_inj : Injective KeyConstructor. destruct x, y; autoinj. Qed.
  Definition KeyConstructor_SameTypes := fun _ _ : KeyType => @eq_refl bool true.
  Definition MatchingFunction ws (key: KeyType) := WS_StringPrefixB ws (snd key) = true.
  Definition TupleConstructor := WSTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition TupleListConstructor := WSTupleList.
  Lemma TupleListConstructor_inj : Injective TupleListConstructor. autoinj. Qed.
  Definition BagConstructor := WSTrie.
  Lemma BagConstructor_inj : Injective3 BagConstructor. autoinj. Qed.
End WSTrieADTSpecParams.

Module WSTrieADTSpec.
  Include (BagOfTuples1ADTSpec (WSTrieADTSpecParams)).

  Definition fieldBelowThreshold tuple index threshold :=
    match List.nth_error tuple index with
    | Some (WSWord w) => Word.wlt w threshold (* Do we need [<=]? *)
    | _ => False
    end.

  Definition dropBelow (tuples: WSTuplSet) (index: W) (threshold: W) : WSTuplSet :=
    (fun t => tuples t /\ fieldBelowThreshold (indexedElement t) (Word.wordToNat index) threshold).

  Definition DropBelow : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len key ts threshold offset idx,
                       args = [ADT (BagConstructor len key ts); SCA _ offset; SCA _ threshold]
                       /\ minFreshIndex ts idx;
        PostCond := fun args ret =>
                      exists len key ts threshold offset idx,
                        args = [ (ADT (BagConstructor len key ts),
                                  Some (BagConstructor len key (dropBelow ts offset threshold)));
                                 (SCA _ offset, None);
                                 (SCA _ threshold, None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.
End WSTrieADTSpec.

Print Module WBagOfTuples1ADTSpec.
Print Module WSBagOfTuples1ADTSpec.
Print Module WSTrieADTSpec.

Module Type BagOfTuples2ADTSpecParams.
  Parameter KeyType1 KeyType2 : Type.
  Parameter FieldType : Type.
  Parameter DefaultField : FieldType.
  Parameter KeyConstructor1 : forall (k: KeyType1), Value ADTValue.
  Parameter KeyConstructor2 : forall (k: KeyType2), Value ADTValue.
  Parameter KeyConstructor1_SameTypes : forall x y, is_same_type (KeyConstructor1 x) (KeyConstructor1 y) = true.
  Parameter KeyConstructor2_SameTypes : forall x y, is_same_type (KeyConstructor2 x) (KeyConstructor2 y) = true.
  Parameter MatchingFunction1 : forall (f: FieldType) (k: KeyType1), Prop.
  Parameter MatchingFunction2 : forall (f: FieldType) (k: KeyType2), Prop.
  Parameter TupleConstructor : forall (t: GenericTuple FieldType), ADTValue.
  Axiom TupleConstructor_inj : (Injective TupleConstructor).
  Parameter TupleListConstructor : forall (ls: list (GenericTuple FieldType)), ADTValue.
  Axiom TupleListConstructor_inj : (Injective TupleListConstructor).
  Parameter BagConstructor : forall (len keyIndex1 keyIndex2 : W) (tuples : GenericTuples FieldType), ADTValue.
  Axiom BagConstructor_inj : (Injective4 BagConstructor).
End BagOfTuples2ADTSpecParams.

Module BagOfTuples2ADTSpec (Params: BagOfTuples2ADTSpecParams).
  Export Params.

  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args => exists len keyIndex1 keyIndex2,
                       args = [SCA _ len; SCA _ keyIndex1; SCA _ keyIndex2]
                       /\ len >= $2
                       /\ keyIndex1 < len
                       /\ keyIndex2 < len;
        PostCond := fun args ret => exists len keyIndex1 keyIndex2,
                        args = [(SCA _ len, None); (SCA _ keyIndex1, None); (SCA _ keyIndex2, None)]
                        /\ ret = ADT (BagConstructor len keyIndex1 keyIndex2 Empty)
      |}; crush_types.
  Defined.

  Definition Insert : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts t idx,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts); ADT (TupleConstructor t)]
                       /\ minFreshIndex ts idx
                       /\ length t = wordToNat len;
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts t idx,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 (insertAt ts idx t)));
                                 (ADT (TupleConstructor t), None) ]
                        /\ minFreshIndex ts idx
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Enumerate : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts)]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts l,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 ts)) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence ts l
      |}; crush_types.
  Defined.

  Hint Rewrite KeyConstructor1_SameTypes : crush_types_db.
  Hint Rewrite KeyConstructor2_SameTypes : crush_types_db.

  Definition FindBoth : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts k1 k2,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts);
                               KeyConstructor1 k1; KeyConstructor2 k2];
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts k1 k2 l,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 ts));
                                 (KeyConstructor1 k1, None); (KeyConstructor2 k2, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence
                             (keepEq MatchingFunction2 DefaultField (keepEq MatchingFunction1 DefaultField ts keyIndex1 k1) keyIndex2 k2)
                             l
      |}; crush_types.
  Defined.

  Definition FindFirst : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts k,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts); KeyConstructor1 k]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len keyIndex1 keyIndex2 ts k l,
                        args = [ (ADT (BagConstructor len keyIndex1 keyIndex2 ts),
                                  Some (BagConstructor len keyIndex1 keyIndex2 ts));
                                 (KeyConstructor1 k, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence (keepEq MatchingFunction1 DefaultField ts keyIndex1 k) l
      |}; crush_types.
  Defined.

  Definition FindSecond : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists len keyIndex1 keyIndex2 ts k,
                       args = [ADT (BagConstructor len keyIndex1 keyIndex2 ts); KeyConstructor2 k]
                       /\ functional ts;
        PostCond := fun args ret =>
                      exists len key1 keyIndex2 ts k l,
                        args = [ (ADT (BagConstructor len key1 keyIndex2 ts),
                                  Some (BagConstructor len key1 keyIndex2 ts));
                                 (KeyConstructor2 k, None) ]
                        /\ ret = ADT (TupleListConstructor l)
                        /\ EnsembleIndexedListEquivalence (keepEq MatchingFunction2 DefaultField ts keyIndex2 k) l
      |}; crush_types.
  Defined.
End BagOfTuples2ADTSpec.

Module WBagOfTuples2ADTSpecParams <: BagOfTuples2ADTSpecParams.
  Definition KeyType1 := W.
  Definition KeyType2 := W.
  Definition FieldType := W.
  Definition DefaultField : W := 0.
  Definition KeyConstructor1 := SCA ADTValue.
  Definition KeyConstructor2 := SCA ADTValue.
  Definition KeyConstructor1_SameTypes := fun _ _ : KeyType1 => @eq_refl bool true.
  Definition KeyConstructor2_SameTypes := fun _ _ : KeyType2 => @eq_refl bool true.
  Definition MatchingFunction1 := @eq KeyType1.
  Definition MatchingFunction2 := @eq KeyType2.
  Definition TupleConstructor := WTuple.
  Lemma TupleConstructor_inj : Injective TupleConstructor. autoinj. Qed.
  Definition TupleListConstructor := WTupleList.
  Lemma TupleListConstructor_inj : Injective TupleListConstructor. autoinj. Qed.
  Definition BagConstructor := WBagOfTuples2.
  Lemma BagConstructor_inj : Injective4 BagConstructor. autoinj. Qed.
End WBagOfTuples2ADTSpecParams.

Module WBagOfTuples2ADTSpec := BagOfTuples2ADTSpec WBagOfTuples2ADTSpecParams.
Print Module WBagOfTuples2ADTSpec.

Module BytesADTSpec.
  Definition New : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity,
                       args = [SCA _ capacity]
                       /\ goodSize (2 + wordToNat capacity * 4);
        PostCond := fun args ret =>
                      exists capacity,
                        args = [(SCA _ capacity, None)]
                        /\ ret = ADT (ByteString (capacity ^* $4) nil)
      |}; crush_types.
  Defined.

  Definition Delete : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes,
                       args = [ADT (ByteString capacity bytes)];
        PostCond := fun args ret => exists capacity bytes,
                        args = [(ADT (ByteString capacity bytes), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Copy : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes,
                       args = [ADT (ByteString capacity bytes)];
        PostCond := fun args ret => exists capacity bytes,
                        args = [(ADT (ByteString capacity bytes), Some (ByteString capacity bytes))]
                        /\ ret = ADT (ByteString capacity bytes)
      |}; crush_types.
  Defined.

  Definition Push : AxiomaticSpec ADTValue.
    refine {| (* FIXME relax the precondition to allow variability on the higher bytes? *)
        PreCond := fun args =>
                     exists capacity bytes byte,
                       (length bytes + 1 <= wordToNat capacity)%nat
                       /\ args = [ADT (ByteString capacity bytes); SCA _ (BtoW byte)];
        PostCond := fun args ret =>
                      exists capacity bytes byte,
                        args = [(ADT (ByteString capacity bytes), Some (ByteString capacity (bytes ++ [byte])));
                                (SCA _ (BtoW byte), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Put : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes index byte,
                       (wordToNat index < length bytes)%nat
                       /\ args = [ADT (ByteString capacity bytes); SCA _ index; SCA _ (BtoW byte)];
        PostCond := fun args ret =>
                      exists capacity bytes index byte,
                        args = [(ADT (ByteString capacity bytes),
                                 Some (ByteString capacity (PutAt bytes (wordToNat index) byte)));
                                (SCA _ index, None); (SCA _ (BtoW byte), None)]
                        /\ ret = SCAZero
      |}; crush_types.
  Defined.

  Definition Get : AxiomaticSpec ADTValue.
    refine {|
        PreCond := fun args =>
                     exists capacity bytes index,
                       (wordToNat index < length bytes)%nat
                       /\ args = [ADT (ByteString capacity bytes); SCA _ index];
        PostCond := fun args ret =>
                      exists capacity bytes index,
                        args = [(ADT (ByteString capacity bytes), Some (ByteString capacity bytes));
                                (SCA _ index, None)]
                        /\ ret = SCA _ (BtoW (nth (wordToNat index) bytes (wzero _)))
      |}; crush_types.
  Defined.
End BytesADTSpec.
