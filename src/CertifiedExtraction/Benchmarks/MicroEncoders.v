Require Import Benchmarks.MicroEncodersSetup.

Instance empty_cache : Cache :=
  {| CacheEncode := unit;
     CacheDecode := unit;
     Equiv := fun _ _ => True |}.

Instance empty_cache_add_nat : CacheAdd empty_cache N :=
  {| addE := fun ce _ => ce;
     addD := fun cd _ => cd;
     add_correct := fun _ _ _ => id |}.

Record FourWords :=
  { w0 : BoundedN 8;
    w1 : BoundedN 8;
    w2 : BoundedN 8;
    w3 : BoundedN 8 }.

Definition FourWords_encode (t : FourWords) :=
  fst ((FixInt_encode t.(w0)
   Then FixInt_encode t.(w1)
   Then FixInt_encode t.(w2)
   Then FixInt_encode t.(w3)
   Then (fun e => (nil, e))) tt).

Definition FourWordsAsCollectionOfVariables
  {av} vw0 vw1 vw2 vw3 t
  : Telescope av :=
  [[ vw0 ->> t.(w0) as _ ]] ::
  [[ vw1 ->> t.(w1) as _ ]] ::
  [[ vw2 ->> t.(w2) as _ ]] ::
  [[ vw3 ->> t.(w3) as _ ]] :: Nil.

Hint Unfold FourWords_encode : f2f_binencoders_autorewrite_db.
Hint Unfold FourWordsAsCollectionOfVariables : f2f_binencoders_autorewrite_db.

Definition FourWords_encode' (t : FourWords) : BytableListOfBools 512.
Proof.
  exists (FourWords_encode t).
  admit.
Defined.

Example FourWords_compile :
  ParametricExtraction
    #vars      fourWords
    #program   ret (FourWords_encode' fourWords)
    #arguments (FourWordsAsCollectionOfVariables
                  (NTSome "w0") (NTSome "w1") (NTSome "w2") (NTSome "w3") fourWords)
    #env       MicroEncoders_Env.
Proof.
  unfold FourWords_encode'.
  compile_encoder_t.

  CompileCompose
  repeat (apply CompileDeallocSCA_discretely; try compile_encoder_t).  (* TODO automate *)
Defined.

Eval lazy in (extract_facade FourWords_compile).

Record BitArrayAndList :=
  { f1 : BitArray 8;
    f2 : { l : list {n : N | (n < exp2 8)%N} | List.length l < exp2_nat 8} } .

Definition BitArrayAndList_encode (t : BitArrayAndList) :=
  fst ((IList.IList_encode Bool.Bool_encode (f1 t)
   Then FixInt_encode (FixList_getlength (f2 t))
   Then FixList_encode FixInt_encode (f2 t)
   Then (fun e => (nil, e))) tt).

Require Import Coq.Program.Program.

Definition BitArrayAndListAsCollectionOfVariables
  {av} vf1 vf2 ll
  : Telescope av :=
  [[ vf1 ->> ll.(f1) as _ ]] ::
  [[ vf2 ->> `ll.(f2) as _ ]] :: Nil.

Hint Unfold BitArrayAndList_encode : f2f_binencoders_autorewrite_db.
Hint Unfold BitArrayAndListAsCollectionOfVariables : f2f_binencoders_autorewrite_db.
Hint Rewrite (@IList_encode'_body_simpl empty_cache) : f2f_binencoders_autorewrite_db.

Typeclasses eauto := 10.

Instance WrapListOfBoundedValues :
  (* FIXME when the elements of the list inject into W, we should have a
     canonical into lists of words. *)
  FacadeWrapper (Value ADTValue) (list (BoundedN 8)). Admitted.

Lemma map_inj {A B}:
  forall (f: A -> B),
    (forall x y, f x = f y -> x = y) ->
    (forall x y, (map f) x = (map f) y -> x = y).
Proof.
  induction x; destruct y; simpl; intros HH; try congruence.
  inversion' HH; f_equal; eauto.
Qed.

Instance WrapList {A B} {Wrp: FacadeWrapper A B} : FacadeWrapper (list A) (list B).
Proof.
  refine {| wrap x := map wrap x |}.
  eauto using map_inj, wrap_inj.
Qed.

Example BitArrayAndList_compile :
  ParametricExtraction
    #vars      bitArrayAndList
    #program   ret (BitArrayAndList_encode bitArrayAndList)
    #arguments (BitArrayAndListAsCollectionOfVariables
                  (NTSome "f1") (NTSome "f2") bitArrayAndList)
    #env       MicroEncoders_Env.
Proof.
  compile_encoder_t.
  repeat (apply CompileDeallocSCA_discretely; try compile_encoder_t).  (* TODO automate *)
  repeat (apply CompileDeallocSCA_discretely; try compile_encoder_t).
  Grab Existential Variables.
  repeat constructor.
  repeat constructor.
  repeat constructor.
Defined.

Eval lazy in (extract_facade BitArrayAndList_compile).

