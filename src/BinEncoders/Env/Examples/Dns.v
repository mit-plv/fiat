Require Import
        Coq.Structures.OrderedTypeEx
        Coq.Structures.OrderedType
        Coq.FSets.FMapAVL
        Coq.Strings.Ascii.

Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig
        Fiat.BinEncoders.Env.Common.Compose.

Set Implicit Arguments.

Module list_as_OT (O : OrderedType) <: OrderedType.
  (* http://www.ensiie.fr/~robillard/Graph_Library/ *)
  Import O.
  Module Import OP := OrderedTypeFacts O.

  Definition t := list O.t.
  Definition eq := eqlistA O.eq.

  Inductive lt_ : t -> t -> Prop :=
  | ltnil : forall a l, lt_ nil (a :: l)
  | ltcons : forall a l a' l', O.lt a a' -> lt_ (a :: l) (a' :: l')
  | lt_tail : forall a a' l l', O.eq a a' -> lt_ l l' -> lt_ (a :: l) (a' :: l').

  Definition lt := lt_.

  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof.
    unfold eq; induction l; intros.
    destruct l'. left. intuition.
    right. intro. inversion H.
    destruct l'. right. intro. inversion H.
    destruct (IHl l').
    destruct (O.eq_dec a t0). left. constructor; auto.
    right. intro. elim n. inversion H; auto.
    right. intro. elim n. inversion H; auto.
  Defined.

  Lemma eq_refl : forall x, eq x x.
  Proof.
    unfold eq; induction x; intros. auto.
    constructor; auto.
  Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    unfold eq; induction x; intros.
    inversion H; auto.
    destruct y. inversion H.
    inversion H. subst.
    constructor. auto. auto.
  Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    induction x; unfold eq; intros.
    inversion H. subst. inversion H0. subst. auto.
    destruct y. inversion H.
    destruct z. inversion H0.
    constructor. inversion H; inversion H0; subst.
    eapply O.eq_trans; eauto.
    eapply IHx; inversion H; inversion H0; subst; eauto.
  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    induction x; unfold lt; intros.
    inversion H; subst.
    inversion H0; subst.
    constructor.
    constructor.
    inversion H; subst.
    inversion H0; subst.
    constructor. eapply O.lt_trans; eauto.
    inversion H0; subst.
    constructor.
    rewrite <-H3. auto.
    constructor.
    rewrite <-H3. auto.
    inversion H0; subst.
    constructor.
    rewrite H3. auto.
    apply lt_tail. rewrite H3. auto. eapply IHx; eauto.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof.
    induction x; unfold lt, eq; intros; intro.
    inversion H; subst.
    inversion H0.
    destruct y. inversion H0.
    inversion H0; subst.
    inversion H; subst.
    elim (O.lt_not_eq H2 H4).
    eapply IHx; eauto.
  Qed.

  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    induction x; intros.
    destruct y.
    apply EQ. apply eq_refl.
    apply LT. constructor.
    destruct y. apply GT. constructor.
    destruct (O.compare a t0).
    apply LT. constructor. auto.
    destruct (IHx y).
    apply LT. apply lt_tail; auto.
    apply EQ. constructor; auto.
    apply GT. apply lt_tail; auto.
    apply GT. constructor. auto.
  Defined.
End list_as_OT.

Module Type OrderedTypeWithP (O : OrderedType).
  Parameter P : O.t -> Prop.
End OrderedTypeWithP.

Module sig_as_OT (O : OrderedType) (O' : OrderedTypeWithP O) <: OrderedType.
  Import O.
  Module Import OP := OrderedTypeFacts O.

  Definition t := sig O'.P.
  Definition eq (t1 t2 : t) := O.eq (proj1_sig t1) (proj1_sig t2).
  Definition lt (t1 t2 : t) := O.lt (proj1_sig t1) (proj1_sig t2).

  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof. intros; destruct l; destruct l'; apply O.eq_dec. Defined.

  Lemma eq_refl : forall x, eq x x.
  Proof. intros; destruct x; apply O.eq_refl. Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof. intros; destruct x; destruct y; unfold eq in *; apply O.eq_sym; eauto. Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. intros; destruct x; destruct y; destruct z; unfold eq in *; eapply eq_trans; eauto. Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof. intros; destruct x; destruct y; destruct z; unfold lt in *; eapply lt_trans; eauto. Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof. intros; destruct x; destruct y; apply O.lt_not_eq; eauto. Qed.

  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    intros; destruct x; destruct y.
    unfold lt, eq.
    destruct (O.compare x x0) eqn: eq; [ eapply LT | eapply EQ | eapply GT ]; eauto.
  Defined.
End sig_as_OT.

Module ascii_as_OT <: OrderedType.
  Definition t := ascii.
  Definition eq (c1 c2 : t) := nat_of_ascii c1 = nat_of_ascii c2.
  Definition lt (c1 c2 : t) := nat_of_ascii c1 < nat_of_ascii c2.

  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof. unfold eq. decide equality. Defined.

  Lemma eq_refl : forall x, eq x x.
  Proof. reflexivity. Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof. intros. symmetry. eauto. Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. intros. unfold eq in *. rewrite H. rewrite H0. eauto. Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof. intros. unfold lt in *. omega. Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof. intros. unfold eq, lt in *. intro. omega. Qed.

  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    intros. unfold lt, eq.
    destruct (Compare_dec.nat_compare (nat_of_ascii x) (nat_of_ascii y)) eqn: eq.
    - eapply EQ. rewrite <- Compare_dec.nat_compare_eq_iff. eauto.
    - eapply LT. rewrite Compare_dec.nat_compare_lt. eauto.
    - eapply GT. rewrite <- Compare_dec.nat_compare_gt in eq. eauto.
  Defined.
End ascii_as_OT.

Require Import
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.BinLib.Char
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Enum
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.Lib.IList
        Fiat.BinEncoders.Env.Lib.SteppingCacheList.

Definition word_t :=  { l : list ascii | length l < exp2_nat 6 }.
Definition position_t := FixInt 6.

Module list_ascii_as_OT := list_as_OT ascii_as_OT.
Module list_ascii_as_OT_with_P <: OrderedTypeWithP list_ascii_as_OT.
  Definition P (l : list ascii) := length l < exp2_nat 6.
End list_ascii_as_OT_with_P.

Module word_as_OT := sig_as_OT list_ascii_as_OT list_ascii_as_OT_with_P.
Module list_word_as_OT := list_as_OT word_as_OT.

Module N_as_OT_with_P <: OrderedTypeWithP N_as_OT.
  Definition P (n : N) := (n < exp2 6)%N.
End N_as_OT_with_P.

Module position_as_OT := sig_as_OT N_as_OT N_as_OT_with_P.

Module EMap := FMapAVL.Make(list_word_as_OT).
Module DMap := FMapAVL.Make(position_as_OT).

Definition EMapT := EMap.t position_t.
Definition DMapT := DMap.t (list word_t).

Record CacheT :=
  { eMap : EMapT;
    dMap : DMapT;
    tick : nat;
    extr : nat }.

Instance cache : Cache :=
  {| CacheEncode := CacheT;
     CacheDecode := CacheT;
     Equiv := fun x y => x = y /\
                         forall p q, EMap.MapsTo p q x.(eMap) <-> DMap.MapsTo q p x.(dMap) |}.

Fixpoint cycle (A : Type) (n : nat) (f : A -> A) (i : A) :=
  match n with
  | O => i
  | S n' => f (cycle n' f i)
  end.

Lemma cycle_irrelevance :
  forall A B (p : A -> B) (f : A -> A), (forall i, p i = p (f i)) ->
                                        (forall n i, p i = p (cycle n f i)).
Proof. induction n; intuition eauto. simpl. rewrite <- H. eauto. Qed.

Instance cacheAddNat : CacheAdd cache nat :=
  {| addE := fun c n => cycle n (fun c => if NPeano.Nat.eq_dec c.(extr) 7
                                          then {| eMap := c.(eMap);
                                                  dMap := c.(dMap);
                                                  tick := 1 + c.(tick);
                                                  extr := 0 |}
                                          else {| eMap := c.(eMap);
                                                  dMap := c.(dMap);
                                                  tick := c.(tick);
                                                  extr := 1 + c.(extr) |}) c;
     addD := fun c n => cycle n (fun c => if NPeano.Nat.eq_dec c.(extr) 7
                                          then {| eMap := c.(eMap);
                                                  dMap := c.(dMap);
                                                  tick := 1 + c.(tick);
                                                  extr := 0 |}
                                          else {| eMap := c.(eMap);
                                                  dMap := c.(dMap);
                                                  tick := c.(tick);
                                                  extr := 1 + c.(extr) |}) c; |}.
Proof.
  simpl; intuition; subst; eauto.
  rewrite <- cycle_irrelevance in *; try (apply H1; eauto);
  intro; destruct (NPeano.Nat.eq_dec (extr i) 7); eauto.
  rewrite <- cycle_irrelevance in *; try (apply H1; eauto);
  intro; destruct (NPeano.Nat.eq_dec (extr i) 7); eauto.
Defined.

Require Import Coq.FSets.FMapFacts.
Module EMapFacts := WFacts_fun (list_word_as_OT) (EMap).
Module DMapFacts := WFacts_fun (position_as_OT) (DMap).


Instance cacheAddPair : CacheAdd cache (list word_t * position_t) :=
  {| addE := fun c (b : _ * _) => let (l, p) := b
                                  in if EMap.mem l c.(eMap) || DMap.mem p c.(dMap)
                                     then c
                                     else {| eMap := EMap.add l p c.(eMap);
                                             dMap := DMap.add p l c.(dMap);
                                             tick := c.(tick);
                                             extr := c.(extr) |};
     addD := fun c (b : _ * _) => let (l, p) := b
                                  in if EMap.mem l c.(eMap) || DMap.mem p c.(dMap)
                                     then c
                                     else {| eMap := EMap.add l p c.(eMap);
                                             dMap := DMap.add p l c.(dMap);
                                             tick := c.(tick);
                                             extr := c.(extr) |} |}.
Proof.
  simpl; intuition; simpl in *; subst; eauto.
  - destruct (EMap.mem a (eMap cd)) eqn: eq1; destruct (DMap.mem b (dMap cd)) eqn: eq2;
      simpl in *; try apply H1; eauto.
    rewrite EMapFacts.add_mapsto_iff in H.
    rewrite DMapFacts.add_mapsto_iff.
    inversion H. clear H. intuition.
    left. subst. assert (a = p).
    { clear -H; generalize dependent p; induction a; intuition.
      inversion H; eauto.
      destruct p; inversion H; subst; clear H.
      erewrite IHa; eauto; f_equal.
      clear -H3.
      destruct a eqn: ?. destruct s eqn: ?. simpl in *. erewrite <- sig_equivalence.
      clear -H3; generalize dependent x0; induction x; intuition.
      inversion H3; eauto.
      destruct x0; inversion H3; subst; clear H3.
      erewrite IHx; eauto; f_equal.
      apply f_equal with (f:=ascii_of_nat) in H2. rewrite !ascii_nat_embedding in H2. eauto. }
    intuition eauto.
    right. intuition. apply H1 in H4. clear - eq2 H4 H0.
    destruct b eqn: ?. destruct q eqn: ?. erewrite sig_equivalence in H0.
    simpl in H0. rewrite <- Heqk in H0. unfold N_as_OT_with_P.P in *. rewrite <- Heqp1 in H0.
    subst. inversion H0. subst. clear H0. rewrite DMapFacts.mem_find_b in eq2.
    rewrite DMapFacts.find_mapsto_iff in H4.
    erewrite (proj1 (sig_equivalence _ _ x0 x0 _ _) eq_refl) in eq2.
    unfold EMap.key, word_t, list_ascii_as_OT_with_P.P in *. erewrite H4 in eq2. congruence.
    apply H1. eauto.
  - destruct (EMap.mem a (eMap cd)) eqn: eq1; destruct (DMap.mem b (dMap cd)) eqn: eq2;
      simpl in *; try apply H1; eauto.
    rewrite DMapFacts.add_mapsto_iff in H.
    rewrite EMapFacts.add_mapsto_iff.
    inversion H.
    { clear H. intuition.
      left. subst. assert (b = q).
      { clear -H. destruct b eqn: ?. destruct q eqn: ?.
        simpl in H. unfold N_as_OT_with_P.P. apply sig_equivalence. eauto. }
      intuition eauto. eapply EMap.E.eq_refl. }
    { right. intuition. apply H1 in H4. clear - eq1 H4 H0.
      rewrite EMapFacts.mem_find_b in eq1.
      assert (a = p).
      { clear -H0; generalize dependent p; induction a; intuition.
        inversion H0; eauto.
        destruct p; inversion H0; subst; clear H0.
        erewrite IHa; eauto; f_equal.
        clear -H3.
        destruct a eqn: ?. destruct s eqn: ?. simpl in *. erewrite <- sig_equivalence.
        clear -H3; generalize dependent x0; induction x; intuition.
        inversion H3; eauto.
        destruct x0; inversion H3; subst; clear H3.
        erewrite IHx; eauto; f_equal.
        apply f_equal with (f:=ascii_of_nat) in H2. rewrite !ascii_nat_embedding in H2. eauto. }
      subst. rewrite EMapFacts.find_mapsto_iff in H4.
      rewrite H4 in eq1. congruence.
      apply H1. eauto. }
Defined.

Instance cachePeek : CachePeek cache position_t :=
  {| peekE := fun c => let n := N.of_nat c.(tick) in
                       if position_as_OT.OP.lt_dec n (exp2 6)
                       then exist _ n _
                       else exist _ 0%N _;
     peekD := fun c => let n := N.of_nat c.(tick) in
                       if position_as_OT.OP.lt_dec n (exp2 6)
                       then exist _ n _
                       else exist _ 0%N _ |}.
Proof.
  eauto. rewrite <- N.compare_lt_iff. eauto.
  eauto. rewrite <- N.compare_lt_iff. eauto.
  simpl; intuition; subst; eauto.
Defined.

Instance cacheGet : CacheGet cache (list word_t) position_t :=
  {| getE := fun c l => EMap.find l c.(eMap);
     getD := fun c p => DMap.find p c.(dMap) |}.
Proof.
  simpl; intuition; subst.
  apply DMap.find_1. apply EMap.find_2 in H. apply H1. eauto.
  apply EMap.find_1. apply DMap.find_2 in H. apply H1. eauto.
Defined.

Inductive type_t := A | CNAME | NS | MX.
Inductive class_t := IN | CH | HS.

Definition halt : word_t.
  refine (exist _ nil _); rewrite Compare_dec.nat_compare_lt; eauto. Defined.
Definition halt_dec (a : word_t) : {a = halt} + {a <> halt}.
  unfold halt; destruct a as [word word_pf];
  destruct word eqn: eq; subst.
  - left; apply sig_equivalence; eauto.
  - right; inversion 1.
Defined. Hint Resolve halt_dec.

Definition name_t := { s : list word_t | length s <= 255 /\ forall x, In x s -> x <> halt }.

Record question_t :=
  { qname  : name_t;
    qtype  : type_t;
    qclass : class_t }.

Record resource_t :=
  { rname  : name_t;
    rtype  : type_t;
    rclass : class_t;
    rttl   : FixInt 32;
    rdata  : { s : list bool |  length s < exp2_nat 16 } }.

Record packet_t :=
  { pid         : { s : list bool | length s = 16 };
    pmask       : { s : list bool | length s = 16 };
    pquestion   : { s : list question_t | length s < exp2_nat 16 };
    panswer     : { s : list resource_t | length s < exp2_nat 16 };
    pauthority  : { s : list resource_t | length s < exp2_nat 16 };
    padditional : { s : list resource_t | length s < exp2_nat 16 } }.

Definition FixInt_of_branch (b : CacheBranch) : {n | (n < exp2 2)%N}.
  refine (match b with
          | Yes => exist _ (3%N) _
          | No  => exist _ (0%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Definition FixInt_of_type (t : type_t) : {n | (n < exp2 16)%N}.
  refine (match t with
          | A     => exist _ (1%N) _
          | CNAME => exist _ (5%N) _
          | NS    => exist _ (2%N) _
          | MX    => exist _ (15%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Definition FixInt_of_class (c : class_t) : {n | (n < exp2 16)%N}.
  refine (match c with
          | IN => exist _ (1%N) _
          | CH => exist _ (3%N) _
          | HS => exist _ (4%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Definition encode_word (w : word_t) (ce : CacheEncode) :=
  compose btransformer (FixInt_encode _ (FixList_getlength w)) (
  compose btransformer (FixList_encode _ btransformer (Char_encode _) w)
                       (fun e => (nil, e))) ce.

Definition encode_branch (b : CacheBranch) (ce : CacheEncode) :=
  Enum_encode _ FixInt_of_branch b ce.

Definition encode_name (n : name_t) (ce : CacheEncode) :=
  SteppingList_encode _ _ _ btransformer encode_word (FixInt_encode _) encode_branch n ce.

Definition encode_question (q : question_t) (ce : CacheEncode) :=
  compose btransformer (encode_name q.(qname)) (
  compose btransformer (Enum_encode _ FixInt_of_type q.(qtype)) (
  compose btransformer (Enum_encode _ FixInt_of_class q.(qclass))
                       (fun e => (nil, e)))) ce.

Definition encode_resource (r : resource_t) (ce : CacheEncode) :=
  compose btransformer (encode_name r.(rname)) (
  compose btransformer (Enum_encode _ FixInt_of_type r.(rtype)) (
  compose btransformer (Enum_encode _ FixInt_of_class r.(rclass)) (
  compose btransformer (FixInt_encode _ r.(rttl)) (
  compose btransformer (FixInt_encode _ (FixList_getlength r.(rdata))) (
  compose btransformer (FixList_encode _ btransformer (Bool_encode _) r.(rdata))
                       (fun e => (nil, e))))))) ce.

Definition encode_packet (p : packet_t) (ce : CacheEncode) :=
  compose btransformer (IList_encode _ btransformer (Bool_encode _) p.(pid)) (
  compose btransformer (IList_encode _ btransformer (Bool_encode _) p.(pmask)) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(pquestion))) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(panswer))) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(pauthority))) (
  compose btransformer (FixInt_encode _ (FixList_getlength p.(padditional))) (
  compose btransformer (FixList_encode _ btransformer encode_question p.(pquestion)) (
  compose btransformer (FixList_encode _ btransformer encode_resource p.(panswer)) (
  compose btransformer (FixList_encode _ btransformer encode_resource p.(pauthority)) (
  compose btransformer (FixList_encode _ btransformer encode_resource p.(padditional))
                       (fun e => (nil, e))))))))))) ce.


Global Instance word_decoder
  : decoder cache btransformer (fun _ => True) encode_word.
Proof.
  unfold encode_word.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold FixList_predicate. intuition eauto. instantiate (1:=fun _ => True); intuition eauto.

  eexists. unfold encode_decode_correct.
  instantiate (1:=fun b e => (proj0, b, e)).
  intuition. inversion H1. inversion H2. subst. eauto. inversion H2.
  subst. eauto. inversion H2. inversion H1. eauto.  Defined.

Ltac enum_part eq_dec :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func in
    let h := fresh in
      evar (h:func_t);
      unify (fun n => if eq_dec _ n arg then res else h n) func;
      reflexivity
  end.

Ltac enum_finish :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func
    in  unify ((fun _  => res) : func_t) func;
        reflexivity
  end.

Ltac idtac' :=
  match goal with
    | |- _ => idtac (* I actually need this idtac for some unknown reason *)
  end.

Definition FixInt_eq_dec (size : nat) (n m : {n | (n < exp2 size)%N }) : {n = m} + {n <> m}.
  refine (if N.eq_dec (proj1_sig n) (proj1_sig m) then left _ else right _);
    destruct n; destruct m; try congruence; simpl in *; rewrite <- sig_equivalence; eauto.
Defined.

Ltac solve_enum :=
  let h := fresh in
  intros h; destruct h;
  [ idtac'; enum_part FixInt_eq_dec ..
  | idtac'; enum_finish ].

Global Instance branch_decoder
  : decoder cache btransformer (fun _ => True) encode_branch.
Proof.
  unfold encode_branch.
  eapply Enum_decoder.
  solve_enum.  Defined.

Global Instance name_decoder
  : decoder cache btransformer
            (@SteppingList_predicate _ (FixInt 6) _ _ (fun _ => True) (fun _ => True) (fun _ => True)) encode_name.
Proof.
  unfold encode_name.
  eapply SteppingListCache_decoder; intuition.
  eapply halt_dec.  Defined.


Global Instance question_decoder
  : decoder cache btransformer (fun _ => True) encode_question.
Proof.
  unfold encode_question.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold SteppingList_predicate. intuition.

  eapply compose_decoder. eapply Enum_decoder. solve_enum. intuition.
  instantiate (1:=fun _ => True). intuition. intuition.

  eapply compose_decoder. eapply Enum_decoder. solve_enum. intuition.
  instantiate (1:=fun _ => True). intuition. intuition.

  eexists. unfold encode_decode_correct.
  instantiate (1:=fun b e => (Build_question_t proj proj0 proj1, b, e)).
  intuition. inversion H1. inversion H2. subst. eauto. inversion H2.
  subst. destruct data. eauto. inversion H1. subst. inversion H2. eauto.  Defined.

Global Instance resource_decoder
  : decoder cache btransformer (fun _ => True) encode_resource.
Proof.
  unfold encode_resource.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold SteppingList_predicate. intuition.

  eapply compose_decoder. eapply Enum_decoder. solve_enum. intuition.
  instantiate (1:=fun _ => True). intuition. intuition.

  eapply compose_decoder. eapply Enum_decoder. solve_enum. intuition.
  instantiate (1:=fun _ => True). intuition. intuition.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold FixList_predicate. intuition eauto. instantiate (1:=fun _ => True); intuition eauto.

  eexists. unfold encode_decode_correct.
  instantiate (1:=fun b e => (Build_resource_t proj proj0 proj1 proj2 proj4, b, e)).
  intuition. inversion H1. inversion H2. subst. eauto. inversion H2.
  subst. destruct data. eauto. inversion H1. subst. inversion H2. eauto.  Defined.

Global Instance packet_decoder
  : decoder cache btransformer (fun _ => True) encode_packet.
Proof.
  unfold encode_packet.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); unfold IList_predicate; intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); unfold IList_predicate; intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold FixList_predicate. intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold FixList_predicate. intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold FixList_predicate. intuition eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  unfold FixList_predicate. intuition eauto.

  eexists. unfold encode_decode_correct.
  instantiate (1:=fun b e => (Build_packet_t proj proj0 proj5 proj6 proj7 proj8, b, e)).
  intuition. inversion H1. inversion H2. subst. eauto. inversion H2.
  subst. destruct data. eauto. inversion H1. subst. inversion H2. eauto.  Defined.

Definition encode_packet_i (p : packet_t) :=
  encode_packet p {| eMap := EMap.empty _;
                     dMap := DMap.empty _;
                     tick := 0;
                     extr := 0 |}.

Definition decode_packet_i (b : bin) :=
  decode (decoder:=packet_decoder) b {| eMap := EMap.empty _;
                                        dMap := DMap.empty _;
                                        tick := 0;
                                        extr := 0 |}.

Definition p : packet_t.
  refine ({| pid := exist _ (true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true :: nil) _;
             pmask := exist _ (true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true ::
                             true :: true :: true :: true :: nil) _;
             pquestion := exist _ nil _;
             panswer := exist _ nil _;
             pauthority := exist _ nil _;
             padditional := exist _ nil _ |}); admit.
Defined.

Eval vm_compute in (fst (encode_packet_i p)).
(* Eval vm_compute in (decode_packet_i (fst (encode_packet_i p))). *)

(*
Global Instance test_decoder
  : decoder test_cache btransformer (fun _ => True) encode_test.
Proof.
  unfold encode_test.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eexists. unfold encode_decode_correct.
  instantiate (1:=fun b e => (Build_test_t proj proj0 proj1 proj2, b, e)).
  intuition. inversion H1. inversion H2. subst. eauto. inversion H2.
  subst. destruct data. eauto. inversion H1. subst. inversion H2. eauto.
Defined. *)

Section Examples.
End Examples.



Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive ascii => char [
"(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

Check DMap.Raw.Proofs.L.find_rect.
Eval vm_compute in (fst (encode_packet_i p)).
(* Extraction "p.ml" encode_packet_i encode_packet'_i p. *)