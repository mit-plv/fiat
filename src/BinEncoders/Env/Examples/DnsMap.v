Require Import
        Coq.Structures.OrderedTypeEx
        Coq.Structures.OrderedType
        Coq.FSets.FMapAVL
        Coq.Strings.Ascii.

Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig
        Fiat.BinEncoders.Env.Common.Compose.

Require Import
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.BinLib.Char
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Enum
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.Lib.IList
        Fiat.BinEncoders.Env.Lib.SteppingCacheList.

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
    destruct l'. left. abstract intuition.
    right. abstract (intro; inversion H).
    destruct l'. right. abstract (intro; inversion H).
    destruct (IHl l').
    destruct (O.eq_dec a t0). left. abstract (constructor; auto).
    right. abstract (intro; elim n; inversion H; auto).
    right. abstract (intro; elim n; inversion H; auto).
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
  Definition eq (c1 c2 : t) := N_of_ascii c1 = N_of_ascii c2.
  Definition lt (c1 c2 : t) := N.lt (N_of_ascii c1) (N_of_ascii c2).

  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof. unfold eq. intros.
         destruct (N.eqb (N_of_ascii l) (N_of_ascii l')) eqn: eq.
         - left. abstract (rewrite <- N.eqb_eq; eauto).
         - right. abstract (rewrite <- N.eqb_neq; eauto).  Defined.

  Lemma eq_refl : forall x, eq x x.
  Proof. reflexivity. Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof. intros. symmetry. eauto. Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. intros. unfold eq in *. rewrite H. rewrite H0. eauto. Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof. intros. unfold lt in *. eapply N.lt_trans; eauto. Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof. intros. unfold eq, lt in *. intro.
         rewrite <- N.compare_lt_iff in H.
         rewrite <- N.compare_eq_iff in H0.
         congruence. Qed.

  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    intros. unfold lt, eq.
    destruct (N.compare (N_of_ascii x) (N_of_ascii y)) eqn: eq.
    - eapply EQ. abstract (rewrite <- N.compare_eq_iff; eauto).
    - eapply LT. abstract (rewrite <- N.compare_lt_iff; eauto).
    - eapply GT. abstract (rewrite <- N.compare_gt_iff; eauto).
  Defined.
End ascii_as_OT.

Record word_t :=
  { word : { l : list ascii | length l < exp2_nat 6 } }.
Definition position_t := uint 14.

Module list_ascii_as_OT := list_as_OT ascii_as_OT.
Module list_ascii_as_OT_with_P <: OrderedTypeWithP list_ascii_as_OT.
  Definition P (l : list ascii) := length l < exp2_nat 6.
End list_ascii_as_OT_with_P.

Module word_as_OT := sig_as_OT list_ascii_as_OT list_ascii_as_OT_with_P.

Module N_as_OT_with_P <: OrderedTypeWithP N_as_OT.
  Definition P (n : N) := (n < exp2 14)%N.
End N_as_OT_with_P.

Module position_as_OT := sig_as_OT N_as_OT N_as_OT_with_P.

Module word_t_as_OT <: OrderedType.
  Import word_as_OT.

  Definition t := word_t.
  Definition eq (a b : word_t) := eq a.(word) b.(word).
  Definition lt (a b : word_t) := lt a.(word) b.(word).

  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof.
    destruct l; destruct l'; apply eq_dec.  Defined.

  Lemma eq_refl : forall x, eq x x.
  Proof.
    destruct x; apply eq_refl.  Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    destruct x; destruct y; apply eq_sym.  Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    destruct x; destruct y; destruct z; apply eq_trans.  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    destruct x; destruct y; destruct z; apply lt_trans.  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
  Proof.
    destruct x; destruct y; apply lt_not_eq.  Qed.

  Lemma compare : forall x y, Compare lt eq x y.
  Proof.
    destruct x; destruct y.
    refine (match compare word0 word1 with
            | LT _ => LT _
            | EQ _ => EQ _
            | GT _ => GT _
            end); unfold lt, eq; eauto.  Defined.
End word_t_as_OT.

Module list_word_t_as_OT := list_as_OT word_t_as_OT.

Module EMap := FMapAVL.Make(list_word_t_as_OT).
Module DMap := FMapAVL.Make(position_as_OT).

Definition EMapT := EMap.t position_t.
Definition DMapT := DMap.t (list word_t).

Record CacheT :=
  { eMap : EMapT;
    dMap : DMapT;
    offs : N }.

Instance cache : Cache :=
  {| CacheEncode := CacheT;
     CacheDecode := CacheT;
     Equiv := fun x y => x = y /\
                         forall p q, EMap.MapsTo p q x.(eMap) <-> DMap.MapsTo q p x.(dMap) |}.

Instance cacheAddN : CacheAdd cache N :=
  {| addE := fun c n => {| eMap := c.(eMap);
                           dMap := c.(dMap);
                           offs := c.(offs) + n |};
     addD := fun c n => {| eMap := c.(eMap);
                           dMap := c.(dMap);
                           offs := c.(offs) + n |} |}.
Proof. abstract (simpl; intuition; subst; eauto).  Defined.

Require Import Coq.FSets.FMapFacts.
Module EMapFacts := WFacts_fun (list_word_t_as_OT) (EMap).
Module DMapFacts := WFacts_fun (position_as_OT) (DMap).

Lemma cacheAddPair' :
  forall (ce : CacheEncode) (cd : CacheDecode) (t : EMap.key * DMap.key),
   Equiv ce cd ->
   Equiv
     (let (l, p) := t in
      if EMap.mem (elt:=position_t) l (eMap ce) || DMap.mem (elt:=list word_t) p (dMap ce)
      then ce
      else {| eMap := EMap.add l p (eMap ce); dMap := DMap.add p l (dMap ce); offs := offs ce |})
     (let (l, p) := t in
      if EMap.mem (elt:=position_t) l (eMap cd) || DMap.mem (elt:=list word_t) p (dMap cd)
      then cd
      else {| eMap := EMap.add l p (eMap cd); dMap := DMap.add p l (dMap cd); offs := offs cd |}).
Proof.
  Local Hint Resolve EMap.E.eq_refl.
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
      clear -H3. destruct a. destruct w. simpl in *.
      destruct word0 eqn: ?. simpl in *. destruct word1 eqn: ?. simpl in *.
      f_equal. erewrite <- sig_equivalence.
      clear -H3; generalize dependent x0; induction x; intuition.
      inversion H3; eauto.
      destruct x0; inversion H3; subst; clear H3.
      erewrite IHx; eauto; f_equal.
      apply f_equal with (f:=ascii_of_N) in H2. rewrite !ascii_N_embedding in H2. eauto. }
    intuition eauto.
    right. intuition. apply H1 in H4. clear - eq2 H4 H0.
    destruct b eqn: ?. destruct q eqn: ?. erewrite sig_equivalence with (P:=N_as_OT_with_P.P) (n_pf:=p0) (m_pf:=l) in H0.
    simpl in H0. erewrite <- Heqk in H0. unfold N_as_OT_with_P.P in *. rewrite <- Heqp1 in H0.
    subst. inversion H0. subst. clear H0. rewrite DMapFacts.mem_find_b in eq2.
    rewrite DMapFacts.find_mapsto_iff in H4.
    erewrite (proj1 (sig_equivalence _ ((fun n : N => (n < exp2 14)%N)) x0 x0 p0 l) eq_refl) in eq2.
    unfold EMap.key, list_ascii_as_OT_with_P.P in *. erewrite H4 in eq2. congruence.
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
      intuition eauto. }
    { right. intuition. apply H1 in H4. clear - eq1 H4 H0.
      rewrite EMapFacts.mem_find_b in eq1.
      assert (a = p).
      { clear -H0; generalize dependent p; induction a; intuition.
        inversion H0; eauto.
        destruct p; inversion H0; subst; clear H0.
        erewrite IHa; eauto; f_equal.
        clear -H3. destruct a. destruct w.
        destruct word0 eqn: ?. destruct word1 eqn: ?. simpl in *.
        f_equal. erewrite <- sig_equivalence.
        clear -H3; generalize dependent x0; induction x; intuition.
        inversion H3; eauto.
        destruct x0; inversion H3; subst; clear H3.
        erewrite IHx; eauto; f_equal.
        apply f_equal with (f:=ascii_of_N) in H2. rewrite !ascii_N_embedding in H2. eauto. }
      subst. rewrite EMapFacts.find_mapsto_iff in H4.
      rewrite H4 in eq1. congruence.
      apply H1. eauto. }
  Grab Existential Variables.
  simpl in *. omega.
  simpl in *. omega.
  simpl in *. omega.
  simpl in *. omega.  Qed.

Instance cacheAddPair : CacheAdd cache (list word_t * position_t) :=
  {| addE := fun c (b : _ * _) => let (l, p) := b
                                  in if EMap.mem l c.(eMap) || DMap.mem p c.(dMap)
                                     then c
                                     else {| eMap := EMap.add l p c.(eMap);
                                             dMap := DMap.add p l c.(dMap);
                                             offs := c.(offs) |};
     addD := fun c (b : _ * _) => let (l, p) := b
                                  in if EMap.mem l c.(eMap) || DMap.mem p c.(dMap)
                                     then c
                                     else {| eMap := EMap.add l p c.(eMap);
                                             dMap := DMap.add p l c.(dMap);
                                             offs := c.(offs) |} |}.
Proof. eapply cacheAddPair'.  Qed.

Definition get_position (n : N) : position_t.
  refine (if position_as_OT.OP.lt_dec n (exp2 14)
          then exist _ n _
          else exist _ 0%N _).
  abstract eauto.
  abstract (rewrite <- N.compare_lt_iff; eauto).
Defined.

Instance cachePeek : CachePeek cache position_t :=
  {| peekE := fun c => get_position (N.div c.(offs) 8);
     peekD := fun c => get_position (N.div c.(offs) 8) |}.
Proof.
  abstract (unfold Equiv;
  intuition;
  destruct ce; destruct cd; simpl in *;
  inversion H; inversion H0; eauto).
Defined.

Instance cacheGet : CacheGet cache (list word_t) position_t :=
  {| getE := fun c l => EMap.find l c.(eMap);
     getD := fun c p => DMap.find p c.(dMap) |}.
Proof.
  abstract (
  simpl; intuition; subst; [
  apply DMap.find_1; apply EMap.find_2 in H; apply H1; eauto |
  apply EMap.find_1; apply DMap.find_2 in H; apply H1; eauto ]).
Defined.