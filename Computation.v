Require Import String Ensembles.
Require Import Common.

Reserved Notation "x >>= y" (at level 42, right associativity).
(*Reserved Notation "x <- y ; z" (at level 42, right associativity).
Reserved Notation "x ;; z" (at level 42, right associativity).*)
Reserved Notation "'call' f 'from' funcs [[ x ]]" (at level 35).
Reserved Notation "'call' f [[ x ]]" (at level 35).

Delimit Scope comp_scope with comp.
Delimit Scope long_comp_scope with long_comp.

Section Comp.
  Variable names : Type.
  Variables dom cod : names -> Type.

  Inductive Comp : Type -> Type :=
  | Return : forall A, A -> Comp A
  | Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B
  | Pick : forall A, Ensemble A -> Comp A
  | Call : forall name : names, Comp (dom name) -> Comp (cod name).
End Comp.

Bind Scope comp_scope with Comp.
Arguments Bind [_%type _ _ A%type B%type] _%comp _.
Arguments Call [_%type _ _] name _%comp.
Arguments Return [_ _ _ _] _.
Arguments Pick [_ _ _ _] _.

(*Notation "x >>= y" := (Bind x%comp y%comp) : comp_scope.
Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp)) : comp_scope.
Notation "x ;; z" := (Bind x%comp (fun _ => z%comp)) : comp_scope.
Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick A%type (fun x => P)) : comp_scope.*)
Notation ret := Return.

Notation "x >>= y" := (Bind x%comp y%comp) : comp_scope.
Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp))
                           (at level 81, right associativity,
                            format "'[v' x  <-  y ; '/' z ']'") : comp_scope.
Notation "x ;; z" := (Bind x%comp (fun _ => z%comp))
                       (at level 81, right associativity,
                        format "'[v' x ;; '/' z ']'") : comp_scope.
Notation "{ x  |  P }" := (@Pick _ _ _ _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick _ _ _ A%type (fun x => P)) : comp_scope.
Notation "'call' f [[ x ]]" := (@Call _ _ _ f x) : comp_scope.

Record BundledComp A :=
  Bundle { CompNames : _;
           CompDom : _;
           CompCod : _;
           Unbundle :> @Comp CompNames CompDom CompCod A;
           Lookup : forall name, CompDom name -> @Comp CompNames CompDom CompCod (CompCod name)}.

Delimit Scope bundled_comp_scope with bundled_comp.
Bind Scope bundled_comp_scope with BundledComp.
Open Scope bundled_comp_scope.

Notation "``[ c 'with' l ]``" := (@Bundle _ _ _ _ c l) (only parsing) : bundled_comp_scope.
Notation "`[ c ]`" := ``[ c with _ ]`` : bundled_comp_scope.
Notation "``[ c 'with' l ]``" := (@Bundle _ _ _ _ c l) : long_comp_scope.

Section comp.
  Definition Lift names dom cod A B (f : A -> B)
  : @Comp names dom cod A -> @Comp names dom cod B
    := fun x => (x' <- x;
                 Return (f x'))%comp.

  Definition Or names dom cod
  : @Comp names dom cod bool -> Comp _ _ bool -> Comp _ _ bool
    := fun c1 c2 =>
         (b1 <- c1;
          if b1
          then Return true
          else c2)%comp.

  Section computes_to.
    Variable names : Type.
    Variables dom cod : names -> Type.
    Variable lookup : forall name, dom name -> @Comp names dom cod (cod name).

    (** TODO(JasonGross): Should this be [CoInductive]? *)
    Inductive computes_to : forall A, @Comp names dom cod A -> A -> Prop :=
    | ReturnComputes : forall A v, @computes_to A (Return v) v
    | BindComputes : forall A B comp_a f comp_a_value comp_b_value,
                       @computes_to A comp_a comp_a_value
                       -> @computes_to B (f comp_a_value) comp_b_value
                       -> @computes_to B (Bind comp_a f) comp_b_value
    | PickComputes : forall A (P : Ensemble A) v, P v -> @computes_to A (Pick P) v
    | CallComputes : forall f x x_value fx_value,
                       @computes_to (dom f) x x_value
                       -> @computes_to (cod f) (@lookup f x_value) fx_value
                       -> @computes_to _ (Call f x) fx_value.

    Theorem computes_to_inv A (c : @Comp names dom cod A) v
    : computes_to c v -> match c in (@Comp _ _ _ A) return A -> Prop with
                           | Return _ x => @eq _ x
                           | Bind _ _ x f => fun v => exists comp_a_value,
                                                        computes_to x comp_a_value
                                                        /\ computes_to (f comp_a_value) v
                           | Pick _ P => P
                           | Call f x => fun fx_v =>
                                           exists xv,
                                             computes_to x xv
                                             /\ computes_to (@lookup f xv) fx_v
                         end v.
    Proof.
      destruct 1; eauto.
    Qed.

    Section CompInv.
      (** Lifting Properties on [A] to Computations on [A] **)

      (* Computation preserves invariants. *)
      Definition computational_inv A (P : Ensemble A) c :=
        forall v, computes_to c v -> P v.

      (* Relation to assist in building proofs of compuational_inv *)
      Inductive CompInv : forall {A : Type}, Ensemble A -> @Comp names dom cod A -> Prop :=
      | Return_Inv : forall A (a : A) (P : Ensemble A),
                       P a -> CompInv P (Return a)
      | Bind_Inv : forall A B (PA : Ensemble A) (PB : Ensemble B) comp_a comp_f,
                     CompInv PA comp_a ->
                     (forall (a : A), PA a -> CompInv PB (comp_f a)) ->
                     CompInv PB (Bind comp_a comp_f)
      | Pick_Inv : forall A (P P' : Ensemble A),
                     (forall a, P a -> P' a) -> CompInv P' (Pick P)
      | Call_Inv : forall f P P' comp_x,
                       @CompInv (dom f) P comp_x
                       -> (forall x, P x -> CompInv P' (@lookup f x))
                       -> CompInv P' (Call f comp_x).

      Lemma CompInv_inv A c (P : Ensemble A)
      : CompInv P c -> match c in (@Comp _ _ _ A) return Ensemble A -> Prop with
                         | Return A x => fun P => P x
                         | Bind A B x f => fun PB => exists PA : Ensemble A,
                                                       CompInv PA x /\
                                                       forall b : A, PA b -> CompInv PB (f b)
                         | Pick A P => fun P' => (forall a, P a -> P' a)
                         | Call f x => fun P' => exists P,
                                                   CompInv P x
                                                   /\ forall xv, P xv -> CompInv P' (@lookup f xv)
                       end P.
      Proof.
        destruct 1; eauto.
      Qed.

      Arguments computational_inv A P c / .

      Lemma CompInv_compuational_inv A (P : Ensemble A) c
      : CompInv P c -> computational_inv P c.
      Proof.
        induction c;
        intros; inversion_by CompInv_inv; simpl in *;
        intros; inversion_by computes_to_inv; simpl in *; subst;
        destruct_ex; split_and;
        eauto;
        try solve [ specialize_all_ways; eauto ].
        admit.
      Qed.
    End CompInv.
  End computes_to.

  Section is_computational.
    Variable names : Type.
    Variables dom cod : names -> Type.
    Variable lookup : forall name, dom name -> @Comp names dom cod (cod name).

    (** A [Comp] is maximally computational if it could be written without [Pick].  For now, we don't permit [Call] in computational things, because the halting problem. *)
    Inductive is_computational : forall A, @Comp names dom cod A -> Prop :=
    | Return_is_computational : forall A (x : A), is_computational (Return x)
    | Bind_is_computational : forall A B (cA : Comp _ _ A) (f : A -> Comp _ _ B),
                                is_computational cA
                                -> (forall a,
                                      @computes_to names dom cod lookup _ cA a -> is_computational (f a))
                                -> is_computational (Bind cA f)
(*    | Call_is_computational : forall f x,
                                is_computational x
                                -> (forall xv,
                                      @computes_to names dom cod lookup _ x xv
                                      -> is_computational (@lookup f xv))
                                -> is_computational (Call f x)*).

    Theorem is_computational_inv A (c : @Comp names dom cod A)
    : is_computational c
      -> match c with
           | Return _ _ => True
           | Bind _ _ x f => is_computational x
                             /\ forall v, @computes_to names dom cod lookup _ x v
                                          -> is_computational (f v)
           | Pick _ _ => False
           | Call f x => False (*is_computational x
                         /\ forall v, @computes_to names dom cod lookup _ x v
                                      -> is_computational (@lookup f v)*)
         end.
    Proof.
      destruct 1; eauto.
    Qed.

    (** It's possible to extract the value from a fully detiministic computation *)
    Fixpoint is_computational_unique_val A (c : @Comp names dom cod A) {struct c}
    : is_computational c -> { a | unique (computes_to lookup c) a }.
    Proof.
      refine match c as c return is_computational c -> { a | unique (computes_to lookup c) a } with
               | Return T x => fun _ => existT (unique (computes_to lookup (ret x)))
                                               x
                                               _
               | Pick _ _ => fun H => match is_computational_inv H with end
               | Bind _ _ x f
                 => fun H
                    => let H' := is_computational_inv H in
                       let xv := @is_computational_unique_val _ _ (proj1 H') in
                       let fxv := @is_computational_unique_val _ _ (proj2 H' _ (proj1 (proj2_sig xv))) in
                       exist (unique (computes_to _ _))
                             (proj1_sig fxv)
                             _
               | Call f x => fun H => match is_computational_inv H with end(*
                               let H' := is_computational_inv H in
                               let xv := @is_computational_unique_val _ _ (proj1 H') in
                               let fxv := @is_computational_unique_val _ _ (proj2 H' _ (proj1 (proj2_sig xv))) in
                               exist (unique (computes_to _ _))
                                     (proj1_sig fxv)
                                     _*)
             end;
      clearbodies;
      clear is_computational_unique_val;
      first [ abstract (repeat econstructor; intros; inversion_by computes_to_inv; eauto)
            | abstract (
                  simpl in *;
                  unfold unique in *;
                  destruct_sig;
                  repeat econstructor;
                  intros;
                  eauto;
                  inversion_by computes_to_inv;
                  apply_hyp;
                  do_with_hyp ltac:(fun H => erewrite H by eassumption);
                  eassumption
                ) ].
    Defined.

    Definition is_computational_val A (c : @Comp names dom cod A) (H : is_computational c) : A
      := proj1_sig (@is_computational_unique_val A c H).
    Definition is_computational_val_computes_to A (c : @Comp names dom cod A) (H : is_computational c) : computes_to lookup c (is_computational_val H)
      := proj1 (proj2_sig (@is_computational_unique_val A c H)).
    Definition is_computational_val_unique A (c : @Comp names dom cod A) (H : is_computational c)
    : forall x, computes_to lookup c x -> is_computational_val H = x
      := proj2 (proj2_sig (@is_computational_unique_val A c H)).
    Definition is_computational_val_all_eq A (c : @Comp names dom cod A) (H : is_computational c)
    : forall x y, computes_to lookup c x -> computes_to lookup c y -> x = y.
    Proof.
      intros.
      transitivity (@is_computational_val A c H); [ symmetry | ];
      apply is_computational_val_unique;
      assumption.
    Qed.
  End is_computational.

  Section monad.
    Variable names : Type.
    Variables dom cod : names -> Type.
    Variable lookup : forall name, dom name -> @Comp names dom cod (cod name).

    Local Ltac t :=
      split;
      intro;
      repeat match goal with
               | [ H : _ |- _ ]
                 => inversion H; clear H; subst; [];
                    repeat match goal with
                             | [ H : _ |- _ ] => apply inj_pair2 in H; subst
                           end
             end;
      repeat first [ eassumption
                   | solve [ constructor ]
                   | eapply BindComputes; (eassumption || (try eassumption; [])) ].

    Lemma bind_bind X Y Z (f : X -> @Comp names dom cod Y) (g : Y -> @Comp _ _ _ Z) x v
    : computes_to lookup (Bind (Bind x f) g) v
      <-> computes_to lookup (Bind x (fun u => Bind (f u) g)) v.
    Proof.
      t.
    Qed.

    Lemma bind_unit X Y (f : X -> @Comp names dom cod Y) x v
    : computes_to lookup (Bind (Return x) f) v
      <-> computes_to lookup (f x) v.
    Proof.
      t.
    Qed.

    Lemma unit_bind X (x : @Comp names dom cod X) v
    : computes_to lookup (Bind x (@Return _ _ _ X)) v
      <-> computes_to lookup x v.
    Proof.
      t.
    Qed.

    Lemma computes_under_bind X Y (f g : X -> @Comp names dom cod Y) x
    : (forall x v, computes_to lookup (f x) v <-> computes_to lookup (g x) v) ->
      (forall v, computes_to lookup (Bind x f) v <-> computes_to lookup (Bind x g) v).
    Proof.
      t; split_iff; eauto.
    Qed.

  End monad.

  (** The old program might be non-deterministic, and the new program
      less so.  This means we want to say that if [new] can compute to
      [v], then [old] should be able to compute to [v], too. *)
  Definition refine {A} {oldNames oldDom oldCod newNames newDom newCod}
             oldLookup newLookup
             (old : @Comp oldNames oldDom oldCod A)
             (new : @Comp newNames newDom newCod A)
    := forall v, computes_to newLookup new v -> computes_to oldLookup old v.
  Definition refineBundled {A} (old new : BundledComp A)
    := refine (Lookup old) (Lookup new) old new.

  Global Arguments refineBundled : simpl never.
  Typeclasses Transparent refineBundled.

  (** Define a symmetrized version of [refine] for ease of rewriting *)
  Definition refineEquiv {A} {oldNames oldDom oldCod newNames newDom newCod}
             oldLookup newLookup
             (old : @Comp oldNames oldDom oldCod A)
             (new : @Comp newNames newDom newCod A)
    := refine oldLookup newLookup old new /\ refine newLookup oldLookup new old.

  Definition refineBundledEquiv {A} (old new : BundledComp A)
    := refineEquiv (Lookup old) (Lookup new) old new.

  Global Arguments refineBundledEquiv : simpl never.
  Typeclasses Transparent refineBundledEquiv.

  Local Obligation Tactic := repeat first [ solve [ eauto ]
                                          | progress hnf in *
                                          | intro
                                          | split
                                          | progress split_and ].

  Global Program Instance refine_PreOrder A names dom cod lookup : PreOrder (@refine A names dom cod names dom cod lookup lookup).
  Global Program Instance refineBundled_PreOrder A : PreOrder (@refineBundled A).
  Global Program Instance refineEquiv_Equivalence A names dom cod lookup : Equivalence (@refineEquiv A names dom cod names dom cod lookup lookup).
  Global Program Instance refineBundledEquiv_Equivalence A : Equivalence (@refineBundledEquiv A).

  Section monad_refine.
    Variable names : Type.
    Variables dom cod : names -> Type.
    Variable lookup : forall name, dom name -> @Comp names dom cod (cod name).

    Lemma refineEquiv_bind_bind X Y Z (f : X -> @Comp names dom cod Y) (g : Y -> @Comp _ _ _ Z) x
    : refineEquiv lookup lookup
                  (Bind (Bind x f) g)
                  (Bind x (fun u => Bind (f u) g)).
    Proof.
      split; intro; apply bind_bind.
    Qed.

    Definition refineBundledEquiv_bind_bind
    : forall X Y Z f g x, refineBundledEquiv ``[ _ with lookup ]`` ``[ _ with lookup ]``
      := refineEquiv_bind_bind.

    Lemma refineEquiv_bind_unit X Y (f : X -> @Comp names dom cod Y) x
    : refineEquiv lookup lookup
                  (Bind (Return x) f)
                  (f x).
    Proof.
      split; intro; simpl; apply bind_unit.
    Qed.

    Definition refineBundledEquiv_bind_unit
    : forall X Y f x, refineBundledEquiv ``[ _ with lookup ]`` ``[ _ with lookup ]``
      := refineEquiv_bind_unit.

    Lemma refineEquiv_unit_bind X (x : @Comp _ _ _ X)
    : refineEquiv lookup lookup
                  (Bind x (@Return _ _ _ X))
                  x.
    Proof.
      split; intro; apply unit_bind.
    Qed.

    Definition refineBundledEquiv_unit_bind
    : forall X x, refineBundledEquiv ``[ _ with lookup ]`` ``[ _ with lookup ]``
      := refineEquiv_unit_bind.

    Lemma refineEquiv_under_bind X Y (f g : X -> @Comp _ _ _ Y) x
          (eqv_f_g : forall x, refineEquiv lookup lookup (f x) (g x))
    : refineEquiv lookup lookup
                  (Bind x f)
                  (Bind x g).
    Proof.
      split; unfold refine; simpl in *; intros; eapply computes_under_bind;
      intros; eauto; split; eapply eqv_f_g.
    Qed.

    Definition refineBundledEquiv_under_bind
    : forall X Y f g x
             (equv_f_g : forall x, refineBundledEquiv ``[ _ with lookup ]`` ``[ _ with lookup ]``),
        refineBundledEquiv ``[ _ with lookup ]`` ``[ _ with lookup ]``
      := refineEquiv_under_bind.
  End monad_refine.
End comp.

Ltac inversion_by rule :=
  progress repeat first [ progress destruct_ex
                        | progress split_and
                        | apply_in_hyp_no_cbv_match rule ].

Add Parametric Relation A names dom cod lookup
: (@Comp names dom cod A) (@refine A names dom cod names dom cod lookup lookup)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refine_rel.

Add Parametric Relation A
: (BundledComp A) (@refineBundled A)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refineBundled_rel.

Add Parametric Relation A names dom cod lookup
: (@Comp names dom cod A) (@refineEquiv A names dom cod names dom cod lookup lookup)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
    as refineEquiv_rel.

Add Parametric Relation A
: (BundledComp A) (@refineBundledEquiv A)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
    as refineBundledEquiv_rel.

Local Ltac t := unfold impl; intros; repeat (eapply_hyp || etransitivity).

Add Parametric Morphism A names dom cod lookup
: (@refine A names dom cod names dom cod lookup lookup)
  with signature
  (@refine A names dom cod names dom cod lookup lookup) --> (@refine A names dom cod names dom cod lookup lookup) ++> impl
    as refine_refine.
Proof. t. Qed.

(*Add Parametric Morphism A names dom cod lookup
: (@refine A names dom cod names dom cod lookup lookup)
  with signature
  (@refineEquiv A names dom cod names dom cod lookup lookup) --> (@refineEquiv A names dom cod names dom cod lookup lookup) ++> impl
    as refine_refineEquiv.
Proof. t. Qed.*)


Add Parametric Morphism A
: (@refineBundled A)
  with signature
  (@refineBundled A) --> (@refineBundled A) ++> impl
    as refineBundled_refineBundled.
Proof. t. Qed.

(*Add Parametric Morphism A
: (@refineBundled A)
  with signature
  (@refineBundledEquiv A) --> (@refineBundledEquiv A) ++> impl
    as refineBundled_refineBundledEquiv.
Proof. t. Qed.*)

Hint Constructors CompInv computes_to.

Add Parametric Morphism names dom cod lookup A B
: (@Bind names dom cod A B)
    with signature
    (@refine A names dom cod names dom cod lookup lookup)
      ==> (pointwise_relation _ (@refine B names dom cod names dom cod lookup lookup))
      ==> (@refine B names dom cod names dom cod lookup lookup)
      as refine_bind.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine in *; simpl in *.
  intros.
  inversion_by computes_to_inv.
  eauto.
Qed.

Add Parametric Morphism names dom cod lookup A B
: (@Bind names dom cod A B)
    with signature
    (@refineEquiv A names dom cod names dom cod lookup lookup)
      ==> (pointwise_relation _ (@refineEquiv B names dom cod names dom cod lookup lookup))
      ==> (@refineEquiv B names dom cod names dom cod lookup lookup)
      as refineEquiv_bind.
Proof.
  simpl; intros.
  unfold pointwise_relation, refineEquiv, refine in *.
  split_and; simpl in *.
  split; intros;
  inversion_by computes_to_inv;
  eauto.
Qed.

(*Add Parametric Morphism names dom cod lookup A B
: (@Bind names dom cod A B)
    with signature
    (@refineEquiv A names dom cod names dom cod lookup lookup)
      ==> (pointwise_relation _ (@refineEquiv B names dom cod names dom cod lookup lookup))
      ==> (@refine B names dom cod names dom cod lookup lookup)
      as refineEquiv_refine_bind.
Proof.
  intros.
  refine (proj1 (_ : refineEquiv _ _ _ _)).
  simpl in *.
  setoid_rewrite <- H.
  setoid_rewrite_hyp.
  reflexivity.
Qed.*)

Local Arguments impl _ _ / .
Global Arguments computational_inv [names dom cod] lookup [A] P c / .

Add Parametric Morphism names dom cod lookup A P : (@computational_inv names dom cod lookup A P)
  with signature
  (@refine A names dom cod names dom cod lookup lookup) ++> impl
    as refineCompInv.
Proof. simpl; eauto. Qed.

Section general_refine_lemmas.
  Local Ltac t :=
    repeat first [ progress eauto
                 | eassumption
                 | progress split_iff
                 | progress inversion_by computes_to_inv
                 | progress subst
                 | intro
                 | econstructor
                 | erewrite is_computational_val_unique
                 | progress destruct_head_hnf prod
                 | progress destruct_head_hnf and
                 | progress specialize_all_ways ].

  Lemma refineEquiv_is_computational A {names dom cod names' dom' cod'} (c : @Comp names dom cod A) lookup lookup' (CompC : is_computational lookup c)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                c (ret (is_computational_val CompC)).
  Proof.
    unfold refineEquiv, refine.
    pose proof (is_computational_val_computes_to CompC).
    t.
  Qed.

  Definition refineBundledEquiv_is_computational A {names dom cod} (c : BundledComp A) lookup
  : forall (CompC : is_computational (Lookup c) c),
      refineBundledEquiv c (@Bundle A names dom cod (ret (is_computational_val CompC)) lookup)
    := refineEquiv_is_computational lookup.

  Lemma refine_pick A {names dom cod names' dom' cod'} lookup lookup'
        (P : A -> Prop) c (H : forall x, computes_to lookup' c x -> P x)
  : @refine A names dom cod names' dom' cod' lookup lookup'
            { x : A | P x }%comp
            c.
  Proof. t. Qed.

  Definition refineBundled_pick A {names dom cod} lookup
             P (c : BundledComp A)
  : _ -> refineBundled ``[ { x : A | P x }%comp with lookup ]``
                       c
    := @refine_pick _ names dom cod _ _ _ lookup _ P c.

  Lemma refine_pick_pick A {names dom cod names' dom' cod'} lookup lookup' (P1 P2 : A -> Prop)
        (H : forall x, P2 x -> P1 x)
  : @refine _ names dom cod names' dom' cod' lookup lookup'
            { x : A | P1 x }%comp
            { x : A | P2 x }%comp.
  Proof. t. Qed.

  Definition refineBundled_pick_pick
  : forall A {names dom cod names' dom' cod'} lookup lookup' P1 P2 H,
      refineBundled ``[ _ with lookup ]``
                    ``[ _ with lookup' ]``
    := refine_pick_pick.

  Lemma refineEquiv_pick_pick A {names dom cod names' dom' cod'} lookup lookup' (P1 P2 : A -> Prop)
        (H : forall x, P1 x <-> P2 x)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                 { x : A | P1 x }%comp
                 { x : A | P2 x }%comp.
  Proof. t. Qed.

  Definition refineBundledEquiv_pick_pick
  : forall A {names dom cod names' dom' cod'} lookup lookup' P1 P2 H,
      refineBundledEquiv ``[ _ with lookup ]``
                         ``[ _ with lookup' ]``
    := refineEquiv_pick_pick.

  Lemma refineEquiv_pick_pair {names dom cod names' dom' cod'} lookup lookup' A B (PA : A -> Prop) (PB : B -> Prop)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                 { x : A * B | PA (fst x) /\ PB (snd x) }%comp
                 (a <- { a : A | PA a };
                  b <- { b : B | PB b };
                  ret (a, b))%comp.
  Proof. t. Qed.

  Definition refineEquivBundled_pick_pair
  : forall A {names dom cod names' dom' cod'} lookup lookup' P1 P2 H,
      refineBundledEquiv ``[ _ with lookup ]``
                         ``[ _ with lookup' ]``
    := refineEquiv_pick_pick.

  Definition refineEquiv_split_ex {names dom cod names' dom' cod'} lookup lookup' A B (P : A -> Prop) (P' : A -> B -> Prop)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                 { b | exists a, P a /\ P' a b }%comp
                 (a <- { a | P a /\ exists b, P' a b };
                  { b | P' a b })%comp.
  Proof. t. Qed.

  Definition refineBundledEquiv_split_ex
  : forall {names dom cod names' dom' cod'} lookup lookup' A B P P',
      refineBundledEquiv `[ _ ]` `[ _ ]`
    := @refineEquiv_split_ex.

  Definition refineEquiv_pick_contr_ret {names dom cod names' dom' cod'} lookup lookup' A (P : A -> Prop)
             (x : A) (H : unique P x)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                 { y | P y }
                 (ret x).
  Proof. t. Qed.

  Definition refineEquiv_pick_eq {names dom cod names' dom' cod'} lookup lookup'
             A (x : A)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                 { y | y = x }%comp
                 (ret x).
  Proof. t. Qed.

  Definition refineBundledEquiv_pick_eq
  : forall {names dom cod names' dom' cod'} lookup lookup'
           A (x : A),
      refineBundledEquiv `[ _ ]` `[ _ ]`
    := @refineEquiv_pick_eq.

  Definition refineEquiv_pick_eq' {names dom cod names' dom' cod'} lookup lookup'
             A (x : A)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                 { y | x = y }%comp
                 (ret x).
  Proof. t. Qed.

  Definition refineBundledEquiv_pick_eq'
  : forall {names dom cod names' dom' cod'} lookup lookup'
           A (x : A),
      refineBundledEquiv `[ _ ]` `[ _ ]`
    := @refineEquiv_pick_eq'.

  Definition refineBundledEquiv_split_func_ex {names dom cod names' dom' cod'} lookup lookup'
             A B (P : A -> Prop) (f : A -> B)
  : refineBundledEquiv (@Bundle _ names dom cod { b | exists a, P a /\ b = f a}%comp lookup)
                       (@Bundle _ names' dom' cod'
                                (a <- { a | P a};
                                 ret (f a))%comp
                                lookup').
  Proof.
    repeat setoid_rewrite refineBundledEquiv_split_ex.
    (** I want to just [setoid_rewrite refineBundledEquiv_pick_eq].  But I can't because things don't line up nicely, and there are no parameterized setoid relations.  :-( *)
    setoid_rewrite refineBundledEquiv_pick_eq.
    erewrite refineEquiv_pick_pick.
    - reflexivity.
    - abstract (repeat (intro || esplit); intuition).
  Qed.

  Definition refineEquiv_split_func_ex {names dom cod names' dom' cod'} lookup lookup'
             A B (P : A -> Prop) (f : A -> B)
  : @refineEquiv _ names dom cod names' dom' cod' lookup lookup'
                 { b | exists a, P a /\ b = f a}%comp
                 (a <- { a | P a};
                  ret (f a))%comp.
  Proof.
    repeat setoid_rewrite refineBundledEquiv_split_ex.
    setoid_rewrite refineEquiv_pick_eq.
    erewrite refineEquiv_pick_pick.
    - reflexivity.
    - abstract (repeat (intro || esplit); intuition).
  Qed.

  Definition refineEquiv_split_func_ex2 A A' B (P : A -> Prop) (P' : A' -> Prop)
             (f : A -> A' -> B)
  : refineEquiv { b | exists a, P a /\ exists a', P' a' /\ b = f a a'}%comp
                (a <- { a | P a};
                 a' <- { a' | P' a'};
                 ret (f a a'))%comp.
  Proof.
    repeat setoid_rewrite refineEquiv_split_ex.
    setoid_rewrite refineEquiv_pick_eq.
    split; intro; intros;
    inversion_by computes_to_inv; subst;
    repeat econstructor; eassumption.
  Qed.
End general_refine_lemmas.

Create HintDb refine_monad discriminated.

(*Hint Rewrite refine_bind_bind refine_bind_unit refine_unit_bind : refine_monad.
Hint Rewrite <- refine_bind_bind' refine_bind_unit' refine_unit_bind' : refine_monad.*)
Hint Rewrite refineEquiv_bind_bind refineEquiv_bind_unit refineEquiv_unit_bind : refine_monad.
(* Ideally we would throw refineEquiv_under_bind in here as well, but it gets stuck *)


Ltac interleave_autorewrite_refine_monad_with tac :=
  repeat first [ reflexivity
               | progress tac
               | progress autorewrite with refine_monad
               (*| rewrite refine_bind_bind'; progress tac
               | rewrite refine_bind_unit'; progress tac
               | rewrite refine_unit_bind'; progress tac
               | rewrite <- refine_bind_bind; progress tac
               | rewrite <- refine_bind_unit; progress tac
               | rewrite <- refine_unit_bind; progress tac ]*)
               | rewrite <- !refineEquiv_bind_bind; progress tac
               | rewrite <- !refineEquiv_bind_unit; progress tac
               | rewrite <- !refineEquiv_unit_bind; progress tac
               (*| rewrite <- !refineEquiv_under_bind; progress tac *)].
