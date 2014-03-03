Require Import String Ensembles.
Require Import Common.

Class Context :=
  { names : Type;
    dom : names -> Type;
    cod : names -> Type }.

Section Comp.
  Context {ctx : Context}.

  Inductive Comp : Type -> Type :=
  | Return : forall A, A -> Comp A
  | Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B
  | Pick : forall A, Ensemble A -> Comp A
  | Call : forall name : names, dom name -> Comp (cod name).
End Comp.

Bind Scope comp_scope with Comp.
Arguments Bind {_} [A%type B%type] _%comp _.
Arguments Call {_} name _%comp.
Arguments Return {_} [_] _.
Arguments Pick {_} [_] _.

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
Notation "{ x  |  P }" := (@Pick _ _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick _ A%type (fun x => P)) : comp_scope.
Notation "'call' f [[ x ]]" := (@Call _ f x) : comp_scope.

Class LookupContext :=
  { LContext :> Context;
    lookup : forall name, dom name -> Comp (cod name) }.

Coercion LContext : LookupContext >-> Context.

Record BundledComp A :=
  Bundle { CompContext : LookupContext;
           Unbundle :> Comp A }.

Bind Scope bundled_comp_scope with BundledComp.
Global Open Scope bundled_comp_scope.

Notation "``[ c 'with' l ]``" := (@Bundle _ l c) (only parsing) : bundled_comp_scope.
Notation "`[ c ]`" := ``[ c with _ ]`` : bundled_comp_scope.
Notation "``[ c 'with' l ]``" := (``[ c with l ]``)%bundled_comp : long_comp_scope.

Section comp.
  Definition Lift `{ctx : Context} A B (f : A -> B)
  : Comp A -> Comp B
    := fun x => (x' <- x;
                 Return (f x'))%comp.

  Definition Or `{ctx : Context}
  : Comp bool -> Comp bool -> Comp bool
    := fun c1 c2 =>
         (b1 <- c1;
          if b1
          then Return true
          else c2)%comp.
End comp.

Section computes_to.
  Context `{ctx : LookupContext}.

  (** TODO(JasonGross): Should this be [CoInductive]? *)
  Inductive computes_to : forall A, Comp A -> A -> Prop :=
  | ReturnComputes : forall A v, @computes_to A (Return v) v
  | BindComputes : forall A B comp_a f comp_a_value comp_b_value,
                     @computes_to A comp_a comp_a_value
                     -> @computes_to B (f comp_a_value) comp_b_value
                     -> @computes_to B (Bind comp_a f) comp_b_value
  | PickComputes : forall A (P : Ensemble A) v, P v -> @computes_to A (Pick P) v
  | CallComputes : forall f x fx_value,
                     @computes_to (cod f) (@lookup _ f x) fx_value
                     -> @computes_to _ (Call f x) fx_value.

  Theorem computes_to_inv A (c : Comp A) v
  : computes_to c v -> match c in (Comp A) return A -> Prop with
                         | Return _ x => @eq _ x
                         | Bind _ _ x f => fun v => exists comp_a_value,
                                                      computes_to x comp_a_value
                                                      /\ computes_to (f comp_a_value) v
                         | Pick _ P => P
                         | Call f x => fun fx_v =>
                                         computes_to (@lookup _ f x) fx_v
                       end v.
  Proof.
    destruct 1; eauto.
  Qed.
End computes_to.

Notation "c ↝ v" := (computes_to c v).

Section is_computational.
  Context `{ctx : LookupContext}.

  (** A [Comp] is maximally computational if it could be written without [Pick].  For now, we don't permit [Call] in computational things, because the halting problem. *)
  Inductive is_computational : forall A, Comp A -> Prop :=
  | Return_is_computational : forall A (x : A), is_computational (Return x)
  | Bind_is_computational : forall A B (cA : Comp A) (f : A -> Comp B),
                              is_computational cA
                              -> (forall a,
                                    @computes_to _ _ cA a -> is_computational (f a))
                              -> is_computational (Bind cA f)
  (*    | Call_is_computational : forall f x,
                                is_computational x
                                -> (forall xv,
                                      @computes_to names dom cod lookup _ x xv
                                      -> is_computational (@lookup f xv))
                                -> is_computational (Call f x)*).

  Theorem is_computational_inv A (c : Comp A)
  : is_computational c
    -> match c with
         | Return _ _ => True
         | Bind _ _ x f => is_computational x
                           /\ forall v, x ↝ v
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
  Fixpoint is_computational_unique_val A (c : Comp A) {struct c}
  : is_computational c -> { a | unique (computes_to c) a }.
  Proof.
    refine match c as c return is_computational c -> { a | unique (computes_to c) a } with
             | Return T x => fun _ => existT (unique (computes_to (ret x)))
                                             x
                                             _
             | Pick _ _ => fun H => match is_computational_inv H with end
             | Bind _ _ x f
               => fun H
                  => let H' := is_computational_inv H in
                     let xv := @is_computational_unique_val _ _ (proj1 H') in
                     let fxv := @is_computational_unique_val _ _ (proj2 H' _ (proj1 (proj2_sig xv))) in
                     exist (unique (computes_to _))
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

  Definition is_computational_val A (c : Comp A) (H : is_computational c) : A
    := proj1_sig (@is_computational_unique_val A c H).
  Definition is_computational_val_computes_to A (c : Comp A) (H : is_computational c) : c ↝ (is_computational_val H)
    := proj1 (proj2_sig (@is_computational_unique_val A c H)).
  Definition is_computational_val_unique A (c : Comp A) (H : is_computational c)
  : forall x, c ↝ x -> is_computational_val H = x
    := proj2 (proj2_sig (@is_computational_unique_val A c H)).
  Definition is_computational_val_all_eq A (c : Comp A) (H : is_computational c)
  : forall x y, c ↝ x -> c ↝ y -> x = y.
  Proof.
    intros.
    transitivity (@is_computational_val A c H); [ symmetry | ];
    apply is_computational_val_unique;
    assumption.
  Qed.
End is_computational.

(** The old program might be non-deterministic, and the new program
      less so.  This means we want to say that if [new] can compute to
      [v], then [old] should be able to compute to [v], too. *)
Definition refine {A}
           {oldCtx newCtx : LookupContext}
           (old : @Comp oldCtx A)
           (new : @Comp newCtx A)
  := forall v, new ↝ v -> old ↝ v.

Definition refineBundled {A} (old new : BundledComp A)
  := refine old new.

Global Arguments refineBundled : simpl never.
Typeclasses Transparent refineBundled.

(** Define a symmetrized version of [refine] for ease of rewriting *)
Definition refineEquiv {A}
           {oldCtx newCtx : LookupContext}
           (old : @Comp oldCtx A)
           (new : @Comp newCtx A)
  := refine old new /\ refine new old.

Definition refineBundledEquiv {A} (old new : BundledComp A)
  := refineEquiv old new.

Global Arguments refineBundledEquiv : simpl never.
Typeclasses Transparent refineBundledEquiv.

Local Obligation Tactic := repeat first [ solve [ eauto ]
                                        | progress hnf in *
                                        | intro
                                        | split
                                        | progress split_and ].

Global Program Instance refine_PreOrder A `{LookupContext} : PreOrder (@refine A _ _).
Global Program Instance refineBundled_PreOrder A : PreOrder (@refineBundled A).
Global Program Instance refineEquiv_Equivalence A `{LookupContext} : Equivalence (@refineEquiv A _ _).
Global Program Instance refineBundledEquiv_Equivalence A : Equivalence (@refineBundledEquiv A).
