Require Import String Ensembles.
Require Import Common.

Inductive Comp : Type -> Type :=
| Return : forall A, A -> Comp A
| Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B
| Pick : forall A, Ensemble A -> Comp A.

Bind Scope comp_scope with Comp.
Arguments Bind [A%type B%type] _%comp _.
Arguments Return [_] _.
Arguments Pick [_] _.

Notation ret := Return.

Notation "x >>= y" := (Bind x%comp y%comp) : comp_scope.
Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp))
                           (at level 81, right associativity,
                            format "'[v' x  <-  y ; '/' z ']'") : comp_scope.
Notation "x ;; z" := (Bind x%comp (fun _ => z%comp))
                       (at level 81, right associativity,
                        format "'[v' x ;; '/' z ']'") : comp_scope.
Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick A%type (fun x => P)) : comp_scope.

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

  Inductive computes_to : forall A, Comp A -> A -> Prop :=
  | ReturnComputes : forall A v, @computes_to A (Return v) v
  | BindComputes : forall A B comp_a f comp_a_value comp_b_value,
                     @computes_to A comp_a comp_a_value
                     -> @computes_to B (f comp_a_value) comp_b_value
                     -> @computes_to B (Bind comp_a f) comp_b_value
  | PickComputes : forall A (P : Ensemble A) v, P v -> @computes_to A (Pick P) v.

  Theorem computes_to_inv A (c : Comp A) v
  : computes_to c v -> match c in (Comp A) return A -> Prop with
                         | Return _ x => @eq _ x
                         | Bind _ _ x f => fun v => exists comp_a_value,
                                                      computes_to x comp_a_value
                                                      /\ computes_to (f comp_a_value) v
                         | Pick _ P => P
                       end v.
  Proof.
    destruct 1; eauto.
  Qed.
End computes_to.

Notation "c ↝ v" := (computes_to c v).

Section is_computational.

  (** A [Comp] is maximally computational if it could be written without [Pick]. *)
  Inductive is_computational : forall A, Comp A -> Prop :=
  | Return_is_computational : forall A (x : A), is_computational (Return x)
  | Bind_is_computational : forall A B (cA : Comp A) (f : A -> Comp B),
                              is_computational cA
                              -> (forall a,
                                    @computes_to _ cA a -> is_computational (f a))
                              -> is_computational (Bind cA f).

  Theorem is_computational_inv A (c : Comp A)
  : is_computational c
    -> match c with
         | Return _ _ => True
         | Bind _ _ x f => is_computational x
                           /\ forall v, x ↝ v
                                        -> is_computational (f v)
         | Pick _ _ => False
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
           (old : Comp A)
           (new : Comp A)
  := forall v, new ↝ v -> old ↝ v.

(* A definition and notation for pretty printing the goals used to
   interactively deriving refinements. *)

Definition Refinement_Of {A} (c : Comp A) :=
  {c' | refine c%comp c'}.

Notation "'Refinement' 'of' c" :=
  {c' | refine c%comp c'}
    (at level 0, no associativity,
     format "'Refinement'  'of' '/' '[v'    c ']' " )
  : comp_scope.

(** Define a symmetrized version of [refine] for ease of rewriting *)
Definition refineEquiv {A}
           (old : Comp A)
           (new : Comp A)
  := refine old new /\ refine new old.

Local Obligation Tactic := repeat first [ solve [ eauto ]
                                        | progress hnf in *
                                        | intro
                                        | split
                                        | progress split_and ].

Global Program Instance refine_PreOrder A : PreOrder (@refine A).
Global Program Instance refineEquiv_Equivalence A : Equivalence (@refineEquiv A).
