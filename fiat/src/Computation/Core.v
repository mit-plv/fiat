Require Import Coq.Strings.String Coq.Sets.Ensembles.
Require Import Fiat.Common.
Require Export Fiat.Computation.Notations.

Definition Comp := @Ensemble.

Definition Return (A : Type) : A -> Comp A :=
  Singleton A.

Definition Bind (A B : Type)
           (ca : Comp A)
           (k : A -> Comp B)
: Comp B :=
  fun b =>
    exists a : A,
      In A ca a /\ In B (k a) b.

Definition Pick (A : Type)
           (P : Ensemble A)
: Comp A := P.

Definition Bind2 (A B C: Type)
           (c : Comp (A * B))
           (k : A -> B -> Comp C)
  := Bind c (fun ab => k (fst ab) (snd ab)).


Bind Scope comp_scope with Comp.
Arguments Bind [A%type B%type] ca%comp k%comp _.
Arguments Bind2 [A%type B%type C%type] c%comp k%comp _.
Arguments Return [_] _ _.
Arguments Pick [_] _ _.

Notation ret := Return.

Notation "x >>= y" := (Bind x%comp y%comp) : comp_scope.
Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp))
                           (at level 81, right associativity,
                            format "'[v' x  <-  y ; '/' z ']'") : comp_scope.

Notation "`( a , b ) <- c ; k" :=
  (Bind2 c%comp (fun a b => k%comp))
    (at level 81, right associativity,
     format "'[v' `( a ,  b )  <-  c ; '/' k ']'") : comp_scope.

Notation "x >> z" := (Bind x%comp (fun _ => z%comp) )
                       (at level 81, right associativity,
                        format "'[v' x >> '/' z ']'") : comp_scope.
Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick A%type (fun x => P)) : comp_scope.

Definition computes_to {A : Type} (ca : Comp A) (a : A) : Prop := ca a.

Notation "c ↝ v" := (computes_to c v).

Lemma ReturnComputes
      {A : Type}
: forall (a : A),
    ret a ↝ a.
Proof.
  constructor.
Qed.

Lemma BindComputes
      {A B: Type}
: forall (ca : Comp A)
         (f : A -> Comp B)
         (a : A)
         (b : B),
    ca ↝ a ->
    f a ↝ b ->
    ca >>= f ↝ b.
Proof.
  econstructor; eauto.
Qed.

Lemma PickComputes {A : Type}
: forall (P : Ensemble A)
         (a : A),
    P a ->
    {a' | P a'} ↝ a.
Proof.
  intros; eauto.
Qed.

Lemma Return_inv {A : Type}
: forall (a v : A),
    ret a ↝ v -> a = v.
Proof.
  destruct 1; reflexivity.
Qed.

Lemma Bind_inv {A B: Type}
: forall (ca : Comp A)
         (f : A -> Comp B)
         (v : B),
    ca >>= f ↝ v ->
  exists a',
    ca ↝ a' /\ f a' ↝ v.
Proof.
  destruct 1; eauto.
Qed.

Lemma Pick_inv {A : Type}
: forall (P : Ensemble A)
         (v : A),
    {a | P a} ↝ v -> P v.
Proof.
  eauto.
Qed.

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
  {c' | refine c c'}.

Notation "'Refinement' 'of' c" :=
  {c' | refine c c'}
    (at level 0, no associativity,
     format "'Refinement'  'of' '/' '[v'    c ']' " )
  : comp_scope.

(** Define a symmetrized version of [refine] for ease of rewriting *)
Definition refineEquiv {A}
           (old : Comp A)
           (new : Comp A)
  := refine old new /\ refine new old.

Local Ltac t := repeat first [ solve [ unfold computes_to in *; eauto ]
                                        | progress hnf in *
                                        | intro
                                        | split
                                        | progress split_and ].

Global Instance refine_PreOrder A : PreOrder (@refine A).
t.
Qed.

Global Instance refineEquiv_Equivalence A : Equivalence (@refineEquiv A).
t.
Qed.

Global Opaque Return.
Global Opaque Bind.
Global Opaque Pick.
Global Opaque computes_to.

Global Hint Resolve ReturnComputes.
Global Hint Resolve BindComputes.
Global Hint Resolve PickComputes.

Ltac computes_to_inv :=
  repeat match goal with
           | H : {a' | @?P a'} ↝ _ |- _ => apply Pick_inv in H
           | H : Return ?a ↝ _ |- _ => apply Return_inv in H
           | H : Bind (A := ?A) ?ca ?k ↝ _ |- _ =>
             apply Bind_inv in H;
               let a' := fresh "v" in
               let H' := fresh H "'" in
               destruct H as [a' [H H'] ]
         end.

Ltac computes_to_econstructor :=
  first
    [ unfold refine; intros; eapply @ReturnComputes
    | unfold refine; intros; eapply @BindComputes
    | unfold refine; intros; eapply @PickComputes ].

Ltac computes_to_constructor :=
  first
    [ unfold refine; intros; apply @ReturnComputes
    | unfold refine; intros; apply @BindComputes
    | unfold refine; intros; apply @PickComputes ].
