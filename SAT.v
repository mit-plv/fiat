Require Import List Ensembles String.
Require Import JMeq ProofIrrelevance.

Set Asymmetric Patterns.
Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.

Reserved Notation "x >>= y" (at level 42, right associativity).
Reserved Notation "x <- y ; z" (at level 42, right associativity).
Reserved Notation "x ;; z" (at level 42, right associativity).
Reserved Notation "'return' x" (at level 40, no associativity).

Delimit Scope comp_scope with comp.
(*Delimit Scope monad_scope with monad.

(* Copying from http://coq.inria.fr/pylons/contribs/files/lc/v8.4/lc.Monad.html *)
Class Monad (carrier : Type -> Type) :=
  { bind : forall X Y,
             carrier X -> (X -> carrier Y) -> carrier Y;
    unit : forall X, X -> carrier X;
    bind_bind :
      forall X Y Z
             (f : X -> carrier Y) (g : Y -> carrier Z)
             (x : carrier X),
        bind (bind x f) g =
        bind x (fun u => bind (f u) g);
    bind_unit : forall X Y (f : X -> carrier Y) (x : X),
                  bind (unit x) f = f x;
    unit_bind : forall X (x : carrier X),
                  bind x (@unit X) = x
  }.

Arguments bind _ _ _%type _%type _ _%monad.

Notation "x >>= y" := (bind x y) (at level 42, right associativity) : monad_scope.
Notation "x <- y ; z" := (bind y (fun x => z)) (at level 42, right associativity) : monad_scope.
Notation "x ;; z" := (bind x (fun _ => z)) (at level 42, right associativity) : monad_scope.
Notation "'return' x" := (unit x) (at level 40, no associativity) : monad_scope.*)

Section funcs.
  Variable funcs : string -> Type * Type.
  Inductive Comp : Type -> Type :=
  | Return : forall A, A -> Comp A
  | Bind : forall A B, Comp A -> (A -> Comp B) -> Comp B
  | Call : forall x, fst (funcs x) -> Comp (snd (funcs x))
  | Pick : forall A, Ensemble A -> Comp A.

  Bind Scope comp_scope with Comp.
  Global Arguments Bind A%type B%type _%comp _.

  Notation "x >>= y" := (Bind x y) : comp_scope.
  Notation "x <- y ; z" := (Bind y (fun x => z)) : comp_scope.
  Notation "x ;; z" := (Bind x (fun _ => z)) : comp_scope.
  Notation "f [[ x ]]" := (@Call f x) (at level 35) : comp_scope.
  Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
  Notation "{ x : A  |  P }" := (@Pick A (fun x => P)) : comp_scope.

  Definition Or : Comp bool -> Comp bool -> Comp bool
    := fun c1 c2 =>
         (b1 <- c1;
          if b1
          then Return true
          else c2)%comp.

  Inductive formula (vars : Type) :=
  | Atomic : vars -> formula vars
  | And : formula vars -> formula vars -> formula vars
  | Not : formula vars -> formula vars
  | TrueF : formula vars.

  Fixpoint get_vars vars (f : formula vars) : Ensemble vars :=
    match f with
      | Atomic x => Singleton _ x
      | And x y => Union _ (get_vars x) (get_vars y)
      | Not x => get_vars x
      | TrueF => Empty_set _
    end.

  Fixpoint denote_formula vars (bool_map : vars -> bool) (f : formula vars)
  : bool
    := match f with
         | Atomic x => bool_map x
         | And x y => andb (denote_formula bool_map x) (denote_formula bool_map y)
         | Not x => negb (denote_formula bool_map x)
         | TrueF => true
       end.

  Definition is_satisfiable vars (f : formula vars) : Prop
    := exists bool_map, denote_formula bool_map f = true.

  Fixpoint subst_vars vars (bool_map : vars -> vars + bool) (f : formula vars)
  : formula vars
    := match f with
         | TrueF => TrueF _
         | Atomic x => match bool_map x with
                         | inl x' => Atomic x'
                         | inr b => if b then TrueF _ else Not (TrueF _)
                       end
         | And x y => And (subst_vars bool_map x) (subst_vars bool_map y)
         | Not x => Not (subst_vars bool_map x)
       end.

  Definition sat var (dec_eq_vars : forall x y : var, {x = y} + {x <> y})
             (sat_func : formula var -> Comp bool)
             (f : formula var)
  : Comp bool :=
    (x0 <- { x0 : option var
           | (x0 = None /\ get_vars f = Empty_set _)
             \/ (exists x', x0 = Some x' /\ In _ (get_vars f) x') };
     match x0 with
       | None => Return (denote_formula (fun _ => false (* do we want to use a [Prop] here? *)) f)
       | Some x0 =>
         let bool_map_t v := if dec_eq_vars x0 v then inr true else inl v in
         let bool_map_f v := if dec_eq_vars x0 v then inr false else inl v in
         let formula_t := subst_vars bool_map_t f in
         let formula_f := subst_vars bool_map_f f in
         Or (sat_func formula_t) (sat_func formula_f)
     end)%comp.

  Inductive computes_to (denote_funcs : forall name, fst (funcs name) -> Comp (snd (funcs name)))
  : forall A, Comp A -> A -> Prop :=
  | ReturnComputes : forall A v, @computes_to denote_funcs A (Return v) v
  | BindComputes : forall A B comp_a f comp_a_value comp_b_value,
                     @computes_to denote_funcs A comp_a comp_a_value
                     -> @computes_to denote_funcs B (f comp_a_value) comp_b_value
                     -> @computes_to denote_funcs B (Bind comp_a f) comp_b_value
  | PickComputes : forall A (P : Ensemble A) v, P v -> @computes_to denote_funcs A (Pick P) v
  | CallComputes : forall name (input : fst (funcs name)) (output_v : snd (funcs name)),
                     @computes_to denote_funcs _ (denote_funcs name input) output_v
                     -> @computes_to denote_funcs _ (Call name input) output_v.


  Section monad.
    Variable denote_funcs : forall name, fst (funcs name) -> Comp (snd (funcs name)).

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

    Lemma bind_bind X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x v
    : computes_to denote_funcs (Bind (Bind x f) g) v
      <-> computes_to denote_funcs (Bind x (fun u => Bind (f u) g)) v.
    Proof.
      t.
    Qed.

    Lemma bind_unit X Y (f : X -> Comp Y) x v
    : computes_to denote_funcs (Bind (Return x) f) v
      <-> computes_to denote_funcs (f x) v.
    Proof.
      t.
    Qed.

    Lemma unit_bind X (x : Comp X) v
    : computes_to denote_funcs (Bind x (@Return X)) v
      <-> computes_to denote_funcs x v.
    Proof.
      t.
    Qed.
  End monad.
End funcs.
