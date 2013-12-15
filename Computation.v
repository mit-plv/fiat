Require Import String Ensembles.
Require Import Common.

Reserved Notation "x >>= y" (at level 42, right associativity).
Reserved Notation "x <- y ; z" (at level 42, right associativity).
Reserved Notation "x ;; z" (at level 42, right associativity).
Reserved Notation "f [[ x ]]" (at level 35).
Reserved Notation "'call' f 'from' funcs [[ x ]]" (at level 35).

Delimit Scope comp_scope with comp.

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
  Notation "f [[ x ]]" := (@Call f x) : comp_scope.
  Notation "{ x  |  P }" := (@Pick _ (fun x => P)) : comp_scope.
  Notation "{ x : A  |  P }" := (@Pick A (fun x => P)) : comp_scope.

  Definition Or : Comp bool -> Comp bool -> Comp bool
    := fun c1 c2 =>
         (b1 <- c1;
          if b1
          then Return true
          else c2)%comp.

  Variable denote_funcs : forall name, fst (funcs name) -> Comp (snd (funcs name)).

  Inductive computes_to
  : forall A : Type, Comp A -> A -> Prop :=
  | ReturnComputes : forall A v, @computes_to A (Return v) v
  | BindComputes : forall A B comp_a f comp_a_value comp_b_value,
                     @computes_to A comp_a comp_a_value
                     -> @computes_to B (f comp_a_value) comp_b_value
                     -> @computes_to B (Bind comp_a f) comp_b_value
  | PickComputes : forall A (P : Ensemble A) v, P v -> @computes_to A (Pick P) v
  | CallComputes : forall name (input : fst (funcs name)) (output_v : snd (funcs name)),
                     @computes_to _ (denote_funcs name input) output_v
                     -> @computes_to _ (Call name input) output_v.

  Theorem computes_to_inv A (c : Comp A) v
    : computes_to c v -> match c with
                           | Return _ x => fun v => v = x
                           | Bind _ _ x f => fun v => exists comp_a_value,
                             computes_to x comp_a_value
                             /\ computes_to (f comp_a_value) v
                           | Call name input => computes_to (denote_funcs name input)
                           | Pick _ P => P
                         end v.
  Proof.
    destruct 1; eauto.
  Qed.

  (** The old program might be non-deterministic, and the new program
      less so.  This means we want to say that if [new] can compute to
      [v], then [old] should be able to compute to [v], too. *)
  Definition refine {A} (old new : Comp A) := forall v, computes_to new v -> computes_to old v.

  Global Instance refine_PreOrder A : PreOrder (@refine A).
  Proof.
    split; compute in *; eauto.
  Qed.

  Section monad.
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
    : computes_to (Bind (Bind x f) g) v
      <-> computes_to (Bind x (fun u => Bind (f u) g)) v.
    Proof.
      t.
    Qed.

    Lemma bind_unit X Y (f : X -> Comp Y) x v
    : computes_to (Bind (Return x) f) v
      <-> computes_to (f x) v.
    Proof.
      t.
    Qed.

    Lemma unit_bind X (x : Comp X) v
    : computes_to (Bind x (@Return X)) v
      <-> computes_to x v.
    Proof.
      t.
    Qed.
  End monad.
End funcs.

Hint Constructors computes_to.

Ltac inversion_computes_to :=
  repeat match goal with
           | _ => progress destruct_ex
           | _ => progress split_and
           | [ H : computes_to _ _ _ |- _ ]
             => let H' := fresh in
                pose proof (computes_to_inv H) as H';
                  clear H;
                  cbv beta iota in H';
                  match type of H' with
                    | appcontext[match _ with _ => _ end] => fail 1
                    | _ => idtac
                  end
         end.

Notation "x >>= y" := (Bind x y) : comp_scope.
Notation "x <- y ; z" := (Bind y (fun x => z)) : comp_scope.
Notation "x ;; z" := (Bind x (fun _ => z)) : comp_scope.
Notation "'call' f 'from' funcs [[ x ]]" := (@Call funcs f x) : comp_scope.
Notation "{ x  |  P }" := (@Pick _ _ (fun x => P)) : comp_scope.
Notation "{ x : A  |  P }" := (@Pick _ A (fun x => P)) : comp_scope.
Notation ret := (Return _).

Add Parametric Relation funcs denote_funcs A : (Comp funcs A) (@refine funcs denote_funcs A)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refine_rel.

Add Parametric Morphism funcs denote_funcs A B : (@Bind funcs A B)
  with signature (@refine funcs denote_funcs A) ==> (pointwise_relation _ (@refine funcs denote_funcs B)) ==> (@refine funcs denote_funcs B)
    as refine_bind.
Proof.
  intros.
  unfold pointwise_relation, refine in *.
  intros.
  repeat (repeat apply_in_hyp_no_match computes_to_inv;
    destruct_ex;
    intuition).
  eauto.
Qed.

Section general_refine_lemmas.
  Variable funcs : string -> Type * Type.
  Variable denote_funcs : forall name, fst (funcs name) -> Comp funcs (snd (funcs name)).

  Lemma refine_pick_pair A B (PA : A -> Prop) (PB : B -> Prop)
  : refine denote_funcs
           { x : A * B | PA (fst x) /\ PB (snd x) }%comp
           (a <- { a : A | PA a };
            b <- { b : B | PB b };
            ret (a, b))%comp.
  Proof.
    intros (a, b) H.
    repeat match goal with
             | _ => constructor; tauto
             | _ => progress destruct_ex
             | _ => progress intuition
             | [ H : (_, _) = (_, _) |- _ ] => inversion_clear H
             | [ H : _ |- _ ] => apply computes_to_inv in H
           end.
  Qed.
End general_refine_lemmas.
