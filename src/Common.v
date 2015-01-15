Require Import Coq.Lists.List Coq.Strings.String.
Require Export Setoid RelationClasses Program Morphisms.

Global Set Implicit Arguments.
Global Generalizable All Variables.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

(** Runs [abstract] after clearing the environment, solving the goal
    with the tactic associated with [cls <goal type>].  In 8.5, we
    could pass a tactic instead. *)
Tactic Notation "clear" "abstract" constr(cls) :=
  let G := match goal with |- ?G => constr:(G) end in
  let pf := constr:(_ : cls G) in
  let pf' := (eval cbv beta in pf) in
  repeat match goal with
           | [ H : _ |- _ ] => clear H; test (abstract (exact pf'))
         end;
    [ abstract (exact pf') ].

(** fail if [x] is a function application, a dependent product ([fun _
    => _]), or a sigma type ([forall _, _]) *)
Ltac atomic x :=
  match x with
    | ?f _ => fail 1 x "is not atomic (application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | _ => idtac
  end.

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
    | [ H : T |- _ ] => fail 1
    | _ => pose proof defn
  end.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.

(** check's if the given hypothesis has a body, i.e., if [clearbody]
    could ever succeed.  We can't just do [test_tac (clearbody H)],
    because maybe the correctness of the proof depends on the body of
    H *)
Tactic Notation "has" "body" hyp(H) :=
  test (let H' := fresh in pose H as H'; unfold H in H').

(** find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(** call [tac H], but first [simpl]ify [H].
    This tactic leaves behind the simplified hypothesis. *)
Ltac simpl_do tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'.

(** clear the left-over hypothesis after [simpl_do]ing it *)
Ltac simpl_do_clear tac H := simpl_do ltac:(fun H => tac H; try clear H) H.

Ltac simpl_rewrite term := simpl_do_clear ltac:(fun H => rewrite H) term.
Ltac simpl_rewrite_rev term := simpl_do_clear ltac:(fun H => rewrite <- H) term.
Tactic Notation "simpl" "rewrite" open_constr(term) := simpl_rewrite term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) := simpl_rewrite term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) := simpl_rewrite_rev term.

Ltac do_with_hyp tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.

(** solve simple setiod goals that can be solved by [transitivity] *)
Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].

    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

Ltac destruct_sig_matcher HT :=
  match eval hnf in HT with
    | ex _ => idtac
    | ex2 _ _ => idtac
    | sig _ => idtac
    | sig2 _ _ => idtac
    | sigT _ => idtac
    | sigT2 _ _ => idtac
    | and _ _ => idtac
    | prod _ _ => idtac
  end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_sig_matcher HT || destruct_sig_matcher HT
).

(** if progress can be made by [exists _], but it doesn't matter what
    fills in the [_], assume that something exists, and leave the two
    goals of finding a member of the apropriate type, and proving that
    all members of the appropriate type prove the goal *)
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @sigT;
  match goal with
(*    | [ |- @sig ?T _ ] => destruct_exists' T*)
    | [ |- @sigT ?T _ ] => destruct_exists' T
(*    | [ |- @sig2 ?T _ _ ] => destruct_exists' T*)
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

(** if the goal can be solved by repeated specialization of some
    hypothesis with other [specialized] hypotheses, solve the goal by
    brute force *)
Ltac specialized_assumption tac := tac;
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption tac
    | _ => assumption
  end.

(** for each hypothesis of type [H : forall _ : ?T, _], if there is
    exactly one hypothesis of type [H' : T], do [specialize (H H')]. *)
Ltac specialize_uniquely :=
  repeat match goal with
           | [ x : ?T, y : ?T, H : _ |- _ ] => test (specialize (H x)); fail 1
           | [ x : ?T, H : _ |- _ ] => specialize (H x)
         end.

(** specialize all hypotheses of type [forall _ : ?T, _] with
    appropriately typed hypotheses *)
Ltac specialize_all_ways_forall :=
  repeat match goal with
           | [ x : ?T, H : forall _ : ?T, _ |- _ ] => unique pose proof (H x)
         end.

(** try to specialize all hypotheses with all other hypotheses.  This
    includes [specialize (H x)] where [H x] requires a coercion from
    the type of [H] to Funclass. *)
Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique pose proof (H x)
         end.

Ltac apply_in_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H
  end.

Ltac apply_in_hyp_no_match lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H;
      match type of H with
        | appcontext[match _ with _ => _ end] => fail 1
        | _ => idtac
      end
  end.

Ltac apply_in_hyp_no_cbv_match lem :=
  match goal with
    | [ H : _ |- _ ]
      => apply lem in H;
        cbv beta iota in H;
        match type of H with
          | appcontext[match _ with _ => _ end] => fail 1
          | _ => idtac
        end
  end.

(* Coq's build in tactics don't work so well with things like [iff]
   so split them up into multiple hypotheses *)
Ltac split_in_context ident funl funr :=
  repeat match goal with
           | [ H : context p [ident] |- _ ] =>
             let H0 := context p[funl] in let H0' := eval simpl in H0 in assert H0' by (apply H);
               let H1 := context p[funr] in let H1' := eval simpl in H1 in assert H1' by (apply H);
                 clear H
         end.

Ltac split_iff := split_in_context iff (fun a b : Prop => a -> b) (fun a b : Prop => b -> a).

Ltac split_and' :=
  repeat match goal with
           | [ H : ?a /\ ?b |- _ ] => let H0 := fresh in let H1 := fresh in
             assert (H0 := fst H); assert (H1 := snd H); clear H
         end.
Ltac split_and := split_and'; split_in_context and (fun a b : Type => a) (fun a b : Type => b).


Ltac destruct_sum_in_match' :=
  match goal with
    | [ H : appcontext[match ?E with inl _ => _ | inr _ => _ end] |- _ ]
      => destruct E
    | [ |- appcontext[match ?E with inl _ => _ | inr _ => _ end] ]
      => destruct E
  end.
Ltac destruct_sum_in_match := repeat destruct_sum_in_match'.

Ltac destruct_ex :=
  repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
         end.

Ltac setoid_rewrite_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite H).
Ltac setoid_rewrite_hyp := repeat setoid_rewrite_hyp'.
Ltac setoid_rewrite_rev_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite <- H).
Ltac setoid_rewrite_rev_hyp := repeat setoid_rewrite_rev_hyp'.

Hint Extern 0 => solve [apply reflexivity] : typeclass_instances.

Ltac set_evars :=
  repeat match goal with
           | [ |- appcontext[?E] ] => is_evar E; let H := fresh in set (H := E)
         end.

Instance pointwise_refl A B (eqB : relation B) `{Reflexive _ eqB} : Reflexive (pointwise_relation A eqB).
Proof.
  compute in *; auto.
Defined.

Instance pointwise_sym A B (eqB : relation B) `{Symmetric _ eqB} : Symmetric (pointwise_relation A eqB).
Proof.
  compute in *; auto.
Defined.

Instance pointwise_transitive A B (eqB : relation B) `{Transitive _ eqB} : Transitive (pointwise_relation A eqB).
Proof.
  compute in *; eauto.
Defined.

Lemma Some_ne_None {T} {x : T} : Some x <> None.
Proof.
  congruence.
Qed.

Lemma None_ne_Some {T} {x : T} : None <> Some x.
Proof.
  congruence.
Qed.

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    | [ H : context[if ?X then _ else _] |- _ ]=> destruct X
  end.

Ltac substs :=
  repeat match goal with
           | [ H : ?x = ?y |- _ ]
             => first [ subst x | subst y ]
         end.

Ltac substss :=
  repeat match goal with
           | [ H : ?x = _ ,
                   H0 : ?x = _ |- _ ]
             => rewrite H in H0
         end.

Ltac injections :=
  repeat match goal with
           | [ H : _ = _ |- _ ]
             => injection H; intros; subst; clear H
         end.


Ltac inversion_by rule :=
  progress repeat first [ progress destruct_ex
                        | progress split_and
                        | apply_in_hyp_no_cbv_match rule ].


Class can_transform_sigma A B := do_transform_sigma : A -> B.

Instance can_transform_sigT_base {A} {P : A -> Type}
: can_transform_sigma (sigT P) (sigT P) | 0
  := fun x => x.

Instance can_transform_sig_base {A} {P : A -> Prop}
: can_transform_sigma (sig P) (sig P) | 0
  := fun x => x.

Instance can_transform_sigT {A B B' C'}
         `{forall x : A, can_transform_sigma (B x) (@sigT (B' x) (C' x))}
: can_transform_sigma (forall x : A, B x)
                (@sigT (forall x, B' x) (fun b => forall x, C' x (b x))) | 0
  := fun f => existT
                (fun b => forall x : A, C' x (b x))
                (fun x => projT1 (do_transform_sigma (f x)))
                (fun x => projT2 (do_transform_sigma (f x))).

Instance can_transform_sig {A B B' C'}
         `{forall x : A, can_transform_sigma (B x) (@sig (B' x) (C' x))}
: can_transform_sigma (forall x : A, B x)
                (@sig (forall x, B' x) (fun b => forall x, C' x (b x))) | 0
  := fun f => exist
                (fun b => forall x : A, C' x (b x))
                (fun x => proj1_sig (do_transform_sigma (f x)))
                (fun x => proj2_sig (do_transform_sigma (f x))).

Ltac split_sig' :=
  match goal with
    | [ H : _ |- _ ]
      => let H' := fresh in
         pose proof (@do_transform_sigma _ _ _ H) as H';
           clear H;
           destruct H'
  end.

Ltac split_sig :=
  repeat split_sig'.

Ltac clearbodies :=
  repeat match goal with
           | [ H := _ |- _ ] => clearbody H
         end.

Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

(** TODO: Maybe we should replace uses of this with [case_eq], which the stdlib defined for us? *)
Ltac caseEq x := generalize (refl_equal x); pattern x at -1; case x; intros.

Class ReflexiveT A (R : A -> A -> Type) :=
  reflexivityT : forall x, R x x.
Class TransitiveT A (R : A -> A -> Type) :=
  transitivityT : forall x y z, R x y -> R y z -> R x z.
Class PreOrderT A (R : A -> A -> Type) :=
  { PreOrderT_ReflexiveT :> ReflexiveT R;
    PreOrderT_TransitiveT :> TransitiveT R }.
Definition respectful_heteroT A B C D
           (R : A -> B -> Type)
           (R' : forall (x : A) (y : B), C x -> D y -> Type)
           (f : forall x, C x) (g : forall x, D x)
  := forall x y, R x y -> R' x y (f x) (g y).

(* Lifting forall and pointwise relations to multiple arguments. *)
Definition forall_relation2 {A : Type} {B : A -> Type} {C : forall a, B a -> Type} R :=
  forall_relation (fun a => (@forall_relation (B a) (C a) (R a))).
Definition pointwise_relation2 {A B C : Type} (R : relation C) :=
  pointwise_relation A (@pointwise_relation B C R).

Definition forall_relation3 {A : Type} {B : A -> Type}
           {C : forall a, B a -> Type} {D : forall a b, C a b -> Type} R :=
  forall_relation (fun a => (@forall_relation2 (B a) (C a) (D a) (R a))).
Definition pointwise_relation3 {A B C D : Type} (R : relation D) :=
  pointwise_relation A (@pointwise_relation2 B C D R).

Definition forall_relation4 {A : Type} {B : A -> Type}
           {C : forall a, B a -> Type} {D : forall a b, C a b -> Type}
           {E : forall a b c, D a b c -> Type} R :=
  forall_relation (fun a => (@forall_relation3 (B a) (C a) (D a) (E a) (R a))).
Definition pointwise_relation4 {A B C D E : Type} (R : relation E) :=
  pointwise_relation A (@pointwise_relation3 B C D E R).

Ltac higher_order_1_reflexivity' :=
  let a := match goal with |- ?R ?a (?f ?x) => constr:(a) end in
  let f := match goal with |- ?R ?a (?f ?x) => constr:(f) end in
  let x := match goal with |- ?R ?a (?f ?x) => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac sym_higher_order_1_reflexivity' :=
  let a := match goal with |- ?R (?f ?x) ?a => constr:(a) end in
  let f := match goal with |- ?R (?f ?x) ?a => constr:(f) end in
  let x := match goal with |- ?R (?f ?x) ?a => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

(* refine is an antisymmetric relation, so we can try to apply
   symmetric versions of higher_order_1_reflexivity. *)

Ltac higher_order_1_reflexivity :=
  solve [ higher_order_1_reflexivity'
        | sym_higher_order_1_reflexivity' ].

  (* This applies reflexivity after refining a method. *)

Ltac higher_order_2_reflexivity' :=
  let x := match goal with |- ?R ?x (?f ?a ?b) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac sym_higher_order_2_reflexivity' :=
  let x := match goal with |- ?R (?f ?a ?b) ?x => constr:(x) end in
  let f := match goal with |- ?R (?f ?a ?b) ?x => constr:(f) end in
  let a := match goal with |- ?R (?f ?a ?b) ?x => constr:(a) end in
  let b := match goal with |- ?R (?f ?a ?b) ?x => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_2_reflexivity :=
  solve [ higher_order_2_reflexivity'
        | sym_higher_order_2_reflexivity' ].

Axiom IsHProp : Type -> Type.
Existing Class IsHProp.
Instance : forall A, IsHProp (IsHProp A).
Admitted.

Axiom allpath_hprop : forall `{H : IsHProp A} (x y : A), x = y.
Axiom hprop_allpath : forall (A : Type), (forall (x y : A), x = y) -> IsHProp A.

Global Arguments f_equal {A B} f {x y} _ .

(*Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = f_equal f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : forall x, f x = g x
  := fun x => match h with eq_refl => eq_refl end.

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }. *)

(* We'll just assume functional extensionality for now. *)

Global Instance trunc_forall `{P : A -> Type} `{forall a, IsHProp (P a)}
  : IsHProp (forall a, P a) | 100.
Admitted.

Instance trunc_prod `{IsHProp A, IsHProp B} : IsHProp (A * B).
Admitted.

Record hProp := hp { hproptype :> Type ; isp : IsHProp hproptype}.
Existing Instance isp.

Instance : forall A : hProp, IsHProp A.
Admitted.

Lemma path_sig_hprop {A} {P : A -> Prop} `{forall x : A, IsHProp (P x)}
      (x y : sig P)
: proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct_head sig; intros; subst; f_equal; apply allpath_hprop.
Defined.

Fixpoint combine_sig_helper {T} {P : T -> Prop} (ls : list T) : (forall x, In x ls -> P x) -> list (sig P).
Proof.
  refine match ls with
           | nil => fun _ => nil
           | x::xs => fun H => (exist _ x _)::@combine_sig_helper _ _ xs _
         end;
  clear combine_sig_helper; simpl in *;
  intros;
  apply H;
  first [ left; reflexivity
        | right; assumption ].
Defined.

Lemma Forall_forall1_transparent_helper_1 {A P} {x : A} {xs : list A} {l : list A}
      (H : Forall P l) (H' : x::xs = l)
: P x.
Proof.
  subst; inversion H; repeat subst; assumption.
Defined.
Lemma Forall_forall1_transparent_helper_2 {A P} {x : A} {xs : list A} {l : list A}
      (H : Forall P l) (H' : x::xs = l)
: Forall P xs.
Proof.
  subst; inversion H; repeat subst; assumption.
Defined.

Fixpoint Forall_forall1_transparent {A} (P : A -> Prop) (l : list A) {struct l}
: Forall P l -> forall x, In x l -> P x
  := match l as l return Forall P l -> forall x, In x l -> P x with
       | nil => fun _ _ f => match f : False with end
       | x::xs => fun H x' H' =>
                    match H' with
                      | or_introl H'' => eq_rect x
                                                 P
                                                 (Forall_forall1_transparent_helper_1 H eq_refl)
                                                 _
                                                 H''
                      | or_intror H'' => @Forall_forall1_transparent A P xs (Forall_forall1_transparent_helper_2 H eq_refl) _ H''
                    end
     end.

Definition combine_sig {T P ls} (H : List.Forall P ls) : list (@sig T P)
  := combine_sig_helper ls (@Forall_forall1_transparent T P ls H).

Arguments Forall_forall1_transparent_helper_1 : simpl never.
Arguments Forall_forall1_transparent_helper_2 : simpl never.

Lemma In_combine_sig {T P ls H x} (H' : In x ls)
: In (exist P x (@Forall_forall1_transparent T P ls H _ H')) (combine_sig H).
Proof.
  unfold combine_sig.
  induction ls; simpl in *; trivial.
  destruct_head or; subst;
  try first [ left; reflexivity ].
  right.
  revert H.
  match goal with
    | [ |- context[@eq_refl ?A ?a] ] => generalize (@eq_refl A a)
  end.
  set (als := a::ls) in *.
  change als with (a::ls) at 1.
  clearbody als.
  intros e H.
  destruct H; [ exfalso; solve [ inversion e ] | ].
  apply IHls.
Defined.

Fixpoint flatten1 {T} (ls : list (list T)) : list T
  := match ls with
       | nil => nil
       | x::xs => (x ++ flatten1 xs)%list
     end.

Lemma flatten1_length_ne_0 {T} (ls : list (list T)) (H0 : Datatypes.length ls <> 0)
      (H1 : Datatypes.length (hd nil ls) <> 0)
: Datatypes.length (flatten1 ls) <> 0.
Proof.
  destruct ls as [| [|] ]; simpl in *; auto.
Qed.

Local Hint Constructors List.Forall.

Lemma Forall_app {T} P (ls1 ls2 : list T)
: List.Forall P ls1 /\ List.Forall P ls2 <-> List.Forall P (ls1 ++ ls2).
Proof.
  split.
  { intros [H1 H2].
    induction H1; simpl; auto. }
  { intro H; split; induction ls1; simpl in *; auto.
    { inversion_clear H; auto. }
    { inversion_clear H; auto. } }
Qed.

Lemma Forall_flatten1 {T ls P}
: List.Forall P (@flatten1 T ls) <-> List.Forall (List.Forall P) ls.
Proof.
  induction ls; simpl.
  { repeat first [ esplit | intro | constructor ]. }
  { etransitivity; [ symmetry; apply Forall_app | ].
    split_iff.
    split.
    { intros [? ?]; auto. }
    { intro H'; inversion_clear H'; split; auto. } }
Qed.


Lemma Forall_map {A B} {f : A -> B} {ls P}
: List.Forall P (map f ls) <-> List.Forall (P ∘ f) ls.
Proof.
  induction ls; simpl.
  { repeat first [ esplit | intro | constructor ]. }
  { split_iff.
    split;
      intro H'; inversion_clear H'; auto. }
Qed.

Lemma fold_right_map {A B C} (f : A -> B) g c ls
: @fold_right C B g
              c
              (map f ls)
  = fold_right (g ∘ f) c ls.
Proof.
  induction ls; unfold compose; simpl; f_equal; auto.
Qed.

Lemma fold_right_orb_true ls
: fold_right orb true ls = true.
Proof.
  induction ls; destruct_head_hnf bool; simpl in *; trivial.
Qed.

Lemma fold_right_orb b ls
: fold_right orb b ls = true
  <-> fold_right or (b = true) (map (fun x => x = true) ls).
Proof.
  induction ls; simpl; intros; try reflexivity.
  rewrite <- IHls; clear.
  repeat match goal with
           | _ => assumption
           | _ => split
           | _ => intro
           | _ => progress subst
           | _ => progress simpl in *
           | _ => progress destruct_head or
           | _ => progress destruct_head bool
           | _ => left; reflexivity
           | _ => right; assumption
         end.
Qed.

Local Hint Constructors Exists.

Local Ltac fold_right_orb_map_sig_t :=
  repeat match goal with
           | _ => split
           | _ => intro
           | _ => progress simpl in *
           | _ => progress subst
           | _ => progress destruct_head sumbool
           | _ => progress destruct_head sig
           | _ => progress destruct_head and
           | _ => progress destruct_head or
           | [ H : _ = true |- _ ] => rewrite H
           | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
           | [ H : ?a, H' : ?a -> ?b |- _ ] => specialize (H' H)
           | [ H : ?a, H' : @sig ?a ?P -> ?b |- _ ] => specialize (fun b => H' (exist P H b))
           | [ H' : _ /\ _ -> _ |- _ ] => specialize (fun a b => H' (conj a b))
           | [ |- (?a || true)%bool = true ] => destruct a; reflexivity
           | _ => solve [ eauto ]
           | _ => congruence
         end.

Lemma fold_right_orb_map_sig1 {T} f (ls : list T)
: fold_right orb false (map f ls) = true
  -> sig (fun x => In x ls /\ f x = true).
Proof.
  induction ls; fold_right_orb_map_sig_t.
Qed.

Lemma fold_right_orb_map_sig2 {T} f (ls : list T)
: sig (fun x => In x ls /\ f x = true)
  -> fold_right orb false (map f ls) = true.
Proof.
  induction ls; fold_right_orb_map_sig_t.
Qed.

Lemma fold_right_orb_map {T} f (ls : list T)
: fold_right orb false (map f ls) = true
  <-> List.Exists (fun x => f x = true) ls.
Proof.
  induction ls;
  repeat match goal with
           | _ => split
           | _ => intro
           | _ => progress simpl in *
           | [ H : Exists _ [] |- _ ] => solve [ inversion H ]
           | [ H : Exists _ (_::_) |- _ ] => inversion_clear H
           | _ => progress split_iff
           | _ => progress destruct_head sumbool
           | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
           | [ H : ?a, H' : ?a -> ?b |- _ ] => specialize (H' H)
           | [ H : _ = true |- _ ] => rewrite H
           | [ |- (?a || true)%bool = _ ] => destruct a; reflexivity
           | _ => solve [ eauto ]
           | _ => congruence
         end.
Qed.

Lemma fold_right_map_andb_andb {T} x y f g (ls : list T)
: fold_right andb x (map f ls) = true /\ fold_right andb y (map g ls) = true
  <-> fold_right andb (andb x y) (map (fun k => andb (f k) (g k)) ls) = true.
Proof.
  induction ls; simpl; intros; destruct_head_hnf bool; try tauto;
  rewrite !Bool.andb_true_iff;
  try tauto.
Qed.

Lemma fold_right_map_andb_orb {T} x y f g (ls : list T)
: fold_right andb x (map f ls) = true /\ fold_right orb y (map g ls) = true
  -> fold_right orb (andb x y) (map (fun k => andb (f k) (g k)) ls) = true.
Proof.
  induction ls; simpl; intros; destruct_head_hnf bool; try tauto;
  repeat match goal with
           | [ H : _ |- _ ] => progress rewrite ?Bool.orb_true_iff, ?Bool.andb_true_iff in H
           | _ => progress rewrite ?Bool.orb_true_iff, ?Bool.andb_true_iff
         end;
  try tauto.
Qed.

Lemma fold_right_map_and_and {T} x y f g (ls : list T)
: fold_right and x (map f ls) /\ fold_right and y (map g ls)
  <-> fold_right and (x /\ y) (map (fun k => f k /\ g k) ls).
Proof.
  revert x y.
  induction ls; simpl; intros; try reflexivity.
  rewrite <- IHls; clear.
  tauto.
Qed.

Lemma fold_right_map_and_or {T} x y f g (ls : list T)
: fold_right and x (map f ls) /\ fold_right or y (map g ls)
  -> fold_right or (x /\ y) (map (fun k => f k /\ g k) ls).
Proof.
  revert x y.
  induction ls; simpl; intros; try assumption.
  intuition.
Qed.

Functional Scheme fold_right_rect := Induction for fold_right Sort Type.

Lemma bool_dec_refl b : Bool.bool_dec b b = left eq_refl.
Proof.
  destruct b; reflexivity.
Qed.

Lemma ascii_dec_refl a : Ascii.ascii_dec a a = left eq_refl.
Proof.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7];
  repeat match goal with
           | _ => reflexivity
           | [ |- ?a = ?b ] => let a' := (eval hnf in a) in progress change (a' = b)
           | _ => rewrite bool_dec_refl
         end.
Qed.

Lemma string_dec_refl a : string_dec a a = left eq_refl.
Proof.
  induction a; trivial.
  simpl; rewrite IHa, ascii_dec_refl; reflexivity.
Qed.

Lemma fold_right_andb_map_impl {T} x y f g (ls : list T)
      (H0 : x = true -> y = true)
      (H1 : forall k, f k = true -> g k = true)
: (fold_right andb x (map f ls) = true -> fold_right andb y (map g ls) = true).
Proof.
  induction ls; simpl; intros; try tauto.
  rewrite IHls; simpl;
  repeat match goal with
           | [ H : _ = true |- _ ] => apply Bool.andb_true_iff in H
           | [ |- _ = true ] => apply Bool.andb_true_iff
           | _ => progress destruct_head and
           | _ => split
           | _ => auto
         end.
Qed.

Lemma if_ext {T} (b : bool) (f1 f2 : b = true -> T true) (g1 g2 : b = false -> T false)
      (ext_f : forall H, f1 H = f2 H)
      (ext_g : forall H, g1 H = g2 H)
: (if b as b' return (b = b' -> T b') then f1 else g1) eq_refl
  = (if b as b' return (b = b' -> T b') then f2 else g2) eq_refl.
Proof.
  destruct b; trivial.
Defined.
