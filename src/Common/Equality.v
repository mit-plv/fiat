Require Import Coq.Lists.List Coq.Lists.SetoidList.
Require Import Coq.Strings.String.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Close Scope nat_scope.

Definition concat_1p {A x y} (p : x = y :> A) : eq_trans eq_refl p = p.
Proof. case p; reflexivity. Defined.
Definition concat_p1 {A x y} (p : x = y :> A) : eq_trans p eq_refl = p.
Proof. case p; reflexivity. Defined.
Definition concat_pV {A x y} (p : x = y :> A) : eq_trans p (eq_sym p) = eq_refl.
Proof. case p; reflexivity. Defined.
Definition concat_Vp {A x y} (p : x = y :> A) : eq_trans (eq_sym p) p = eq_refl.
Proof. case p; reflexivity. Defined.
Definition transport_pp {A} {P : A -> Type} {x y z} (p : x = y) (q : y = z) (k : P x)
: eq_rect _ P k _ (eq_trans p q) = eq_rect _ P (eq_rect _ P k _ p) _ q.
Proof. case q; simpl; reflexivity. Defined.
Lemma transport_const {A P x y} (p : x = y :> A) k
: eq_rect _ (fun _ : A => P) k _ p = k.
Proof. case p; reflexivity. Defined.
Lemma ap_const {A B x y} (b : B) (p : x = y :> A)
: f_equal (fun _ => b) p = eq_refl.
Proof. case p; reflexivity. Defined.
Lemma inv_pp {A x y z} (p : x = y :> A) (q : y = z :> A)
: eq_sym (eq_trans p q) = eq_trans (eq_sym q) (eq_sym p).
Proof. case q; case p; reflexivity. Defined.
Lemma inv_V {A x y} (p : x = y :> A)
: eq_sym (eq_sym p) = p.
Proof. case p; reflexivity. Defined.

Section sigT.
  Definition pr1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : projT1 u = projT1 v
    := f_equal (@projT1 _ _) p.

  Definition pr2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : eq_rect _ _ (projT2 u) _ (pr1_path p) = projT2 v.
  Proof.
    destruct p; reflexivity.
  Defined.

  Definition path_sigT_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
             (pq : {p : projT1 u = projT1 v & eq_rect _ _ (projT2 u) _ p = projT2 v})
  : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  Definition path_sigT {A : Type} (P : A -> Type) (u v : sigT P)
             (p : projT1 u = projT1 v) (q : eq_rect _ _ (projT2 u) _ p = projT2 v)
  : u = v
    := path_sigT_uncurried u v (existT _ p q).

  Definition path_sigT_nondep {A B : Type} (u v : @sigT A (fun _ => B))
             (p : projT1 u = projT1 v) (q : projT2 u = projT2 v)
  : u = v
    := @path_sigT _ _ u v p (eq_trans (transport_const _ _) q).

  Lemma eq_rect_sigT {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sigT (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => sigT (Q a)) u y H
    = existT
        (Q y)
        (eq_rect x P (projT1 u) y H)
        match H in (_ = y) return Q y (eq_rect x P (projT1 u) y H) with
          | eq_refl => projT2 u
        end.
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sigT.

Section sig.
  Definition proj1_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : proj1_sig u = proj1_sig v
    := f_equal (@proj1_sig _ _) p.

  Definition proj2_sig_path {A} {P : A -> Prop} {u v : sig P} (p : u = v)
  : eq_rect _ _ (proj2_sig u) _ (proj1_sig_path p) = proj2_sig v.
  Proof.
    destruct p; reflexivity.
  Defined.

  Definition path_sig_uncurried {A : Type} (P : A -> Prop) (u v : sig P)
             (pq : {p : proj1_sig u = proj1_sig v | eq_rect _ _ (proj2_sig u) _ p = proj2_sig v})
  : u = v.
  Proof.
    destruct u as [u1 u2], v as [v1 v2]; simpl in *.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  Definition path_sig {A : Type} (P : A -> Prop) (u v : sig P)
             (p : proj1_sig u = proj1_sig v) (q : eq_rect _ _ (proj2_sig u) _ p = proj2_sig v)
  : u = v
    := path_sig_uncurried u v (exist _ p q).

  Lemma eq_rect_sig {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : sig (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => sig (Q a)) u y H
    = exist
        (Q y)
        (eq_rect x P (proj1_sig u) y H)
        match H in (_ = y) return Q y (eq_rect x P (proj1_sig u) y H) with
          | eq_refl => proj2_sig u
        end.
  Proof.
    destruct H, u; reflexivity.
  Defined.
End sig.

Section ex.
  Definition path_ex_uncurried' {A : Type} (P : A -> Prop) {u1 v1 : A} {u2 : P u1} {v2 : P v1}
             (pq : exists p : u1 = v1, eq_rect _ _ u2 _ p = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2.
  Proof.
    destruct pq as [p q].
    destruct q; simpl in *.
    destruct p; reflexivity.
  Defined.

  Definition path_ex' {A : Type} (P : A -> Prop) (u1 v1 : A) (u2 : P u1) (v2 : P v1)
             (p : u1 = v1) (q : eq_rect _ _ u2 _ p = v2)
  : ex_intro P u1 u2 = ex_intro P v1 v2
    := path_ex_uncurried' P (ex_intro _ p q).

  Lemma eq_rect_ex {A x} {P : A -> Type} (Q : forall a, P a -> Prop) (u : ex (Q x)) {y} (H : x = y)
  : eq_rect x (fun a => ex (Q a)) u y H
    = match u with
        | ex_intro u1 u2
          => ex_intro
               (Q y)
               (eq_rect x P u1 y H)
               match H in (_ = y) return Q y (eq_rect x P u1 y H) with
                 | eq_refl => u2
               end
      end.
  Proof.
    destruct H, u; reflexivity.
  Defined.
End ex.

Lemma eq_rect_const {A x P} (u : P) {y} (H : x = y)
: @eq_rect A x (fun _ => P) u y H = u.
Proof.
  destruct H; reflexivity.
Defined.

Lemma in_map_iff_injective {A B} (f : A -> B) (l : list A) (y : A)
      (f_injective : forall x, f x = f y -> x = y)
: In (f y) (map f l) <-> In y l.
Proof.
  split; intro H.
  { apply in_map_iff in H.
    destruct H as [x [H H']].
    apply f_injective in H.
    subst; assumption. }
  { apply in_map_iff.
    exists y; split; trivial. }
Qed.

Section option.
  Context {A : Type}.

  Definition option_code (x y : option A) : Prop
    := match x, y with
         | Some x', Some y' => x' = y'
         | None, None => True
         | _, _ => False
       end.

  Definition option_code_idpath {x} : option_code x x
    := match x return option_code x x with
         | Some _ => eq_refl
         | None => I
       end.

  Definition option_encode {x y} (p : x = y) : option_code x y
    := eq_rect _ _ option_code_idpath _ p.

  Definition option_decode {x y} : option_code x y -> x = y
    := match x, y return option_code x y -> x = y with
         | Some x', Some y' => @f_equal _ _ (@Some _) _ _
         | None, None => fun _ => eq_refl
         | _, _ => fun H => match H : False with end
       end.

  Definition option_deenecode {x y} (p : x = y)
  : option_decode (option_encode p) = p.
  Proof.
    destruct p, x; reflexivity.
  Defined.

  Definition option_endecode {x y} (p : option_code x y)
  : option_encode (option_decode p) = p.
  Proof.
    destruct x, y, p; reflexivity.
  Defined.

  Definition Some_injective {x y : A} : Some x = Some y -> x = y
    := option_encode.
End option.

Section sum.
  Context {A B : Type}.

  Definition sum_code (x y : A + B) : Prop
    := match x, y with
         | inl x', inl y' => x' = y'
         | inr x', inr y' => x' = y'
         | _, _ => False
       end.

  Definition sum_code_idpath {x} : sum_code x x
    := match x return sum_code x x with
         | inl _ => eq_refl
         | inr _ => eq_refl
       end.

  Definition sum_encode {x y} (p : x = y) : sum_code x y
    := eq_rect _ _ sum_code_idpath _ p.

  Definition sum_decode {x y} : sum_code x y -> x = y
    := match x, y return sum_code x y -> x = y with
         | inl x', inl y' => @f_equal _ _ (@inl _ _) _ _
         | inr x', inr y' => @f_equal _ _ (@inr _ _) _ _
         | _, _ => fun H => match H : False with end
       end.

  Definition sum_deenecode {x y} (p : x = y)
  : sum_decode (sum_encode p) = p.
  Proof.
    destruct p, x; reflexivity.
  Defined.

  Definition sum_endecode {x y} (p : sum_code x y)
  : sum_encode (sum_decode p) = p.
  Proof.
    destruct x, y, p; reflexivity.
  Defined.

  Definition inl_injective {x y : A} : inl x = inl y -> x = y
    := sum_encode.

  Definition inr_injective {x y : B} : inr x = inr y -> x = y
    := sum_encode.
End sum.

Definition prod_dec {A B}
           (HA : forall a b : A, {a = b} + {a <> b})
           (HB : forall a b : B, {a = b} + {a <> b})
: forall a b : A * B, {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

Definition option_dec {A}
           (H : forall a b : A, {a = b} + {a <> b})
: forall a b : option A, {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

Scheme Equality for unit.
Scheme Equality for Empty_set.
Scheme Equality for bool.
Scheme Equality for Ascii.ascii.
Scheme Equality for string.
Scheme Equality for list.
Scheme Equality for option.

Lemma unit_bl {x y} : unit_beq x y = true -> x = y.
Proof. apply internal_unit_dec_bl. Qed.
Lemma unit_lb {x y} : x = y -> unit_beq x y = true.
Proof. apply internal_unit_dec_lb. Qed.
Lemma Empty_set_bl {x y} : Empty_set_beq x y = true -> x = y.
Proof. apply internal_Empty_set_dec_bl. Qed.
Lemma Empty_set_lb {x y} : x = y -> Empty_set_beq x y = true.
Proof. apply internal_Empty_set_dec_lb. Qed.
Lemma bool_bl {x y} : bool_beq x y = true -> x = y.
Proof. apply internal_bool_dec_bl. Qed.
Lemma bool_lb {x y} : x = y -> bool_beq x y = true.
Proof. apply internal_bool_dec_lb. Qed.
Lemma ascii_bl {x y} : ascii_beq x y = true -> x = y.
Proof. apply internal_ascii_dec_bl. Qed.
Lemma ascii_lb {x y} : x = y -> ascii_beq x y = true.
Proof. apply internal_ascii_dec_lb. Qed.
Lemma string_bl {x y} : string_beq x y = true -> x = y.
Proof. apply internal_string_dec_bl. Qed.
Lemma string_lb {x y} : x = y -> string_beq x y = true.
Proof. apply internal_string_dec_lb. Qed.
Lemma list_beq_eqlistA_iff {A eq_A} {x y : list A}
: list_beq eq_A x y = true <-> SetoidList.eqlistA eq_A x y.
Proof.
  split; intro H.
  { generalize dependent y; induction x as [|x xs IHxs]; simpl;
    intros [|??]; simpl; intro H; try discriminate; constructor.
    { apply Bool.andb_true_iff in H; apply H. }
    { apply Bool.andb_true_iff in H.
      destruct H.
      eauto with nocore. } }
  { induction H; simpl; try reflexivity.
    apply Bool.andb_true_iff; split; assumption. }
Qed.
Lemma list_blA {A eq_A} {R : relation A} (A_bl : forall x y : A, eq_A x y = true -> R x y)
      {x y : list A}
: list_beq eq_A x y = true -> SetoidList.eqlistA R x y.
Proof.
  generalize dependent y; induction x as [|x xs IHxs]; simpl;
  intros [|??]; simpl; intro H; try discriminate; constructor;
  apply Bool.andb_true_iff in H; destruct H; eauto with nocore.
Qed.
Lemma list_bl {A eq_A} (A_bl : forall x y : A, eq_A x y = true -> x = y) {x y}
: list_beq eq_A x y = true -> x = y.
Proof. apply internal_list_dec_bl; assumption. Qed.
Lemma list_lb {A eq_A} (A_lb : forall x y : A, x = y -> eq_A x y = true) {x y}
: x = y -> list_beq eq_A x y = true.
Proof. apply internal_list_dec_lb; assumption. Qed.
Lemma option_bl {A eq_A} (A_bl : forall x y : A, eq_A x y = true -> x = y) {x y}
: option_beq eq_A x y = true -> x = y.
Proof. apply internal_option_dec_bl; assumption. Qed.
Lemma option_lb {A eq_A} (A_lb : forall x y : A, x = y -> eq_A x y = true) {x y}
: x = y -> option_beq eq_A x y = true.
Proof. apply internal_option_dec_lb; assumption. Qed.

Section beq_correct.
  Local Ltac t rew_t :=
    match goal with
      | [ |- _ = bool_of_sumbool (?eq_dec ?x ?y) ]
        => revert y; induction x; intro y; simpl
    end;
    match goal with
      | [ |- _ = bool_of_sumbool (?eq_dec ?x ?y) ]
        => destruct (eq_dec x y)
    end;
    subst; simpl in *;
    try solve [ repeat match goal with
                         | [ H : _ <> ?y |- _ ] => is_var y; destruct y
                         | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
                         | [ H : _ |- _ ] => rewrite !H; []
                         | _ => progress rew_t
                         | _ => progress simpl in *
                         | _ => split; (congruence || discriminate)
                         | _ => progress subst
                         | [ |- context[bool_of_sumbool ?e] ]
                           => destruct e; simpl
                         | [ |- true = false ] => exfalso
                         | [ |- false = true ] => exfalso
                         | [ H : _ <> _ |- False ] => apply H; clear H
                         | [ |- ?x = false ] => case_eq x; intro
                       end ].

  Lemma bool_beq_correct {x y} : bool_beq x y = bool_eq_dec x y.
  Proof. t idtac. Qed.
  Lemma ascii_beq_correct {x y} : ascii_beq x y = ascii_eq_dec x y.
  Proof. t ltac:(rewrite !bool_beq_correct). Qed.
  Lemma string_beq_correct {x y} : string_beq x y = string_eq_dec x y.
  Proof. t ltac:(rewrite !ascii_beq_correct). Qed.
  Lemma list_beq_correct {A eq_A}
        (A_bl : forall x y : A, eq_A x y = true -> x = y)
        (A_lb : forall x y : A, x = y -> eq_A x y = true)
        {x y : list A}
  : list_beq eq_A x y = list_eq_dec eq_A A_bl A_lb x y.
  Proof.
    t ltac:(first [ rewrite !(A_lb _ _) by congruence
                  | erewrite (A_bl _ _) by eassumption
                  | rewrite Bool.andb_true_r
                  | rewrite Bool.andb_false_r ]).
  Qed.
  Definition list_eq_dec' {A} (dec_eq_A : forall x y : A, {x = y} + {x <> y})
  : forall x y : list A, {x = y} + {x <> y}.
  Proof.
    refine (list_eq_dec dec_eq_A _ _);
    abstract (intros; edestruct dec_eq_A; simpl in *; subst; congruence).
  Defined.
  Lemma list_beq_correct' {A} {eq_A : A -> A -> bool} {dec_eq_A : forall x y : A, {x = y} + {x <> y}}
        (eq_A_correct : forall x y, eq_A x y = dec_eq_A x y)
        {x y : list A}
  : list_beq eq_A x y = list_eq_dec' dec_eq_A x y.
  Proof.
    unfold list_eq_dec'; erewrite list_beq_correct.
    do 2 edestruct list_eq_dec; subst; simpl; congruence.
    Grab Existential Variables.
    intros ??; rewrite eq_A_correct; edestruct dec_eq_A; simpl; congruence.
    intros ??; rewrite eq_A_correct; edestruct dec_eq_A; simpl; congruence.
  Qed.
  Lemma option_beq_correct {A eq_A}
        (A_bl : forall x y : A, eq_A x y = true -> x = y)
        (A_lb : forall x y : A, x = y -> eq_A x y = true)
        {x y : option A}
  : option_beq eq_A x y = option_eq_dec eq_A A_bl A_lb x y.
  Proof.
    t ltac:(first [ rewrite !(A_lb _ _) by congruence
                  | erewrite (A_bl _ _) by eassumption
                  | rewrite Bool.andb_true_r
                  | rewrite Bool.andb_false_r ]).
  Qed.
  Definition option_eq_dec' {A} (dec_eq_A : forall x y : A, {x = y} + {x <> y})
  : forall x y : option A, {x = y} + {x <> y}.
  Proof.
    refine (option_eq_dec dec_eq_A _ _);
    abstract (intros; edestruct dec_eq_A; simpl in *; subst; congruence).
  Defined.
  Lemma option_beq_correct' {A} {eq_A : A -> A -> bool} {dec_eq_A : forall x y : A, {x = y} + {x <> y}}
        (eq_A_correct : forall x y, eq_A x y = dec_eq_A x y)
        {x y : option A}
  : option_beq eq_A x y = option_eq_dec' dec_eq_A x y.
  Proof.
    unfold option_eq_dec'; erewrite option_beq_correct.
    do 2 edestruct option_eq_dec; subst; simpl; congruence.
    Grab Existential Variables.
    intros ??; rewrite eq_A_correct; edestruct dec_eq_A; simpl; congruence.
    intros ??; rewrite eq_A_correct; edestruct dec_eq_A; simpl; congruence.
  Qed.
End beq_correct.

Section In.
  Section list_bin.
    Context {A} (eq_A : A -> A -> bool) (a : A).

    Fixpoint list_bin (ls : list A) : bool
      := match ls with
           | nil => false
           | x::xs => orb (list_bin xs) (eq_A x a)
         end.
  End list_bin.

  Local Ltac t :=
    repeat match goal with
             | _ => intro
             | _ => progress simpl in *
             | _ => congruence || discriminate
             | [ H : orb _ _ = true |- _ ] => apply Bool.orb_true_iff in H
             | [ |- orb _ _ = true ] => apply Bool.orb_true_iff
             | [ H : ?eqA _ _ = true, H_eqA : forall x y, ?eqA _ _ = true -> _ |- _ ] => apply H_eqA in H
             | [ H : SetoidList.InA _ _ nil |- _ ] => solve [ inversion H ]
             | _ => progress subst
             | [ H : SetoidList.InA _ _ (_::_) |- _ ] => inversion H; clear H
             | [ |- ?x = ?x \/ _ ] => left; reflexivity
             | [ |- _ \/ ?x = ?x ] => right; reflexivity
             | [ |- _ \/ _ ] => right; assumption
             | [ |- _ \/ _ ] => left; assumption
             | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
             | [ H : False |- _ ] => destruct H
             | [ H_eqA : forall x y, x = y -> ?eqA x y = true |- context[?eqA ?x ?x] ] => rewrite (H_eqA x x eq_refl)
             | [ H : _ \/ _ |- _ ] => destruct H
             | _ => left; assumption
             | _ => right; assumption
           end.

  Lemma list_in_bl {A eq_A} (A_bl : forall x y : A, eq_A x y = true -> x = y) {a ls}
  : list_bin eq_A a ls = true -> List.In a ls.
  Proof. induction ls; t. Qed.
  Lemma list_in_lb {A eq_A} (A_lb : forall x y : A, x = y -> eq_A x y = true) {a ls}
  : List.In a ls -> list_bin eq_A a ls = true.
  Proof. induction ls; t. Qed.

  Lemma list_inA_bl {A eq_A} {a ls}
  : list_bin eq_A a ls = true -> SetoidList.InA (fun x y : A => eq_A y x) a ls.
  Proof. induction ls; t. Qed.
  Lemma list_inA_lb {A eq_A} {a ls}
  : SetoidList.InA (fun x y : A => is_true (eq_A y x)) a ls -> list_bin eq_A a ls = true.
  Proof. induction ls; t. Qed.
End In.

Lemma option_rect_ext {A P} Ps Ps' Pn Pn' x
      (Hs : forall k, Ps k = Ps' k)
      (Hn : Pn = Pn')
: @option_rect A P Ps Pn x = @option_rect A P Ps' Pn' x.
Proof.
  destruct x; simpl;
  rewrite ?Hs, ?Hn; reflexivity.
Defined.

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
