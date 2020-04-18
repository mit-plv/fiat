Require Import Coq.omega.Omega.
Require Coq.Setoids.Setoid.

(** This file defines some inductives, type-classes and tactics to
perform reflection on a small scale *)

(** Two inductives to perform case-based reasonning *)
Inductive reflect (P Q : Prop) : bool -> Type :=
| reflect_true : P -> reflect P Q true
| reflect_false : Q -> reflect P Q false.

Inductive semi_reflect (P : Prop) : bool -> Type :=
  | semi_reflect_true : P -> semi_reflect P true
  | semi_reflect_false : semi_reflect P false.

Lemma iff_to_reflect {A B} (P : A -> B -> Prop) (T : A -> B -> bool)  :
  (forall x y, T x y = true <-> P x y) ->
  (forall x y, reflect (P x y) (~P x y) (T x y)).
Proof.
  intros. case_eq (T x y); intros Hxy; constructor.
  rewrite <- H; auto.
  intros Hf;   rewrite <- H, Hxy in Hf; discriminate.
Qed.

Lemma impl_to_semireflect {A B} (P : A -> B -> Prop) (T : A -> B -> bool)  :
  (forall x y, T x y = true -> P x y) ->
  (forall x y, semi_reflect (P x y) (T x y)).
Proof.
  intros. case_eq (T x y); intros Hxy; constructor.
  apply H; auto.
Qed.

Lemma reflect_true_inv P Q : reflect P Q true -> P.
Proof.
  exact (fun x => match x in reflect _ _ b
                    return if b then P else ID
                 with | reflect_true H => H | reflect_false H => (fun _ x => x) end).
Qed.

Lemma reflect_false_inv P Q : reflect P Q false -> Q.
Proof.
  exact (fun x => match x in reflect _ _ b
                    return if b then ID else Q
                 with | reflect_true H => fun _ x => x | reflect_false H => H end).
Qed.

Lemma semi_reflect_true_inv P : semi_reflect P true -> P.
Proof.
  exact (fun x => match x in semi_reflect _ b
                    return if b then P else ID
                 with | semi_reflect_true H => H | semi_reflect_false => (fun _ x => x) end).
Qed.


Class Reflect (T : bool) (P Q : Prop) := _Reflect : reflect P Q T.
Class SemiReflect (T : bool) (P : Prop) := _SemiReflect : semi_reflect P T.

Section boolean_logic.
  Ltac t :=
    repeat match goal with
           | H: Reflect true ?P ?Q |- _ => apply (reflect_true_inv P Q) in H
           | H: Reflect false ?P ?Q |- _ => apply (reflect_false_inv P Q) in H
           end.

  Context {T1 T2 P1 Q1 P2 Q2} {R1 : Reflect T1 P1 Q1} {R2: Reflect T2 P2 Q2}.

  Global Instance Reflect_andb : Reflect (T1 && T2)%bool (P1 /\ P2) (Q1 \/ Q2).
  Proof.
    destruct T1; destruct T2; t; constructor; tauto.
  Qed.

  Global Instance Reflect_orb : Reflect (T1 || T2)%bool (P1 \/ P2) (Q1 /\ Q2).
  Proof.
    destruct T1; destruct T2; t; constructor; tauto.
  Qed.

  Global Instance Reflect_negb : Reflect (negb T1)%bool Q1 P1.
  Proof.
    destruct T1; t; constructor; tauto.
  Qed.

End boolean_logic.

Require Coq.Arith.Arith.
Section reflect_peano.

  Global Instance Reflect_eqb_nat x y : Reflect (EqNat.beq_nat x y) (x = y) (x <> y).
  Proof.
    apply iff_to_reflect.
    apply EqNat.beq_nat_true_iff.
  Qed.

  Global Instance Reflect_leb_nat x y : Reflect (NPeano.leb x y) (x <= y) (y < x).
  Proof.
    intros. case_eq (NPeano.leb x y); intros; constructor.
    apply NPeano.leb_le in H; auto.
    destruct (Compare_dec.le_lt_dec x y); auto.
    exfalso.
    apply NPeano.leb_le in l; auto. congruence.
  Qed.

  Global Instance Reflect_ltb_nat x y : Reflect (NPeano.ltb x y) (x < y) (y <= x).
  Proof.
    intros. case_eq (NPeano.ltb x y); intros; constructor.
    apply NPeano.ltb_lt in H; auto.
    destruct (Compare_dec.le_lt_dec y x); auto.
    exfalso.
    apply NPeano.ltb_lt in l; auto. congruence.
  Qed.
End reflect_peano.

(** The main tactic. [consider f] will perform case-analysis (using
[case]) on the function symbol [f] using a reflection-lemma that is
inferred by type-class resolution. *)

Ltac consider f :=
  let rec clean :=
    match goal with
      | |- true = true -> _ => intros _ ; clean
      | |- false = true -> _ => discriminate
      | |- ?P1 -> ?P2 =>
        let H := fresh in intros H ; clean; revert H
      | |- _ => idtac
    end
  in
  (repeat match goal with
            | [ H : context [ f ] |- _ ] =>
              revert H
          end) ;
  match type of f with
    | sumbool _ _ =>
      destruct f
    | _ =>
      match goal with
        | _ =>
          ((let c := constr:(_ : Reflect f _ _) in
            case c;
            let H := fresh in
            intros H; try rewrite H; revert H))
        | _ =>
          ((let c := constr:(_ : SemiReflect f _) in
            case c;
            let H := fresh in
            try (intros H; try rewrite H; revert H)))
        | _ =>
          (** default to remembering the equality **)
          case_eq f
      end
  end ; clean.

(**  Some tests *)
Section test.
  Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Bool.Bool.

  Require Import Coq.omega.Omega.
  Goal forall x y z,  (ltb x y && ltb y z) = true ->
                 ltb x z = true.
  intros x y z.
  consider (ltb x y && ltb y z).
  consider (ltb x z); auto. intros. exfalso. omega.
  Qed.

  Goal forall x y z,
    ltb x y = true ->
    ltb y z = true ->
    ltb x z = true.
  Proof.
    intros. consider (ltb x y); consider (ltb y z); consider (ltb x z); intros; auto.
    exfalso; omega.
  Qed.

End test.

(** A more powerful tactic that takes as argument a tuple of functions
  symbols, and use the fact that some reflection lemmas have been declared for them *)

(* NOT YET PORTED
Ltac t L :=
  let rec foo l :=
      match l with
        | (?t,?q) => case (_test (t _)); foo q
        | (?t,?q) => case (_test (t _ _)); foo q
        | (?t,?q) => case (_test (t _ _ _)); foo q
        | (?t,?q) => case (_test (t _ _ _ _)); foo q

        | tt => idtac
      end  in
    foo L;
  intros;
  repeat match goal with
           | H : true = true |- _ => clear H
           | H : false = false |- _ => clear H
           | H : true = false |- _ => clear - H; discriminate
           | H : false = true |- _ => clear - H; discriminate
         end.
*)
