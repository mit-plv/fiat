Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.EquivDec.

Section Classes.
  Context {A : Type}.
  Context {dec : EqDec A (@eq A)}.

  Theorem UIP_refl : forall {x : A} (p1 : x = x), p1 = refl_equal _.
    intros.
    eapply UIP_dec. apply equiv_dec.
  Qed.

  Theorem UIP_equal : forall {x y : A} (p1 p2 : x = y), p1 = p2.
    eapply UIP_dec. apply equiv_dec.
  Qed.

  Lemma inj_pair2 :
    forall (P:A -> Type) (p:A) (x y:P p),
      existT P p x = existT P p y -> x = y.
  Proof.
    intros. eapply inj_pair2_eq_dec; auto.
  Qed.

End Classes.

Global Instance option_eqdec T (_ : EqDec T (@eq T)) : EqDec (option T) (@eq (option T)).
  red; refine (
  fun a b =>
    match a, b with
      | None, None => left (refl_equal _)
      | Some a, Some b => match equiv_dec a b with
                            | left pf => left match (pf : a = b) in _ = t return Some a = Some t with
                                                | refl_equal => refl_equal
                                              end
                            | right pf => right (fun pf' => pf _)
                          end
      | None , Some _ => right _
      | Some _ , None => right _
    end).
  inversion pf'; reflexivity.
  abstract (intro; congruence).
  abstract (intro; congruence).
Defined.


(*
Global Instance list_eqdec T (_ : EqDec T (@eq T)) : EqDec (list T) (@eq (list T)).
  red; refine (
  fun a b =>
    match a, b with
      | None, None => left (refl_equal _)
      | Some a, Some b => match equiv_dec a b with
                            | left pf => left _
                            | right pf => right _
                          end
      | _ , _ => right _
    end).
  abstract (rewrite pf; reflexivity).
  abstract (intro H; apply pf; inversion H; reflexivity).
  abstract (intro; congruence).
  abstract (intro; congruence).
Defined.
*)

Ltac notVar X :=
  match X with
    | _ _ => idtac
    | _ _ _ => idtac
    | _ _ _ _ => idtac
    | _ _ _ _ _ => idtac
    | _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
    | _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.

Ltac uip_all :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
           | [ |- context [ match ?X in _ = t return _ with
                              | refl_equal => _
                            end ] ] => notVar X; generalize X
           | [ |- context [ eq_rect_r _ _ ?X ] ] => notVar X; generalize X
         end;
  intros;
    repeat match goal with
             | [ H : ?X = ?X |- _ ] => rewrite (UIP_refl H) in *
           end.

Require Export Coq.Classes.EquivDec.
