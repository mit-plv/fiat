Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Fiat.Common.UIP.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Enumerable.

Local Arguments leb !_ !_.

Local Ltac t' :=
  idtac;
  match goal with
    | [ |- ?x = ?x ] => reflexivity
    | _ => assumption
    | _ => intro
    | _ => progress simpl in *
    | [ H : sig _ |- _ ] => destruct H
    | _ => progress unfold is_true in *
    | [ H : andb ?x ?y = true |- _ ]
      => match goal with
           | [ H' : x = true |- _ ] => fail 1
           | _ => idtac
         end;
        let H' := fresh in
        pose proof (proj1 (Bool.andb_true_iff _ _) H) as H';
          destruct H'
    | [ |- In _ (flat_map _ _) ]
      => apply in_flat_map
    | [ H : ?P ?k |- exists x : sig ?P, _ ] => exists (exist P k H)
    | [ |- exists x : @sig ?A ?P, _ ]
      => (let e := fresh in
          evar (e : A);
          let c := (eval unfold e in (P e)) in
          match goal with
            | [ H : ?T |- _ ] => unify T c; (exists (exist P e H))
          end;
          subst e)
    | [ |- _ /\ _ ] => split
    | [ |- In _ (Enumerable.enumerate _) ] => apply Enumerable.enumerate_correct
    | [ |- In (exist _ _ _) (map _ _) ]
      => apply (in_sig_uip (fun _ => @UIP_bool _ _))
    | _ => rewrite map_map
    | [ |- In _ (map _ (Enumerable.enumerate _)) ] => apply in_map_iff
    | [ x : prod ?A ?B |- _ ] => destruct x
    | [ H : In _ (up_to _) |- _ ] => apply in_up_to_iff in H
    | [ |- In _ (up_to _) ] => apply in_up_to_iff
    | [ |- leb _ _ = true ] => apply leb_iff
    | [ H : leb _ _ = true |- _ ] => apply leb_iff in H
    | _ => rewrite map_proj1_sig_sig_In
    | [ H : ?x = true |- context[?x] ] => rewrite H
  end.

Local Ltac t := repeat t'.

Local Obligation Tactic := try abstract t.

Global Program Instance enumerable_sig_ltb k
: Enumerable { x : nat | is_true (leb (S x) k) }
  := { enumerate
       := List.map
            (fun xp => exist _ (proj1_sig xp) _)
            (sig_In (up_to k)) }.

Global Instance enumerable_sig_leb k
: Enumerable { x : nat | is_true (leb x k) }
  := enumerable_sig_ltb (S k).

Global Program Instance enumerable_sig_andb_dep {A B P Q}
       {HA : Enumerable { x : A | is_true (P x) }}
       {HB : forall a,
               is_true (P a)
               -> Enumerable { x : B | is_true (Q (a, x)) }}
: Enumerable { x : A * B | is_true (P (fst x) && Q x) }
  := { enumerate
       := flat_map (fun aP
                    => List.map
                         (fun bQ => exist _ (proj1_sig aP, proj1_sig bQ) _)
                         (@Enumerable.enumerate
                            _ (HB (proj1_sig aP) (proj2_sig aP))))
                   (Enumerable.enumerate { x : A | is_true (P x) }) }.

Global Instance enumerable_sig_andb {A B P Q}
       {HA : Enumerable { x : A | is_true (P x) }}
       {HB : Enumerable { x : B | is_true (Q x) }}
: Enumerable { x : A * B | is_true (P (fst x) && Q (snd x)) }
  := @enumerable_sig_andb_dep A B P (fun k => Q (snd k)) HA (fun _ _ => HB).

Ltac apply_enumerable_sig_andb_dep :=
  idtac;
  let rec head_under_binders x :=
      match x with
        | ?f _ => head_under_binders f
        | (fun a => ?f a)
          => head_under_binders (fun a => f)
        | (fun a => ?f)
          => head_under_binders f
        | ?x' => x'
      end in
  repeat match goal with
           | [ |- Enumerable { x : ?T | ?P } ]
             => let T' := (eval hnf in T) in
                progress change (Enumerable { x : T' | P })
           | [ |- Enumerable { x : ?T | is_true (_ && _) } ]
             => idtac
           | [ |- Enumerable { x : ?T | is_true (?P x) } ]
             => let h := head_under_binders P in
                unfold h
         end;
    (lazymatch goal with
    | [ |- Enumerable { x : ?A * ?B | is_true (@?P x && @?Q x) } ]
      => (idtac;
          let P' := constr:(fun b a => P (a, b)) in
          let P' := (eval cbv beta in P') in
          let P' := (eval simpl @fst in P') in
          let P' := match P' with (fun _ => ?P') => P' end in
          apply (@enumerable_sig_andb_dep A B P' Q);
          simpl @fst; simpl @snd)
     end).

Hint Extern 2 (Enumerable (sig _)) => apply_enumerable_sig_andb_dep : typeclass_instances.
