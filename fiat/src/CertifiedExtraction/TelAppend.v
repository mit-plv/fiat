Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeNotations
        CertifiedExtraction.PropertiesOfTelescopes
        CertifiedExtraction.ExtendedPropertiesOfTelescopes
        CertifiedExtraction.ExtendedLemmas.

Fixpoint TelAppend {av} (t1 t2: Telescope av) :=
  match t1 with
  | Nil => t2
  | Cons T key val tail => Cons (T := T) key val (fun v => TelAppend (tail v) t2)
  end.

Lemma TelAppend_Nil {av} :
  forall t: Telescope av,
    TelStrongEq (TelAppend t Nil) t.
Proof.
  induction t; simpl.
  + reflexivity.
  + econstructor; eauto with typeclass_instances.
Qed.

Lemma TelEq_TelAppend_Cons_Second {av A B}:
  forall {H : FacadeWrapper (Value av) B} (t1: Telescope av) t2 k (v : Comp A) ext,
    TelEq ext
          ([[ k ~~> v as vv]] :: TelAppend t1 (t2 vv))
          (TelAppend t1 ([[ k ~~> v as vv]] :: (t2 vv))).
Proof.
  intros.
  induction t1; simpl.
  + reflexivity.
  + rewrite TelEq_swap.
    setoid_rewrite H0.
    reflexivity.
Qed.

Add Parametric Morphism {av} : (@TelAppend av)
    with signature ((TelStrongEq) ==> (TelStrongEq) ==> (TelStrongEq))
      as TelAppend_TelStrongEq_morphism.
Proof.
  induction 1; simpl.
  + eauto with typeclass_instances.
  + intros.
    econstructor; eauto.
Qed.

Add Parametric Morphism {av} ext : (@TelAppend av)
    with signature (TelStrongEq ==> (TelEq ext) ==> (TelEq ext))
      as TelAppend_TelStrongEq_TelEq_morphism.
Proof.
  intros.
  rewrite H; clear H.
  induction y; simpl; intros.
  + assumption.
  + apply Cons_TelEq_pointwise_morphism; red; eauto.
Qed.

Add Parametric Morphism {av} ext : (@TelAppend av)
    with signature (TelEq ext ==> TelEq ext ==> (TelEq ext))
      as TelAppend_TelEq_morphism.
Proof.
  intros.
  rewrite H0; clear H0.
  induction y0.
  + rewrite !TelAppend_Nil; assumption.
  + setoid_rewrite <- TelEq_TelAppend_Cons_Second.
    setoid_rewrite H0.
    reflexivity.
Qed.

Ltac standalone_tail tail :=
  (* Recurse down the TAIL of telescope (of type (a: A) → Telescope) to find the
     first subtelescope that doesn't depend on ‘a’. *)
  lazymatch tail with (* This is a really cute piece of code *)
  | (fun a => Cons _ _ (fun _ => ?tail)) => constr:(tail)
  | (fun a => Cons _ _ (fun _ => @?tail a)) => standalone_tail tail
  end.

Ltac function_surrounding_standalone_tail tail :=
  (* Recurse down the TAIL of telescope (of type (a: A) → Telescope) to find the
     first subtelescope that doesn't depend on ‘a’, and construct a function
     plugging an arbitrary argument instead of that subtelescope. *)
  lazymatch tail with
  | (fun a: ?A => Cons ?k ?v (fun _ => ?tail)) =>
    let _t := constr:(tail) in (* Fails if ‘tail’ depends on a *)
    constr:(fun plug => fun a: A => (Cons k v (fun _ => plug)))
  | (fun a: ?A => Cons ?k ?v (fun _ => @?tail a)) =>
    let fn := function_surrounding_standalone_tail tail in
    eval cbv beta in (fun plug => fun a: A => (Cons k v (fun _ => fn plug a)))
  end.

Ltac split_tail_of_telescope tel :=
  (* Split the tail TEL (a function) into two parts, using ‘standalone_tail’ and
     ‘function_surrounding_standalone_tail’. *)
  match tel with
  | Cons ?k ?v ?tail =>
    let tl := standalone_tail tail in
    let tenvF := function_surrounding_standalone_tail tail in
    (* let tenvF := (eval cbv beta in (fun plug => Cons k v (tenvF plug))) in *)
    constr:(tenvF, tl)
  end.

Ltac make_TelAppend tel :=
  (** Change the tail of TEL into a ‘TelAppend’ of two parts: one depending on
      the head value of tail, and the other independent of it. *)
  match tel with
  | Cons ?k ?v ?tail =>
    let appTl := standalone_tail tail in
    let tenvF := function_surrounding_standalone_tail tail in
    let appHead := (eval cbv beta in (Cons k v (tenvF Nil))) in
    constr:(TelAppend appHead appTl)
  end.
