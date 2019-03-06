Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.Syntactify.
Require Import Fiat.Common.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.List.Operations.
Set Implicit Arguments.

Local Open Scope list_scope.

Section normalization_by_evaluation.
  Context (var : TypeCode -> Type).

  Fixpoint normalized_of (T : TypeCode) : Type :=
    match T with
    | csimple T' => Term var T'
    | carrow A B => normalized_of A -> normalized_of B
    end.

  Fixpoint reify {T} : normalized_of T -> Term var T
    := match T return normalized_of T -> Term var T with
       | csimple _
         => fun x => x
       | carrow A B => fun f => RLambda (fun x => reify (f (reflect (RVar x))))
       end
  with reflect {T} : Term var T -> normalized_of T
       := match T return Term var T -> normalized_of T with
          | csimple _
            => fun x => x
          | carrow A B => fun e x => reflect (RApp e (reify x))
          end.

  Definition onelevel (T : SimpleTypeCode) : Type
    := interp_SimpleTypeCode_step (Term var) T.

  Definition onelevelG (T : TypeCode) : Type :=
    match T with
    | csimple T' => onelevel T'
    | _ => Empty_set
    end.

  Definition args_for_onelevel : TypeCode -> Type
    := args_for (fun A => option (onelevelG A)).

  Section constantOfs.
    Context (constantOf : forall {T} (t : Term var T), option (onelevelG T)).

    Definition constantOfs {T} (af : args_for (Term var) T) : args_for_onelevel T :=
      map_args_for constantOf af.
  End constantOfs.

  Fixpoint constantOf {T} (t : Term var T) : option (onelevelG T)
    := match t in Term _ T return option (onelevelG T) with
       | RLiteralApp _ l af =>
         match l with
         | RLC l'
           => match l' in RLiteralConstructor T return args_for (Term var) T -> args_for_onelevel T -> option (onelevel (range_of T)) with
              | Rpair _ _ => fun af _ => Some (ahd af, ahd (atl af))
              | RS => fun af afr => option_map S (ahd afr)
              | RO => fun _ _ => Some O
              | Rnil _ => fun _ _ => Some nil
              | Rcons _ => fun af afr => option_map (cons (ahd af)) (ahd (atl afr))
              | Rbool v
              | Rrchar_expr_ascii v
              | Rstring v
              | Rritem_ascii v
                => fun _ _ => Some v
              end
         | RLNC _
           => fun _ _ => None
         end af (constantOfs (@constantOf) af)
       | _ => None
       end.

  Definition arg_meanings_for : TypeCode -> Type :=
    args_for normalized_of.

  Section meanings.
    Context (meaning : forall {T} (t : Term normalized_of T), normalized_of T).

    Definition meanings {T} (af : args_for (Term normalized_of) T) : arg_meanings_for T :=
      map_args_for meaning af.
  End meanings.

  Definition unmeanings {T}
             (args : arg_meanings_for T)
    : args_for (Term var) T
    := map_args_for (fun _ => reify) args.

  Fixpoint apply_meaning_helper {P}
           (af : arg_meanings_for P)
    : forall (f : normalized_of P),
      normalized_of (range_of P)
    := match af in args_for _ P return normalized_of P -> normalized_of (range_of P) with
       | an_arg _ _ arg args
         => fun f => @apply_meaning_helper _ args (f arg)
       | noargs _ => fun v => v
       end.

  Definition specific_meaning_apply1 {A : SimpleTypeCode} {B} {B'}
             (syntactify : B' -> normalized_of (range_of B))
             (f : onelevelG A -> B')
             (args : arg_meanings_for (A --> B))
    : option (normalized_of (range_of (A --> B)))
      := option_map (fun v => syntactify (f v)) (constantOf (ahd args)).
  Global Arguments specific_meaning_apply1 _ _ {_} _ _ _.

  Definition specific_meaning_apply2 {A B : SimpleTypeCode} {C} {C'}
             (syntactify : C' -> normalized_of (range_of C))
             (f : onelevelG A -> onelevelG B -> C')
             (args : arg_meanings_for (A --> B --> C))
    : option (normalized_of (range_of (A --> B --> C)))
      := match constantOf (ahd args), constantOf (ahd (atl args)) with
         | Some v0, Some v1 => Some (syntactify (f v0 v1))
         | _, _ => None
         end.
  Global Arguments specific_meaning_apply2 _ _ _ {_} _ _ _.

  Definition specific_meaning {T} (t : RLiteralNonConstructor T)
    : arg_meanings_for T -> option (normalized_of (range_of T))
    := match t in RLiteralNonConstructor T return arg_meanings_for T -> option (normalized_of (range_of T)) with
       | Rfst _ _ => specific_meaning_apply1 (cprod _ _) (csimple _) (fun x => x) fst
       | Rsnd _ _ => specific_meaning_apply1 (cprod _ _) (csimple _) (fun x => x) snd
       | Rnth' _
         => fun af
            => specific_meaning_apply2
                 cnat (clist _) (_ --> csimple _) (fun x => x)
                 (fun n ls => List.nth' n ls (ahd (atl (atl af))))
                 af
       | Rnth _
         => fun af
            => specific_meaning_apply2
                 cnat (clist _) (_ --> csimple _) (fun x => x)
                 (fun n ls => List.nth n ls (ahd (atl (atl af))))
                 af
       | Rbeq_nat
         => specific_meaning_apply2
              cnat cnat cbool (syntactify_bool _)
              EqNat.beq_nat
       | Rmap A B
         => fun af
            => option_map (@syntactify_list _ _)
                          (option_map (List.map (ahd af))
                                      (constantOf (ahd (atl af))))
       | Rfold_left A B
         => fun af
            => option_map
                 (fun ls =>
                    let init := ahd (atl (atl af)) in
                    let f := ahd af in
                    List.fold_left f ls init)
                 (constantOf (ahd (atl af)))
       | Rorb | Rorbr
         => fun af
            => match constantOf (ahd af), constantOf (ahd (atl af)) with
               | Some b, _
                 => Some (if b then syntactify_bool var true else ahd (atl af))
               | _, Some b
                 => Some (if b then syntactify_bool var true else ahd af)
               | None, None => None
               end
       | Randb | Randbr
         => fun af
            => match constantOf (ahd af), constantOf (ahd (atl af)) with
               | Some b, _
                 => Some (if b then ahd (atl af) else syntactify_bool var false)
               | _, Some b
                 => Some (if b then ahd af else syntactify_bool var false)
               | None, None => None
               end
       | Rminusr
         => fun af
            => match constantOf (ahd af), constantOf (ahd (atl af)) with
               | Some n, Some n'
                 => Some (syntactify_nat var (minusr n n'))
               | _, Some n'
                 => Some (apply_n n' (fun n0 => RLiteralApp Rpred (n0 :: noargs)) (ahd af))
               | _, _ => None
               end
       | Rpred
         => specific_meaning_apply1
              cnat cnat (syntactify_nat _)
              pred
       | Rlength _
         => specific_meaning_apply1
              (clist _) cnat (syntactify_nat _)
              (@List.length _)
       | Rbool_rect_nodep cbool
         => fun af
            => let rtest := ahd (atl (atl af)) in
               let rtrue := ahd af in
               let rfalse := ahd (atl af) in
               match constantOf rtest, constantOf rtrue, constantOf rfalse with
               | Some b, _, _
                 => Some (if b then rtrue else rfalse)
               | None, Some true, Some true
                 => Some (Syntactify.syntactify_bool _ true)
               | None, Some false, Some false
                 => Some (Syntactify.syntactify_bool _ false)
               | None, Some true, Some false
                 => Some rtest
               | None, Some false, Some true
               | None, None, _
               | None, _, None
                 => None
               end
       | Rbool_rect_nodep _
         => fun af
            => option_map (fun b : bool
                           => if b
                              then ahd af
                              else ahd (atl af))
                          (constantOf (ahd (atl (atl af))))
       | Rlist_rect_nodep A P
         => fun af
            => option_map (fun ls
                           => apply_meaning_helper
                                (atl (atl (atl af)))
                                (list_rect_nodep
                                   (ahd af)
                                   (fun x xs => ahd (atl af) x (syntactify_list xs))
                                   ls))
                          (constantOf (ahd (atl (atl af))))
       | Rlist_caset_nodep _ _
         => fun af
            => option_map (fun ls
                           => list_caset_nodep
                                (ahd af)
                                (fun x xs => ahd (atl af) x (syntactify_list xs))
                                ls)
                          (constantOf (ahd (atl (atl af))))
       | Rleb
         => specific_meaning_apply2
              cnat cnat cbool (syntactify_bool _)
              Compare_dec.leb
       | Rcombine _ _
         => specific_meaning_apply2
              (clist _) (clist _) (clist _) (fun ls => syntactify_list (List.map (@syntactify_prod _ _ _) ls))
              (@List.combine _ _)
       | Rrev _
         => specific_meaning_apply1 (clist _) (csimple _) (@syntactify_list _ _) (@List.rev _)
       | Rup_to
         => specific_meaning_apply1
              cnat (clist _) (fun ls => syntactify_list (List.map (@syntactify_nat _) ls))
              List.up_to
       | Rplus
         => fun af
            => match constantOf (ahd af), constantOf (ahd (atl af)) with
               | Some n, Some n'
                 => Some (syntactify_nat var (plus n n'))
               | Some n, _
                 => Some (apply_n n (fun n0 => RLiteralApp RS (n0 :: noargs)) (ahd (atl af)))
               | _, Some n'
                 => Some (apply_n n' (fun n0 => RLiteralApp RS (n0 :: noargs)) (ahd af))
               | None, None => None
               end
       | Rmax
         => specific_meaning_apply2
              cnat cnat cnat (syntactify_nat _)
              max
       | Rritem_rect_nodep _
         => fun af
            => option_map (fun v
                           => Reflective.ritem_rect_nodep
                                (fun x => ahd af (syntactify_rchar_expr_ascii var x))
                                (fun s => ahd (atl af) (syntactify_string var s))
                                v)
                          (constantOf (ahd (atl (atl af))))
       | Rfirst_index_default _
         => fun af
            => match constantOf (ahd (atl af)), constantOf (ahd (atl (atl af))) with
               | Some v, Some ls =>
                 let f := ahd af in
                 option_map (syntactify_nat var)
                            (first_index_default_partial (fun a => constantOf (f a)) v ls)
               | _, _ => None
               end
       | Rstring_beq
         => specific_meaning_apply2
              cstring cstring cbool (syntactify_bool _)
              Equality.string_beq
       | Rinterp_RCharExpr_ascii => fun _ => None
       end.

  Fixpoint meaning {T} (t : Term normalized_of T) : normalized_of T
      := match t in Term _ T return normalized_of T with
         | RLiteralApp _ l af =>
           match l with
           | RLC l'
             => fun af => RLiteralApp l' (unmeanings af)
           | RLNC l'
             => fun af => option_rect (fun _ => _)
                                      (fun x => x)
                                      (RLiteralApp l' (unmeanings af))
                                      (specific_meaning l' af)
           end (meanings (@meaning) af)
         | RLambda _ _ f => fun x => @meaning _ (f x)
         | RVar _ v => v
         | RApp _ _ f x => @meaning _ f (@meaning _ x)
         end.

  Definition normalize {T} (term : Term normalized_of T) : Term var T := reify (meaning term).
End normalization_by_evaluation.

Definition polynormalize {T} (term : polyTerm T) : polyTerm T
  := fun var => normalize (term _).

Section lemmas.
  Definition interp_constantOf {T} : onelevelG interp_TypeCode T -> interp_TypeCode T
    := match T return onelevelG _ T -> interp_TypeCode T with
       | cnat
       | cbool
       | cstring
       | cascii
       | critem_ascii
       | crchar_expr_ascii
         => fun x => x
       | clist T => List.map interp_Term
       | cprod A B => fun xy => (interp_Term (fst xy), interp_Term (snd xy))
       | carrow A B => fun x : Empty_set => match x with end
       end.

  Fixpoint interp_constantOfs_to_values {T}
           (args : args_for_onelevel interp_TypeCode T)
    : args_for (fun T => option (interp_TypeCode T)) T
    := match args in args_for _ T return args_for _ T with
       | an_arg _ _ arg args => an_arg (option_map interp_constantOf arg) (@interp_constantOfs_to_values _ args)
       | noargs T => noargs
       end.
End lemmas.
