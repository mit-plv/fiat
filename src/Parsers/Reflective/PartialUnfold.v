Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.Syntactify.
Require Import Fiat.Common.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.BoolFacts.
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

  Fixpoint meaning {T} (t : Term normalized_of T) : normalized_of T.
  Proof.
    refine match t in Term _ T return normalized_of T with
           | RLiteralApp _ l af =>
             match l with
             | RLC l'
               => fun af => RLiteralApp l' (unmeanings af)
             | RLNC l'
               => fun af
                  => match l' in RLiteralNonConstructor T return arg_meanings_for T -> normalized_of (range_of T) -> normalized_of (range_of T) with
                     | Rfst _ _
                       => fun af default
                          => option_rect (fun _ => _)
                                         fst default
                                         (constantOf (ahd af))
                     | Rsnd _ _
                       => fun af default
                          => option_rect (fun _ => _)
                                         snd default
                                         (constantOf (ahd af))
                     | Rnth' _
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some ls
                               => List.nth' n ls (ahd (atl (atl af)))
                             | _, _ => default
                             end
                     | Rnth _
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some ls
                               => List.nth n ls (ahd (atl (atl af)))
                             | _, _ => default
                             end
                     | Rbeq_nat
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some n' =>
                               syntactify_bool var (EqNat.beq_nat n n')
                             | _, _ => default
                             end
                     | Rmap A B
                       => fun af default
                          => option_rect
                               (fun _ => _)
                               (fun ls => syntactify_list (List.map (ahd af) ls))
                               default
                               (constantOf (ahd (atl af)))
                     | Rfold_left A B
                       => fun af default
                          => option_rect
                               (fun _ => _)
                               (fun ls =>
                                  let init := ahd (atl (atl af)) in
                                  let f := ahd af in
                                  List.fold_left f ls init)
                               default
                               (constantOf (ahd (atl af)))
                     | Rorb
                       => fun af default
                          => match constantOf (ahd af) with
                             | Some b
                               => if b then syntactify_bool var true else ahd (atl af)
                             | _ => default
                             end
                     | Randb
                       => fun af default
                          => match constantOf (ahd af) with
                             | Some b
                               => if b then ahd (atl af) else syntactify_bool var false
                             | _ => default
                             end
                     | Rorbr
                       => fun af default
                          => match constantOf (ahd (atl af)) with
                             | Some b
                               => if b then syntactify_bool var true else ahd af
                             | _ => default
                             end
                     | Randbr
                       => fun af default
                          => match constantOf (ahd (atl af)) with
                             | Some b
                               => if b then ahd af else syntactify_bool var false
                             | _ => default
                             end
                     | Rminusr
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some n'
                               => syntactify_nat var (minusr n n')
                             | _, Some n'
                               => apply_n n' (fun n0 => RLiteralApp Rpred (n0 :: noargs)) (ahd af)
                             | _, _ => default
                             end
                     | Rpred
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun n => syntactify_nat var (pred n))
                                         default
                                         (constantOf (ahd af))
                     | Rlength _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun ls => syntactify_nat var (List.length ls))
                                         default
                                         (constantOf (ahd af))
                     | Rbool_rect_nodep _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun b : bool
                                          => if b
                                             then ahd af
                                             else ahd (atl af))
                                         default
                                         (constantOf (ahd (atl (atl af))))
                     | Rlist_rect_nodep A P
                       => fun af default
                          => option_rect (fun _ => normalized_of (range_of P))
                                         (fun ls
                                          => apply_meaning_helper
                                               (atl (atl (atl af)))
                                               (list_rect_nodep
                                                  (ahd af)
                                                  (fun x xs => ahd (atl af) x (syntactify_list xs))
                                                  ls))
                                         default
                                         (constantOf (ahd (atl (atl af))))
                     | Rlist_caset_nodep _ _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun ls
                                          => list_caset_nodep
                                               (ahd af)
                                               (fun x xs => ahd (atl af) x (syntactify_list xs))
                                               ls)
                                         default
                                         (constantOf (ahd (atl (atl af))))
                     | Rleb
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some n' =>
                               syntactify_bool var (Compare_dec.leb n n')
                             | _, _ => default
                             end
                     | Rcombine _ _
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some ls1, Some ls2 =>
                               syntactify_list
                                 (List.map
                                    (fun p => RLiteralApp
                                                Rpair
                                                (fst p :: snd p :: noargs))
                                    (List.combine ls1 ls2))
                             | _, _ => default
                             end
                     | Rrev _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun ls => syntactify_list (List.rev ls))
                                         default
                                         (constantOf (ahd af))
                     | Rup_to
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun n
                                          => syntactify_list (List.map (syntactify_nat var) (List.up_to n)))
                                         default
                                         (constantOf (ahd af))
                     | Rplus
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some n'
                               => syntactify_nat var (plus n n')
                             | Some n, _
                               => apply_n n (fun n0 => RLiteralApp RS (n0 :: noargs)) (ahd (atl af))
                             | _, _ => default
                             end
                     | Rmax
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some n'
                               => syntactify_nat var (max n n')
                             | _, _ => default
                             end
                     | Rritem_rect_nodep _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun v
                                          => Reflective.ritem_rect_nodep
                                               (fun x => ahd af (syntactify_rchar_expr_ascii var x))
                                               (fun s => ahd (atl af) (syntactify_string var s))
                                               v)
                                         default
                                         (constantOf (ahd (atl (atl af))))
                     | Rfirst_index_default _
                       => fun af default
                          => match constantOf (ahd (atl af)), constantOf (ahd (atl (atl af))) with
                             | Some v, Some ls =>
                               let f := ahd af in
                               match first_index_default_partial (fun a => constantOf (f a)) v ls with
                               | None => default
                               | Some n => syntactify_nat var n
                               end
                             | _, _ => default
                             end
                     | Rinterp_RCharExpr_ascii => fun af default => default
                     | Rstring_beq
                       => fun af default
                          => match constantOf (ahd af), constantOf (ahd (atl af)) with
                             | Some n, Some n' =>
                               syntactify_bool var (Equality.string_beq n n')
                             | _, _ => default
                             end
                     end af (RLiteralApp l' (unmeanings af))
             end (meanings (@meaning) af)
           | RLambda _ _ f => fun x => @meaning _ (f x)
           | RVar _ v => v
           | RApp _ _ f x => @meaning _ f (@meaning _ x)
           end.
  Defined.

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
