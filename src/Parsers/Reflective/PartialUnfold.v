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

  Inductive args_for_onelevel : TypeCode -> Type :=
  | an_arg_ol {A B}
              (arg : option (onelevelG A))
              (args : args_for_onelevel B)
    : args_for_onelevel (A --> B)
  | noargs_ol {T} : args_for_onelevel (csimple T).

  Definition ahdo {A B} (af : args_for_onelevel (A --> B))
    : option (onelevelG A) :=
    match af in args_for_onelevel T
          return match T with
                 | carrow A B => option (onelevelG A)
                 | _ => unit
                 end
    with
    | an_arg_ol _ _ arg _ => arg
    | _ => tt
    end.

  Definition atlo {A B} (af : args_for_onelevel (A --> B))
    : args_for_onelevel B :=
    match af in args_for_onelevel T
          return match T with
                 | carrow A B => args_for_onelevel B
                 | _ => unit
                 end
    with
    | an_arg_ol _ _ _ af' => af'
    | _ => tt
    end.

  Fixpoint aino {T U} (v : onelevelG T) (args : args_for_onelevel U) : Prop
    := match args with
       | an_arg_ol A B arg args
         => (exists pf : T = A,
                arg = Some (eq_rect T onelevelG v A pf))
            \/ @aino _ _ v args
       | noargs_ol T => False
       end.

  Section constantOfs.
    Context (constantOf : forall {T} (t : Term var T), option (onelevelG T)).

    Fixpoint constantOfs {T} (af : args_for var T) : args_for_onelevel T :=
      match af with
      | noargs _ => noargs_ol
      | an_arg _ _ arg af' => an_arg_ol (constantOf arg) (constantOfs af')
      end.
  End constantOfs.

  Fixpoint constantOf {T} (t : Term var T) : option (onelevelG T)
    := match t in Term _ T return option (onelevelG T) with
       | RLiteralApp _ l af =>
         match l with
         | RLC l'
           => match l' in RLiteralConstructor T return args_for var T -> args_for_onelevel T -> option (onelevel (range_of T)) with
              | Rpair _ _ => fun af _ => Some (ahd af, ahd (atl af))
              | RS => fun af afr => option_map S (ahdo afr)
              | RO => fun _ _ => Some O
              | Rnil _ => fun _ _ => Some nil
              | Rcons _ => fun af afr => option_map (cons (ahd af)) (ahdo (atlo afr))
              | Rfalse => fun _ _ => Some false
              | Rtrue => fun _ _ => Some true
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

  Inductive arg_meanings_for : TypeCode -> Type :=
  | an_argm {A B} (arg : normalized_of A) (args : arg_meanings_for B) : arg_meanings_for (carrow A B)
  | noargsm {T} : arg_meanings_for (csimple T).

  Definition ahdm {A} {B} (af : arg_meanings_for (A --> B)) : normalized_of A :=
    match af in arg_meanings_for T return match T with
                                          | carrow A B => normalized_of A
                                          | _ => unit
                                          end with
    | an_argm _ _ arg _ => arg
    | _ => tt
    end.

  Definition atlm {A} {B} (af : arg_meanings_for (A --> B)) : arg_meanings_for B :=
    match af in arg_meanings_for T return match T with
                                          | carrow A B => arg_meanings_for B
                                          | _ => unit
                                          end with
    | an_argm _ _ _ af' => af'
    | _ => tt
    end.

  Section meanings.
    Context (meaning : forall {T} (t : Term normalized_of T), normalized_of T).

    Fixpoint meanings {T} (af : args_for normalized_of T) : arg_meanings_for T :=
      match af with
      | noargs _ => noargsm
      | an_arg _ _ arg af' => an_argm (meaning arg) (meanings af')
      end.
  End meanings.

  Fixpoint unmeanings {T}
           (args : arg_meanings_for T)
    : args_for var T
    := match args in arg_meanings_for T
             return args_for _ T
       with
       | an_argm _ _ arg args => an_arg (reify arg) (@unmeanings _ args)
       | noargsm _ => noargs
       end.

  Fixpoint apply_meaning_helper {P}
           (af : arg_meanings_for P)
    : forall (f : normalized_of P),
      normalized_of (range_of P)
    := match af in arg_meanings_for P return normalized_of P -> normalized_of (range_of P) with
       | an_argm _ _ arg args
         => fun f => @apply_meaning_helper _ args (f arg)
       | noargsm _ => fun v => v
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
                                         (constantOf (ahdm af))
                     | Rsnd _ _
                       => fun af default
                          => option_rect (fun _ => _)
                                         snd default
                                         (constantOf (ahdm af))
                     | Rnth' _
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some ls
                               => List.nth' n ls (ahdm (atlm (atlm af)))
                             | _, _ => default
                             end
                     | Rnth _
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some ls
                               => List.nth n ls (ahdm (atlm (atlm af)))
                             | _, _ => default
                             end
                     | Rbeq_nat
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some n' =>
                               syntactify_bool var (EqNat.beq_nat n n')
                             | _, _ => default
                             end
                     | Rmap A B
                       => fun af default
                          => option_rect
                               (fun _ => _)
                               (fun ls => syntactify_list (List.map (ahdm af) ls))
                               default
                               (constantOf (ahdm (atlm af)))
                     | Rfold_left A B
                       => fun af default
                          => option_rect
                               (fun _ => _)
                               (fun ls =>
                                  let init := ahdm (atlm (atlm af)) in
                                  let f := ahdm af in
                                  List.fold_left f ls init)
                               default
                               (constantOf (ahdm (atlm af)))
                     | Rorb
                       => fun af default
                          => match constantOf (ahdm af) with
                             | Some b
                               => if b then syntactify_bool var true else ahdm (atlm af)
                             | _ => default
                             end
                     | Randb
                       => fun af default
                          => match constantOf (ahdm af) with
                             | Some b
                               => if b then ahdm (atlm af) else syntactify_bool var false
                             | _ => default
                             end
                     | Rorbr
                       => fun af default
                          => match constantOf (ahdm (atlm af)) with
                             | Some b
                               => if b then syntactify_bool var true else ahdm af
                             | _ => default
                             end
                     | Randbr
                       => fun af default
                          => match constantOf (ahdm (atlm af)) with
                             | Some b
                               => if b then ahdm af else syntactify_bool var false
                             | _ => default
                             end
                     | Rminusr
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some n'
                               => syntactify_nat var (minusr n n')
                             | _, Some n'
                               => apply_n n' (fun n0 => RLiteralApp Rpred (n0 :: noargs)) (ahdm af)
                             | _, _ => default
                             end
                     | Rpred
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun n => syntactify_nat var (pred n))
                                         default
                                         (constantOf (ahdm af))
                     | Rlength _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun ls => syntactify_nat var (List.length ls))
                                         default
                                         (constantOf (ahdm af))
                     | Rbool_rect_nodep _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun b : bool
                                          => if b
                                             then ahdm af
                                             else ahdm (atlm af))
                                         default
                                         (constantOf (ahdm (atlm (atlm af))))
                     | Rlist_rect_nodep A P
                       => fun af default
                          => option_rect (fun _ => normalized_of (range_of P))
                                         (fun ls
                                          => apply_meaning_helper
                                               (atlm (atlm (atlm af)))
                                               (list_rect_nodep
                                                  (ahdm af)
                                                  (fun x xs => ahdm (atlm af) x (syntactify_list xs))
                                                  ls))
                                         default
                                         (constantOf (ahdm (atlm (atlm af))))
                     | Rlist_caset_nodep _ _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun ls
                                          => list_caset_nodep
                                               (ahdm af)
                                               (fun x xs => ahdm (atlm af) x (syntactify_list xs))
                                               ls)
                                         default
                                         (constantOf (ahdm (atlm (atlm af))))
                     | Rleb
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some n' =>
                               syntactify_bool var (Compare_dec.leb n n')
                             | _, _ => default
                             end
                     | Rcombine _ _
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
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
                                         (constantOf (ahdm af))
                     | Rup_to
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun n
                                          => syntactify_list (List.map (syntactify_nat var) (List.up_to n)))
                                         default
                                         (constantOf (ahdm af))
                     | Rplus
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some n'
                               => syntactify_nat var (plus n n')
                             | Some n, _
                               => apply_n n (fun n0 => RLiteralApp RS (n0 :: noargs)) (ahdm af)
                             | _, _ => default
                             end
                     | Rmax
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some n'
                               => syntactify_nat var (max n n')
                             | _, _ => default
                             end
                     | Rritem_rect_nodep _
                       => fun af default
                          => option_rect (fun _ => _)
                                         (fun v
                                          => Reflective.ritem_rect_nodep
                                               (fun x => ahdm af (syntactify_rchar_expr_ascii var x))
                                               (fun s => ahdm (atlm af) (syntactify_string var s))
                                               v)
                                         default
                                         (constantOf (ahdm (atlm (atlm af))))
                     | Rfirst_index_default _
                       => fun af default
                          => match constantOf (ahdm (atlm af)), constantOf (ahdm (atlm (atlm af))) with
                             | Some v, Some ls =>
                               let f := ahdm af in
                               match first_index_default_partial (fun a => constantOf (f a)) v ls with
                               | None => default
                               | Some n => syntactify_nat var n
                               end
                             | _, _ => default
                             end
                     | Rinterp_RCharExpr_ascii => fun af default => default
                     | Rstring_beq
                       => fun af default
                          => match constantOf (ahdm af), constantOf (ahdm (atlm af)) with
                             | Some n, Some n' =>
                               syntactify_bool var (Equality.string_beq n n')
                             | _, _ => default
                             end
                     (*| Rchar_at_matches => fun af default => default
                     | Rsplit_string_for_production => fun af default => default*)
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

  Fixpoint has_no_nones {var T}
           (args : args_for_onelevel var T)
    : bool
    := match args with
       | an_arg_ol _ _ (Some _) args => @has_no_nones _ _ args
       | an_arg_ol A B None _ => false
       | noargs_ol _ => true
       end.

  Fixpoint interp_constantOfs {T} (f : interp_TypeCode T)
           (args : args_for_onelevel interp_TypeCode T)
           (H : has_no_nones args = true)
    : interp_TypeCode (range_of T)
    := match args in args_for_onelevel _ T return interp_TypeCode T -> has_no_nones args -> interp_TypeCode (range_of T) with
       | an_arg_ol _ _ (Some arg) args => fun f H => @interp_constantOfs _ (f (interp_constantOf arg)) args H
       | an_arg_ol _ _ None args => fun _ H => match (Bool.diff_false_true H : False) with end
       | noargs_ol T => fun f _ => f
       end f H.
End lemmas.
