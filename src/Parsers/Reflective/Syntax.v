Require Import Coq.Classes.Morphisms. (* for reserved [-->] notation *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Common.Notations.

Set Implicit Arguments.
Delimit Scope typecode_scope with typecode.
Delimit Scope term_scope with term.
Delimit Scope termargs_scope with termargs.
Local Set Boolean Equality Schemes.
Local Set Decidable Equality Schemes.
Inductive SimpleTypeCode : Set :=
| cnat
| cbool
| cstring
| cascii
| critem_ascii
| crchar_expr_ascii
| clist (T : SimpleTypeCode)
| cprod (A B : SimpleTypeCode).
Inductive TypeCode : Set :=
| csimple (T : SimpleTypeCode)
| carrow (A B : TypeCode).
Module Export TypeCodeCoercions.
  Global Coercion csimple : SimpleTypeCode >-> TypeCode.
End TypeCodeCoercions.
Local Unset Boolean Equality Schemes.
Local Unset Decidable Equality Schemes.

Bind Scope typecode_scope with TypeCode.
Bind Scope typecode_scope with SimpleTypeCode.
Arguments clist _%typecode.
Arguments carrow (_ _)%typecode.
Arguments cprod (_ _)%typecode.

Infix "-->" := carrow : typecode_scope.
Infix "*" := cprod : typecode_scope.

Definition f_equal2_transparent {A1 A2 B} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2} (H : x1 = y1) : x2 = y2 -> f x1 x2 = f y1 y2
  := match H in (_ = y) return (x2 = y2 -> f x1 x2 = f y y2) with
     | eq_refl => fun H0 : x2 = y2 => match H0 in (_ = y) return (f x1 x2 = f x1 y) with
                                      | eq_refl => eq_refl
                                      end
     end.

Fixpoint SimpleTypeCode_eq_semidec_transparent (T1 T2 : SimpleTypeCode) : option (T1 = T2)
  := match T1, T2 return option (T1 = T2) with
     | cnat, cnat => Some eq_refl
     | cbool, cbool => Some eq_refl
     | cstring, cstring => Some eq_refl
     | cascii, cascii => Some eq_refl
     | critem_ascii, critem_ascii => Some eq_refl
     | crchar_expr_ascii, crchar_expr_ascii => Some eq_refl
     | clist T, clist T'
       => match SimpleTypeCode_eq_semidec_transparent T T' with
          | Some p => Some (f_equal clist p)
          | None => None
          end
     | cprod A B, cprod A' B'
       => match SimpleTypeCode_eq_semidec_transparent A A', SimpleTypeCode_eq_semidec_transparent B B' with
          | Some p, Some q => Some (f_equal2_transparent cprod p q)
          | _, _ => None
          end
     | _, _ => None
     end.
Fixpoint TypeCode_eq_semidec_transparent (T1 T2 : TypeCode) : option (T1 = T2)
  := match T1, T2 return option (T1 = T2) with
     | csimple T, csimple T' => option_map (f_equal csimple) (SimpleTypeCode_eq_semidec_transparent T T')
     | csimple _, _ => None
     | carrow A B, carrow A' B'
       => match TypeCode_eq_semidec_transparent A A', TypeCode_eq_semidec_transparent B B' with
          | Some p, Some q => Some (f_equal2_transparent carrow p q)
          | _, _ => None
          end
     | carrow _ _, _ => None
     end.

Local Ltac t_is_dec :=
  repeat match goal with
         | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
         | _ => progress subst
         | _ => progress simpl in *
         | _ => congruence
         | [ H : forall x, _ = None -> _, H' : _ = None |- _ ]
           => specialize (H _ H')
         | _ => progress unfold option_map
         | [ H : csimple _ = csimple _ |- _ ] => inversion H; clear H
         | _ => intro
         | _ => solve [ intuition eauto ]
         end.

Lemma SimpleTypeCode_eq_semidec_is_dec : forall {T1 T2}, SimpleTypeCode_eq_semidec_transparent T1 T2 = None -> T1 <> T2.
Proof. induction T1, T2; t_is_dec. Qed.

Lemma TypeCode_eq_semidec_is_dec : forall {T1 T2}, TypeCode_eq_semidec_transparent T1 T2 = None -> T1 <> T2.
Proof. pose proof (@SimpleTypeCode_eq_semidec_is_dec); induction T1, T2; t_is_dec. Qed.

Fixpoint range_of (T : TypeCode) : SimpleTypeCode
  := match T with
     | carrow A B => range_of B
     | csimple T => T
     end.

Section args.
  Section monadic.
    Context (M : TypeCode -> Type).

    Inductive args_for : TypeCode -> Type :=
    | an_arg {A B} (arg : M A) (args : args_for B) : args_for (A --> B)
    | noargs {T} : args_for (csimple T).

    Definition ahd {A B} (af : args_for (A --> B)) : M A :=
      match af in args_for T return match T with
                                    | carrow A B => M A
                                    | _ => unit
                                    end with
      | an_arg _ _ arg _ => arg
      | _ => tt
      end.

    Definition atl {A B} (af : args_for (A --> B)) : args_for B :=
      match af in args_for T return match T with
                                    | carrow A B => args_for B
                                    | _ => unit
                                    end with
      | an_arg _ _ _ af' => af'
      | _ => tt
      end.

    Fixpoint aIn {A T} (v : M A) (args : args_for T) : Type
      := match args with
         | an_arg A' B' arg args
           => ({ pf : A' = A
               | eq_rect A' M arg A pf = v}
               + @aIn _ _ v args)%type
         | noargs T => False
         end.

    Definition invert_args_for {T} (args : args_for T)
      : args = match T return args_for T -> args_for T with
               | csimple T' => fun _ => noargs
               | carrow A B => fun args' => an_arg (ahd args') (atl args')
               end args.
    Proof.
      destruct args; reflexivity.
    Defined.

    Definition invert_args_for_ex {T} (args : args_for T)
      : match T return args_for T -> Prop with
        | csimple T' => fun args => args = noargs
        | carrow A B => fun args => exists hd tl, args = an_arg hd tl
        end args.
    Proof.
      destruct args; repeat esplit.
    Defined.
  End monadic.

  Global Arguments an_arg {M _ _} _ _.
  Global Arguments noargs {M _}.
  Global Arguments ahd {M _ _} _.
  Global Arguments atl {M _ _} _.
  Global Arguments aIn {M _ _} _ _.

  Section aIn2.
    Fixpoint aIn2
             {M N : TypeCode -> Type}
             {A T} (v1 : M A) (v2 : N A) (args1 : args_for M T)
    : args_for N T -> Type
      := match args1 in args_for _ T return args_for _ T -> Type with
         | an_arg A' B' arg args
           => fun args2
              => ({ pf : A' = A
                  | eq_rect A' M arg A pf = v1
                    /\ eq_rect A' N (ahd args2) A pf = v2 }
                  + @aIn2 _ _ _ _ v1 v2 args (atl args2))%type
         | noargs T => fun _ => False
         end.
  End aIn2.

  Section map.
    Context {M N : TypeCode -> Type}
            (F : forall {A}, M A -> N A).

    Fixpoint map_args_for {T} (args : args_for M T) : args_for N T
      := match args in args_for _ T return args_for _ T with
         | an_arg A B arg args => an_arg (F arg) (map_args_for args)
         | noargs T => noargs
         end.
  End map.

  Section related.
    Context {M N : TypeCode -> Type}
            (R : forall {T}, M T -> N T -> Prop).

    Inductive args_for_related_ind : forall {T} (args0 : args_for M T), args_for N T -> Prop :=
    | rel_an_arg {A B arg0 arg1 args0 args1}
      : R arg0 arg1 -> args_for_related_ind args0 args1
        -> @args_for_related_ind (carrow A B) (an_arg arg0 args0) (an_arg arg1 args1)
    | rel_noargs {T}
      : @args_for_related_ind (csimple T) noargs noargs.

    Fixpoint args_for_related {T} (args0 : args_for M T) : args_for N T -> Prop
      := match args0 in args_for _ T return args_for _ T -> Prop with
         | an_arg A B arg args
           => fun args1
              => R arg (ahd args1)
                 /\ @args_for_related _ args (atl args1)
         | noargs T => fun args1 => noargs = args1
         end.

    Lemma args_for_related_noind_ind {T args0 args1}
      : @args_for_related T args0 args1 <-> @args_for_related_ind T args0 args1.
    Proof.
      split; intro H.
      { revert dependent args1; induction args0; intros; simpl in *;
        pose proof (invert_args_for_ex args1) as H'; simpl in *;
        subst; [ | solve [ repeat (intro || constructor) ] ].
        destruct H' as [? [? H']]; subst; simpl in *.
        inversion H; constructor; eauto. }
      { induction H; simpl; intuition. }
    Qed.
  End related.

  Lemma args_for_related_impl {M N P R T} args0 args1
    : (P -> @args_for_related M N R T args0 args1)
      <-> @args_for_related M N (fun _ m n => P -> R _ m n) T args0 args1.
  Proof.
    revert dependent args1; induction args0; simpl in *; intros;
      pose proof (invert_args_for_ex args1) as H'; simpl in H';
        subst; [ destruct H' as [? [? ?]]; subst | tauto ];
          simpl in *.
    setoid_rewrite <- IHargs0.
    tauto.
  Qed.
End args.

Section term.
  Context (var : TypeCode -> Type).

  Inductive RLiteralConstructor : TypeCode -> Set :=
  | Rpair {A B : SimpleTypeCode} : RLiteralConstructor (A --> B --> A * B)
  | RS : RLiteralConstructor (cnat --> cnat)
  | RO : RLiteralConstructor cnat
  | Rnil {A} : RLiteralConstructor (clist A)
  | Rcons {A : SimpleTypeCode} : RLiteralConstructor (A --> clist A --> clist A)
  | Rbool (b : bool) : RLiteralConstructor cbool
  | Rrchar_expr_ascii (_ : Reflective.RCharExpr ascii) : RLiteralConstructor crchar_expr_ascii
  | Rstring (_ : string) : RLiteralConstructor cstring
  | Rritem_ascii (_ : Reflective.ritem ascii) : RLiteralConstructor critem_ascii.
  Inductive RLiteralNonConstructor : TypeCode -> Set :=
  | Rfst {A B} : RLiteralNonConstructor (A * B --> A)
  | Rsnd {A B} : RLiteralNonConstructor (A * B --> B)
  | Rnth' {A} : RLiteralNonConstructor (cnat --> clist A --> A --> csimple A)
  | Rnth {A} : RLiteralNonConstructor (cnat --> clist A --> A --> csimple A)
  | Rbeq_nat : RLiteralNonConstructor (cnat --> cnat --> cbool)
  | Rmap {A B : SimpleTypeCode} : RLiteralNonConstructor ((A --> B) --> clist A --> clist B)
  | Rfold_left {A B : SimpleTypeCode} : RLiteralNonConstructor ((A --> B --> A) --> clist B --> A --> csimple A)
  | Rorb : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Randb : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Randbr : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Rorbr : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Rminusr : RLiteralNonConstructor (cnat --> cnat --> cnat)
  | Rpred : RLiteralNonConstructor (cnat --> cnat)
  | Rlength A : RLiteralNonConstructor (clist A --> cnat)
  | Rbool_rect_nodep {A : SimpleTypeCode} : RLiteralNonConstructor (A --> A --> cbool --> csimple A)
  | Rlist_rect_nodep {A : SimpleTypeCode} {P : TypeCode} : RLiteralNonConstructor (P --> (A --> clist A --> P --> P) --> clist A --> P)
  | Rlist_caset_nodep {A P : SimpleTypeCode} : RLiteralNonConstructor (P --> (A --> clist A --> P) --> clist A --> P)
  | Rleb : RLiteralNonConstructor (cnat --> cnat --> cbool)
  | Rcombine {A B} : RLiteralNonConstructor (clist A --> clist B --> clist (A * B))
  | Rrev {A} : RLiteralNonConstructor (clist A --> clist A)
  | Rup_to : RLiteralNonConstructor (cnat --> clist cnat)
  | Rplus : RLiteralNonConstructor (cnat --> cnat --> cnat)
  | Rmax : RLiteralNonConstructor (cnat --> cnat --> cnat)
  | Rritem_rect_nodep {A : SimpleTypeCode} : RLiteralNonConstructor ((crchar_expr_ascii --> A) --> (cstring --> A) --> critem_ascii --> csimple A)
  | Rfirst_index_default {A : SimpleTypeCode} : RLiteralNonConstructor ((A --> cbool) --> cnat --> clist A --> cnat)
  | Rinterp_RCharExpr_ascii : RLiteralNonConstructor (crchar_expr_ascii --> cascii --> cbool)
  | Rstring_beq : RLiteralNonConstructor (cstring --> cstring --> cbool).
  (*| Rchar_at_matches
    : RLiteralNonConstructor (cnat --> (cascii --> cbool) --> cbool)
  | Rsplit_string_for_production
    : RLiteralNonConstructor (cnat * (cnat * cnat) --> cnat --> cnat --> (clist cnat)).*)

  Inductive RLiteralTerm (T : TypeCode) : Set :=
  | RLC (_ : RLiteralConstructor T)
  | RLNC (_ : RLiteralNonConstructor T).

  Local Unset Elimination Schemes.
  Inductive Term : TypeCode -> Type :=
  | RVar {T} (v : var T) : Term T
  | RLambda {A B} (f : var A -> Term B)
    : Term (A --> B)
  | RApp {A B} (f : Term (A --> B)) (x : Term A)
    : Term B
  | RLiteralApp c (t : RLiteralTerm c) (args : args_for Term c)
    : Term (range_of c).

  Bind Scope term_scope with Term.
  Bind Scope termargs_scope with args_for.

  Section rect.
    Context (P : forall t, Term t -> Type)
            (RVarCase : forall T v, P T (RVar v))
            (RLambdaCase : forall A B f,
                (forall v, P B (f v))
                -> P (A --> B)%typecode (RLambda f))
            (RAppCase : forall A B f,
                P (A --> B)%typecode f
                -> forall x, P A x -> P B (RApp f x))
            (RLiteralAppCase
             : forall c (t : RLiteralTerm c) (args : args_for Term c),
                (forall T v, aIn v args -> P T v)
                -> P (range_of c) (RLiteralApp t args)).

    Fixpoint Term_rect
             T (t : Term T)
      : P t.
    Proof.
      refine match t return P t with
             | RVar T v => RVarCase _
             | RLambda A B f => RLambdaCase _ (fun v => @Term_rect _ _)
             | RApp A B f x => RAppCase (@Term_rect _ _) (@Term_rect _ _)
             | RLiteralApp c t' args => RLiteralAppCase _ _ _
             end.
      clear t'.
      induction args as [A B arg args IHargs|].
      { pose proof (@Term_rect _ arg) as rarg; clear Term_rect.
        intros ?? [[pf H]|H].
        { destruct pf, H; simpl.
          exact rarg. }
        { apply IHargs; assumption. } }
      { simpl.
        intros ?? []. }
    Defined.
  End rect.

  Section rec.
    Context (P : forall t, Term t -> Set)
            (RVarCase : forall T v, P T (RVar v))
            (RLambdaCase : forall A B f,
                (forall v, P B (f v))
                -> P (A --> B)%typecode (RLambda f))
            (RAppCase : forall A B f,
                P (A --> B)%typecode f
                -> forall x, P A x -> P B (RApp f x))
            (RLiteralAppCase
             : forall c (t : RLiteralTerm c) (args : args_for Term c),
                (forall T v, aIn v args -> P T v)
                -> P (range_of c) (RLiteralApp t args)).

    Fixpoint Term_rec
             T (t : Term T)
      : P t.
    Proof.
      refine match t return P t with
             | RVar T v => RVarCase _
             | RLambda A B f => RLambdaCase _ (fun v => @Term_rec _ _)
             | RApp A B f x => RAppCase (@Term_rec _ _) (@Term_rec _ _)
             | RLiteralApp c t' args => RLiteralAppCase _ _ _
             end.
      clear t'.
      induction args as [A B arg args IHargs|].
      { pose proof (@Term_rec _ arg) as rarg; clear Term_rec.
        intros ?? [[pf H]|H].
        { destruct pf, H; simpl.
          exact rarg. }
        { apply IHargs; assumption. } }
      { simpl.
        intros ?? []. }
    Defined.
  End rec.

  Section ind.
    Context (P : forall t, Term t -> Prop)
            (RVarCase : forall T v, P T (RVar v))
            (RLambdaCase : forall A B f,
                (forall v, P B (f v))
                -> P (A --> B)%typecode (RLambda f))
            (RAppCase : forall A B f,
                P (A --> B)%typecode f
                -> forall x, P A x -> P B (RApp f x))
            (RLiteralAppCase
             : forall c (t : RLiteralTerm c) (args : args_for Term c),
                (forall T v, aIn v args -> P T v)
                -> P (range_of c) (RLiteralApp t args)).

    Fixpoint Term_ind
             T (t : Term T)
      : P t.
    Proof.
      refine match t return P t with
             | RVar T v => RVarCase _
             | RLambda A B f => RLambdaCase _ (fun v => @Term_ind _ _)
             | RApp A B f x => RAppCase (@Term_ind _ _) (@Term_ind _ _)
             | RLiteralApp c t' args => RLiteralAppCase _ _ _
             end.
      clear t'.
      induction args as [A B arg args IHargs|].
      { pose proof (@Term_ind _ arg) as rarg; clear Term_ind.
        intros ?? [[pf H]|H].
        { destruct pf, H; simpl.
          exact rarg. }
        { apply IHargs; assumption. } }
      { simpl.
        intros ?? []. }
    Defined.
  End ind.
End term.

Bind Scope term_scope with Term.
Bind Scope termargs_scope with args_for.
Arguments RVar {var T%typecode} v.
Arguments RLambda {var} {A B}%typecode f%term.
Arguments RApp {var} {A B}%typecode (f x)%term.
Arguments RLiteralApp {var} {c}%typecode t%term args%termargs.

Notation "# v" := (RVar v) : term_scope.
Infix "@" := RApp : term_scope.

Notation "\ x , e" := (RLambda (fun x => e)) : term_scope.
Notation "\ ! , e" := (RLambda (fun _ => e)) : term_scope.
Notation "x :: y" := (@an_arg (Term _) _ _ x%term y%termargs) : termargs_scope.

Definition polyTerm T := forall var, Term var T.

Local Notation rcStepT cbool :=
  ((*Rchar_at_matches*)
    (cnat --> (cascii --> cbool) --> cbool)
      --> (*Rsplit_string_for_production*)
      (cnat * (cnat * cnat) --> cnat --> cnat --> (clist cnat))
      --> cnat --> cnat --> (cnat --> cnat --> cnat --> cbool) --> clist cnat --> cnat --> cnat --> cnat --> cbool)%typecode
                                                                                                                   (only parsing).

Inductive has_parse_term var : Type :=
| RFix2
    (G_length : nat) (up_to_G_length : list nat)
    (f : Term var (rcStepT cbool))
    (valid_len : nat)
    (valids : list nat)
    (nt_idx : nat).

Definition polyhas_parse_term := forall var, has_parse_term var.

Module Export Coercions.
  Export TypeCodeCoercions.
  Coercion RLC : RLiteralConstructor >-> RLiteralTerm.
  Coercion RLNC : RLiteralNonConstructor >-> RLiteralTerm.
End Coercions.
