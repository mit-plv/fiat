(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarNotations.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Wf.
Require Import ADTSynthesis.Parsers.BooleanRecognizer.
Require Import ADTSynthesis.Common.Match.
Require Import ADTSynthesis.Common.Equality.
Require Export ADTSynthesis.Common.SetoidInstances.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Global Arguments string_dec : simpl never.
Global Arguments string_beq : simpl never.

Ltac extract_parser_opt :=
  eexists;
  let L := match goal with |- ?L = _ => constr:L end in
  let e := fresh "e" in
  set (e := L);
  let G := match goal with |- _ = parse_nonterminal (G := ?G) _ _ => constr:G end in
  let G' := head G in
  try unfold G';
    cbv beta iota zeta delta [parse_nonterminal parse_nonterminal_or_abort parse_nonterminal_step parse_productions parse_item Lookup list_to_grammar list_to_productions];
    simpl;
    (let H0 := fresh "H0" in
     (lazymatch goal with
     | [ |- context[fold_right ?f ?i (map _ (bool_rect _ ?x ?y (string_beq ?s _)))] ]
       => pose proof (fun g s' => @pull_bool_rect _ _ (fun ls => fold_right f i (map g ls)) x y (string_beq s s')) as H0;
      simpl in H0
      end);
     etransitivity;
     [ clear H0
     | clear e;
       match goal with
         | [ |- _ = @Fix3 ?A ?B ?C ?D ?R ?wf ?P ?f ?a ?b ?c ?d ]
           => refine ((fun H => @Fix3_Proper_eq A B C D R wf P _ f H a b c d) _)
       end;
       unfold forall_relation, pointwise_relation, respectful;
       let H := fresh in
       intros ??? H ???;
              let L := match goal with |- ?L = _ => constr:L end in
              let e := fresh "e" in
              set (e := L);
                setoid_rewrite H0; clear H0;
                unfold parse_production, parse_item;
                simpl;
                setoid_rewrite <- H; subst e;
                reflexivity
     ]);
    cbv beta iota zeta delta [sumbool_rect bool_rect];
    subst e;
    reflexivity.

Require Import Grammars.ABStar.

Section recursive_descent_parser.
  Context {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.
  Context {data : @boolean_parser_dataT Ascii.ascii _}.

  Definition parse_nonterminal_opt
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := ab_star_grammar) str nt }.
  Proof.
    extract_parser_opt.
  Defined.



Focus 2.
reflexivity.
let H := fresh in
intros
  Focus 2.

  setoid_rewrite <- H.
  clear H y.


  setoid_rewrite <- H.

  let H0'

  setoid_rewrite H0.

Ltac pre_higher_order_reflexivity_one_evar :=
  idtac;
  match goal with
    | [ |- ?l = ?r ]
      => has_evar l; not has_evar r
    | [ |- ?l = ?r ]
      => has_evar r; not has_evar l; symmetry
  end.

Ltac higher_order_reflexivity_one_evar' :=
  clear;
  (lazymatch goal with
  | [ |- ?f ?x = ?g ]
    => revert x
   end);
  (lazymatch goal with
  | [ |- forall x, ?f x = @?g x ]
    => (let y := fresh in
        intro y;
        refine (@f_equal _ _ (fun f' => f' y) f g _))
   end).

Ltac higher_order_reflexivity_one_evar :=
  pre_higher_order_reflexivity_one_evar;
  repeat higher_order_reflexivity_one_evar'.

{ higher_order_reflexivity_one_evar.
  move a at bottom.
  clear.
  clear.

  clear;
  (lazymatch goal with
  | [ |- ?f ?x = ?g ]
    => revert x
   end);
  (lazymatch goal with
  | [ |- forall x, ?f x = @?g x ]
    => (let y := fresh in
        intro y;
        refine (@f_equal _ _ (fun f' => f' y) f g _))
   end).


  (lazymatch goal with
  | [ |- ?f ?x = ?g ]
    => revert x
   end);
  (lazymatch goal with
  | [ |- forall x, ?f x = @?g x ]
    => (let y := fresh in
        intro y;
        refine (@f_equal _ _ (fun f' => f' y) f g _))
   end).
  idtac;
  (lazymatch goal with
  | [ |- ?f ?x = ?g ]
    => revert x
   end);
  (lazymatch goal with
  | [ |- forall x, ?f x = @?g x ]
    => intro x;
   refine (@f_equal _ _ (fun f' => f' x) f g _)
   end).
(lazymatch goal with
  | [ |- ?f ?x = ?g ]
    => let g' := fresh "g'" in
       set (g' := g);
   pattern x in g';
   subst g'
   end);
  (lazymatch goal with
  | [ |- ?f ?x = ?g ?x ]
    => refine (@f_equal _ _ (fun f' => f' x) f g _)
   end).

Lemma fg_equal_dep {A B} (f g : forall x : A, B x) (H : f = g)


Ltac higher_order_5_reflexivity :=
  let x := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(b) end in
  let c := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(c) end in
  let d := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(d) end in
  let e := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(e) end in
  let x' := (eval pattern a, b, c, d, e in x) in
  let f' := match x' with ?f' _ _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_5_f_reflexivity :=
  let x := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d ?e)) => constr:(x) end in
  let f := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d ?e)) => constr:(f) end in
  let a := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d ?e)) => constr:(a) end in
  let b := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d ?e)) => constr:(b) end in
  let c := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d ?e)) => constr:(c) end in
  let d := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d ?e)) => constr:(d) end in
  let e := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d ?e)) => constr:(e) end in
  let x' := (eval pattern a, b, c, d, e in x) in
  let f' := match x' with ?f' _ _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].
let x := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(b) end in
  let c := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(c) end in
  let d := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(d) end in
  let e := match goal with |- ?R ?x (?f ?a ?b ?c ?d ?e) => constr:(e) end in
  let x' := (eval pattern e, d, b in x) in
  idtac.
  let f' := match x' with ?f' _ _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].


  higher_order_5_reflexivity.
  higher_order_reflexivity.
  Print Ltac higher_order_reflexivity.
  higher_order_reflexivity.
  reflexivity.
      setoid_rewrite H0 ].
  Focus 2.

  reflexivity.
  Focus 2.
Require Import Ascii.
Delimit Scope char_scope with char.
  setoid_rewrite H.



  setoid_rewrite

specialize (H0 X).
  refine (Fix3_Proper_eq _ _ _ _ _ _ _).
  appyl
    Typeclasses eauto := debug.
    try timeout 1 setoid_rewrite H.
    match goal with
    eexists; simpl.
    reflexivity.
  Defined.
End recursive_descent_parser.

Require Import Grammars.ABStar.
Require Import StringLike.String.
Require Import Splitters.RDPList.
Section recursive_descent_parser'.
  Definition parse_nonterminal_opt' d : _ -> _ -> bool := fun str nt => proj1_sig (@parse_nonterminal_opt _ string_stringlike string_stringlike_properties ab_star_grammar d str nt).
  Locate string_dec.
  Local Arguments String.string_dec : simpl never.
  Goal True.
    pose parse_nonterminal_opt' as b.
    unfold parse_nonterminal_opt' in b.
    unfold parse_nonterminal_opt in b.
    Opaque parse_production.
    simpl in b.

  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}.

    match goal with
      | [ |-


    unfold parse_nonterminal,
    := @parse_nonterminal_or_abort
         (str : String, initial_nonterminals_data) str
         (or_intror (reflexivity _)) nt.



  Section bool.
    Section parts.
      Definition parse_item
                 (str_matches_nonterminal : String.string -> bool)
                 (str : String)
                 (it : item Char)
      : bool
        := match it with
             | Terminal ch => str ~= [ ch ]
             | NonTerminal nt => str_matches_nonterminal nt
           end.

      Section production.
        Context {str0}
                (parse_nonterminal
                 : forall (str : String),
                     str ≤s str0
                     -> String.string
                     -> bool).

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Fixpoint parse_production
                 (str : String)
                 (pf : str ≤s str0)
                 (prod : production Char)
        : bool.
        Proof.
          refine
            match prod with
              | nil =>
                (** 0-length production, only accept empty *)
                Nat.eq_dec (length str) 0
              | it::its
                => let parse_production' := fun str pf => parse_production str pf its in
                   fold_right
                     orb
                     false
                     (map (fun n =>
                             (parse_item
                                (parse_nonterminal (str := take n str) _)
                                (take n str)
                                it)
                               && parse_production' (drop n str) _)%bool
                          (split_string_for_production it its str))
            end;
          revert pf; clear -HSLP; intros;
          abstract (rewrite ?str_le_take, ?str_le_drop; assumption).
        Defined.
      End production.

      Section productions.
        Context {str0}
                (parse_nonterminal
                 : forall (str : String)
                          (pf : str ≤s str0),
                     String.string -> bool).

        (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
        Definition parse_productions
                   (str : String)
                   (pf : str ≤s str0)
                   (prods : productions Char)
        : bool
          := fold_right orb
                        false
                        (map (parse_production parse_nonterminal pf)
                             prods).
      End productions.


      Section nonterminals.
        Section step.
          Context {str0 valid}
                  (parse_nonterminal
                   : forall (p : String * nonterminals_listT),
                       prod_relation (ltof _ length) nonterminals_listT_R p (str0, valid)
                       -> forall str : String,
                            str ≤s fst p -> String.string -> bool).

          Definition parse_nonterminal_step
                     (str : String)
                     (pf : str ≤s str0)
                     (nt : String.string)
          : bool.
          Proof.
            refine
              (if lt_dec (length str) (length str0)
               then (** [str] got smaller, so we reset the valid nonterminals list *)
                 parse_productions
                   (@parse_nonterminal
                      (str : String, initial_nonterminals_data)
                      (or_introl _))
                   (or_intror (reflexivity _))
                   (Lookup G nt)
               else (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
                 if Sumbool.sumbool_of_bool (is_valid_nonterminal valid nt)
                 then (** It was valid, so we can remove it *)
                   parse_productions
                     (@parse_nonterminal
                        (str0 : String, remove_nonterminal valid nt)
                        (or_intror (conj eq_refl (remove_nonterminal_dec _ nt _))))
                     (str := str)
                     _
                     (Lookup G nt)
                 else (** oops, we already saw this nonterminal in the past.  ABORT! *)
                   false);
            assumption.
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_or_abort
          : forall (p : String * nonterminals_listT)
                   (str : String),
              str ≤s fst p
              -> String.string
              -> bool
            := Fix3
                 _ _ _
                 (well_founded_prod_relation
                    (well_founded_ltof _ length)
                    ntl_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

          Definition parse_nonterminal
                     (str : String)
                     (nt : String.string)
          : bool
            := @parse_nonterminal_or_abort
                 (str : String, initial_nonterminals_data) str
                 (or_intror (reflexivity _)) nt.
        End wf.
      End nonterminals.
    End parts.
  End bool.
End recursive_descent_parser.
