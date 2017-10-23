Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common Fiat.Common.Wf Fiat.Common.Wf2 Fiat.Common.Equality.
Import NPeano.

Ltac t_reduce_fix :=
  repeat match goal with
         | _ => progress simpl sumbool_rect
         | _ => progress simpl option_rect
         | [ |- context[lt_dec ?x ?y] ]
           => destruct (lt_dec x y)
         | [ |- context[dec ?x] ]
           => destruct (dec x)
         | [ |- @fold_right ?A ?B ?f ?x ?ls = @fold_right ?A ?B ?f ?x ?ls' ]
           => apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@fold_right A B))
         | [ |- @fold_left ?A ?B ?f ?ls ?x = @fold_left ?A ?B ?f ?ls' ?x ]
           => apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@fold_left A B))
         | [ |- @list_caset ?A (fun _ => ?P) _ _ ?ls = @list_caset ?A (fun _ => ?P) _ _ ?ls' ]
           => apply (_ : Proper (_ ==> pointwise_relation _ (pointwise_relation _ _) ==> _ ==> eq) (@list_caset A (fun _ => P)))
         | [ |- @map ?A ?B ?f ?ls = @map ?A ?B ?f' ?ls' ]
           => apply (_ : Proper (pointwise_relation _ _ ==> _ ==> eq) (@map A B))
         | [ |- @nth' ?A ?n ?ls ?d = @nth' ?A ?n' ?ls' ?d' ]
           => apply f_equal3
         | [ |- @nth ?A ?n ?ls ?d = @nth ?A ?n' ?ls' ?d' ]
           => apply f_equal3
         | _ => intro
         | [ |- ?x = ?x ] => reflexivity
         | [ |- bool_rect ?P _ _ ?b = bool_rect ?P _ _ ?b ] => apply f_equal3
         | [ |- andb _ _ = andb _ _ ] => apply f_equal2
         | [ |- andbr _ _ = andbr _ _ ] => apply f_equal2
         | [ |- orb _ _ = orb _ _ ] => apply f_equal2
         | [ |- ret_nt _ _ = ret_nt _ _ ] => apply f_equal
         | [ |- ret_NonTerminal_true _ _ = ret_NonTerminal_true _ _ ] => apply f_equal
         | [ |- ret_production_cons _ _ = ret_production_cons _ _ ] => apply f_equal2
         | [ |- match ?it with Terminal _ => _ | _ => _ end = match ?it with _ => _ end ] => is_var it; destruct it
         | [ |- context[(fst ?x, snd ?x)] ] => rewrite <- !surjective_pairing
         | [ |- context[andb _ true] ] => rewrite Bool.andb_true_r
         | [ |- context[andb true _] ] => rewrite Bool.andb_true_l
         | [ |- context[andb _ false] ] => rewrite Bool.andb_false_r
         | [ |- context[andb false _] ] => rewrite Bool.andb_false_l
         | [ |- context[andb ?x true] ] => rewrite (andbr_andb x true)
         | [ |- context[andb true _] ] => rewrite (andbr_andb true)
         | [ |- context[andb ?x false] ] => rewrite (andbr_andb x false)
         | [ |- context[andbr false _] ] => rewrite (andbr_andb false)
         | [ |- context[orb _ true] ] => rewrite Bool.orb_true_r
         | [ |- context[orb true _] ] => rewrite Bool.orb_true_l
         | [ |- context[orb _ false] ] => rewrite Bool.orb_false_r
         | [ |- context[orb false _] ] => rewrite Bool.orb_false_l
         | [ |- cons _ _ = cons _ _ ]
           => apply f_equal2
         | _ => solve [ auto with nocore ]
         | [ |- prod_relation lt lt _ _ ] => hnf; simpl; omega
         | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
         | [ H : _ = in_left |- _ ] => clear H
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : context[negb (EqNat.beq_nat ?x ?y)] |- _ ] => destruct (EqNat.beq_nat x y) eqn:?
         | [ H : EqNat.beq_nat _ _ = false |- _ ] => apply EqNat.beq_nat_false in H
         | [ H : EqNat.beq_nat _ _ = true |- _ ] => apply EqNat.beq_nat_true in H
         | [ H : snd ?x = _ |- _ ] => is_var x; destruct x
         | _ => progress simpl negb in *
         | [ H : false = true |- _ ] => inversion H
         | [ |- ?f _ (match ?p with eq_refl => ?k end) = ?f' _ ?k ]
           => destruct p
         | [ |- match ?ls with nil => _ | _ => _ end = match ?ls with _ => _ end ]
           => destruct ls eqn:?
         | [ |- match ?ls with NonTerminal _ => _ | _ => _ end = match ?ls with _ => _ end ]
           => destruct ls eqn:?
         | [ |- match ?ls with RNonTerminal _ => _ | _ => _ end = match ?ls with _ => _ end ]
           => destruct ls eqn:?
         | [ |- (if ?e then _ else _) = (if ?e then _ else _) ]
           => destruct e eqn:?
         | _ => solve [ intuition ]
         | [ H : context[sub_nonterminals_listT] |- _ ]
           => solve [ apply H;
                      intuition;
                      (etransitivity; [ | eapply sub_nonterminals_listT_remove_2; eassumption ]); simpl;
                      unfold remove_nonterminal; simpl;
                      unfold rdp_list_remove_nonterminal;
                      reflexivity ]
         end.

Ltac t_reduce_list :=
  idtac;
  lazymatch goal with
  | [ |- list_rect ?P ?n ?c ?ls ?idx ?offset ?len = list_rect ?P' ?n' ?c' ?ls ?idx ?offset ?len ]
    => let n0 := fresh in
       let c0 := fresh in
       let n1 := fresh in
       let c1 := fresh in
       set (n0 := n);
       set (n1 := n');
       set (c0 := c);
       set (c1 := c');
       refine (list_rect
                 (fun ls' => forall idx' offset' len', list_rect P n0 c0 ls' idx' offset' len' = list_rect P' n1 c1 ls' idx' offset' len')
                 _
                 _
                 ls
                 idx
                 offset len);
       simpl list_rect;
       [ subst n0 c0 n1 c1; cbv beta
       | intros; unfold c0 at 1, c1 at 1 ]
  end.

Ltac refine_Fix2_5_Proper_eq :=
  idtac;
  (lazymatch goal with
   | [ |- context[_ = @Fix2 ?A ?A' ?R ?Rwf ?T (fun a0 b0 c0 d0 e0 h0 i0 => @?f a0 b0 c0 d0 e0 h0 i0) ?a ?a' ?b ?c ?d ?e ?h] ]
     => (lazymatch T with
         | (fun a' : ?A0 => forall (b' :@?B a') (c' : @?C a' b') (d' : @?D a' b' c') (e' : @?E a' b' c' d') (h' : @?H a' b' c' d' e'), @?P a' b' c' d' e' h')
           => let H' := fresh in
              (*refine (_ : @Fix A R Rwf T (fun a0 b0 c0 d0 e0 h0 i0 => _) a b c d e h = _);
                 let f' := match goal with |- @Fix _ _ _ _ ?f' _ _ _ _ _ _ = _ => constr:(f') end in*)
              pose proof ((fun f' H0 => @Fix2_5_Proper_eq A A' B C D E H R Rwf P f' f H0 a a' b c d e h)) as H';
              cbv beta in H';
              (lazymatch type of H' with
               | forall f' : ?f'T, @?H'T f' -> _
                 => let H'' := fresh in
                    let f'' := fresh in
                    assert (H'' : { f' : f'T & H'T f' });
                    [ clear H'
                    | destruct H'' as [f'' H''];
                      specialize (H' f'' H'');
                      clear H''; eexists; exact H' ]
               end)
         end)
   end);
  unfold forall_relation, pointwise_relation, respectful;
  cbv beta;
  eexists (fun a0 a0' b0 c0 d0 e0 h0 i0 => _); intros.

Ltac refine_Fix2_5_Proper_eq_with_assumptions' HP HPpf :=
  idtac;
  (lazymatch goal with
   | [ |- context[_ = @Fix2 ?A ?A' ?R ?Rwf ?T (fun a0 b0 c0 d0 e0 h0 i0 => @?f a0 b0 c0 d0 e0 h0 i0) ?a ?a' ?b ?c ?d ?e ?h] ]
     => (lazymatch T with
         | (fun a' : ?A0 => forall (b' :@?B a') (c' : @?C a' b') (d' : @?D a' b' c') (e' : @?E a' b' c' d') (h' : @?H a' b' c' d' e'), @?P a' b' c' d' e' h')
           => let H' := fresh in
              pose proof ((fun f' H0 => @Fix2_5_Proper_eq_with_assumption A A' B C D E H R Rwf P HP f' f H0 a a' b c d e h HPpf)) as H';
              cbv beta in H';
              (lazymatch type of H' with
               | forall f' : ?f'T, @?H'T f' -> _
                 => let H'' := fresh in
                    let f'' := fresh in
                    assert (H'' : { f' : f'T & H'T f' });
                    [ clear H'
                    | destruct H'' as [f'' H''];
                      specialize (H' f'' H'');
                      clear H''; eexists; exact H' ]
               end)
         end)
   end);
  unfold forall_relation, pointwise_relation, respectful;
  cbv beta;
  eexists (fun a0 a0' b0 c0 d0 e0 h0 i0 => _); intros.

Ltac refine_Fix2_5_Proper_eq_with_assumptions :=
  idtac;
  let HPHPpf := lazymatch goal with
                | [ |- context[Fix2 _ _ (fun (a0 : ?A0) (b0 :@?B a0) (c0 : @?C a0 b0) (d0 : @?D a0 b0) (e0 : @?E a0 b0 d0) (h0 : @?H a0 b0 d0 e0) (i0 : @?I a0 b0 d0 e0 h0) (j0 : @?J a0 b0 d0 e0 h0 i0) => _) ?a ?b ?d ?e ?h ?i ?j] ]
                  => let HP := constr:(fun a0 b0 d0 e0 h0 i0 (j0 : J a0 b0 d0 e0 h0 i0) => sub_nonterminals_listT d0 initial_nonterminals_data /\ (a0 <= h0 \/ is_valid_nonterminal initial_nonterminals_data j0)) in
                     let HPpfT := (eval cbv beta in (HP a b d e h i j)) in
                     let HPpf := constr:(fun pf => conj pf (or_introl (reflexivity _)) : HPpfT) in
                     (eval cbv beta in (HP, HPpf))
                end in
  let HP := match HPHPpf with (?HP, ?HPpf) => HP end in
  let HPpf := match HPHPpf with (?HP, ?HPpf) => HPpf end in
  let T := match type of HPpf with ?T -> _ => T end in
  let H0 := fresh "H" in
  assert (H0 : T)
    by (simpl; unfold rdp_list_initial_nonterminals_data, pregrammar'_of_pregrammar, pregrammar_productions; rewrite !map_length; reflexivity);
  let HPpf := constr:(HPpf H0) in
  refine_Fix2_5_Proper_eq_with_assumptions' HP HPpf.

Ltac fin_step_opt :=
  repeat match goal with
         | [ |- _ = true ] => reflexivity
         | [ |- _ = false ] => reflexivity
         | [ |- _ = ret_nt_invalid ] => reflexivity
         | [ |- _ = ret_production_nil_true ] => reflexivity
         | [ |- _ = ret_orb_productions_base ] => reflexivity
         | [ |- ?x = ?x ] => reflexivity
         | [ |- _ = ?x ] => is_var x; reflexivity
         | [ |- _ = (_::_) ] => apply (f_equal2 (@cons _))
         | [ |- _ = nil ] => reflexivity
         | [ |- _ = 0 ] => reflexivity
         | [ |- _ = 1 ] => reflexivity
         | [ |- _ = None ] => reflexivity
         | [ |- _ = EqNat.beq_nat _ _ ] => apply f_equal2
         | [ |- _ = Compare_dec.leb _ _ ] => apply f_equal2
         | [ |- _ = S _ ] => apply f_equal
         | [ |- _ = string_beq _ _ ] => apply f_equal2
         | [ |- _ = fst ?x ] => is_var x; reflexivity
         | [ |- _ = snd ?x ] => is_var x; reflexivity
         | [ |- _ = pregrammar_productions ?x ] => is_var x; reflexivity
         | [ |- _ = pregrammar_rproductions ?x ] => is_var x; reflexivity
         | [ |- context[(0 - _)%natr] ] => rewrite (minusr_minus 0); change (minus 0) with (fun x : nat => 0); cbv beta
         | [ |- context[minus 0] ] => change (minus 0) with (fun x : nat => 0); cbv beta
         | [ |- _ = (_, _) ] => apply f_equal2
         | _ => progress cbv beta
         | [ |- context[orb _ false] ] => rewrite Bool.orb_false_r
         | [ |- context[orb _ true] ] => rewrite Bool.orb_true_r
         | [ |- context[andbr _ false] ] => rewrite (andbr_andb _ false)
         | [ |- context[andbr _ true] ] => rewrite (andbr_andb _ true)
         | [ |- context[andb _ false] ] => rewrite Bool.andb_false_r
         | [ |- context[andb _ true] ] => rewrite Bool.andb_true_r
         | [ |- _ = match ?b with true => ret_production_nil_true | false => ret_production_nil_false end ]
           => refine (f_equal (fun b' : bool => if b' then ret_production_nil_true else ret_production_nil_false) _)
         | _ => rewrite <- !minusr_minus
         end.

Ltac misc_opt' :=
  idtac;
  match goal with
  | _ => progress rewrite ?max_min_n, ?Minus.minus_diag, ?Nat.sub_0_r, ?uneta_bool, ?beq_nat_min_0(*, ?bool_rect_flatten*)
  | _ => rewrite Min.min_l by assumption
  | _ => rewrite Min.min_r by assumption
  | [ |- context[if ?ltb ?x ?y then _ else _] ] => rewrite if_to_min
  | [ |- context[min ?x ?y - ?x] ] => rewrite min_sub_same
  | [ |- context[(min ?x ?y - ?x)%natr] ] => rewrite min_subr_same
  | [ |- context[?x - (?x - ?y)%natr] ]
    => rewrite !(minusr_minus x y), sub_twice, <- ?minusr_minus
  | [ |- context[(?x - (?x - ?y)%natr)%natr] ]
    => rewrite !minusr_minus, sub_twice, <- ?minusr_minus
  | _ => progress fin_step_opt
  end.

Ltac misc_opt := set_evars; progress repeat misc_opt'; subst_evars.

Ltac step_opt' :=
  idtac;
  match goal with
  | _ => rewrite <- !minusr_minus
  | [ |- _ = @option_rect ?A ?B (fun s => _) _ _ ]
    => refine (_ : @option_rect A B (fun s => _) _ _ = _);
       apply (_ : Proper (pointwise_relation _ _ ==> _ ==> _ ==> eq) (@option_rect A B));
       repeat intro
  | [ |- _ = @bool_rect ?A _ _ _ ]
    => refine (_ : @bool_rect A _ _ _ = _);
       apply (_ : Proper (_ ==> _ ==> _ ==> eq) (@bool_rect A));
       repeat intro
  | [ |- _ = fold_right orb false _ ]
    => rewrite <- !(@fold_symmetric _ orb) by first [ apply Bool.orb_assoc | apply Bool.orb_comm ]
  | [ |- _ = @fold_left ?A ?B orb _ false ]
    => refine (_ : fold_left orb _ false = _);
       apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B)); repeat intro
  | [ |- _ = @fold_left ?A ?B orbr _ false ]
    => refine (_ : fold_left orbr _ false = _);
       apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B)); repeat intro
  | [ |- _ = @fold_right ?A ?B (fun x y => _) _ _ ]
    => refine (_ : fold_right (fun x y => _) _ _ = _);
       apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_right A B)); repeat intro
  | [ |- _ = @map ?A ?B _ _ ]
    => refine (_ : @map A B (fun x => _) _ = _);
       apply (_ : Proper (pointwise_relation _ _ ==> _ ==> _) (@map A B)); repeat intro
  | [ |- _ = @list_caset ?A ?P _ _ _ ]
    => refine (_ : @list_caset A P _ _ _ = _);
       apply (_ : Proper (forall_relation _ ==> forall_relation (fun _ => forall_relation _) ==> forall_relation _) (@list_caset A P)); repeat intro
  | [ |- _ = @list_caset ?A (fun _ => ?P) _ _ _ ]
    => refine (_ : @list_caset A (fun _ => P) _ _ _ = _);
       apply (_ : Proper (_ ==> pointwise_relation _ (pointwise_relation _ _) ==> _ ==> _) (@list_caset A (fun _ => P))); repeat intro
  | [ |- _ = @nth ?A _ _ _ ]
    => rewrite <- nth'_nth
  | [ |- _ = @nth' ?A _ _ _ ]
    => refine (_ : @nth' A _ _ _ = _);
       apply f_equal3
  | [ |- _ = sumbool_rect ?T ?A ?B ?c ]
    => let A' := fresh in
       let B' := fresh in
       let TA := type of A in
       let TB := type of B in
       evar (A' : TA); evar (B' : TB);
       refine (sumbool_rect
                 (fun c' => sumbool_rect T A' B' c' = sumbool_rect T A B c')
                 _ _ c); intro; subst A' B'; simpl @sumbool_rect
  | [ |- ?e = match ?ls with nil => _ | _ => _ end ]
    => is_evar e; refine (_ : match ls with nil => _ | _ => _ end = _)
  | [ |- match ?ls with nil => ?A | x::xs => @?B x xs end = match ?ls with nil => ?A' | x'::xs' => @?B' x' xs' end ]
    => refine (match ls
                     as ls'
                     return match ls' with nil => A | x::xs => B x xs end = match ls' with nil => A' | x'::xs' => B' x' xs' end
               with
               | nil => _
               | _ => _
               end)
  | [ |- _ = item_rect ?T ?A ?B ?c ] (* evar kludge following *)
    => revert c;
       let RHS := match goal with |- forall c', _ = ?RHS c' => RHS end in
       let f := constr:(fun TC NC =>
                          forall c, item_rect T TC NC c = RHS c) in
       let f := (eval cbv beta in f) in
       let e1 := fresh in
       let e2 := fresh in
       match type of f with
       | ?X -> ?Y -> _
         => evar (e1 : X); evar (e2 : Y)
       end;
       intro c;
       let ty := constr:(item_rect T e1 e2 c = RHS c) in
       etransitivity_rev _; [ refine (_ : ty) | reflexivity ];
       revert c;
       refine (item_rect
                 (fun c => item_rect T e1 e2 c = RHS c)
                 _ _);
       intro c; simpl @item_rect; subst e1 e2
  | [ |- _ = ritem_rect ?T ?A ?B ?c ] (* evar kludge following *)
    => revert c;
       let RHS := match goal with |- forall c', _ = ?RHS c' => RHS end in
       let f := constr:(fun TC NC =>
                          forall c, ritem_rect T TC NC c = RHS c) in
       let f := (eval cbv beta in f) in
       let e1 := fresh in
       let e2 := fresh in
       match type of f with
       | ?X -> ?Y -> _
         => evar (e1 : X); evar (e2 : Y)
       end;
       intro c;
       let ty := constr:(ritem_rect T e1 e2 c = RHS c) in
       etransitivity_rev _; [ refine (_ : ty) | reflexivity ];
       revert c;
       refine (ritem_rect
                 (fun c => ritem_rect T e1 e2 c = RHS c)
                 _ _);
       intro c; simpl @ritem_rect; subst e1 e2
  | [ |- _ = match ?x with true => true | false => false end ]
    => transitivity x; [ | destruct x; reflexivity ]
  | [ |- _ = ret_nt _ _ ]
    => refine (_ : ret_nt _ _ = _);
       refine (f_equal (ret_nt _) _)
  | [ |- _ = ret_NonTerminal_true ?x _ ]
    => refine (_ : ret_NonTerminal_true x _ = _);
       refine (f_equal (ret_NonTerminal_true x) _)
  | [ |- _ = fold_right ret_orb_productions ?init ?ls ]
    => rewrite <- (rev_involutive ls), fold_left_rev_right
  | [ |- _ = fold_right ret_orb_production ?init ?ls ]
    => rewrite <- (rev_involutive ls), fold_left_rev_right
  | [ |- _ = @fold_left ?A ?B ?orb _ ret_orb_productions_base ]
    => refine (_ : fold_left orb _ ret_orb_productions_base = _);
       apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B)); repeat intro
  | [ |- _ = @fold_left ?A ?B ?orb _ ret_orb_production_base ]
    => refine (_ : fold_left orb _ ret_orb_production_base = _);
       apply (_ : Proper (_ ==> _ ==> _ ==> _) (@fold_left A B)); repeat intro
  | [ |- _ = rev (map _ _) ]
    => rewrite <- map_rev
  end;
  fin_step_opt.

Ltac step_opt := repeat step_opt'.

Ltac sigL_transitivity term :=
  idtac;
  (lazymatch goal with
   | [ |- ?sig (fun x : ?T => @?A x = ?B) ]
     => (let H := fresh in
         let H' := fresh in
         assert (H : sig (fun x : T => A x = term));
         [
         | assert (H' : term = B);
           [ clear H
           | let x' := fresh in
             destruct H as [x' H];
             exists x'; transitivity term; [ exact H | exact H' ] ] ])
   end).

Ltac fix_trans_helper RHS x y :=
  match RHS with
  | context G[y] => let RHS' := context G[x] in
                       fix_trans_helper RHS' x y
  | _ => constr:(RHS)
  end.

Ltac fix2_trans :=
  match goal with
  | [ H : forall a0 a0' a1 a2 a3 a4 a5 a6, ?x a0 a0' a1 a2 a3 a4 a5 a6 = ?y a0 a0' a1 a2 a3 a4 a5 a6 |- _ = ?RHS ]
    => let RHS' := fix_trans_helper RHS x y
       in transitivity RHS'; [ clear H y | ]
  end.

Ltac fix2_trans_with_assumptions :=
  match goal with
  | [ H : forall a0 a0' a1 a2 a3 a4 a5 a6, _ -> ?x a0 a0' a1 a2 a3 a4 a5 a6 = ?y a0 a0' a1 a2 a3 a4 a5 a6 |- _ = ?RHS ]
    => let RHS' := fix_trans_helper RHS x y
       in transitivity RHS'; [ clear H y | ]
  end.

Ltac t_prereduce_list_evar :=
  idtac;
  let RHS := match goal with |- _ = ?RHS => RHS end in
  lazymatch RHS with
  | context RHS'[list_rect ?P ?f ?g]
    => let ft := type of f in
       let gt := type of g in
       let f' := fresh in
       let g' := fresh in
       evar (f' : ft); evar (g' : gt);
       let f0 := (eval unfold f' in f') in
       let g0 := (eval unfold g' in g') in
       let RHS'' := context RHS'[list_rect P f0 g0] in
       refine (_ : RHS'' = _)
  end.

Ltac t_postreduce_list :=
  idtac;
  lazymatch goal with
  | [ |- list_rect ?P ?N ?C ?ls ?a ?b ?c = list_rect ?P ?N' ?C' ?ls ?a ?b ?c ]
    => let P0 := fresh in
       let N0 := fresh in
       let C0 := fresh in
       let N1 := fresh in
       let C1 := fresh in
       set (P0 := P);
       set (N0 := N);
       set (C0 := C);
       set (N1 := N');
       set (C1 := C');
       let IH := fresh "IH" in
       let xs := fresh "xs" in
       refine (list_rect
                 (fun ls' => forall a' b' c',
                      list_rect P0 N0 C0 ls' a' b' c'
                      = list_rect P0 N1 C1 ls' a' b' c')
                 _
                 _
                 ls a b c);
       simpl @list_rect;
       [ subst P0 N0 C0 N1 C1; intros; cbv beta
       | intros ? xs IH; intros; unfold C0 at 1, C1 at 1; cbv beta;
         setoid_rewrite <- IH; clear IH N1 C1;
         generalize (list_rect P0 N0 C0 xs); intro ]
  end.

Ltac t_reduce_list_evar :=
  t_prereduce_list_evar;
  t_postreduce_list.

Ltac t_postreduce_list_with_hyp :=
  idtac;
  lazymatch goal with
  | [ |- list_rect ?P ?N ?C ?fa ?a ?b ?c = list_rect ?P ?N' ?C' ?fa ?a ?b ?c ]
    => idtac;
       let f := match (eval pattern a in fa) with ?f _ => f end in
       let P0 := fresh in
       let N0 := fresh in
       let C0 := fresh in
       let N1 := fresh in
       let C1 := fresh in
       set (P0 := P);
       set (N0 := N);
       set (C0 := C);
       set (N1 := N');
       set (C1 := C');
       let IH := fresh "IH" in
       let xs := fresh "xs" in
       refine (list_rect
                 (fun ls' => forall a' (pf : ls' = f a') b' c',
                      list_rect P0 N0 C0 ls' a' b' c'
                      = list_rect P0 N1 C1 ls' a' b' c')
                 _
                 _
                 (f a) a eq_refl b c);
       simpl @list_rect;
       [ subst P0 N0 C0 N1 C1; intros; cbv beta
       | intros ? xs IH; intros; unfold C0 at 1, C1 at 1; cbv beta;
         match goal with
         | [ |- context[list_rect P0 N1 C1 ?ls'' ?a''] ]
           => specialize (IH a'')
         end;
         let T := match type of IH with ?T -> _ => T end in
         let H_helper := fresh in
         assert (H_helper : T);
         [
                   | specialize (IH H_helper);
                     setoid_rewrite <- IH; clear IH N1 C1;
                     generalize (list_rect P0 N0 C0 xs); intro ] ]
  end.

Ltac t_postreduce_list_with_hyp_with_assumption :=
  idtac;
  lazymatch goal with
  | [ H : ?HP (?HP' (?f ?a)) = true |- list_rect ?P ?N ?C (?f ?a) ?a ?b ?c = list_rect ?P ?N' ?C' (?f ?a) ?a ?b ?c ]
    => let P0 := fresh in
       let N0 := fresh in
       let C0 := fresh in
       let N1 := fresh in
       let C1 := fresh in
       set (P0 := P);
       set (N0 := N);
       set (C0 := C);
       set (N1 := N');
       set (C1 := C');
       let IH := fresh "IH" in
       let xs := fresh "xs" in
       let pf := fresh "pf" in
       refine (list_rect
                 (fun ls' => forall a' (pf : ls' = f a') (H' : HP (HP' (f a')) = true) b' c',
                      list_rect P0 N0 C0 ls' a' b' c'
                      = list_rect P0 N1 C1 ls' a' b' c')
                 _
                 _
                 (f a) a eq_refl H b c);
       simpl @list_rect;
       [ subst P0 N0 C0 N1 C1; intros; cbv beta
       | intros ? xs IH pg; intros; unfold C0 at 1, C1 at 1; cbv beta;
         match goal with
         | [ |- context[list_rect P0 N1 C1 ?ls'' ?a''] ]
           => specialize (IH a'')
         end;
         let T := match type of IH with ?T1 -> ?T2 -> _ => constr:((T1 * T2)%type) end in
         let H_helper := fresh in
         let H_helper' := fresh in
         assert (H_helper : T);
         [ split
         | specialize (IH (fst H_helper) (snd H_helper));
           setoid_rewrite <- IH; clear IH N1 C1;
           generalize (list_rect P0 N0 C0 xs); intro ] ]
  end.

Ltac t_reduce_list_evar_with_hyp :=
  t_prereduce_list_evar;
  t_postreduce_list_with_hyp.

Ltac t_refine_item_match_terminal :=
  idtac;
  match goal with
  | [ |- _ = match ?it with Terminal _ => _ | NonTerminal nt => @?NT nt end :> ?T ]
    => refine (_ : item_rect (fun _ => T) _ NT it = _);
       revert it;
       refine (item_rect
                 _
                 _
                 _); simpl @item_rect; intro;
       [ | reflexivity ]
  end.

Ltac t_refine_item_match :=
  idtac;
  (lazymatch goal with
   | [ |- _ = match ?it with Terminal _ => _ | _ => _ end :> ?T ]
     => (refine (_ : item_rect (fun _ => T) _ _ it = _);
         (lazymatch goal with
          | [ |- item_rect ?P ?TC ?NC it = match it with Terminal t => @?TC' t | NonTerminal nt => @?NC' nt end ]
            => refine (item_rect
                         (fun it' => item_rect (fun _ => T) TC NC it'
                                     = item_rect (fun _ => T) TC' NC' it')
                         _
                         _
                         it)
          end;
          clear it; simpl @item_rect; intro))
   end).

Ltac rewrite_map_nth_rhs :=
  idtac;
  match goal with
  | [ |- _ = ?RHS ]
    => let v := match RHS with
                | context[match nth ?n ?ls ?d with _ => _ end]
                  => constr:(nth n ls d)
                | context[nth ?n ?ls ?d]
                  => constr:(nth n ls d)
                end in
       let P := match (eval pattern v in RHS) with
                | ?P _ => P
                end in
       rewrite <- (map_nth P)
  end.

Ltac rewrite_map_nth_dep_rhs :=
  idtac;
  match goal with
  | [ |- _ = ?RHS ]
    => let v := match RHS with
                | context[match nth ?n ?ls ?d with _ => _ end]
                  => constr:(nth n ls d)
                | context[nth ?n ?ls ?d]
                  => constr:(nth n ls d)
                end in
       let n := match v with nth ?n ?ls ?d => n end in
       let ls := match v with nth ?n ?ls ?d => ls end in
       let d := match v with nth ?n ?ls ?d => d end in
       let P := match (eval pattern v in RHS) with
                | ?P _ => P
                end in
       let P := match (eval pattern n in P) with
                | ?P _ => P
                end in
       rewrite <- (map_nth_dep P ls d n)
  end.

Ltac t_pull_nth :=
  repeat match goal with
         | _ => rewrite drop_all by (simpl; omega)
         | [ |- _ = nth _ _ _ ] => step_opt'
         | [ |- _ = nth' _ _ _ ] => step_opt'
         | _ => rewrite !map_map
         | _ => progress simpl
         | _ => rewrite <- !surjective_pairing
         | _ => progress rewrite_map_nth_rhs
         end;
  fin_step_opt.
Ltac t_after_pull_nth_fin :=
  idtac;
  match goal with
  | [ |- context[@nth] ] => fail 1
  | [ |- context[@nth'] ] => fail 1
  | _ => repeat step_opt'
  end.

Ltac optsplit_t' :=
  idtac;
  match goal with
  | [ |- _ = ?f match ?v with nil => ?N | x::xs => @?C x xs end ]
    => let RHS := match goal with |- _ = ?RHS => RHS end in
       let P := match (eval pattern v in RHS) with ?P _ => P end in
       transitivity (match v with
                     | nil => P nil
                     | x::xs => P (x::xs)
                     end);
       [ simpl | destruct v; reflexivity ]
  | [ |- _ = ?f match ?v with Terminal t => @?T t | NonTerminal nt => @?NT nt end ]
    => let RHS := match goal with |- _ = ?RHS => RHS end in
       let P := match (eval pattern v in RHS) with ?P _ => P end in
       transitivity (match v with
                     | Terminal t => P (Terminal t)
                     | NonTerminal nt => P (NonTerminal nt)
                     end);
       [ simpl | destruct v; reflexivity ]
  | [ |- ?e = match ?v with nil => ?N | x::xs => @?C x xs end :> ?T ]
    => idtac;
       repeat match goal with
              | [ H : context[v] |- _ ]
                => hnf in H;
                   match type of H with
                   | context[v] => fail 1
                   | _ => idtac
                   end
              end;
       let P := match (eval pattern v in T) with ?P _ => P end in
       change (e = list_caset P N C v);
       revert dependent v;
       let NT := type of N in
       let CT := type of C in
       let N' := fresh in
       let C' := fresh in
       evar (N' : NT);
       evar (C' : CT);
       intro v; intros;
       refine (_ : list_caset P N' C' v = list_caset P N C v);
       refine (list_caset
                 (fun v' => list_caset P N' C' v' = list_caset P N C v')
                 _
                 _
                 v);
       subst N' C'; simpl @list_caset; repeat intro
  | [ H : is_true (item_rvalid ?G ?v)
      |- ?e = match ?v with Terminal t => @?T t | NonTerminal nt => @?NT nt end ]
    => idtac; let TT := type of T in
              let NTT := type of NT in
              let T' := fresh in
              let NT' := fresh in
              revert dependent v;
              evar (T' : TT);
              evar (NT' : NTT);
              intro v; intros;
              let eqP := match goal with |- _ = _ :> ?P => P end in
              let P := match (eval pattern v in eqP) with ?P _ => P end in
              change (e = item_rect P T NT v);
              refine (_ : item_rect P T' NT' v = item_rect P T NT v);
              refine (item_rect
                        (fun v' => item_rvalid G v' -> item_rect P T' NT' v' = item_rect P T NT v')
                        _
                        _
                        v H);
              subst T' NT';
              simpl @item_rect; intros ??
  | [ |- ?e = match ?v with Terminal t => @?T t | NonTerminal nt => @?NT nt end ]
    => idtac; let TT := type of T in
              let NTT := type of NT in
              let T' := fresh in
              let NT' := fresh in
              revert dependent v;
              evar (T' : TT);
              evar (NT' : NTT);
              intro v; intros;
              let eqP := match goal with |- _ = _ :> ?P => P end in
              let P := match (eval pattern v in eqP) with ?P _ => P end in
              change (e = item_rect P T NT v);
              refine (_ : item_rect P T' NT' v = item_rect P T NT v);
              refine (item_rect
                        (fun v' => item_rect P T' NT' v' = item_rect P T NT v')
                        _
                        _
                        v);
              subst T' NT';
              simpl @item_rect; intro
  | [ |- _ = _::_ ] => etransitivity_rev (_::_);
                       [ apply f_equal2
                       | reflexivity ]
  | _ => progress fin_step_opt
  end.

Ltac change_char_at_matches :=
  idtac;
  lazymatch goal with
  | [ |- context G[@char_at_matches ?Char ?HSLM ?n ?str (@interp_RCharExpr _ ?data ?P)] ]
    => idtac;
       let G' := context G[@char_at_matches_interp Char HSLM data n str P] in
       change G'
  end.

Ltac rewrite_map_map :=
  idtac;
  match goal with
  | [ |- context[@map ?B ?C ?g (@map ?A ?B ?f ?ls)] ]
    => rewrite (@map_map A B C f g)
  end.

Ltac rewrite_map_length :=
  idtac;
  match goal with
  | [ |- context[@List.length ?B (@List.map ?A ?B ?f ?ls)] ]
    => rewrite (@map_length A B f ls)
  end.
