Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Cito.GeneralTactics.

Ltac clear_imports :=
  try match goal with
          Him : LabelMap.t assert |- _ =>
          repeat match goal with
                     H : context [ Him ] |- _ => clear H
                 end;
            clear Him
      end.

Ltac open_Some :=
  match goal with
      H : Some _ = Some _ |- _ => injection H; clear H; intros
  end.

Ltac cond_solver :=
  match goal with
      H : evalCond _ _ _ _ _ = Some ?T |- wneb _ _ = ?T =>
      unfold evalCond in *; simpl in *; open_Some; rewriter_r; f_equal
  end.

Require Import Bedrock.Platform.Cito.SemanticsExpr.

Ltac find_cond :=
  match goal with
    | H1 : evalCond _ _ _ _ _ = Some ?b, H2 : _ = eval ?V ?E |- _ => assert (wneb (eval V E) $0 = b) by cond_solver
  end.

Ltac not_exist t :=
  match goal with
    | H : t |- _ => fail 1
    | |- _ => idtac
  end.

Ltac assert_new t := not_exist t; assert t.

Ltac cond_gen :=
  try
    match goal with
      | H_interp : interp _ (![_](_, ?ST)), H_eval : evalInstrs _ ?ST ?INST = _ |- _ =>
        match INST with
          | context [variablePosition ?vars ?s] => assert_new (In s vars)
          | context [variableSlot ?s ?vars] => assert_new (In s vars)
        end; [ clear H_eval .. | cond_gen ]
    end.

Ltac HypothesisParty H :=
  match type of H with
    | interp _ (![ _ ](_, ?x)) =>
      repeat
        match goal with
          | [H0: evalInstrs _ x _ = _, H1: evalInstrs _ _ _ = _ |- _] => not_eq H0 H1; generalize dependent H1
          | [H0: evalInstrs _ x _ = _, H1: interp _ _ |- _] => not_eq H H1; generalize dependent H1
        end
  end.

Lemma fold_4S : forall n, (S (S (S (S (4 * n))))) = (4 + (4 * n)).
  eauto.
Qed.

Ltac simpl_interp :=
  match goal with
    | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
      simpl in H; try rewrite fold_4S in H
  end.

Ltac simpl_sp :=
  repeat match goal with
             H : (_, _) # Sp = _ |- _ => simpl in H
         end.

Require Import Bedrock.Platform.Wrap.

Lemma pack_pair' : forall A B (x : A * B), (let (x, _) := x in x, let (_, y) := x in y) = x.
  destruct x; simpl; intuition.
Qed.

Lemma fold_second : forall A B (p : A * B), (let (_, y) := p in y) = snd p.
  destruct p; simpl; intuition.
Qed.

Lemma fold_first : forall A B (p : A * B), (let (x, _) := p in x) = fst p.
  destruct p; simpl; intuition.
Qed.

Ltac post_step := repeat first [ rewrite pack_pair' in * | rewrite fold_second in * | rewrite fold_first in *].

Ltac fold_length :=
  change (fix length (l : list string) : nat :=
            match l with
              | nil => 0
              | _ :: l' => S (length l')
            end) with (@length string) in *.

Ltac not_mem_rv INST :=
  match INST with
    | context [LvMem ?LOC] =>
      match LOC with
        | context [Rv] => fail 2
        | _ => idtac
      end
    | _ => idtac
  end.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Make E.
  Import SemanticsMake.

  Ltac hiding tac :=
    clear_imports;
    ((let P := fresh "P" in
      match goal with
        | H : Safe ?fs _ _ |- _ => set (P := Safe fs) in *
        | H : RunsTo ?fs _ _ _ |- _ => set (P := RunsTo fs) in *
      end;
      hiding tac;
      subst P) || tac).

  (* transit *)

  Ltac eapply_cancel h specs st :=
    let HP := fresh in
    let Hnew := fresh in
    evar (HP : HProp); assert (interp specs (![HP] st)) as Hnew;
    [ | eapply h in Hnew; [ | clear Hnew .. ] ]; unfold HP in *; clear HP;
    [ solve [clear_imports; repeat hiding ltac:(step auto_ext) ] | .. ].

  Ltac transit :=
    match goal with
      | H_interp : interp ?SPECS (![_] ?ST), H : context [interp _ (![_] ?ST) -> _] |- _ => eapply_cancel H SPECS ST; clear H H_interp; auto; []
    end.

  (* eval_instrs *)

  Ltac clear_bad H_interp s :=
    repeat
      match goal with
        | H : Regs ?ST Rv = _  |- _ => not_eq ST s; generalize H; clear H
        | H : context [Safe _ _ _] |- _ => not_eq H H_interp; generalize H; clear H
      end.

  Ltac pre_eval :=
    match goal with
      | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
        try clear_imports; HypothesisParty H; prep_locals; clear_bad H ST;
        simpl_interp; simpl_sp; try rewrite fold_4S in *
    end.

  Module Import InvMake2 := Make M.

  Ltac pre_eval_auto :=
    repeat
      match goal with
        | H_eval : evalInstrs _ ?ST ?INST = _, H_interp : interp _ (![?P] (_, ?ST)) |- _ =>
          match INST with
              context [ Rv ] =>
              match goal with
                  H_rv : Regs ST Rv = _ |- _ => not_mem_rv INST; post_step; generalize dependent H_rv
              end
          end
        | H_eval : evalInstrs _ ?ST ?INST = _, H_interp : interp _ (![?P] (_, ?ST)) |- _ =>
          match P with
              context [ is_heap _ ?HEAP ] =>
              match goal with
                  H_heap : HEAP = _ |- _ => post_step; generalize dependent H_heap
              end
          end
      end.

  Ltac evaluate_hints hints :=
    match goal with
        H : evalInstrs _ ?ST _ = _ |- _ => generalize dependent H; evaluate hints; intro; evaluate auto_ext
    end.

  Ltac my_evaluate hints :=
    match goal with
      | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST ?INST = _ |- _  =>
        match INST with
          | context [LvMem (Reg Rv) ] => evaluate_hints hints
          | _ => pre_eval_auto; evaluate hints
        end
    end.

  Ltac post_eval := intros; try fold (@length W) in *; post_step; try fold_length; try rewrite fold_4S in *.

  Ltac try_post :=
    try match goal with
            H_interp : interp _ ?P |- _ =>
            match P with
              | context [ Exists ] => post
            end
        end.

  Ltac eval_instrs hints :=
    match goal with
      | H: interp _ (![_](_, ?ST)), H_eval: evalInstrs _ ?ST _ = _ |- _  =>
        cond_gen;
          [ .. |
            let P := fresh "P" in
            try match goal with
                  | [ _ : context[Safe ?fs _ _] |- _ ] => set (P := Safe fs) in *
                end;
              pre_eval;
              try match goal with
                    | [ H : _ = Regs ?X Rv, H' : _ = Regs ?X Rv |- _ ] => generalize dependent H'
                  end;
              my_evaluate hints;
              try subst P;
              post_eval; clear H_eval]
    end.

  Ltac clear_all :=
    repeat match goal with
             | H : _ |- _ => clear H
           end.

  Ltac clear_Imply :=
    repeat match goal with
             | H : context [ (_ ---> _)%PropX ] |- _ => clear H
           end.

  Ltac clear_evalInstrs :=
    repeat match goal with
             | H : evalInstrs _ _ _ = _ |- _ => clear H
           end.

  Ltac clear_Forall_PreCond :=
    repeat match goal with
             | H : List.Forall _ _ |- _ => clear H
             | H : AxSpec.PreCond _ _ |- _ => clear H
           end.

  Ltac hide_evalInstrs :=
    repeat match goal with
             | H : evalInstrs _ _ _ = _ |- _ => generalize dependent H
           end.

  Ltac hide_all_eq :=
    repeat match goal with
             | H : _ = _ |- _ => generalize dependent H
           end.

  Ltac hide_all_eq_except H1 :=
    repeat match goal with
             | H : _ = _ |- _ => not_eq H H1; generalize dependent H
           end.

  Ltac hide_le :=
    repeat match goal with
             | H : (_ <= _)%nat |- _ => generalize dependent H
           end.

  Ltac hide_Safe :=
    repeat match goal with
             | H : Safe _ _ _ |- _ => generalize dependent H
           end.

  Ltac destruct_state :=
    repeat
      match goal with
        | [ x : State |- _ ] => destruct x; simpl in *
        | [ x : (settings * state)%type |- _ ] => destruct x; simpl in *
      end.

  Ltac unfold_all :=
    repeat match goal with
             | H := _ |- _ => unfold H in *; clear H
           end.

  Ltac rearrange_stars HEAD :=
    match goal with
        H : interp ?SPECS (![?P] ?ST) |- _ =>
        let OTHER := fresh in
        evar (OTHER : HProp);
          assert (interp SPECS (![HEAD * OTHER] ST));
          unfold OTHER in *; clear OTHER;
          [ hiding ltac:(step auto_ext) | .. ]
    end.

End Make.
