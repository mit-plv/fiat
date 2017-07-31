Require Import Coq.micromega.Lia.
Require Import Coq.PArith.BinPos.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.
Export ListNotations.
Global Open Scope list_scope.
Global Open Scope char_scope.
Global Open Scope string_scope.
Notation NT s := (RNonTerminal s%string).
Notation t e := (RTerminal e).
Notation "=? v" := (rbeq v%char) (at level 30).

Module AsciiOrder <: Orders.TotalLeBool.
  Definition t := ascii.
  Definition leb (x y : t) := Pos.leb (pos_of_ascii x) (pos_of_ascii y).
  Infix "<=?" := leb.
  Local Coercion is_true : bool >-> Sortclass.
  Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
  Proof. intros; setoid_rewrite Pos.leb_le; lia. Qed.
End AsciiOrder.

Module Import AsciiSort := Sort AsciiOrder.

Definition default_to_rproduction {Char} (G : pregrammar Char) (idx : Carriers.default_production_carrierT)
  : rproduction Char
  := let nt_idx := fst idx in
     let nts := RLookup_idx G nt_idx in
     let ps_idx := List.length nts - S (fst (snd idx)) in
     let drop_count := snd (snd idx) in
     let ps := List.nth ps_idx nts nil
     in Operations.List.drop drop_count ps.
Ltac lookup_production g idx :=
  let v := constr:(default_to_rproduction g idx) in
  eval vm_compute in v.
Ltac lookup_productions g nt :=
  let v := constr:(list_to_productions nil (pregrammar_rproductions g) nt) in
  eval vm_compute in v.
Ltac print_production g idx :=
  let v := lookup_production g idx in
  idtac v.
Ltac print_productions g idx :=
  let v := lookup_productions g idx in
  idtac v.
Ltac norm_pregrammar G :=
  lazymatch G with
  | pregrammar'_of_pregrammar ?G => G
  | _ => G
  end.
Ltac norm_lookup_val_to_production_or_nt G v cont_nt cont_production :=
  let G := norm_pregrammar G in
  let T := type of v in
  lazymatch eval compute in T with
  | string
    => cont_nt v
  | list (ritem _)
    => let v := constr:(@interp_rproduction _ (@pregrammar_idata _ G) v) in
       cont_production v
  | list (item _)
    => cont_production v
  | (nat * (nat * nat))%type
    => let v := lookup_production G v in
       norm_lookup_val_to_production_or_nt G v cont_nt cont_production
  | ?T' => let dummy := match goal with
                        | _ => fail 100 "Invalid type for index:" T'
                        end in
           constr:(tt)
  end.
Ltac get_possible lem_nt lem_prod v :=
  lazymatch goal with
  | [ pdata : PossibleTerminalsSets.possible_data ?G |- _ ]
    => let v := norm_lookup_val_to_production_or_nt
                  G v
                  ltac:(fun nt => constr:(@lem_nt G pdata nt))
                         ltac:(fun p => constr:(@lem_prod G pdata p)) in
       let v := (eval vm_compute in v) in
       lazymatch type of v with
       | list ascii
         => (eval vm_compute in (List.map (fun c => String.String c String.EmptyString) (sort v)))
       | _ => v
       end
  end.
Ltac get_all_possible_chars v := get_possible (@PossibleTerminalsSets.all_possible_ascii_of_nt) (@PossibleTerminalsSets.all_possible_ascii_of_production) v.
Ltac get_first_possible_chars v := get_possible (@PossibleTerminalsSets.possible_first_ascii_of_nt) (@PossibleTerminalsSets.possible_first_ascii_of_production) v.
Ltac get_last_possible_chars v := get_possible (@PossibleTerminalsSets.possible_last_ascii_of_nt) (@PossibleTerminalsSets.possible_last_ascii_of_production) v.
Ltac get_might_be_empty v := get_possible (@PossibleTerminalsSets.might_be_empty_of_pr_nt) (@PossibleTerminalsSets.might_be_empty_of_pr_production) v.
Ltac print_chars v :=
  let v := get_all_possible_chars v in
  idtac v.
Ltac print_first_chars v :=
  let v := get_first_possible_chars v in
  idtac v.
Ltac print_last_chars v :=
  let v := get_last_possible_chars v in
  idtac v.
Ltac print_empty v :=
  let v := get_might_be_empty v in
  lazymatch v with
  | true => idtac "maybe"
  | false => idtac "definitely not"
  | _ => idtac "Huh? (" v ")"
  end.
