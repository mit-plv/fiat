(** Sharpened ADT for JSON *)
Require Import Fiat.Parsers.Grammars.JSON.
Require Import Fiat.Parsers.Refinement.Tactics.

Section IndexedImpl.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringEqProperties Ascii.ascii}.

  Local Opaque json_grammar.

  Lemma ComputationalSplitter'
  : FullySharpened (string_spec json_grammar HSL).
  Proof.

    start sharpening ADT.
    start honing parser using indexed representation.

    Local Transparent json_grammar.

    set (x := json_grammar).
    set (y := Valid_nonterminals x).
    set (z := Lookup x).
    unfold json_grammar, list_to_grammar in x.
    simpl in x.
    repeat match goal with
           | [ |- context[Operations.List.uniquize ?beq ?ls] ]
             => change (Operations.List.uniquize beq ls) with ls
           end.
    set (w := Operations.List.up_to (List.length y)).
    cbv in w.
    subst w.
    unfold List.flat_map at 1.
    repeat match goal with
           | [ |- context[Operations.List.uniquize ?beq ?ls] ]
             => change (Operations.List.uniquize beq ls) with ls
           end.
    match goal with
    | [ |- context[@Carriers.default_to_nonterminal ?x ?y ?z] ]
      => set (v := @Carriers.default_to_nonterminal x y)
    end.
    unfold Carriers.default_to_nonterminal in v.
    repeat match eval unfold v in v with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of v)
           end.
    unfold Valid_nonterminals, x in y.
    simpl in y.
    change (Valid_nonterminals x) with y in (value of v).
    unfold y in v.
    unfold List.nth in v.
    unfold v; subst v.
    unfold Lookup, x, list_to_productions in z.
    repeat match eval unfold z in z with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of z)
           end.
    simpl @List.map in z.
    repeat match goal with
           | [ |- context[z ?nt] ]
             => let z' := fresh "z'" in
                set (z' := z nt);
                  unfold z in z';
                  match eval unfold z' in z' with
                  | context[Operations.List.first_index_error ?f ?ls]
                    => let c := constr:(Operations.List.first_index_error f ls) in
                       let c' := (eval cbv in c) in
                       change c with c' in (value of z')
                  end;
                  unfold option_rect, List.nth in z';
                  subst z'
           end.
    simpl @List.length.
    simpl @Operations.List.up_to.
    unfold List.flat_map.
    simpl @List.length.
    simpl @List.map.
    simpl @List.app.
    unfold List.fold_right at 1.
    unfold RDPList.rdp_list_to_production.
    match goal with
    | [ |- context[@Carriers.default_to_production ?x ?y ?z] ]
      => set (v := @Carriers.default_to_production x y)
    end.
    unfold Carriers.default_to_production, Carriers.default_to_nonterminal in v.
    repeat match eval unfold v in v with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of v)
           end.
    change (Valid_nonterminals x) with y in (value of v).
    unfold y in v.
    unfold Lookup, x, list_to_productions in v.
    repeat match eval unfold v in v with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of v)
           end.
    simpl @List.map in v.
    Local Ltac simpl_lookup v :=
      match goal with
           | [ |- context[v ?nt] ]
             => let z' := fresh "z'" in
                set (z' := v nt);
                  unfold v in z';
                  match eval unfold z' in z' with
                  | context[Operations.List.first_index_error ?f ?ls]
                    => let c := constr:(Operations.List.first_index_error f ls) in
                       let c' := (eval cbv in c) in
                       change c with c' in (value of z')
                  end;
                  unfold option_rect in z';
                  unfold List.nth at 2 3 in (value of z');
                  unfold Datatypes.length in z';
                  simpl in z';
                  subst z'
           end.
      lazymatch goal with
           | [ |- context[v ?nt] ]
             => let z' := fresh "z'" in
                set (z' := v nt);
                  unfold v in z'           end.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    simpl_lookup v.
    cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl @fst.
    simpl @snd.
    Set Printing Depth 1000000.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    simpl_lookup v; cbv beta iota.
    unfold has_only_terminals.
    simpl @List.length.
    set (k := FixedLengthLemmas.collapse_length_result (FixedLengthLemmas.length_of_any x "HEX")).
    cbv in k.
    subst k.
    Local Ltac simpl_collapse :=
      match goal with
      | [ |- context[FixedLengthLemmas.collapse_length_result ?v] ]
        => let k := fresh "k" in
           set (k := FixedLengthLemmas.collapse_length_result v);
           vm_compute in k;
           subst k
      end.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Time simpl_collapse.
    Fail simpl_collapse.
    unfold option_rect.
    change x with json_grammar.
    clear x y z v.
    Local Opaque json_grammar.
    Time simpl.

    hone method "splits".
    {
      (*simplify parser splitter.*)
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
Lemma c_if_aggregate4 {A} (b1 b2 b3 b4 b5 : bool) (x y z w v : A) (H : b1 = false -> (b2 || b3 || b4)%bool = true -> b5 = true -> False)
  : (if b1 then x else if b2 then y else if b3 then z else if b4 then w else if b5 then x else v) = (if (b1 || b5)%bool then x else if b2 then y else if b3 then z else if b4 then w else v).
Proof.
  destruct b1, b2, b3, b4, b5; simpl in *; try reflexivity; specialize_by ltac:(exact eq_refl);
    destruct_head False.
Qed.
Definition if_aggregate4 {A} (b1 b2 b3 b4 b5 : bool) (x y z w v : A) (H : b1 = false -> (b2 || b3 || b4)%bool = true -> b5 = true -> False)
: (If b1 Then x Else If b2 Then y Else If b3 Then z Else If b4 Then w Else If b5 Then x Else v) = (If (b1 || b5)%bool Then x Else If b2 Then y Else If b3 Then z Else If b4 Then w Else v)
  := @c_if_aggregate4 _ _ _ _ _ _ x y z w v H.
rewrite !if_aggregate4 by solve_prod_beq.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
Lemma c_swap_if {A} (b1 b2 : bool) (x y z : A) (H : b1 = true -> b2 = true -> False)
: (if b1 then x else if b2 then y else z) = (if b2 then y else if b1 then x else z).
Proof.
  destruct b1, b2; try reflexivity; specialize_by ltac:(exact eq_refl);
    destruct_head False.
Qed.
Definition swap_if {A} (b1 b2 : bool) (x y z : A) (H : b1 = true -> b2 = true -> False)
: (If b1 Then x Else If b2 Then y Else z) = (If b2 Then y Else If b1 Then x Else z)
  := @c_swap_if A b1 b2 x y z H.
 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       Set Printing Width 10000.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 10 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.


      simplify_parser_splitter'.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.


      simplify_parser_splitter'.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
 do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
 do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.


      simplify_parser_splitter'.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.


      simplify_parser_splitter'.

      simplify_parser_splitter'.
 do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.

Notation "'If' c 'ThenT' t 'Else' e" :=
  (If_Then_Else c t e)
    (at level 70, format "'[hv  ' 'If'  c  'ThenT' '//' '[' t ']' ']' '//' 'Else'  '[' e ']'").

      simplify_parser_splitter'.



      simplify_parser_splitter'.
      simplify_parser_splitter'.
 do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
 do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
 do 5 match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
        match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
        match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
        match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G _ _ _ ?idx] ]
        => set (v := Carriers.default_to_production (G := G) idx)
      end.
      unfold Carriers.default_to_production in v.
      unfold Carriers.default_to_production, Carriers.default_to_nonterminal in v.
      Transparent json_grammar.
      repeat match eval unfold v in v with
             | context[Operations.List.uniquize ?beq ?ls]
               => change (Operations.List.uniquize beq ls) with ls in (value of v)
             end.
      set (y := Valid_nonterminals json_grammar) in (value of v).
      unfold Valid_nonterminals, json_grammar, list_to_grammar, list_to_productions in y.
      repeat match eval unfold y in y with
             | context[Operations.List.uniquize ?beq ?ls]
               => change (Operations.List.uniquize beq ls) with ls in (value of y)
             end.
      simpl in y.
      unfold y in v.
      simpl @fst in v.
      unfold Lookup, json_grammar, list_to_grammar, list_to_productions in v.
    repeat match eval unfold v in v with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of v)
           end.
    simpl @List.map in v.
    simpl @snd in v.
    unfold List.nth at 3 6 in (value of v).
    lazymatch eval unfold v in v with
    | context[Operations.List.first_index_error ?f ?ls]
      => let c := constr:(Operations.List.first_index_error f ls) in
         let c' := (eval cbv in c) in
         change c with c' in (value of v)
    end.
    unfold option_rect in v.
    unfold List.nth in v.
    unfold List.length in v.
    simpl in v.
Require Import Fiat.Parsers.Refinement.DisjointRules.
Require Import Fiat.Parsers.ExtrOcamlParsers. (* for simpl rules for [find_first_char_such_that] *)
Set Printing Implicit.
Axiom HSI : StringIso Ascii.ascii.
Axiom HSIIP : StringIsoProperties Ascii.ascii.
set (x := json_grammar).
unfold json_grammar, list_to_grammar in x.
    repeat match eval unfold x in x with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of x)
           | _ => progress simpl @List.hd in x
           end.
Unset Printing Implicit.
simpl @List.map in x.
unfold list_to_productions in x.
    repeat match eval unfold x in x with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of x)
           | _ => progress simpl @List.hd in x
           end.
    simpl @List.map in x.
assert (H' : ValidReflective.grammar_rvalid x).
{ Time lazy.
  reflexivity. }
set (z := Carriers.default_to_production (G := x)).
unfold Carriers.default_to_production, Carriers.default_to_nonterminal in z.
simpl @Valid_nonterminals in z.
    repeat match eval unfold z in z with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of z)
           end.
unfold Lookup, x in z.
    repeat match eval unfold z in z with
           | context[Operations.List.uniquize ?beq ?ls]
             => change (Operations.List.uniquize beq ls) with ls in (value of z)
           end.
Local Ltac special_solve_side z :=
lazymatch goal with
| [ H : is_true (ValidReflective.grammar_rvalid ?G) |- is_true (ValidReflective.grammar_rvalid ?G) ]
  => exact H
| [ |- Carriers.default_to_production ?k = ?e ]
  => change (z k = e);
       unfold z;
       simpl @fst;
       match goal with
       | [ |- context[Operations.List.first_index_error ?f ?ls] ]
         => let c := constr:(Operations.List.first_index_error f ls) in
            let c' := (eval cbv in c) in
            change c with c'
       end;
       unfold option_rect;
       simpl @snd;
       unfold List.nth at 2 3;
       unfold List.length, minus;
       unfold List.nth;
       unfold Operations.List.drop;
       reflexivity
| [ |- is_true (Operations.List.disjoint ?beq ?A ?B) ]
  => timeout 10 vm_compute; reflexivity
end.
Time let lem' := constr:(@refine_disjoint_search_for_idx HSLM HSL HSI HSLP HSIIP) in
pose proof lem' as lem.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.

match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len _] ]
        => specialize (fun idx nt its => lem G str offset len nt its idx H')
end.
setoid_rewrite lem.
change (Carriers.default_to_production (G := x)) with z in lem.

2:unfold z;
       simpl @fst;
       match goal with
       | [ |- context[Operations.List.first_index_error ?f ?ls] ]
         => let c := constr:(Operations.List.first_index_error f ls) in
            let c' := (eval cbv in c) in
            change c with c'
       end;
       unfold option_rect;
       simpl @snd;
       unfold List.nth at 2 3;
       unfold List.length, minus;
       unfold List.nth;
       unfold Operations.List.drop.




















match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
match goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => setoid_rewrite (fun nt its => lem G str offset len nt its idx H');
             [ | solve [ special_solve_side z ].. ]
end.
setoid_rewrite lem by ltac:(special_solve_side z).
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 2:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 3:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 4:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 5:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 6:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Time 7:special_solve_side z.
Focus 2.
match goal with
end.
Focus 2.
Time vm_compute.
match goal with
unfold List.nth at
Time lazy.
reflexivity.
Focus 2.
unfold Carriers.default_to_production, Carriers.default_to_nonterminal.
simpl @Valid_nonterminals.
    repeat match goal with
           | [ |- context[Operations.List.uniquize ?beq ?ls] ]
             => change (Operations.List.uniquize beq ls) with ls
           end.
simpl @fst.
unfold List.nth at 2 3.
simpl @snd.
unfold Lookup, x.
match goal with
| [ |- context[Operations.List.first_index_error ?f ?ls] ]
  => let c := constr:(Operations.List.first_index_error f ls) in
     let c' := (eval cbv in c) in
     change c with c'
end.
unfold option_rect.
simpl List.length.
simpl minus.
unfold List.nth.
simpl.
reflexivity.
Focus 2.
unfold DisjointLemmas.possible_terminals_of.
unfold DisjointLemmas.possible_first_terminals_of_production.
unfold FoldGrammar.fold_production.
unfold FoldGrammar.fold_production'.
unfold List.map.
unfold FoldGrammar.on_nonterminal.
unfold DisjointLemmas.only_first_fold_data.
unfold List.fold_right.
unfold FoldGrammar.combine_production, FoldGrammar.on_nil_production.
unfold DisjointLemmas.actual_possible_first_terminals at 1.
unfold DisjointLemmas.actual_possible_first_terminals at 2.
unfold FoldGrammar.fold_nt.
unfold DisjointLemmas.actual_possible_first_terminals at 2.
unfold DisjointLemmas.actual_possible_first_terminals at 5.
unfold DisjointLemmas.actual_possible_first_terminals at 7.
unfold BaseTypes.nonterminals_length, BaseTypes.initial_nonterminals_data.
unfold RDPList.rdp_list_predata.
unfold RDPList.rdp_list_initial_nonterminals_data.
    repeat match goal with
           | [ |- context[Operations.List.uniquize ?beq ?ls] ]
             => change (Operations.List.uniquize beq ls) with ls
           end.
simpl @Valid_nonterminals.
simpl @List.length.
simpl @Operations.List.up_to.
unfold FoldGrammar.fold_nt'.
unfold FoldGrammar.fold_nt_step at 1 3 5.
cbv beta iota zeta delta.
reflexivity.

Focus 2.
fold @FoldGrammar.fold_nt'.
unfold
match goal with
| [ |- context[
Timeout 5 2:reflexivity.
      lazymatch goal with
      | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
        => pose (fun nt its => lem G str offset len nt its idx)
      end.


    lazymatch goal with
           | [ |- context[v ?nt] ]
             => let z' := fresh "z'" in
                set (z' := v nt);
                  unfold v in z';
                  match eval unfold z' in z' with
                  | context[Operations.List.first_index_error ?f ?ls]
                    => let c := constr:(Operations.List.first_index_error f ls) in
                       let c' := (eval cbv in c) in
                       change c with c' in (value of z')
                  end;
                  unfold option_rect in z';
                  unfold List.nth at 2 3 in (value of z');
                  unfold Datatypes.length in z';
                  simpl in z';
                  subst z'
           end.
    simpl_lookup v.
      unfold List.nth at 2 3 in (value of v).
      change (Valid_nonterminals x) with y in (value of v).
    unfold y in v.
    unfold Lookup, x, list_to_productions in v.
    simpl @List.map in v.

      simplify_parser_splitter'.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
       do 5 try
       match goal with
       | [ |- context[If _ Then ret ?v Else If _ Then Pick ?P Else _] ]
         => rewrite !(@swap_if _ _ _ (ret v) (Pick P) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.

      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
repeat match goal with
       | [ |- context[If ?b Then _ Else _] ]
         => not is_var b;
              let b' := fresh "b" in set (b' := b)
       | [ |- context[If _ Then Pick ?P Else _] ]
         => not is_var P; let b' := fresh "P" in set (b' := P)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
Start Profiling.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst_body; solve_prod_beq)
       end.
Show Profile.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
match goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => idtac P v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => move P at bottom; pose v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => move P at bottom; pose v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => move P at bottom; pose v; rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
do 9 try lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
do 9 try lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
do 9 try lazymatch goal with
       | [ |- context[If ?b Then (Pick ?P) Else If ?b' Then ret ?v Else _] ]
         => rewrite (@swap_if _ _ _ (Pick P) (ret v) _) by (subst b b'; solve_prod_beq)
       end.
2:subst_body.


 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
 match goal with
       | [ |- context[If _ Then (Pick ?P) Else If _ Then ret ?v Else _] ]
         => rewrite !(@swap_if _ _ _ (Pick P) (ret v) _) by solve_prod_beq
       end.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      simplify_parser_splitter'.
      finish honing parser method.
    }

    finish_Sharpening_SplitterADT.

  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec json_grammar HSL).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.
Require Export Fiat.Parsers.ExtrOcamlParsers.
Export Fiat.Parsers.ExtrOcamlParsers.HideProofs.
Require Export Fiat.Parsers.StringLike.OcamlString.

Definition json_parser (str : Coq.Strings.String.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ String.string_stringlike _ _). (* 0.82 s *)
Defined.

Definition json_parser_ocaml (str : Ocaml.Ocaml.string) : bool.
Proof.
  Time make_parser (@ComputationalSplitter _ Ocaml.string_stringlike _ _). (* 0.82 s *)
Defined.

Print json_parser_ocaml.

Recursive Extraction json_parser_ocaml.

Definition main_json := premain json_parser.
Definition main_json_ocaml := premain_ocaml json_parser_ocaml.

Parameter reference_json_parser : Coq.Strings.String.string -> bool.
Parameter reference_json_parser_ocaml : Ocaml.Ocaml.string -> bool.
Extract Constant reference_json_parser
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (List.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".
Extract Constant reference_json_parser_ocaml
=> "fun str ->
  let needs_b : bool Pervasives.ref = Pervasives.ref false in
  try
    (String.iter (fun ch ->
       match ch, !needs_b with
       | 'a', false -> needs_b := true; ()
       | 'b', true  -> needs_b := false; ()
       | _, _       -> raise Not_found)
       str;
     if !needs_b then false else true)
  with
   | Not_found -> false".

Definition main_json_reference := premain reference_json_parser.
Definition main_json_reference_ocaml := premain_ocaml reference_json_parser_ocaml.

(*
(* val needs_b : bool Pervasives.ref;; *)
let needs_b = Pervasives.ref false;;

let chan = match Array.length Sys.argv with
| 0 | 1 -> Pervasives.stdin
| 2 -> let chan = Pervasives.open_in Sys.argv.(1)
       in Pervasives.at_exit (fun () -> Pervasives.close_in chan);
	  chan
| argc -> Pervasives.exit argc;;

(* val line : string;; *)
let line = Pervasives.input_line chan;;

String.iter (fun ch ->
  match ch, !needs_b with
  | 'a', false -> needs_b := true; ()
  | 'b', true  -> needs_b := false; ()
  | _, _       -> Pervasives.exit 1)
  line;;

Pervasives.exit 0;;
*)
(*
Definition test0 := json_parser "".
Definition test1 := json_parser "ab".
Definition str400 := "abababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababababab".
Definition test2 := json_parser (str400 ++ str400 ++ str400 ++ str400).

Recursive Extraction test0 test1 test2.
*)
