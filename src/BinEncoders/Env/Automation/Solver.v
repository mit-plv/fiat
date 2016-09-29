Require Import
        Fiat.Common.DecideableEnsembles
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Common.Sig
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.BinLib.Char
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Enum
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.Lib.IList
        Fiat.BinEncoders.Env.Lib.SteppingCacheList.

Ltac apply_compose :=
  intros;
  match goal with
    H : cache_inv_Property ?P ?P_inv |- _ =>
    first [eapply (compose_encode_correct_no_dep _ H); clear H
          | eapply (compose_encode_correct H); clear H
          | eapply (composeIf_encode_correct H); clear H;
            [ |
              | solve [intros; intuition (eauto with bin_split_hints) ]
              | solve [intros; intuition (eauto with bin_split_hints) ] ]
          ]
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac shelve_inv :=
  let H' := fresh in
  let data := fresh in
  intros data H';
  repeat destruct H';
  match goal with
  | H : ?P data |- ?P_inv' =>
    is_evar P;
    let P_inv' := (eval pattern data in P_inv') in
    let P_inv := match P_inv' with ?P_inv data => P_inv end in
    let new_P_T := type of P in
    makeEvar new_P_T
             ltac:(fun new_P =>
                     unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
  end.

(* Solves data invariants using the data_inv_hints database *)
Ltac solve_data_inv :=
  first [ simpl; intros; exact I
        | solve [intuition eauto with data_inv_hints]
        | shelve_inv ].

Ltac start_synthesizing_decoder :=
  (* Unfold encoder specification and the data and packet invariants *)
  repeat
    match goal with
      |- appcontext [encode_decode_correct_f _ _ ?dataInv ?restInv ?encodeSpec] =>
      first [unfold dataInv
            | unfold restInv
            | unfold encodeSpec ]
    | |- appcontext [encode_decode_correct_f _ _ ?dataInv ?restInv (?encodeSpec _)] =>
      first [unfold dataInv
            | unfold restInv
            | unfold encodeSpec ]
    end;

  (* Memoize any string constants *)
  pose_string_hyps;
  (* Initialize the various goals with evars *)
  eexists (_, _), _; split; simpl.

Ltac build_fully_determined_type :=
  (* Build the parsed object by showing it can be built *)
  (* from previously parsed terms and that and that the *)
  (* byte string was a valid encoding of this object. *)
  (* Start by destructing the encoded object  *)
  let a' := fresh in
  intros a'; repeat destruct a' as [? a'];
  (* Show that it is determined by the constraints (equalities) *)
  (* inferred during parsing. *)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros;
  (* Decompose data predicate *) intuition;
  (* Substitute any inferred equalities *) subst;
  (* And unify with original object *) reflexivity.

Ltac decide_data_invariant :=
  (* Show that the invariant on the data is decideable. Most *)
  (* of the clauses in this predicate are obviously true by *)
  (* construction, but there may be some that need to be checked *)
  (* by a decision procedure*)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros; intuition;
  repeat
    first [eapply decides_and
          | eapply decides_assumption; eassumption
          | apply decides_eq_refl
          | eapply decides_dec_eq; auto using Peano_dec.eq_nat_dec, weq ].

Ltac decode_step :=
  (* Processes the goal by either: *)
  match goal with
  (* A) decomposing one of the parser combinators, *)
  | |- _ => apply_compose
  (* B) applying one of the rules for a base type  *)
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_Vector_Spec _) _ _] =>
    intros; eapply Vector_decode_correct
  | H : cache_inv_Property _ _
    |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    intros; revert H; eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_nat_Spec _) _ _] =>
    eapply Nat_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_enum_Spec _) _ _] =>
    eapply Enum_decode_correct
  (* C) Discharging a side condition of one of the base rules *)
  | |- NoDupVector _ => Discharge_NoDupVector
  | |- context[Vector_predicate_rest (fun _ _ => True) _ _ _ _] =>
    intros; apply Vector_predicate_rest_True
  | _ => solve [solve_data_inv]
  (* D) Solving the goal once all the byte string has been parsed *)
  | _ =>  solve [simpl; intros;
                 eapply encode_decode_correct_finish;
                 [ build_fully_determined_type
                 | decide_data_invariant ] ]
  end.

Ltac synthesize_cache_invariant :=
  (* Synthesize an invariant satisfying the derived constraints *)
  (* on the cache. *)
  solve [repeat (instantiate (1 := fun _ => True));
         unfold cache_inv_Property; intuition].

Ltac synthesize_decoder :=
  (* Combines tactics into one-liner. *)
  start_synthesizing_decoder;
    [ repeat decode_step
    | cbv beta; synthesize_cache_invariant ].


(* Older tactics follow, leaving in for now for backwards compatibility. *)



Ltac enum_part eq_dec :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func in
    let h := fresh in
      evar (h:func_t);
      unify (fun n => if eq_dec _ n arg then res else h n) func;
      reflexivity
  end.

Ltac enum_finish :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func
    in  unify ((fun _  => res) : func_t) func;
        reflexivity
  end.

Ltac idtac' :=
  match goal with
    | |- _ => idtac (* I actually need this idtac for some unknown reason *)
  end.

Definition FixInt_eq_dec (size : nat) (n m : {n | (N.lt n (exp2 size))%N }) : {n = m} + {~ n = m}.
  refine (if N.eq_dec (proj1_sig n) (proj1_sig m) then left _ else right _);
    destruct n; destruct m; try congruence; simpl in *; rewrite <- sig_equivalence; eauto.
Defined.

Ltac solve_enum :=
  let h := fresh in
  intros h; destruct h;
  [ idtac'; enum_part FixInt_eq_dec ..
  | idtac'; enum_finish ].

Ltac solve_done :=
  intros ? ? ? ? data ? ? ? ?;
    instantiate (1:=fun _ b e => (_, b, e));
    intros; destruct data; simpl in *; repeat match goal with
                   | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
                   | H : _ /\ _ |- _ => inversion H; subst; clear H
                   end; intuition eauto; fail 0.

Ltac solve_predicate :=
  unfold SteppingList_predicate, IList_predicate, FixList_predicate;
  intuition eauto; instantiate (1:=fun _ => True); solve_predicate.

Ltac eauto_typeclass :=
  match goal with
  | |- context [ Bool_encode ] => eapply Bool_encode_correct
  | |- context [ Char_encode ] => eapply Char_encode_correct
  | |- context [ FixInt_encode ] => eapply FixInt_encode_correct
  | |- context [ FixList_encode _ ] => eapply FixList_encode_correct
  | |- context [ IList_encode _ ] => eapply IList_encode_correct
  | |- context [ SteppingList_encode _ _ _ ] => eapply SteppingList_encode_correct
  end; eauto.

Ltac solve_decoder :=
  match goal with
  | |- _ => solve [ eauto_typeclass; solve_decoder ]
  | |- _ => solve [ eapply Enum_encode_correct; solve_enum ]
  | |- _ => solve [ solve_done ]
  | |- _ => eapply compose_encode_correct; [ solve_decoder | solve_predicate | intro; solve_decoder ]
  end.
