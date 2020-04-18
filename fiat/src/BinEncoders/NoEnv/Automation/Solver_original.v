Require Import Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.FixList
               Fiat.BinEncoders.NoEnv.Libraries.FixList2
               Fiat.BinEncoders.NoEnv.Libraries.SteppingList
               Fiat.BinEncoders.NoEnv.Libraries.Helpers.

Lemma func_unprod :
  forall (A B C : Type) (f : A * B -> C), (fun x => f (fst x, snd x)) = f.
Proof.
  Require Import Coq.Logic.FunctionalExtensionality.
  intuition.
  eapply functional_extensionality; intro x; destruct x; eauto.
Qed.

Ltac solve_predicate :=
  let hdata := fresh
  in  intro hdata; intuition; simpl in *;
    match goal with
    | |- context[ @fst ?a ?b hdata ] => solve [ pattern (@fst a b hdata); eauto ]
    | |- _ => solve [ intuition eauto ]
    | |- ?func _ =>
      let func_t := type of func
      in  solve [ unify ((fun _ => True) : func_t) func; intuition eauto ]
    end.

Ltac solve_unpack' e1 e2 ex proj d_t b_t :=
  match proj with
  | (fun bundle => FixList_getlength _) =>
                   eapply unpacking_decoder with
                    (project:=proj)
                    (encode1:=fun bundle => e1 (ex (fst bundle), snd bundle))
                    (encode2:=e2)
  | (fun bundle => (?proj1 (@?proj2 bundle))) =>
    match type of proj1 with
    | d_t -> _ => eapply unpacking_decoder with
                    (project:=proj)
                    (encode1:=fun bundle => e1 (ex (fst bundle), snd bundle))
                    (encode2:=e2)
    | ?d_t' -> _ => solve_unpack' e1 e2 (fun data : d_t' => ex (proj1 data)) proj2 d_t b_t
    end
  end.

Ltac solve_unpack :=
  match goal with
  | |- decoder _ ?encode =>
    match type of encode with
    | ?d_t * ?b_t -> _ =>
      match goal with
      | |- decoder _ (fun data => ?e1 (@?proj data, @?e2 data)) =>
        match type of e1 with
        | ?o_t * _ -> _ =>
          solve_unpack' e1 e2 (fun data : o_t => data) proj d_t b_t;
          repeat rewrite func_unprod
        end
      end
    end
  end.

Ltac solve_decoder :=
  (eauto with typeclass_instances) ||
  (match goal with
   | |- context [ SteppingList_encode _ ] => eapply SteppingList_decoder; eauto
   | |- context [ FixList_encode _  ] => eapply FixList_decoder
   | |- context [ FixList2_encode _ ] => eapply FixList2_decoder
   end).

Ltac solve_step' :=
  eapply strengthening_decoder; [ solve_decoder; solve_step' | solve_predicate ].

Ltac solve_step :=
  solve_unpack;
  [ solve_step' | solve_predicate | intro ].

Ltac solve_done :=
  let hdata := fresh in
  let hdata' := fresh in
  eexists; intro hdata; destruct hdata as [hdata' ?]; destruct hdata';
  intuition; simpl in *; subst; instantiate (1:=fun b => (_, b)); eauto.

Ltac enum_part eq_dec :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func in
    let h := fresh in
      evar (h:func_t);
      unify (fun n => if eq_dec n arg then res else h n) func;
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