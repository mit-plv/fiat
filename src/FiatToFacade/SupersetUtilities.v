Require Import Coq.Program.Program.
Require Import Bedrock.Platform.Cito.StringMap.
Require Import FiatToFacade.Utilities FiatToFacade.Superset FiatToFacade.SupersetMorphisms
               FiatToFacade.StringMapNotations FiatToFacade.StringMapUtilities.
Require Import Facade.DFacade.

Unset Implicit Arguments.

Lemma Superset_mapsto :
  forall {elt welt} {k v state map} wrapper,
    @Superset elt welt state ([k >> wrapper v]::map) wrapper ->
    state[k >> wrapper v].
Proof.
  unfold Superset; intros * add.
  apply add; map_iff_solve intuition.
Qed.

Lemma SomeSCAs_mapsto :
  forall {av} {state: State av} {k v map},
    SomeSCAs state ([k >sca> v]::map) ->
    state[k >> SCA _ v].
Proof.
  intros *; apply Superset_mapsto.
Qed.

Lemma AllADTs_mapsto :
  forall {av} {state: State av} {k v map},
    AllADTs state ([k >adt> v]::map) ->
    state[k >> ADT v].
Proof.
  unfold AllADTs; intros * (? & ?); eapply Superset_mapsto; eauto.
Qed.

Lemma Superset_remove :
  forall {elt welt} {k v state map} wrapper,
    @Superset elt welt state ([k >> wrapper v]::map) wrapper ->
    @Superset elt welt state (StringMap.remove k map) wrapper.
Proof.
  unfold Superset; intros.
  apply H. rewrite StringMapFacts.remove_mapsto_iff in *.
  destruct_pairs; map_iff_solve assumption.
Qed.

Lemma SomeSCAs_remove :
  forall {av} {state: State av} {k v map},
    SomeSCAs state ([k >sca> v]::map) ->
    SomeSCAs state (StringMap.remove k map).
Proof.
  intros *; apply Superset_remove.
Qed.

Lemma AllADTs_remove :
  forall {av} {state: State av} {k v map},
    AllADTs state ([k >adt> v]::map) ->
    Superset state (StringMap.remove k map) (@ADT _).
Proof.
  unfold AllADTs; intros * (? & ?); eapply Superset_remove; eauto.
Qed.

Lemma Superset_swap_remove :
  forall {elt welt} {k1 k2 v state map} wrapper,
    k1 <> k2 ->
    @Superset elt welt state (StringMap.remove k1 ([k2 >> wrapper v]::map)) wrapper ->
    @Superset elt welt state ([k2 >> wrapper v]::(StringMap.remove k1 map)) wrapper.
Proof.
  unfold Superset; intros.
  apply H0. map_iff_solve idtac.

  destruct (StringMap.E.eq_dec k k1); subst.
  rewrite StringMapFacts.add_neq_mapsto_iff in * by congruence.
  rewrite StringMapFacts.remove_mapsto_iff in *; destruct_pairs; assumption.
  congruence.

  destruct (StringMap.E.eq_dec k k2); subst; map_iff_solve idtac;
  rewrite StringMapFacts.add_mapsto_iff in *;
  rewrite StringMapFacts.remove_mapsto_iff in *;
  intuition.
Qed.

Lemma SomeSCAs_swap_remove :
  forall {av} {state: State av} {k1 k2 v map},
    k1 <> k2 ->
    SomeSCAs state (StringMap.remove k1 ([k2 >sca> v]::map)) ->
    SomeSCAs state ([k2 >sca> v]::(StringMap.remove k1 map)).
Proof.
  intros *; apply Superset_swap_remove.
Qed.

Lemma AllADTs_swap_remove :
  forall {av} {state: State av} {k1 k2 v map},
    k1 <> k2 ->
    AllADTs state (StringMap.remove k1 ([k2 >adt> v]::map)) ->
    Superset state ([k2 >> ADT v]::(StringMap.remove k1 map)) (@ADT _).
Proof.
  unfold AllADTs; intros * ? (? & ?); eapply Superset_swap_remove; eauto.
Qed.

Lemma Superset_empty :
  forall {elt welt} state wrapper,
    @Superset elt welt state ∅ wrapper.
Proof.
  unfold Superset; intros; rewrite StringMapFacts.empty_mapsto_iff in *; exfalso; assumption.
Qed.

Lemma SomeSCAs_empty :
  forall {av} state,
    @SomeSCAs av state ∅ .
Proof.
  intros; apply Superset_empty.
Qed.

(* No AllADTs_empty *)

Lemma Superset_chomp_left :
  forall {elt welt} {k v state map} wrapper,
    ~ StringMap.In k map ->
    @Superset elt welt state map wrapper ->
    @Superset elt welt ([k >> wrapper v]::state) map wrapper.
Proof.
  unfold Superset; intros ** k' v' mapsto.
  destruct (StringMap.E.eq_dec k k'); subst;
  map_iff_solve idtac; try solve [intuition].
  exfalso. apply StringMapFacts.MapsTo_In in mapsto; intuition.
Qed.

Lemma SomeSCAs_chomp_left :
  forall {av} {k v state map},
    ~ StringMap.In k map ->
    @SomeSCAs av state map ->
    @SomeSCAs av ([k >sca> v]::state) map.
Proof.
  intros; apply Superset_chomp_left; intuition.
Qed.

(* chomp_left could work for AllADTs, if needed, too *)

Lemma Superset_chomp :
  forall {elt welt} {k v state map} wrapper,
    @Superset elt welt state map wrapper ->
    @Superset elt welt ([k >> wrapper v]::state) ([k >> wrapper v]::map) wrapper.
Proof.
  unfold Superset; intros * h ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k');
    subst; rewrite StringMapFacts.add_mapsto_iff in *;
    intuition.
Qed.

Lemma SomeSCAs_chomp :
  forall {av} (state: State av) k v scas,
    SomeSCAs state scas ->
    SomeSCAs ([k >sca> v]::state) ([k >sca> v]::scas).
Proof.
  intros *; apply Superset_chomp.
Qed.

Lemma AllADTs_chomp :
  forall {av} (state: State av) k v adts,
    AllADTs state adts ->
    AllADTs ([k >adt> v]::state) ([k >adt> v]::adts).
Proof.
  unfold AllADTs; split; apply Superset_chomp; tauto.
Qed.

Lemma Superset_chomp_remove :
  forall {elt welt} {k v state map} wrapper,
    @Superset elt welt (StringMap.remove k state) (StringMap.remove k map) wrapper ->
    @Superset elt welt ([k >> wrapper v]::state) ([k >> wrapper v]::map) wrapper.
Proof.
  unfold Superset; intros * h ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k');
    subst; rewrite StringMapFacts.add_mapsto_iff in *;
    setoid_rewrite StringMapFacts.remove_mapsto_iff in h;
    intuition.
Qed.

Lemma SomeSCAs_chomp_remove :
  forall {av} (state: State av) k v scas,
    SomeSCAs (StringMap.remove k state) (StringMap.remove k scas) ->
    SomeSCAs ([k >sca> v]::state) ([k >sca> v]::scas).
Proof.
  intros *; apply Superset_chomp_remove.
Qed.

Lemma AllADTs_chomp_remove :
  forall {av} (state: State av) k v adts,
    AllADTs (StringMap.remove k state) (StringMap.remove k adts) ->
    AllADTs ([k >adt> v]::state) ([k >adt> v]::adts).
Proof.
  unfold AllADTs; split; apply Superset_chomp_remove; tauto.
Qed.


Lemma Superset_swap_left :
  forall {elt welt} {k1 k2 v1 v2 state map} wrapper,
    k1 <> k2 ->
    @Superset elt welt ([k1 >> v1]::[k2 >> v2]::state) map wrapper ->
    @Superset elt welt ([k2 >> v2]::[k1 >> v1]::state) map wrapper.
Proof.
  unfold Superset; intros ** k v mp.
  destruct (StringMap.E.eq_dec k k1), (StringMap.E.eq_dec k k2);
    subst; map_iff_solve idtac; try discriminates;
    specialize (H0 _ _ mp);
    repeat setoid_rewrite StringMapFacts.add_mapsto_iff in H0;
    intuition.
Qed.

Lemma Superset_swap_right :
  forall {elt welt} {k1 k2 v1 v2 state map} wrapper,
    k1 <> k2 ->
    @Superset elt welt map ([k1 >> v1]::[k2 >> v2]::state) wrapper ->
    @Superset elt welt map ([k2 >> v2]::[k1 >> v1]::state) wrapper.
Proof.
  unfold Superset; intros ** k v mp.
  destruct (StringMap.E.eq_dec k k1), (StringMap.E.eq_dec k k2);
    subst; map_iff_solve idtac; try discriminates;
    rewrite MapsTo_swap in mp by auto; specialize (H0 _ _ mp);
    repeat setoid_rewrite StringMapFacts.add_mapsto_iff in H0;
    intuition.
Qed.

Lemma AllADTs_swap :
  forall {av} {state: State av} {k1 k2 v1 v2 map},
    k1 <> k2 ->
    @AllADTs av ([k1 >> v1]::[k2 >> v2]::state) map ->
    @AllADTs av ([k2 >> v2]::[k1 >> v1]::state) map.
Proof.
  unfold AllADTs; intros; split; destruct_pairs.
  apply Superset_swap_left; trivial.
  apply Superset_swap_right; trivial.
Qed.

Lemma AllADTs_swap_iff :
  forall (av : Type) (state : State av) (k1 k2 : StringMap.key)
         (v1 v2 : Value av) (map : StringMap.t (Value av)),
    k1 <> k2 ->
    (AllADTs ([k1 >> v1]::[k2 >> v2]::state) map <->
     AllADTs ([k2 >> v2]::[k1 >> v1]::state) map).
Proof.
  split; eauto using AllADTs_swap.
Qed.

Lemma AllADTs_swap_left_iff :
  forall (av : Type) (state : State av) (k1 k2 : StringMap.key)
         (v1 v2 : Value av) (map : StringMap.t (Value av)),
    k1 <> k2 ->
    (AllADTs map ([k1 >> v1]::[k2 >> v2]::state) <->
     AllADTs map ([k2 >> v2]::[k1 >> v1]::state)).
Proof.
  split; intros; symmetry; apply AllADTs_swap; try symmetry; try congruence.
Qed.

Lemma Superset_mapsto' :
  forall {elt welt} k v st map wrapper,
    @Superset elt welt st map wrapper ->
    map[k >> wrapper v] ->
    st[k >> wrapper v].
Proof.
  unfold Superset; intros * h ** maps_to.
  apply (h _ _ maps_to).
Qed.

Lemma SomeSCAs_mapsto' :
  forall {av} k v st scas,
    @SomeSCAs av st scas ->
    scas[k >> SCA _ v] ->
    st[k >> SCA _ v].
Proof.
  eauto using Superset_mapsto'.
Qed.

Lemma AllADTs_mapsto' :
  forall {av} k v st adts,
    @AllADTs av st adts ->
    adts[k >> ADT v] ->
    st[k >> ADT v].
Proof.
  intros * (h & _) **. eauto using Superset_mapsto'.
Qed.

Lemma Superset_add_in_left :
  forall {elt welt} st bindings k v wrapper,
    bindings[k >> wrapper v] ->
    @Superset elt welt st bindings wrapper ->
    Superset ([k >> wrapper v]::st) bindings wrapper.
Proof.
  unfold Superset; intros ** k' v' ? .
  destruct (StringMap.E.eq_dec k k'); subst;
  try match goal with (* TODO fix auto_mapsto_unique *)
        | H:(?st) [?k >> ?v], H':(?st) [?k >> ?v'] |- _ =>
          let h := fresh in
          pose proof (MapsTo_unique st k v v' H H') as h
      end; map_iff_solve intuition.
Qed.

Lemma Superset_add_in_right :
  forall {elt welt} st bindings k v wrapper,
    st[k >> wrapper v] ->
    @Superset elt welt st bindings wrapper ->
    Superset st ([k >> wrapper v]::bindings) wrapper.
Proof.
  unfold Superset; intros ** k' v' ? .
  destruct (StringMap.E.eq_dec k k'); subst;
  try match goal with (* TODO fix mapsto_unique *)
        | H:(?st) [?k >> ?v], H':(?st) [?k >> ?v'] |- _ =>
          let h := fresh in
          pose proof (MapsTo_unique st k v v' H H') as h;
            rewrite !h in *; clear H
      end;
  map_iff_solve intuition;
  rewrite StringMapFacts.add_mapsto_iff in *; intuition;
  match goal with
    | H: wrapper _ = wrapper _ |- _ => rewrite H in *
  end; intuition.
Qed.

Lemma AllADTs_add_in :
  forall {av} st bindings k v,
    bindings[k >> @ADT av v] ->
    AllADTs st bindings ->
    AllADTs ([k >> ADT v]::st) bindings.
Proof.
  unfold AllADTs; split; intros;
  destruct_pairs; eauto using Superset_add_in_left, Superset_add_in_right.
Qed.

Lemma Superset_not_In_remove :
  forall {elt welt} k state map wrapper,
    ~ StringMap.In k map ->
    @Superset elt welt state map wrapper ->
    @Superset elt welt (StringMap.remove k state) map wrapper.
Proof.
  unfold Superset; intros ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k'); subst.

  pose proof (StringMapFacts.MapsTo_In maps_to); exfalso; intuition.
  map_iff_solve intuition.
Qed.

Lemma Superset_remove_self :
  forall {elt welt} k state wrapper,
    @Superset elt welt state (StringMap.remove k state) wrapper.
Proof.
  unfold Superset; intros *; map_iff_solve intuition.
Qed.

Lemma AllADTs_not_In_remove_left :
  forall {av} k state map,
    ~ StringMap.In k map ->
    @AllADTs av state map ->
    @AllADTs av (StringMap.remove k state) map.
Proof.
  unfold AllADTs; split; intros; destruct_pairs.

  apply Superset_not_In_remove; intuition.
  eapply superset_Transitive; try eassumption.
  eauto using Superset_remove_self.
Qed.

Lemma AllADTs_not_In_remove_right :
  forall {av} k state map,
    ~ StringMap.In k map ->
    @AllADTs av map state ->
    @AllADTs av map (StringMap.remove k state).
Proof.
  symmetry. apply AllADTs_not_In_remove_left; trivial; symmetry; assumption.
Qed.

Lemma SomeSCAs_not_In_remove :
  forall {av} k state map,
    ~ StringMap.In k map ->
    @SomeSCAs av state map ->
    @SomeSCAs av (StringMap.remove k state) map.
Proof.
  intros *; apply Superset_not_In_remove.
Qed.

(* AllADTs/SomeSCAs specific *)

Lemma add_adts_pop_sca :
  forall {av} k v map (state: State av),
    ~ StringMap.In k map ->
    AllADTs state map ->
    AllADTs ([k >sca> v]::state) map.
Proof.
  setoid_rewrite AllADTs_equiv.
  intros ** k' v'.
  destruct (StringMap.E.eq_dec k k'); subst;
  split; intros H';
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac.

  apply StringMapFacts.MapsTo_In in H'; congruence.
  intuition; discriminate.

  rewrite H0 in *; intuition.
  rewrite H0 in *; intuition.
Qed.

Lemma add_sca_pop_adts :
  forall {av} k v map (state: State av),
    ~ StringMap.In k map ->
    SomeSCAs state map ->
    SomeSCAs ([k >adt> v]::state) map.
Proof.
  intros ** k' v'.
  destruct (StringMap.E.eq_dec k k'); subst;
  intros H';
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac.

  apply StringMapFacts.MapsTo_In in H'; congruence.
  intuition; discriminate.
Qed.

Lemma SomeSCAs_mapsto_inv:
  forall {av} state scas k v,
    state[k >> SCA av v] ->
    SomeSCAs state scas ->
    SomeSCAs state ([k >sca> v]::scas).
Proof.
  unfold SomeSCAs, Superset; intros * ? * some_scas ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k'); rewrite StringMapFacts.add_mapsto_iff in *;
  subst; intuition. autoinj.
Qed.

Lemma Superset_replace_right :
  forall {elt welt} k v v' state map wrapper,
    @Superset elt welt state ([k >> v]::map) wrapper ->
    @Superset elt welt ([k >> v']::state) ([k >> v']::map) wrapper.
Proof.
  unfold Superset; intros ** k'' v'' maps_to.
  destruct (StringMap.E.eq_dec k k''); subst;
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac; [ | apply H ];
  map_iff_solve intuition.
Qed.

Lemma Superset_replace_left :
  forall {elt welt} k v v' state map wrapper,
    @Superset elt welt ([k >> v]::state) map wrapper ->
    @Superset elt welt ([k >> v']::state) ([k >> v']::map) wrapper.
Proof.
  unfold Superset; intros ** k'' v'' maps_to.
  destruct (StringMap.E.eq_dec k k''); subst;
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac; intuition.
  specialize (H _ _ H2);
    rewrite StringMapFacts.add_mapsto_iff in *;
    intuition.
Qed.

(* Not translated for SomeSCAs *)

Lemma AllADTs_replace :
  forall {av} k v v' state map,
    @AllADTs av state ([k >> v]::map) ->
    @AllADTs av ([k >> v']::state) ([k >> v']::map).
Proof.
  unfold AllADTs; split; intros;
  [ eapply Superset_replace_right
  | eapply Superset_replace_left ];
  intuition eassumption.
Qed.

(* AllADTs specific *)

Lemma AllADTs_not_in :
  forall {av} {var map state},
    @AllADTs av state map ->
    ~ StringMap.In (elt:=Value av) var map ->
    (exists v, StringMap.find var state = Some (SCA _ v)) \/ ~ StringMapFacts.M.In var state.
Proof.
  unfold AllADTs; intros.
  destruct (StringMap.find var state) eqn:eq0.

  destruct v.
  left; eexists; reflexivity.
  destruct_pairs.
  rewrite <- StringMapFacts.find_mapsto_iff in eq0.
  apply H1 in eq0.
  apply StringMapFacts.MapsTo_In in eq0.
  congruence.

  rewrite StringMapFacts.not_find_in_iff; right; assumption.
Qed.

Lemma AllADTs_chomp_remove' :
  forall {av} k state map,
    @AllADTs av map state ->
    @AllADTs av (StringMap.remove k map) (StringMap.remove k state).
Proof.
  unfold AllADTs, Superset; split; intros *; map_iff_solve intuition.
Qed.

Lemma not_in_adts_not_mapsto_adt :
  forall {av} var state map,
    @AllADTs av state map ->
    ~ StringMap.In var map ->
    not_mapsto_adt var state = true.
Proof.
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p;
  intros * h h'.
  destruct (AllADTs_not_in h h') as [ [ v sbst ] | ];
    [ rewrite sbst; trivial  | ].

  rewrite StringMapFacts.not_in_find; trivial.
Qed.

(* Tactics *)
Ltac specialize_initial_state :=
  repeat match goal with
           | [ H: (forall initial_state : State _,
                     ?init_knowledge /\
                     SomeSCAs initial_state ?init_scas /\
                     AllADTs initial_state ?init_adts -> _),
               Hknowledge: ?init_knowledge,
               Hscas: SomeSCAs ?initial_state ?init_scas,
               Hadts: AllADTs ?initial_state ?init_adts
               |- _] => specialize (H _ (conj Hknowledge (conj Hscas Hadts)))
         end.

Ltac specialize_final_state :=
  repeat match goal with
           | [ H: (forall final_state : State _,
                     RunsTo ?env ?prog ?initial_state final_state -> _),
               Hruns: RunsTo ?env ?prog ?initial_state ?final_state
               |- _ ] => specialize (H _ Hruns)
         end.

Ltac specialize_states :=
  repeat (specialize_initial_state;
          specialize_final_state).

Ltac supersets_mapsto H mapsto remove swap_remove :=
  progress (let maps_to := fresh "maps_to" in
            let superset := fresh "superset" in
            pose proof mapsto as maps_to;
            pose proof remove as superset;
            try (apply swap_remove in superset; [ | solve [auto] ]);
            clear_dups).

Ltac scas_adts_mapsto_one :=
  trickle_deletion;
  repeat match goal with
           | [ H: SomeSCAs ?state ([?k >sca> ?v]::?map) |- _ ] =>
             supersets_mapsto H (SomeSCAs_mapsto H) (SomeSCAs_remove H) @SomeSCAs_swap_remove
           | [ H: AllADTs ?state ([?k >adt> ?v]::?map) |- _ ] =>
             supersets_mapsto H (AllADTs_mapsto H) (AllADTs_remove H) @Superset_swap_remove
           | [ H: Superset ?state ([?k >> ?wrapper ?v]::?map) ?wrapper |- _ ] =>
             supersets_mapsto H (Superset_mapsto _ H) (Superset_remove _ H) @Superset_swap_remove
           | [ H: ?adts[?k >> ?v], H': AllADTs ?state ?adts |- _ ] =>
             progress (pose proof (AllADTs_mapsto' _ _ _ _ H' H); clear_dups)
           | [ H: ?scas[?k >> ?v], H': SomeSCAs ?state ?adts |- _ ] =>
             progress (pose proof (SomeSCAs_mapsto' _ _ _ _ H' H); clear_dups)
           | [ H: ?scas[?k >> ?v], H': SomeSCAs ?state ?adts |- _ ] =>
             progress (pose proof (Superset_mapsto' _ _ _ _ H' H); clear_dups)
         end.

Ltac scas_adts_mapsto :=
  repeat (scas_adts_mapsto_one; scas_adts_mapsto_one); try scas_adts_mapsto_one.
