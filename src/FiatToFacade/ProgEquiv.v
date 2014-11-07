
Definition ProgEquiv {av} p1 p2 := 
  forall env st1 st2,
    (@RunsTo av env p1 st1 st2 <-> RunsTo env p2 st1 st2). 

Require Import Setoid.

Add Parametric Relation {av} : (Stmt) (@ProgEquiv av)
    reflexivity proved by _
    symmetry proved by _
    transitivity proved by _
      as prog_equiv. 
Proof.
  firstorder.
  firstorder.
  unfold Transitive, ProgEquiv; intros; etransitivity; eauto.
Qed.

Show.

(* Uh? *)
unfold Transitive, ProgEquiv; intros; etransitivity; eauto.

Add Parametric Morphism {av: Type} :
  (@RunsTo av)
    with signature (eq ==> @ProgEquiv av ==> eq ==> eq ==> iff)
      as runsto_morphism.
Proof.
  unfold ProgEquiv; intros * prog_equiv ** ; apply prog_equiv; assumption.
Qed.

Add Parametric Morphism {av} :
  (Seq)
    with signature (@ProgEquiv av ==> @ProgEquiv av ==> @ProgEquiv av)
      as seq_morphism.
Proof.  
  unfold ProgEquiv; intros.

  split; intro runs_to; inversion_clear' runs_to; econstructor; [
    rewrite <- H | rewrite <- H0 |
    rewrite -> H | rewrite -> H0 ];
  eauto; reflexivity.
Qed.

Lemma while_morph {av env} :
  forall while_p1,
  forall (st1 st2: State av),
    RunsTo env (while_p1) st1 st2 ->
    forall p1 p2 test,
      while_p1 = Facade.While test p1 -> 
      @ProgEquiv av p1 p2 ->
      RunsTo env (Facade.While test p2) st1 st2.
Proof.
  unfold ProgEquiv; induction 1; intros ** equiv; subst; try discriminate; autoinj.

  econstructor; eauto; rewrite <- equiv; assumption.
  constructor; trivial.
Qed.  
  
Add Parametric Morphism {av} :
  (Facade.While)
    with signature (eq ==> @ProgEquiv av ==> @ProgEquiv av)
      as while_morphism.
Proof.  
  split; intros; eapply while_morph; eauto; symmetry; assumption.
Qed.

Add Parametric Morphism {av} :
  (Facade.If)
    with signature (eq ==> @ProgEquiv av ==> @ProgEquiv av ==> @ProgEquiv av)
      as if_morphism.
Proof.  
  unfold ProgEquiv; intros * true_equiv * false_equiv ** .
  split; intro runs_to; inversion_clear' runs_to;
  [ constructor 3 | constructor 4 | constructor 3 | constructor 4];
  rewrite ?true_equiv, ?false_equiv in *; try assumption.
Qed.
  
Lemma Skip_Seq av :
  forall prog, 
    @ProgEquiv av (Seq Skip prog) prog. 
Proof.
  unfold ProgEquiv; split; intros.
  inversion_clear' H; inversion_clear' H2; eauto.
  repeat (econstructor; eauto).
Qed.

Lemma Seq_Skip av :
  forall prog, 
    @ProgEquiv av (Seq prog Skip) prog.
Proof.
  unfold ProgEquiv; split; intros.
  inversion_clear' H; inversion_clear' H5; eauto.
  repeat (econstructor; eauto).
Qed.
