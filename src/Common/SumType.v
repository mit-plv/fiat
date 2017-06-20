Require Import
        Coq.Vectors.Vector
        Coq.Vectors.VectorDef.

Require Import
        Fiat.Common.BoundedLookup.

Import Vectors.VectorDef.VectorNotations.
Local Open Scope vector_scope.
Local Open Scope string_scope.

Fixpoint SumType {n} (v : Vector.t Type n) {struct v} : Type :=
  match v with
  | Vector.nil => (False : Type)
  | Vector.cons T _ Vector.nil => T
  | Vector.cons T _ v' => T + (SumType v')
  end%type.

Arguments SumType : simpl never.

Fixpoint inj_SumType {n}
         (v : Vector.t Type n)
         (tag : Fin.t n)
         (el : Vector.nth v tag)
         {struct v} : SumType v.
  refine (match v in Vector.t _ n return
                forall
                  (tag : Fin.t n)
                  (el : Vector.nth v tag),
                  SumType v
          with
          | Vector.nil => fun tag el => Fin.case0 _ tag
          | Vector.cons T n' v' => fun tag0 el1 => _
          end tag el).
  generalize v' (inj_SumType n' v') el1; pattern n', tag0.
  eapply Fin.caseS; simpl.
  - intros ? v'0 ? ?; destruct v'0; simpl.
    + eapply el0.
    + exact (inl el0).
  - intros ? p v'0 ? ?; destruct v'0; simpl.
    + exact (Fin.case0 _ p).
    + exact (inr (X p el0)).
Defined.

Fixpoint SumType_index {n}
         (v : Vector.t Type n)
         (el : SumType v)
         {struct v} : Fin.t n.
  refine (match v in Vector.t _ n return
                SumType v -> Fin.t n
          with
          | Vector.nil => fun el' => match el' with end
          | Vector.cons T _ v' => fun el' => _
          end el).
  generalize (SumType_index _ v'); clear SumType_index; intros.
  destruct v'; simpl.
  - exact Fin.F1.
  - destruct el' as [|s].
    + exact Fin.F1.
    + exact (Fin.FS (X s)).
Defined.

Fixpoint SumType_proj {n}
         (v : Vector.t Type n)
         (el : SumType v)
         {struct v} : v[@SumType_index v el].
  refine (match v in Vector.t _ n return
                forall el : SumType v, v[@SumType_index v el]
          with
          | Vector.nil => fun el' => match el' with end
          | Vector.cons T _ v' => fun el' => _
          end el).
  generalize (SumType_proj _ v'); clear SumType_proj; intros.
  destruct v'; simpl.
  - exact el'.
  - destruct el' as [|s].
    + exact t.
    + exact (X s).
Defined.

Lemma inj_SumType_proj_inverse {n}
  : forall (v : Vector.t Type n)
           (el : SumType v),
    inj_SumType v _ (SumType_proj v el) = el.
Proof.
  induction v; simpl; intros.
  - destruct el.
  - destruct v.
    + simpl; reflexivity.
    + destruct el; simpl; eauto.
      f_equal; apply IHv.
Qed.

Lemma index_SumType_inj_inverse {n}
  : forall  (tag : Fin.t n)
            (v : Vector.t Type n)
            (el : Vector.nth v tag),
    SumType_index v (inj_SumType v tag el) = tag.
Proof.
  induction tag.
  - intro; pattern n, v; eapply Vector.caseS; simpl.
    clear; intros; destruct t; eauto.
  - intro; revert tag IHtag; pattern n, v; eapply Vector.caseS; simpl; intros.
    destruct t.
    + inversion tag.
    + f_equal.
      eapply IHtag.
Qed.

Lemma SumType_proj_inj {n} (v : Vector.t Type n):
  forall tag (P : forall (tag : Fin.t n),
                 VectorDef.nth v tag -> Type),
  forall el,
    P tag el ->
    P (SumType_index v (inj_SumType v tag el))
      (SumType_proj v (inj_SumType v tag el)).
  induction v.
  - simpl; inversion tag.
  - intro; revert v IHv; pattern n, tag;
      apply Fin.caseS.
    + intros.
      revert X.
      destruct v; simpl; eauto.
    + intros.
      eapply (IHv _ (fun tag => P (Fin.FS tag))) in X.
      simpl; destruct v.
      * inversion p.
      * apply X.
Qed.
