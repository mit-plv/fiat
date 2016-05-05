Require Import
        Coq.Vectors.Vector
        Coq.Vectors.VectorDef.

Require Import
        Fiat.Common.BoundedLookup.

Import Coq.Vectors.VectorDef.VectorNotations.
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
          | Vector.cons T n' v' => fun tag el => _
          end tag el).

  generalize v' (inj_SumType n' v') el0; clear; pattern n', tag0; apply Fin.caseS; simpl; intros.
  - destruct v'; simpl.
    + exact el0.
    + exact (inl el0).
  - destruct v'; simpl.
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
          | Vector.nil => fun el => match el with end
          | Vector.cons T _ v' => fun el => _
          end el).
  generalize (SumType_index _ v'); clear SumType_index; intros.
  destruct v'; simpl.
  - exact Fin.F1.
  - destruct el0.
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
          | Vector.nil => fun el => match el with end
          | Vector.cons T _ v' => fun el => _
          end el).
  generalize (SumType_proj _ v'); clear SumType_proj; intros.
  destruct v'; simpl.
  - exact el0.
  - destruct el0.
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
