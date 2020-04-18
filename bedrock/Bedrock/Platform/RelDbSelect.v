Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Wrap Bedrock.Platform.StringOps Bedrock.Platform.Malloc Bedrock.Platform.ArrayOps Bedrock.Platform.Buffers Bedrock.Platform.Bags.
Require Import Bedrock.Platform.SinglyLinkedList Bedrock.Platform.ListSegment Bedrock.Platform.RelDb Bedrock.Platform.RelDbCondition.

Set Implicit Arguments.

Local Hint Extern 1 (@eq W _ _) => words.


(** * Iterating over matching rows of a table *)

Opaque mult.
Local Infix ";;" := SimpleSeq : SP_scope.

Section Select.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  Variable tptr : W.
  Variable sch : schema.

  (* Store a pointer to the current linked list node and actual row data, respectively,
   * in these variables. *)
  Variables rw data : string.

  (* Test to use in filtering rows *)
  Variable cond : condition.

  (* Run this command on every matching row. *)
  Variable body : chunk.

  Definition inv (V_rw V_data : W) := (Ex head, Ex done, Ex remaining, Ex p,
    tptr =*> head * lseg done head V_rw
    * (V_rw ==*> V_data, p) * sll remaining p
    * rows sch head done * rows sch head remaining
    * [| freeable V_rw 2 |] * [| V_rw <> 0 |])%Sep.

  Definition Select' : chunk := (
    rw <-* tptr;;

    [Al bs, Al a : A, Al head, Al done, Al remaining,
      PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
        * tptr =*> head * lseg done head (V rw) * sll remaining (V rw)
        * rows sch head done * rows sch head remaining * invPre a V
      POST[R] array8 bs (V "buf") * invPost a V R]
    While (rw <> 0) {
      data <-* rw;;

      Assert [Al bs, Al a : A, Al head, Al done, Al remaining,
        PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
          * [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw) * sll (V data :: remaining) (V rw)
          * rows sch head remaining * rows sch head done * row sch (V data) * invPre a V
        POST[R] array8 bs (V "buf") * invPost a V R];;

      compileEqualities
      (fun a V => invPre a V
        * Ex head, Ex done, Ex remaining,
          [| V rw <> 0 |] * tptr =*> head * lseg done head (V rw) * sll (V data :: remaining) (V rw)
          * rows sch head remaining * rows sch head done)%Sep
      invPost
      sch data cond cond;;

      If ("matched" = 0) {
        Skip
      } else {
        body
      };;

      rw <-* rw + 4;;

      Assert [Al bs, Al a : A, Al head, Al done, Al remaining,
        PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
          * tptr =*> head * lseg_append (done ++ V data :: nil) head (V rw) * sll remaining (V rw)
          * rows sch head (done ++ V data :: nil) * rows sch head remaining * invPre a V
        POST[R] array8 bs (V "buf") * invPost a V R]
    }
  )%SP.

  Definition sinvar :=
    Al bs, Al a : A,
    PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
      * table sch tptr * invPre a V
    POST[R] array8 bs (V "buf") * invPost a V R.

  Definition spost :=
    Al bs, Al a : A,
    PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
      * row sch (V data) * inv (V rw) (V data) * invPre a V
    POST[R] array8 bs (V "buf") * invPost a V R.

  Notation svars := (rw :: data :: nil).

  Definition noOverlapExp (e : exp) :=
    match e with
      | Const _ => True
      | Input pos len => pos <> rw /\ pos <> data /\ len <> rw /\ len <> data
    end.

  Definition noOverlapExps := List.Forall noOverlapExp.

  Notation SelectVcs := (fun im ns res =>
    (~In "rp" ns) :: incl svars ns :: (rw <> "rp")%type :: (data <> "rp")%type
    :: incl baseVars ns
    :: (rw <> data)%type
    :: (forall a V V', (forall x, x <> rw -> x <> data
      -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> rw -> x <> data
      -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: (forall pre mn H,
      (forall specs st, interp specs (pre st)
        -> interp specs (spost true (fun w => w) ns res st))
      -> vcs (VerifCond (toCmd body mn (im := im) H ns res pre)))
    :: (forall specs pre mn H st,
      (forall specs st, interp specs (pre st)
        -> interp specs (spost true (fun w => w) ns res st))
      -> interp specs (Postcondition (toCmd body mn (im := im) H ns res pre) st)
      -> interp specs (spost true (fun w => w) ns res st))
    :: "array8"!"equal" ~~ im ~~> ArrayOps.equalS
    :: (res >= 10)%nat
    :: wfEqualities ns sch cond
    :: ("matched" <> rw)%type
    :: ("matched" <> data)%type
    :: (data <> "ibuf")%type
    :: (data <> "overflowed")%type
    :: (data <> "ipos")%type
    :: (data <> "ilen")%type
    :: (data <> "tmp")%type
    :: (data <> "len")%type
    :: (data <> "buf")%type
    :: In data ns
    :: (rw <> "rp")%type
    :: (rw <> "ibuf")%type
    :: (rw <> "ipos")%type
    :: (rw <> "ilen")%type
    :: (rw <> "tmp")%type
    :: (rw <> "len")%type
    :: (rw <> "buf")%type
    :: (rw <> "overflowed")%type
    :: goodSize (length sch)
    :: noOverlapExps (exps cond)
    :: nil).

  Hint Immediate incl_refl.

  Theorem Forall_impl3 : forall A (P Q R S : A -> Prop) ls,
    List.Forall P ls
    -> List.Forall Q ls
    -> List.Forall R ls
    -> (forall x : A, P x -> Q x -> R x -> S x)
    -> List.Forall S ls.
    induction 1; inversion 1; inversion 1; auto.
  Qed.

  Theorem inputOk_weaken_params : forall ns V V' es,
    inputOk V es
    -> noOverlapExps es
    -> wfExps ns es
    -> (forall x, x <> rw -> x <> data -> sel V x = sel V' x)
    -> rw <> "len"
    -> data <> "len"
    -> inputOk V' es.
    intros; eapply Forall_impl3; [ apply H | apply H0 | apply H1 | ].
    intro e; destruct e; simpl; intuition idtac.
    repeat rewrite <- H2 by (simpl; congruence); assumption.
  Qed.

  Hint Extern 2 (inputOk _ _) => eapply inputOk_weaken_params; try eassumption;
    try (eapply wfEqualities_wfExps; eassumption); [ descend ].

  Ltac q :=
    repeat match goal with
             | [ H : interp ?x ?y, _ : context[Binop _ _ Plus (immInR (natToW 4) _)] |- _ ] =>
               apply compileEqualities_post in H; auto; intros;
                 try match goal with
                       | [ H : interp x y |- _ ] => clear H
                     end;
                 try match goal with
                       | [ |- context[_ ===> _] ] => intros;
                         match goal with
                           | [ H : importsGlobal _ |- _ ] => clear dependent H
                         end
                     end;
                 pre; prep; evalu;
                 try match goal with
                       | [ _ : _ = _ :: ?ls |- _ ] => do 4 eexists; exists ls
                     end
             | [ H : interp ?x ?y |- _ ] => apply compileEqualities_post in H; auto; intros;
               try match goal with
                     | [ H : interp x y |- _ ] => clear H
                   end
             | [ H : _ |- vcs _ ] => apply H; intros; pre; unfold inv
             | [ |- vcs _ ] => apply compileEqualities_vcs; auto; intros
             | [ H : interp _ (Postcondition (toCmd body _ _ _ _ _) _) |- _ ] =>
               invoke1; unfold inv in *
           end; t.

  Definition Select : chunk.
    refine (WrapC Select'
      sinvar
      sinvar
      SelectVcs
      _ _); abstract (wrap0; abstract q).
  Defined.
End Select.

Global Opaque inv.
