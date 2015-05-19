Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Fiat.Common.
Require Coq.Vectors.Vector.

Section ilist.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Import Coq.Vectors.VectorDef.VectorNotations.

  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The type of indexed elements. *)

  Record prim_prod A B : Type :=
    { prim_fst : A;
      prim_snd : B }.

  Fixpoint ilist {n} (l : Vector.t A n) : Type :=
    match l with
      | [] => unit
      | a :: l => @prim_prod (B a) (ilist l)
    end.

  Definition icons
             (a : A)
             {n}
             {l : Vector.t A n}
             (b : B a)
             (il : ilist l)
  : ilist (a :: l)
    := {| prim_fst := b; prim_snd := il |}.

  Definition inil : ilist [] := tt.

  (* Get the car of an ilist. *)
  Definition ilist_hd {n} {As : Vector.t A n} (il : ilist As) :
    match As return ilist As -> Type with
      | a :: As' => fun il => B a
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist As),
            match As return ilist As -> Type with
              | a :: As' => fun il => B a
              | [] => fun _ => unit
            end il with
      | a :: As => fun il => prim_fst il
      | [] => fun il => tt
    end il.

  Definition ilist_hd' {n} {As : Vector.t A (S n)} (il : ilist As) :
    B (Vector.hd As)
    := Vector.caseS (fun n As => ilist As -> B (Vector.hd As))
                           (fun a As m => ilist_hd) As il.

  (* Get the cdr of an ilist. *)
  Definition ilist_tl {n} {As : Vector.t A n} (il : ilist As) :
    match As return ilist As -> Type with
      | a :: As' => fun il => ilist As'
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist As),
            match As return ilist As -> Type with
              | a :: As' => fun il => ilist As'
              | [] => fun _ => unit
            end il with
      | a :: As => fun il => prim_snd il
      | [] => fun il => tt
    end il.

  Definition ilist_tl'
             {n} {As : Vector.t A (S n)} (il : ilist As)
    : ilist (Vector.tl As) :=
    Vector.caseS (fun n As => ilist As -> ilist (Vector.tl As))
                 (fun a As m => ilist_tl) As il.

  Infix "++" := Vector.append : vector_scope.

  (* Appending ilists *)
  Fixpoint ilist_app {n} {As : Vector.t A n}
    : forall {n'} {As' : Vector.t A n'},  ilist As -> ilist As' -> ilist (As ++ As') :=
      match As return
            forall {n'} (As' : Vector.t A n'),
              ilist As -> ilist As' -> ilist (As ++ As') with
        | [] =>
          fun n' As' il il' => il'
        | a :: As'' =>
          fun n' As' il il' =>
            {| prim_fst := ilist_hd il;
               prim_snd := ilist_app (ilist_tl il) il' |}
      end.

  (* Membership in an indexed list. *)

  Inductive ilist_In {a : A} (b : B a)
  : forall {n} {As : Vector.t A n} (il : ilist As), Prop :=
  | In_hd : forall n' As' (il : ilist (n := n') As'),
              ilist_In b (icons b il)
  | In_tl : forall {n'} a' (b' : B a') As' (il : ilist (n := n') As'),
              ilist_In b il ->
              ilist_In b (icons b' il).

  (* Looking up the ith value, returning None for indices not in the Vector.t *)

  Fixpoint ith
           {m : nat}
           {As : Vector.t A m}
           (n : Fin.t m)
           (il : ilist As)
           {struct n}
    : B (Vector.nth As n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist As
            -> B (Vector.nth As n) with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist As
                                  -> B (Vector.nth As (@Fin.F1 n)))
                     (fun h n t => ilist_hd) As
    | Fin.FS k n' =>
      fun As =>
        Vector.caseS (fun n As => forall n',
                          ilist As
                          -> B (Vector.nth As (@Fin.FS n n')))
                     (fun h n t m il => ith m (ilist_tl il))
                     As n'
    end As il.

  Lemma ilist_invert {n} (As : Vector.t A n) (il : ilist As) :
    match As as As' return ilist As' -> Prop with
      | a :: As' => fun il => exists b il', il = icons b il'
      | [] => fun il => il = inil
    end il.
  Proof.
    destruct As; destruct il; simpl; unfold icons; eauto.
  Qed.

  Lemma ilist_invert' {n} (As : Vector.t A n) (il : ilist As) :
    match As as As' return ilist As' -> Type with
      | a :: As' => fun il => sigT (fun b => sigT (fun il' => il = icons b il'))
      | [] => fun il => il = inil
    end il.
  Proof.
    destruct As; destruct il; unfold icons; eauto.
  Qed.

  (* The [ith_induction] tactic is for working with lookups of bounded indices.
     It first inducts on n, then destructs the index Vector.t [As] and eliminates
     the contradictory cases, then finally destructs any indexed Vector.t in the
     context with Bounds of [As]. *)

End ilist.

(** ** Mapping a function over a(n i)[list], in two non-dependent ways *)
Section ilist_map.
  Context {A} (B : A -> Type).

  Import Coq.Vectors.VectorDef.VectorNotations.

  Fixpoint imap_list (f : forall a : A, B a) {n} (As : Vector.t A n) : ilist B As
    := match As with
         | [] => inil _
         | x :: xs => @icons _ B x _ _ (f x) (imap_list f xs)
       end.

End ilist_map.

Ltac icons_invert :=
  repeat match goal with
           | [il : ilist _ (_ :: _) |- _]
             => let il' := fresh "il" in
                let b' := fresh "b" in
                let il'_eq := fresh "il_eq" in
                generalize (ilist_invert il);
                  intros il'; destruct il' as [b' [il' il'_eq]]; subst
         end.

Section ilist_imap.

  (* Mapping a function over an indexed Vector.t. *)

  Import Coq.Vectors.VectorDef.VectorNotations.
  
  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the Vector.t. *)

  Fixpoint imap {n} (As : Vector.t A n)           
    : ilist B As -> ilist B' As :=
    match As return ilist B As -> ilist B' As with
    | [] => fun il => inil _
    | a :: As' => fun il => icons B' (f (ilist_hd _ il)) (imap As' (ilist_tl _ il))
    end.
        
  (* [imap] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith_imap :
    forall {n}
           (m : Fin.t n)
           (As : Vector.t A n)
           (il : ilist _ As),
      f (ith B m il) = ith B' m (imap As il).
  Proof.
    induction m; intro.
    - eapply Vector.caseS with (v := As); intros; simpl in *; destruct il; reflexivity.
    - revert m IHm.
      pattern n, As.
      match goal with
        |- ?P n As => 
        simpl; eapply (@Vector.rectS _ P); intros
      end.
      inversion m.
      eapply IHm.
  Qed.

End ilist_imap.

Section ilist_replace.

  Import Coq.Vectors.VectorDef.VectorNotations.
  
  (* Replacing an element of an indexed Vector.t. *)
  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)
  
  Fixpoint replace_Index
             {m}
             (n : Fin.t m)
             (As : Vector.t A m)
             (il : ilist B As)
             (new_b : B (Vector.nth As n))
             {struct n}
    : ilist B As := 
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist B As
            -> B (Vector.nth As n)
            -> ilist B As with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist B As
                                  -> B (Vector.nth As (@Fin.F1 n))
                                  -> ilist B As)
                     (fun h n t il new_b => icons B new_b (ilist_tl B il) ) As
    | Fin.FS k n' =>
      fun As =>
        Vector.caseS (fun n As => forall n',
                          ilist B As
                          -> B (Vector.nth As (@Fin.FS n n'))
                          -> ilist B As)
                     (fun h n t m il new_b => icons B (ilist_hd B il)
                                                    (@replace_Index _ m _ (ilist_tl B il) new_b))
                     As n'
    end As il new_b.

  Lemma ith_replace_Index_neq {m}
    : forall
      (n n' : Fin.t m)
      (As : Vector.t A m)
      (il : ilist B As)
      (new_b : B (Vector.nth As n')),
      n <> n'
      -> ith B n (replace_Index n' As il new_b) = ith B n il.
  Proof.
    intros n n'; pattern m, n, n'.
    match goal with
      |- ?P m n n' => simpl; eapply (Fin.rect2 P); intros
    end.
    - congruence.
    - generalize il f new_b; clear f new_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As => 
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - generalize il f new_b; clear f new_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As => 
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - assert (f <> g) by congruence.
      generalize il f g new_b H H1; clear f g new_b il H H1 H0.
      pattern n0, As.
      match goal with
        |- ?P n0 As => 
        simpl; apply (@Vector.caseS _ P); intros;
        eapply (H _ (prim_snd il) new_b); eauto
      end.
  Qed.

  Lemma ith_replace_Index_eq {m}
    : forall
      (n : Fin.t m)
      (As : Vector.t A m)
      (il : ilist _ As)
      (new_b : B (Vector.nth As n)),
      ith B n (replace_Index n As il new_b) = new_b.
  Proof.
    induction n; simpl.
    - intro As; pattern n, As.
      match goal with
        |- ?P n As => 
        simpl; apply (@Vector.caseS _ P); intros; reflexivity
      end.
    - intro As; revert n0 IHn; pattern n, As.
      match goal with
        |- ?P n As =>
        simpl; apply (@Vector.caseS _ P); simpl; eauto
      end.
  Qed.

End ilist_replace.

