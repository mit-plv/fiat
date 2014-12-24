Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith ADTSynthesis.Common.ilist.

Section i2list.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The type of indexed elements. *)
  Variable C : forall a, B a ->  Type. (* The type of doubly-indexed elements. *)

  Inductive i2list : forall (As : list A), ilist B As -> Type :=
  | i2cons : forall a As (Bs : ilist B (a :: As))
                    (c : C (ilist_hd Bs)),
               i2list (ilist_tl Bs) -> i2list Bs
  | i2nil : forall Bs : ilist B nil, i2list Bs.

  (* Get the car of an i2list. *)

  Definition i2list_hd (As : list A)
             (Bs : ilist B As)
             (i2l : i2list Bs) :
    match As return forall Bs : ilist B As, i2list Bs -> Type with
      | a :: As' => fun Bs i2l => C (ilist_hd Bs)
      | nil => fun _ _ => unit
    end Bs i2l :=
    match i2l with
      | i2cons a As Bs c i2l' => c
      | i2nil Bs => tt
    end.

  (* Get the cdr of an i2list. *)
  Definition i2list_tl (As : list A)
             (Bs : ilist B As)
             (i2l : i2list Bs) :
    match As as As' return
          forall Bs : ilist B As', i2list Bs -> Type with
      | a :: As' => fun Bs il => i2list (ilist_tl Bs)
      | nil => fun _ _ => unit
    end Bs i2l :=
    match i2l with
      | i2cons a As Bs c i2l' => i2l'
      | i2nil Bs => tt
    end.

  (* Membership in a doubly-indexed list. *)
  Inductive i2list_In
  : forall {a : A} {b : B a} (c : C b) (As : list A) (il : ilist B As) (i2l : i2list il), Prop :=
  | In2_hd : forall a' As (Bs : ilist B (a' :: As)) (i2l : i2list (ilist_tl Bs)) c,
              i2list_In c (i2cons Bs c i2l)
  | In2_tl : forall a a' As (Bs : ilist B (a' :: As)) (b' : B a) c' (i2l : i2list (ilist_tl Bs)) (c : C b'),
              i2list_In c i2l ->
              i2list_In c (i2cons Bs c' i2l).

  (* Fixpoint siglist2i2list *)
  (*          (As : list A) *)
  (*          (il : ilist (fun a => sigT (@C a)) As) *)
  (* : i2list (imap _ (fun a => @projT1 _ (@C a)) il)  := *)
  (*   match il *)
  (*         return i2list (imap _ (fun a => @projT1 _ (@C a)) il) *)
  (*   with *)
  (*     | inil => i2nil *)
  (*     | icons a As' (existT b c) il' => i2cons c (siglist2i2list il') *)
  (*   end. *)

  (* (* and vice versa. *) *)
  (* Fixpoint i2list2siglist {As : list A} {Bs : ilist B As} *)
  (* (i2l : i2list Bs) *)
  (* : ilist (fun a => sigT (@C a)) As := *)
  (*   match i2l in @i2list As' Bs' return ilist (fun a => sigT (@C a)) As' with *)
  (*     | i2nil => @inil _ _ *)
  (*     | i2cons a As b Bs' c Cs' => *)
  (*       icons a (existT _ b c) (i2list2siglist Cs') *)
  (*   end. *)

  (* (* i2list2siglist is the inverse of siglist2i2list *) *)
  (* Lemma siglist2i2list_id *)
  (* : forall As (Bs : ilist _ As), *)
  (*     i2list2siglist (siglist2i2list Bs) = Bs. *)
  (* Proof. *)
  (*   induction Bs; simpl; auto. *)
  (*   destruct b; simpl; congruence. *)
  (* Qed. *)

  (* and vice-versa.

  (* i2list2siglist is the inverse of siglist2i2list *)
  Lemma i2list2siglist_id
  : forall As Bs (Cs : i2list Bs),
      siglist2i2list (i2list2siglist Cs) = Cs.
  Proof.
    induction Bs; simpl; auto.
    destruct b; simpl; congruence.
  Qed.

  Fixpoint ilist2siglist_map
          As (il : ilist As)
  : map (@projT1 _ B) (ilist2siglist il) = As :=
    match il as il' in ilist As' return
          map (@projT1 _ B) (ilist2siglist il') = As' with
      | inil => eq_refl
      | icons a As' b il' => f_equal (fun b' => cons a b') (ilist2siglist_map il')
    end.

  Lemma ilist2sislist_map_cons
  : forall a b As (il il' : ilist As),
      match ilist2siglist_map il in (_ = y) return (ilist y -> Prop) with
        | eq_refl =>
          fun il' => siglist2ilist (ilist2siglist il) = il'
      end il'
      ->
      match
        f_equal (fun b' : list A => a :: b') (ilist2siglist_map il) in (_ = y)
        return (ilist y -> Prop)
      with
        | eq_refl =>
          fun il' : ilist (a :: map (projT1 (P:=B)) (ilist2siglist il)) =>
            icons b (siglist2ilist (ilist2siglist il)) = il'
      end (icons b il').
  Proof.
    intros until il; destruct (ilist2siglist_map il); congruence.
  Qed.

  Lemma ilist2siglist_id
  : forall As (il : ilist As),
      match (ilist2siglist_map il) in (_ = y) return
            forall (il' : ilist y), Prop
      with
        | eq_refl => fun il' => siglist2ilist (ilist2siglist il) = il'
      end il.
  Proof.
    induction il; simpl; auto.
    apply ilist2sislist_map_cons; auto.
  Qed. *)

  (* Looking up the ith value, returning None for indices not in the list *)

  (* A doubly-dependent option. *)

  Fixpoint i2th_error
          (As : list A)
          (Bs : ilist B As)
          (i2l : i2list Bs)
          (n : nat)
          {struct n}
  : Dep_Option_elim_P C (ith_error Bs n) :=
    match n as n' return
          forall (Bs : ilist B As),
            i2list Bs
            -> Dep_Option_elim_P C (ith_error Bs n')
    with
      | 0 => fun Bs =>
               match Bs as Bs' return
                     i2list Bs'
                     -> Dep_Option_elim_P C (ith_error Bs' 0) with
                 | inil => fun i2l => I
                 | icons a As' b Bs' => fun i2l => i2list_hd i2l
               end
      | S n => fun Bs =>
                 match Bs as Bs' return
                       i2list Bs'
                       -> Dep_Option_elim_P C (ith_error Bs' (S n)) with
                   | inil => fun i2l => I
                   | icons a As' b Bs' => fun i2l => i2th_error (i2list_tl i2l) n
                 end
    end Bs i2l.

  Fixpoint i2th_error'
          (As : list A)
          (Bs : ilist B As)
          (i2l : i2list Bs)
          (n : nat)
          {struct n}
  : Dep_Option_elim_P C (ith_error Bs n) :=
    match n as n' return
          forall (Bs : ilist B As),
            i2list Bs
            -> Dep_Option_elim_P C (ith_error Bs n')
    with
      | 0 => fun Bs i2l =>
               match i2l as i2l' in i2list Bs' return
                     Dep_Option_elim_P C (ith_error Bs' 0) with
                 | i2nil _ => I
                 | i2cons a As' Bs' c i2l' => c
               end
      | S n => fun Bs i2l =>
                 match i2l as i2l' in i2list Bs' return
                       Dep_Option_elim_P C (ith_error Bs' (S n)) with
                   | i2nil _ => I
                   | i2cons a As' Bs' c i2l' => i2th_error' i2l' n
                 end
    end Bs i2l.

  (* Looking up the ith value, returning a default value
     for indices not in the list. *)
  Fixpoint i2th_default
          (default_A : A)
          (default_B : B default_A)
          (default_C : C default_B)
          (As : list A)
          (Bs : ilist B As)
          (i2l : i2list Bs)
          (n : nat)
          {struct As}
  : C (ith_default default_A default_B Bs n) :=
    match As as As', n as n' return
          forall (Bs' : ilist B As'),
            i2list Bs'
            -> C (ith_default default_A default_B Bs' n') with
      | a :: As', 0    => @i2list_hd (a :: As')
      | a :: As', S n' => fun il i2l => i2th_default default_C (i2list_tl i2l) n'
      | nil      , 0    => fun il i2l => default_C
      | nil      , S n' => fun il i2l => default_C
    end Bs i2l.

  Lemma i2list_invert (As : list A) (Bs : ilist B As) (Cs : i2list Bs):
    match Bs as Bs' return i2list Bs' -> Prop with
      | icons a As b Bs' => fun Cs =>
                           exists (c : C b) (Cs' : i2list Bs'),
                             Cs = i2cons (icons a b Bs') c Cs'
      | inil => fun Cs => Cs = i2nil (inil _)
    end Cs.
  Proof.
    destruct Cs.
    - destruct (ilist_invert Bs) as [b [Bs' Bs'_eq]]; subst.
      eexists; eauto.
    - pose (ilist_invert Bs) as Bs_eq; simpl in Bs_eq; subst; eauto.
  Qed.

  Lemma i2th_default_In :
    forall (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list Bs)
           (default_A : A)
           (default_B : B default_A)
           (default_C : C default_B),
      n < List.length As ->
      i2list_In (i2th_default default_C Cs n) Cs.
  Proof.
    ith_induction n As; simpl;
    destruct (i2list_invert Cs) as [c [Cs' Cs_eq]]; subst; simpl;
    [apply (In2_hd (icons a b il) Cs' c) |  constructor 2];
    eauto with arith.
  Qed.

  Lemma i2th_default_indep :
    forall (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list Bs)
           (default_A : A)
           (default_B : B default_A)
           (default_C default_C' : C default_B),
      n < List.length As ->
      i2th_default default_C Cs n = i2th_default default_C' Cs n.
  Proof.
    ith_induction n As; simpl; eauto with arith.
  Qed.

End i2list.

(** ** Mapping a function over a(n i)[list], in two non-dependent ways
Section i2list_map.
  Context {A} (B : A -> Type).

  Fixpoint imap_list (f : forall a : A, B a) (As : list A) : ilist B As
    := match As with
         | nil => inil _
         | x::xs => @icons _ B x _ (f x) (imap_list f xs)
       end.

  Fixpoint map_ilist {C} (f : forall (a : A), B a -> C) {As} (Bs : ilist B As) : list C
    := match Bs with
         | inil => nil
         | icons _ _ x xs => (f _ x)::map_ilist f xs
       end.

End ilist_map.

Section of_list.
  Context {T : Type}.

  Definition ilist_of_list : forall ls : list T, ilist (fun _ => T) ls := imap_list (fun _ => T) (fun x => x).
  Definition list_of_ilist {T'} {is} (ls : ilist (fun _ : T' => T) is) : list T
    := map_ilist (B := fun _ => T) (fun _ x => x) ls.

  Lemma list_of_ilist_of_list ls : list_of_ilist (ilist_of_list ls) = ls.
  Proof.
    unfold list_of_ilist, ilist_of_list.
    induction ls; simpl in *; f_equal; assumption.
  Qed.
End of_list.


Section ilist_imap.

  (* Mapping a function over an indexed list. *)

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the list. *)

  Fixpoint imap (As : list A)
           (il : ilist B As)
  : ilist B' As :=
    match il in ilist _ As return ilist _ As with
      | icons a As b il' => icons a (f b) (imap il')
      | inil => inil B'
    end.

  (* [imap] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith_default_imap :
    forall (n : nat)
           (As : list A)
           (il : ilist _ As)
           (default_A : A)
           (default_B : B default_A),
      f (ith_default default_A default_B il n) =
      ith_default default_A (f default_B) (imap il) n.
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

  (* Mapping [f] over a dependent option. *)
  Definition Dep_Option_Map
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt) :
    Dep_Option B' a_opt :=
    match b_opt with
      | Dep_Some a b' => Dep_Some B' a (f b')
      | Dep_None => Dep_None B'
    end.

  (* Applying [f] to the value projected from a dependent option [b_opt]
     is the same as mapping [f] over the [b_opt] and projecting.
   *)
  Lemma Dep_Option_Map_elim
  : forall (a_opt : option A)
           (b_opt : Dep_Option B a_opt),
      Dep_Option_elim (Dep_Option_Map b_opt) =
      match a_opt return
            Dep_Option B a_opt -> Dep_Option_elimT B' a_opt with
        | Some a => fun b => f (Dep_Option_elim b)
        | None => fun _ => tt
      end b_opt.
  Proof.
    unfold Dep_Option_elim, Dep_Option_Map; destruct b_opt; reflexivity.
  Qed.

  (* Concrete values for [a_opt] produce corrolaries of
     [Dep_Option_Map_elim] with nicer statements. *)
  Corollary Dep_Option_Map_elim_Some
  : forall (a : A)
           (b_opt : Dep_Option B (Some a)),
      Dep_Option_elim (Dep_Option_Map b_opt) = f (Dep_Option_elim b_opt).
  Proof.
    intros; eapply Dep_Option_Map_elim; eauto.
  Qed.

  Corollary Dep_Option_Map_elim_None
  : forall (b_opt : Dep_Option B None),
      Dep_Option_elim (Dep_Option_Map b_opt) = tt.
  Proof.
    intros; eapply Dep_Option_Map_elim; eauto.
  Qed.

  (* [imap] behaves as expected with the [ith_error] lookup
     function as well, albeit with a more dependently-typed statement. *)
  Lemma ith_error_imap :
    forall (n : nat)
           (As : list A)
           (il : ilist _ As),
      Dep_Option_Map (ith_error il n) =
      ith_error (imap il) n.
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

End ilist_imap.

Section ilist_izip.

  (* Merging two indexed lists together. *)

  Variable A : Type. (* The indexing type. *)
  Variable B B' D : A -> Type. (* The three types of indexed elements. *)
  Variable f : forall a, B a -> B' a -> D a.

  (* The function which merges the two sets of elements. *)
  Fixpoint izip (As : list A)
           (il : ilist B As) (il' : ilist B' As)
  : ilist D As :=
    match As return ilist B As -> ilist B' As -> ilist D As with
      | a :: As' =>
        fun il il' =>
          icons a (f (ilist_hd il) (ilist_hd il'))
                (izip (ilist_tl il) (ilist_tl il'))
      | [] => fun il il' => inil D
    end il il'.

  (* [izip] behaves as expected with the [ith_default] lookup
     function. *)
  Lemma ith_default_izip :
    forall (n : nat)
           (As : list A)
           (il : ilist B As)
           (il' : ilist B' As)
           (default_A : A)
           (default_B : B default_A)
           (default_B' : B' default_A),
      ith_default _ (f default_B default_B') (izip il il') n =
      f (ith_default _ default_B il n) (ith_default _ default_B' il' n).
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

  (* Merging two dependent options together. *)
  Definition Dep_Option_Zip
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (b'_opt : Dep_Option B' a_opt):
    Dep_Option D a_opt :=
    match a_opt return
          Dep_Option B a_opt -> Dep_Option B' a_opt ->
          Dep_Option D a_opt with
      | Some a =>
        fun b b' =>
          Dep_Some D a (f (Dep_Option_elim b) (Dep_Option_elim b'))
      | None => fun _ _ => Dep_None D
    end b_opt b'_opt.

  (* Projecting the combination of two dependent sums [b_opt] and [b'_opt]
     is the same as combining the projections of [b_opt] and [b'_opt]. *)
  Lemma Dep_Option_Zip_elim
  : forall (a_opt : option A)
           (b_opt : Dep_Option B a_opt)
           (b'_opt : Dep_Option B' a_opt),
      Dep_Option_elim (Dep_Option_Zip b_opt b'_opt) =
      match a_opt return
            Dep_Option B a_opt
            -> Dep_Option B' a_opt
            -> Dep_Option_elimT D a_opt with
        | Some a => fun b b' => f (Dep_Option_elim b) (Dep_Option_elim b')
        | None => fun _ _ => tt
      end b_opt b'_opt.
  Proof.
    unfold Dep_Option_elim, Dep_Option_Zip; destruct b_opt; reflexivity.
  Qed.

  (* Concrete values for [a_opt] produce corrolaries of
     [Dep_Option_Zip_elim] with nicer statements. *)
  Corollary Dep_Option_Zip_elim_Some
  : forall (a : A)
           (b_opt : Dep_Option B (Some a))
           (b'_opt : Dep_Option B' (Some a)),
      Dep_Option_elim (Dep_Option_Zip b_opt b'_opt) =
      f (Dep_Option_elim b_opt) (Dep_Option_elim b'_opt).
  Proof.
    intros; eapply Dep_Option_Zip_elim; eauto.
  Qed.

  Corollary Dep_Option_Zip_elim_None
  : forall (b_opt : Dep_Option B None)
           (b'_opt : Dep_Option B' None),
      Dep_Option_elim (Dep_Option_Zip b_opt b'_opt) = tt.
  Proof.
    intros; eapply Dep_Option_Zip_elim; eauto.
  Qed.

  (* [izip] behaves as expected with the [ith_error] lookup
     function as well, albeit with a more dependently-typed statement. *)

  Lemma ith_error_izip :
    forall (n : nat)
           (As : list A)
           (il : ilist B As)
           (il' : ilist B' As),
      ith_error (izip il il') n =
      Dep_Option_Zip (ith_error il n) (ith_error il' n).
  Proof.
    induction n; destruct As; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

End ilist_izip.
*)

Section i2list_replace.

  (* Replacing an element of an indexed list. *)
  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)
  Variable C : forall a, B a -> Type. (* The type of doubly-indexed elements. *)

  Program Fixpoint replace_Index2
           (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (new_c : Dep_Option_elim_P C (ith_error Bs n))
           {struct Bs} : i2list C Bs :=
    match n return
            i2list C Bs
            -> Dep_Option_elim_P C (ith_error Bs n)
            -> i2list C Bs with
      | 0 => match Bs return
                     i2list C Bs
                     -> Dep_Option_elim_P C (ith_error Bs 0)
                     -> i2list C Bs with
                 | inil =>
                   fun il _ => i2nil _ _
                 | icons a b As' Bs' =>
                   fun Cs' new_c =>
                     i2cons _ new_c (i2list_tl Cs')
               end
      | S n => match Bs return
                     i2list C Bs
                     -> Dep_Option_elim_P C (ith_error Bs (S n))
                     -> i2list C Bs with
                 | inil => fun il _ => i2nil _ _
                 | icons a As' b Bs' =>
                   fun Cs' new_c =>
                     i2cons _ (i2list_hd Cs')
                            (@replace_Index2 n As' Bs'
                                             (i2list_tl Cs') new_c)
               end
    end Cs new_c.

  (*Definition Dep2_Option_elim_P2
             {C' : forall a, B a -> Type}
             (P : forall a (b : B a), C b -> C' a b -> Prop)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (c_opt : Dep2_Option C b_opt)
             (c'_opt : Dep2_Option C' b_opt)
      := match b_opt return
               Dep_Option_elim_P C b_opt
               -> Dep_Option_elim_P C' b_opt
               -> Prop with
           | Dep_Some a b => P a b
           | Dep_None => fun _ _ => True
         end (Dep2_Option_elim c_opt) (Dep2_Option_elim c'_opt).

  Definition Dep_Option_elim_T2
             {A : Type}
             {B B' : A -> Type}
             (P : forall a, B a -> B' a -> Type)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (b'_opt : Dep_Option B' a_opt)
      := match a_opt return
               Dep_Option_elimT B a_opt -> Dep_Option_elimT B' a_opt -> Type with
           | Some a => P a
           | None => fun _ _ => unit
         end (Dep_Option_elim b_opt) (Dep_Option_elim b'_opt).

  Lemma Dep_Option_P2_refl
  : forall n As b,
      @Dep_Option_elim_P2 B _ (fun a b b' => b = b')
                     (nth_error As n) b b.
  Proof.
    intros n As; destruct (nth_error As n); simpl; auto.
  Qed. *)

  Lemma i2th_replace_Index_neq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list C Bs)
      (n' : nat)
      (new_c : Dep_Option_elim_P C (ith_error Bs n')),
      n <> n'
      -> i2th_error (replace_Index2 n' Cs new_c) n =
         i2th_error Cs n.
  Proof.
    induction n; simpl; destruct Bs; intros; icons_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    eapply IHn; congruence.
  Qed.

  Lemma i2th_replace_Index_eq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list C Bs)
      (new_c : Dep_Option_elim_P C (ith_error Bs n)),
      i2th_error (replace_Index2 n Cs new_c) n = new_c.
  Proof.
    induction n; destruct Bs; simpl; auto; intros;
    destruct new_c; eauto.
  Qed.

  Program Fixpoint replace_Index2'
           (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (new_c : Dep_Option_elim_P C (ith_error Bs n))
           {struct Cs} : i2list C Bs :=
    match n return
          Dep_Option_elim_P C (ith_error Bs n)
            -> i2list C Bs with
      | 0 => match Cs in i2list _ Bs return
                   Dep_Option_elim_P C (ith_error Bs 0)
                   -> i2list C Bs with
                 | i2nil Bs =>
                   fun _ => i2nil _ Bs
                 | i2cons a As' Bs' c i2l' =>
                   fun new_c =>
                     i2cons Bs' new_c i2l'
               end
      | S n => match Cs in i2list _ Bs return
                     Dep_Option_elim_P C (ith_error Bs (S n))
                     -> i2list C Bs with
                 | i2nil Bs => fun _ => i2nil _ Bs
                 | i2cons a As' Bs' c i2l' =>
                   fun new_c =>
                     i2cons Bs' c (@replace_Index2' n As' (ilist_tl Bs') i2l' new_c)
               end
    end new_c.

  Lemma i2th_replace_Index'_neq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list C Bs)
      (n' : nat)
      (new_c : Dep_Option_elim_P C (ith_error Bs n')),
      n <> n'
      -> i2th_error' (replace_Index2' n' Cs new_c) n =
         i2th_error' Cs n.
  Proof.
    induction n; simpl; destruct Cs; intros; icons_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    unfold replace_Index2.
    eapply IHn; congruence.
  Qed.

  Lemma i2th_replace_Index'_eq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list C Bs)
      (new_c : Dep_Option_elim_P C (ith_error Bs n)),
      i2th_error' (replace_Index2' n Cs new_c) n = new_c.
  Proof.
    induction n; destruct Cs; simpl; auto; intros;
    destruct new_c; eauto.
  Qed.

End i2list_replace.
