Require Import List String Arith.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Section IndexBound.

  Context {A : Type}.

  Class IndexBound (a : A) (Bound : list A) :=
    { ibound :> nat;
      boundi : nth_error Bound ibound = Some a;
      ibound_lt : ibound < List.length Bound}.

  Global Instance IndexBound_head (a : A) (Bound : list A)
  : IndexBound a (a :: Bound) :=
    {| ibound := 0;
       boundi := eq_refl;
       ibound_lt := lt_0_Sn _ |}.

  Global Instance IndexBound_tail
           (a a' : A) (Bound : list A)
           {sB' : IndexBound a Bound}
  : IndexBound a (a' :: Bound) :=
    {| ibound := S ibound;
       boundi := boundi;
       ibound_lt := lt_n_S _ _ ibound_lt |}.

  Definition tail_IndexBound
           (a : A) (Bound : list A)
           (n : nat)
           (nth_n : nth_error Bound n = Some a)
           (lt_n : S n < S (List.length Bound))
  : IndexBound a Bound :=
    {| ibound := n;
       boundi := nth_n;
       ibound_lt := lt_S_n _ _ lt_n |}.

  Global Arguments ibound [a Bound] _ .
  Global Arguments boundi [a Bound] _.
  Global Arguments ibound_lt [a Bound] _ .

  Record BoundedIndex (Bound : list A) :=
    { bindex :> A;
      indexb :> IndexBound bindex Bound }.

  Global Arguments bindex [Bound] _ .
  Global Arguments indexb [Bound] _ .

  Definition BoundedIndex_nil
             (AnyT : Type)
             (idx : BoundedIndex nil)
  : AnyT.
  Proof.
    destruct idx as [idx [n _ lt_n ]].
    elimtype False; eapply lt_n_0; eassumption.
  Qed.

  Lemma indexb_ibound_eq :
    forall Bound (bidx bidx' : BoundedIndex Bound),
      ibound (indexb bidx) = ibound (indexb bidx') ->
      bindex bidx = bindex bidx'.
  Proof.
    intros; induction Bound; simpl in *.
    - apply BoundedIndex_nil; auto.
    - destruct bidx as [bindex [n nth_n lt_n]];
      destruct bidx' as [bindex' [n' nth_n' lt_n']]; simpl in *; subst.
      congruence.
  Qed.

End IndexBound.

Definition BoundedString := @BoundedIndex string.
Definition BoundedString_eq {Bound} (bidx bidx' : BoundedString Bound) :=
  string_dec (bindex bidx) (bindex bidx').

Section ithIndexBound.

  Context {A C : Type}.
  Variable (projAC : A -> C).
  (*Variable AC_eq :
    forall a c, {True} + {projAC a <> c}.

  Definition AC_eq_bool a c :=
    if (AC_eq a c) then true else false. *)

  Require Import ilist.

  (* Program Definition BoundIndex_tail
             (As : list C)
             (a : C)
             (a' : BoundedIndex (a :: As))
             (a_neq_a' : a <> (bindex _ a'))
    : BoundedIndex As :=
    {| bindex := bindex (a :: As) a';
       indexb := _ |}.
  Next Obligation.
    destruct a' as [a' [[a_eq | In_a]]]; simpl in *;
    [congruence | econstructor; eauto].
  Qed. *)

  Definition nth_Bounded'
           (n : nat)
           (Bound : list A)
  : option A := nth_error Bound n.

  Fixpoint default_BoundedIndex
          (n : nat)
          (Bound : list A)
          (lt_n : n < List.length Bound)
          {struct n}
  : A :=
    match n as n' return
          n' < List.length Bound -> A with
      | 0 => match Bound as Bound' return
                   0 < List.length Bound' -> A with
               | nil => fun lt_0 => match (lt_n_0 _ lt_0) with end
               | cons a Bound' => fun lt_0 => a
             end
      | S n => match Bound as Bound' return
                     S n < List.length Bound' -> A with
                 | nil =>
                   fun lt_Sn => match (lt_n_0 _ lt_Sn) with end
                 | cons a Bound' =>
                   fun lt_Sn => @default_BoundedIndex n Bound' (lt_S_n _ _ lt_Sn)
               end
    end lt_n.

  Lemma default_BoundedIndex_eq
  : forall (n : nat)
           (Bound : list A)
           (lt_n : n < List.length Bound)
           (default_A : A),
      default_BoundedIndex Bound lt_n =
      nth n Bound default_A.
  Proof.
    induction n; (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl; intros; eauto ]).
  Qed.

  Lemma default_BoundedIndex_lt_agnostic
  : forall (n : nat)
           (Bound : list A)
           (lt_n lt_n' : n < List.length Bound),
           default_BoundedIndex Bound lt_n =
           default_BoundedIndex Bound lt_n'.
  Proof.
    induction n; (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl; intros; eauto ]).
  Qed.

  Lemma nth_error_ex_0 :
    forall (As : list A) (n : nat),
      nth_error As n = None
      -> ~ (n < List.length As).
  Proof.
    induction As; destruct n; simpl in *; intuition;
    first [eapply lt_n_0; eauto; fail | discriminate | idtac].
    eapply IHAs; eauto; eapply lt_S_n; auto.
  Qed.

  Definition nth_Index_error
             (AnyT : Type)
             (As : list A)
             (n : nat)
             (lt_n : n < List.length (map projAC As))
             (nth_eq : nth_error As n = None)
  : AnyT.
  Proof.
    elimtype False; eapply nth_error_ex_0; try eassumption.
    rewrite map_length in lt_n; assumption.
  Defined.

  Lemma nth_Index_Some_a
  : forall (c : C)
           (As : list A)
           (n : nat),
      nth_error (map projAC As) n = Some c
      -> n < List.length (map projAC As)
      -> option_map projAC (nth_error As n) = Some c.
  Proof.
    induction As; destruct n; simpl in *; intros; 
    try discriminate; eauto.
    eapply IHAs; auto.
    apply lt_S_n; auto.
  Defined.

  Lemma nth_error_Some_a  :
    forall (As : list A) (n : nat),
      nth_error As n = None
      -> ~ (n < List.length As).
  Proof.

  Definition nth_BoundedIndex_error_eq
             (As : list A)
             (n : nat)
             (lt_n : n < List.length (map projAC As))
             (default_A : A)
             (nth_eq : nth_error As n = None)
  : nth_Index_error A _ lt_n nth_eq = default_A.
  Proof.
    elimtype False; eapply nth_error_ex_0; try eassumption.
    rewrite map_length in lt_n; assumption.
  Defined.

  Hint Resolve nth_BoundedIndex_error_eq.

  Definition nth_BoundedIndex_error
    (Bound : list A)
    (idx : BoundedIndex (map projAC Bound))
    (nth_error : nth_Bounded' (ibound idx) Bound = None)
    : A := nth_Index_error _ _ (ibound_lt idx) nth_error.

  Lemma None_neq_Some 
  : forall (AnyT AnyT' : Type) (a : AnyT),
      None = Some a -> AnyT'.
  Proof.
    intros; discriminate.
  Qed.

  Program Definition nth_Bounded
             (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
  : A := match @nth_Bounded' (ibound idx) Bound as x
               return (option_map projAC x = Some (bindex idx)) -> A with
             | Some a => fun _ => a
             | None => fun f => None_neq_Some _ f
         end (nth_Index_Some_a _ (boundi idx) (ibound_lt idx)).

  Definition Dep_Option 
             (B : A -> Type)
             (opt_A : option A) :=
    match opt_A with 
        | Some a => B a
        | None => unit
    end.

  Definition nth_Bounded_ind
        (P : forall As, BoundedIndex (map projAC As) -> A -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound)),
      Dep_Option (P Bound idx) (nth_error Bound (ibound idx))
      -> P Bound idx (nth_Bounded Bound idx) := 
    fun Bound idx => 
      match (nth_error Bound (ibound idx)) as e
            return
            (forall (f : option_map projAC e = Some (bindex idx)),
               (Dep_Option (P Bound idx) e) ->
               P _ _
                 (match e as e' return
                        option_map projAC e' = Some (bindex idx)
                        -> A
                  with
                    | Some a => fun _ => a
                    | None => fun f => _
                  end f)) with
        | Some a => fun _ H => H
        | None => fun f => None_neq_Some _ f
      end (nth_Index_Some_a _ (boundi idx) (ibound_lt idx)).

  Lemma nth_Bounded_eq
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (default_A : A),
      nth_Bounded Bound idx = nth (ibound idx) Bound default_A.
  Proof.
    intros Bound idx; eapply nth_Bounded_ind.
    unfold Dep_Option; case_eq (nth_error Bound (ibound idx)); auto.
    intros; rewrite <- nth_default_eq; unfold nth_default; 
    rewrite H; reflexivity.
    constructor.
  Qed.

  (*Global Arguments nth_Bounded_obligation_1 _ _ / .  *)

  Fixpoint ith_Bounded'
          {B : A -> Type}
          (n : nat)
          (Bound : list A)
          (il : ilist B Bound)
          {struct n}
  : Dep_Option B (nth_Bounded' n Bound) :=
    match n as n' return
          ilist B Bound
          -> Dep_Option B (nth_Bounded' n' Bound)
    with
      | 0 => match Bound as Bound' return
                   ilist B Bound'
                   -> Dep_Option B (nth_Bounded' 0 Bound') with
               | nil => fun il => tt
               | cons a Bound' => fun il => ilist_hd il
             end
      | S n => match Bound as Bound' return
                     ilist B Bound'
                     -> Dep_Option B (nth_Bounded' (S n) Bound') with
                 | nil => fun il => tt
                 | cons a Bound' =>
                   fun il =>
                     @ith_Bounded' B n Bound' (ilist_tail il)
             end
    end il.

  Fixpoint default_ith_BoundedIndex
          {B : A -> Type}
          (n : nat)
          (Bound : list A)
          (lt_n : n < Datatypes.length Bound)
          (il : ilist B Bound)
          {struct n}
  : B (default_BoundedIndex Bound lt_n) :=
    match n as n' return
          forall (lt_n : n' < Datatypes.length Bound),
            ilist B Bound
            -> B (default_BoundedIndex Bound lt_n)
    with
      | 0 => match Bound as Bound' return
                   forall lt_0 : 0 < Datatypes.length Bound',
                     ilist B Bound'
                     -> B (default_BoundedIndex Bound' lt_0) with
               | nil => fun lt_0 il =>
                          match (lt_n_0 _ lt_0) with end
               | cons a Bound' => fun lt_0 il => ilist_hd il
             end
      | S n => match Bound as Bound' return
                     forall (lt_Sn : (S n) < Datatypes.length Bound'),
                       ilist B Bound'
                       -> B (default_BoundedIndex Bound' lt_Sn) with
                 | nil =>
                   fun lt_Sn il =>
                     match (lt_n_0 _ lt_Sn) with end
                 | cons a Bound' =>
                   fun lt_Sn il =>
                     @default_ith_BoundedIndex B n _
                                   (lt_S_n _ _ lt_Sn) (ilist_tail il)
             end
    end lt_n il.

  Definition ith_BoundedIndex_error_eq
             {B : A -> Type}
             (As : list A)
             (n : nat)
             (lt_n : n < List.length (map projAC As))
             (nth_eq : nth_error As n = None)
  : B (nth_Index_error A As lt_n nth_eq).
  Proof.
    elimtype False; eapply nth_error_ex_0; try eassumption.
    rewrite map_length in lt_n; assumption.
  Defined.

  Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx) :=
    match (nth_Bounded' (ibound idx) Bound) as a'
                  return
                  Dep_Option B a' ->
                  forall (f : option_map projAC a' = Some (bindex idx)),
                    B (match a' as e return
                             option_map projAC e = Some (bindex idx) -> A
                        with
                          | Some a0 => fun _ => a0
                          | None => fun f => None_neq_Some _ f
                      end f) with
        | Some a => fun b _ => b
        | None => fun _ f => None_neq_Some _ f
    end (ith_Bounded' (ibound idx) il)
        (nth_Index_Some_a _ (boundi idx) (ibound_lt idx)).

  (* Lemma ith_Bounded_eq
        {B : A -> Type}
  : forall (default_A : A)
           (default_B : B default_A)
           {Bound : list A}
           (il : ilist B Bound)
           (idx : BoundedIndex (map projAC Bound)),
      ith_Bounded il idx =
      match (nth_Bounded' (ibound idx) Bound) as a'
            return
            match a' with
              | Some a => B a
              | None => unit
            end ->
                  forall (f : a' = None -> A)
                         (f' : forall eq, B (f eq)),
                    B (match
                          a' as x
                          return (a' = x -> A)
                        with
                          | Some a0 => fun _ => a0
                          | None =>
                            fun eq => f eq
                      end eq_refl) with
        | Some a => fun b _ _ => b
        | None => fun _ f f' => (f' eq_refl)
    end (ith_Bounded' (ibound idx) il)
        (nth_BoundedIndex_error A _ (ibound_lt idx))
        (ith_BoundedIndex_error_eq Bound (ibound_lt idx)).


      match nth_Bounded' (ibound idx) Bound as a' return
            B (nth (ibound idx) Bound default_A) with
          | Some b => b
          | None => default_B
      end.
  Proof.

  Lemma ith_Bounded'_eq
        {B : A -> Type}
  : forall (n : nat)
           (Bound : list A)
           (il : ilist B Bound)
           (lt_n : n < List.length Bound)
           (default_A : A)
           (default_B default_B' : B (@nth_Bounded' default_A n Bound)),
      ith_Bounded' _ default_B n il =
      ith_Bounded' _ default_B' n il.
  Proof.
    induction n; simpl;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl; intros; eauto ]).
    eapply IHn; apply lt_S_n; auto.
  Qed.

  Lemma ith_Bounded'_eq'
        {B : A -> Type}
  : forall (n : nat)
           (Bound : list A)
           (il : ilist B Bound)
           (lt_n : n < List.length Bound)
           (default_B default_B' : B (default_BoundedIndex Bound lt_n)),
      ith_Bounded' _ default_B n il =
      ith_Bounded' _ default_B' n il.
  Proof.
    induction n; simpl;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl; intros; eauto ]).
  Qed.

  Lemma ith_Bounded_eq
        {B : A -> Type}
  : forall (Bound : list A)
           (il : ilist B Bound)
           (idx : BoundedIndex (map projAC Bound))
           (default_B : B _),
      ith_Bounded il idx =
      ith_Bounded' _ default_B (ibound idx) il.
  Proof.
    unfold ith_Bounded; simpl; intros.
    apply ith_Bounded'_eq'.
  Qed. *)

    Definition Dep_Dep_Option 
               {B : A -> Type}
               (P : forall a, B a -> Type)
               (a_opt : option A)
               (b_opt : Dep_Option B a_opt)
      := match a_opt as a' return 
               Dep_Option B a' -> Type with 
           | Some a => P a 
           | None => fun _ => unit
         end b_opt.

    Definition Dep_Dep_Option2
               {B B' : A -> Type}
               (P : forall a, B a -> B' a -> Prop)
               (a_opt : option A)
               (b_opt : Dep_Option B a_opt)
               (b_opt' : Dep_Option B' a_opt)
      := match a_opt as a' return 
               Dep_Option B a' -> Dep_Option B' a' -> Prop with 
           | Some a => P a 
           | None => fun _ _ => True
         end b_opt b_opt'.

    Print ilist_invert.

    Lemma ith_Bounded'_imap
        {B B' : A -> Type}
    : forall (n : nat)
          (Bound : list A)
          (il : ilist B Bound)
          (f : forall idx, B idx -> B' idx),
        Dep_Dep_Option2 (fun a b b' => f a b = b')
                        (nth_Bounded' n Bound)
                        (@ith_Bounded' B n Bound il)
                        (@ith_Bounded' B' n Bound (imap B' f il)).
    Proof.
      unfold Dep_Dep_Option2; simpl.
      induction n; simpl; destruct Bound; simpl; auto; intros;
      generalize (ilist_invert il);
      intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
      simpl; eauto.
      eapply IHn.
  Qed.

    Definition ith_Bounded'_eq_P 
               {B : A -> Type}
               (Bound : list A)
               (idx : BoundedIndex (map projAC Bound))
               (il : ilist B Bound) 
               e' b c d :=
      match e' as e'
        return
        (Dep_Option B e' ->
         forall c : option_map projAC e' = Some (bindex idx),
           B
             (match
                 e' as x return (option_map projAC x = Some (bindex idx) -> A)
               with
                 | Some a => fun _ => a
                 | None => fun f => None_neq_Some A f
               end c) -> Type)
      with
        | Some e =>
          fun b c d => b = d
        | None => fun b c d => True
      end b c d.

    Lemma ith_Bounded'_eq
          {B : A -> Type}
    : forall (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
             (il : ilist B Bound),
        ith_Bounded'_eq_P idx il 
                          (nth_Bounded' (ibound idx) Bound)
                          (ith_Bounded' (ibound idx) il)
                          (nth_Index_Some_a Bound (boundi idx) (ibound_lt idx))
                          (ith_Bounded il idx).
    Proof.
      unfold ith_Bounded'_eq_P; simpl.
      destruct idx as [idx [n In_n lt_n ]]; simpl in *.
      revert n In_n lt_n.
      induction Bound; destruct n; simpl; eauto.
      intros; eapply IHBound.
    Qed.

    Program Definition ith_Bounded_ind
            {B : A -> Type}
        (P : forall As, BoundedIndex (map projAC As) 
                        -> ilist B As
                        -> forall a : A, B a -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound),
      Dep_Dep_Option (P Bound idx il) (nth_error Bound (ibound idx))
                     (@ith_Bounded' B (ibound idx) Bound il)
      -> P Bound idx il _ (ith_Bounded il idx) := 
    fun Bound idx il => 
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e) 
                        (c : option_map projAC e = Some (bindex idx))
                        d, 
                   (ith_Bounded'_eq_P idx il e b c d)
                   -> Dep_Dep_Option (P Bound idx il) e b ->                   
                   P _ _ _
                   (match e as x return 
                          (option_map projAC x = Some (bindex idx) -> A) with
                      | Some a => fun _ => a
                      | None => fun f =>
                          None_neq_Some A f
                    end c) d with 
          | Some a => _
          | None => _
           end (ith_Bounded' (ibound idx) il)
               (nth_Index_Some_a Bound (boundi idx) (ibound_lt idx))
               (ith_Bounded il idx)
               (ith_Bounded'_eq idx il). 

    Program Definition ith_Bounded_ind2
            {B B' : A -> Type}
        (P : forall As, BoundedIndex (map projAC As) 
                        -> ilist B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound),
      Dep_Dep_Option2 (P Bound idx il) (nth_error Bound (ibound idx))
                      (@ith_Bounded' B (ibound idx) Bound il)
                      (@ith_Bounded' B' (ibound idx) Bound il')
      -> P Bound idx il _ (ith_Bounded il idx) (ith_Bounded il' idx) := 
    fun Bound idx il il' => 
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e) 
                        (b' : Dep_Option B' e) 
                        (c : option_map projAC e = Some (bindex idx))
                        d d',
                   (ith_Bounded'_eq_P idx il e b c d)
                   -> (ith_Bounded'_eq_P idx il' e b' c d')
                   -> Dep_Dep_Option2 (P Bound idx il) e b b' ->
                   P _ _ _
                   (match e as x return 
                          (option_map projAC x = Some (bindex idx) -> A) with
                      | Some a => fun _ => a
                      | None => fun f =>
                          None_neq_Some A f
                    end c) d d' with 
          | Some a => _
          | None => _
           end (ith_Bounded' (ibound idx) il)
               (ith_Bounded' (ibound idx) il')
               (nth_Index_Some_a Bound (boundi idx) (ibound_lt idx))
               (ith_Bounded il idx)
               (ith_Bounded il' idx)
               (ith_Bounded'_eq idx il)
               (ith_Bounded'_eq idx il').

  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    intros.
    eapply ith_Bounded_ind2 with (idx0 := idx) (il0 := il) (il' := imap B' f il).
    apply ith_Bounded'_imap.
  Qed.

  Program Fixpoint replace_Index
           {B : A -> Type}
           (default_A : A)
           (n : nat)
           (As : list A)
           (il : ilist B As)
           (new_b : B (nth_Bounded' default_A n As))
           {struct As} : ilist B As :=
    match n as n' return
            ilist B As
            -> B (nth_Bounded' default_A n' As)
            -> ilist B As with
      | 0 => match As as As' return
                   ilist B As'
                   -> B (nth_Bounded' default_A 0 As')
                   -> ilist B As' with
               | nil =>
                 fun il _ => inil _
               | cons a Bound' =>
                 fun il new_b =>
                   icons _ new_b (ilist_tail il)
             end
      | S n => match As as As' return
                     ilist B As'
                     -> B (nth_Bounded' default_A (S n) As')
                     -> ilist B As' with
                 | nil => fun il _ => inil _
                 | cons a Bound' =>
                   fun il new_b =>
                     icons _ (ilist_hd il)
                           (@replace_Index B default_A n Bound'
                                           (ilist_tail il) new_b)
               end
    end il new_b.

  Lemma ith_replace_Index_neq
        {B : A -> Type}
  : forall
      (default_A default_A' : A)
      (default_B : B default_A)
      (n n' : nat)
      (As : list A)
      (il : ilist _ As)
      (new_b : B (nth_Bounded' default_A' n As)),
      n <> n'
      -> ith_Bounded' default_A default_B n'
                      (replace_Index default_A' n il new_b) =
         ith_Bounded' default_A default_B n' il.
  Proof.
    induction n; simpl; destruct As; simpl; auto; intros;
    generalize (ilist_invert il); intros; subst; auto;
    destruct H0 as [b [il' il_eq]]; subst;
      destruct n'; simpl; auto.
    congruence.
  Qed.

  Definition transport_A
             {B : A -> Type}
             (a a' : A)
  : a = a'
    -> B a
    -> B a'.
  Proof.
    intro.
    induction H; auto.
  Defined.

  Lemma transport_A_refl
        {B : A -> Type} :
    forall (a : A) (b : B a),
      b = transport_A (eq_refl a) b.
  Proof.
    simpl; reflexivity.
  Qed.

  Definition transport_A'
             (a a' : A)
             (n n' : nat)
             (As : list A)
  : a = a'
    -> n = n'
    -> nth_Bounded' a n As = nth_Bounded' a' n' As.
  Proof.
    intros; induction H; induction H0; auto.
  Defined.

  Definition transport_A_QWAZA'
             {B : A -> Type}
             (a a' : A) (n n' : nat) (As : list A) b
             (a_eq_a' : a = a') (n_eq_n' : n = n') :=
    transport_A (B := B) (transport_A' As a_eq_a' n_eq_n') b.

  Lemma transport_A'_refl
        {B : A -> Type} :
    forall (a : A) (n : nat) (As : list A) b,
      b = transport_A_A' (B := B) As b (eq_refl a) (eq_refl n).
  Proof.
    reflexivity.`
  Qed.

  Definition transport_A''
          {B : A -> Type}
          (a : nat -> A) (n n': nat) (As : list A)
          (b : B (nth_Bounded' (a n') n' As))
          (b' : B (nth_Bounded' (a n) n As))
          : B (nth_Bounded' (a n') n' As).
  Proof.
    refine (match (eq_nat_dec n n') with
              | left (eq_refl) =>
                @transport_A_A' B (a n) (a n') n n' As b' _ _
              | right neq => b
            end); eauto.
  Defined.

  Lemma ith_replace_Index_eq
        {B : A -> Type}
  : forall
      (default_A default_A' : A)
      (default_B : B _)
      (n n' : nat)
      (As : list A)
      (default_eq : default_A' = default_A)
      (n_eq_n' : n = n')
      (il : ilist _ As)
      (new_b : B (nth_Bounded' default_A' n As)),
      n < List.length As
      -> ith_Bounded' default_A default_B n'
                      (replace_Index default_A' n il new_b) =
         transport_A_A' _ new_b default_eq n_eq_n'.
  Proof.
    induction n; simpl;
    (destruct As;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      intros; generalize (ilist_invert il); intros;
      destruct H0 as [b [il' il_eq]]; subst; simpl; eauto]).
    simpl in *.
    rewrite (IHn _ _ (eq_refl _) (eq_refl _)); simpl; auto.
    apply lt_S_n; assumption.
  Qed.

  Definition replace_BoundedIndex
           {B : A -> Type}
           (Bound : list A)
           (il : ilist B Bound)
           (idx : BoundedIndex (map projAC Bound))
           (new_b : B (nth_Bounded Bound idx))
  : ilist B Bound :=
    replace_Index _ (ibound idx) il new_b.

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx )),
      ibound idx <> ibound idx'
      -> ith_Bounded (replace_BoundedIndex il idx new_b) idx' =
         ith_Bounded il idx'.
  Proof.
    unfold ith_Bounded, replace_BoundedIndex; simpl.
    intros; erewrite ith_replace_Index_neq; eauto.
    apply ith_Bounded'_eq'.
  Qed.

  Lemma default_BoundedIndex_eq'
  : forall Bound (idx idx' : BoundedIndex (map projAC Bound)),
      ibound idx = ibound idx'
      -> default_BoundedIndex
           Bound
           (eq_ind (Datatypes.length (map projAC Bound))
                   (fun n : nat => ibound idx < n) (ibound_lt idx)
                   (Datatypes.length Bound) (map_length projAC Bound)) =
         default_BoundedIndex
           Bound
           (eq_ind (Datatypes.length (map projAC Bound))
                   (fun n : nat => ibound idx' < n) (ibound_lt idx')
                   (Datatypes.length Bound) (map_length projAC Bound)).
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    destruct idx' as [idx' [n' nth_n' lt_n']]; intros; simpl in *;
    subst; apply default_BoundedIndex_lt_agnostic.
  Defined.

  Lemma nth_Bounded'_eq :
    forall Bound (idx idx' : BoundedIndex (map projAC Bound))
           default_B default_B',
      ibound idx = ibound idx'
      -> nth_Bounded' default_B (ibound idx) Bound
         = nth_Bounded' default_B' (ibound idx') Bound.
  Proof.
    intros; rewrite H.
    unfold nth_Bounded'; repeat rewrite <- nth_Bounded_eq; reflexivity.
  Qed.

  Lemma nth_BoundedIndex_eq :
    forall Bound (idx idx' : BoundedIndex (map projAC Bound)),
      ibound idx = ibound idx'
      -> nth_Bounded Bound idx
         = nth_Bounded Bound idx'.
  Proof.
    unfold nth_Bounded; intros; eapply nth_Bounded'_eq; auto.
  Qed.

  Eval simpl in (forall Bound idx a, nth_Bounded_obligation_1 Bound idx =
                a).

  Lemma ith_replace_BoundIndex_eq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx))
      (idx_eq_idx' : ibound idx = ibound idx'),
      ith_Bounded (replace_BoundedIndex il idx new_b) idx' =
      @transport_A_A' B _ _ _ _ _ new_b (default_BoundedIndex_eq' _ _ _ idx_eq_idx') idx_eq_idx'.
  Proof.
    unfold ith_Bounded, replace_BoundedIndex; simpl.
    intros; erewrite <- ith_replace_Index_eq; eauto.
    erewrite <- map_length; apply (ibound_lt idx).
  Qed.

  Print nth_Bounded_obligation_1.

  Lemma ith_replace_BoundIndex
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx')),
      ith_Bounded (replace_BoundedIndex il idx' new_b) idx =
      @transport_A'' B _ (ibound idx) (ibound idx') Bound
                      new_b (ith_Bounded il idx).
  .
  Check (eq_nat_dec).

  Lemma ith_replace_BoundIndex
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx)),
      ith_Bounded (replace_BoundedIndex il idx new_b) idx' =
      match (eq_nat_dec (ibound idx) (ibound idx')) as
            eq_test
             return
             match eq_test return Set with
                 | left _  => B (nth_Bounded Bound idx')
                 | right _ => B (nth_Bounded Bound idx')
             end
      with
          | left (eq_refl) =>
            @transport_A_A' B _ _ _ _ _ new_b (default_BoundedIndex_eq' _ _ _ eq_refl) eq_refl
          | right _ => ith_Bounded (replace_BoundedIndex il idx new_b) idx'
      end.
            |

 .
  Proof.
    unfold ith_Bounded, replace_BoundedIndex; simpl.
    intros; erewrite <- ith_replace_Index_eq; eauto.
    erewrite <- map_length; apply (ibound_lt idx).
  Qed.

End ithIndexBound.


  (* Lemma ith_Bounded_lt
          {B : A -> Type}
  : forall (n : nat)
           (Bound : list A)
           (lt_n lt_n' : n < Datatypes.length Bound)
           (il : ilist B Bound),
      ith_Bounded' lt_n il =
      ith_Bounded' lt_n' il .
  Proof.
    induction n;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl ]); auto.
  Qed.

  Program Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx) :=
    @ith_Bounded' B (ibound idx) Bound _ _.

  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_Bounded'; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Lemma ith_Bounded_Sn :
    forall (a : A) b il idx n
           (nth_n : forall a' : C, nth (S n) (map projAC (a :: b)) a' = idx)
           (lt_n : S n < Datatypes.length (map projAC (a :: b))),
      (ith_Bounded (icons a b il)
                   {| bindex := idx;
                      indexb := {| ibound := S n; boundi := nth_n; ibound_lt := lt_n |} |}) =
      ith_Bounded il {| bindex := idx;
                        indexb := (tail_IndexBound idx _ n nth_n lt_n) |}.
  Proof.
    simpl; unfold ith_Bounded. simpl; intros.
    unfold nth_Bounded_obligation_1; simpl.
    unfold ith_Bounded_obligation_1.
    f_equal.
    revert lt_n; clear; induction b; simpl; auto.
    intros.
    unfold map_length_obligation_1; simpl.
    unfold eq_ind, eq_rect; simpl.

    unfold nth_Bounded_obligation_1; destruct b; simpl.
    unfold ith_Bounded_obligation_2, ith_Bounded_obligation_1; simpl.
    unfold map_length_obligation_1, f_equal; simpl.
    unfold ith_Bounded' at 1; simpl.
    unfold map_length, list_ind, list_rect, f_equal; simpl.
    destruct b; simpl; unfold map_length_obligation_1, f_equal; simpl.


    simpl.


  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_Bounded'; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Fixpoint replace_BoundIndex
           {B : A -> Type}
           (As : list A)
           (il : ilist B As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           {struct As} : ilist B As.
  Proof.
    refine (match As as As' return
                  forall (idx : BoundedIndex (map projAC As')),
                    ilist B As'
                  -> B (nth_Bounded As' idx)
                  -> ilist B As' with
              | a :: As' => (fun idx il' new_b' => _)
              | _ => fun idx il' new_b' => inil _
            end idx il new_b).
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As') idx0)).
    exact (icons _ new_b' (ilist_tail il')).
    exact (icons _ (ilist_hd il')
                 (replace_BoundIndex B As' (ilist_tail il')
                                     (BoundIndex_tail idx0 n) new_b')).
  Defined.

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           (idx' : BoundedIndex (map projAC As))
           c_neq,
      AC_eq (nth_Bounded As idx) (bindex _ idx') = right c_neq
      -> ith_Bounded (replace_BoundIndex il idx new_b) idx' =
      ith_Bounded il idx'.
  Proof.
    induction As; intros; subst; auto.
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      try rewrite H in *; simpl; auto.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx')); eauto.
  Qed.

  Lemma ith_replace_BoundIndex_eq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx)),
      ith_Bounded (replace_BoundIndex il idx new_b) idx = new_b.
  Proof.
    induction As; intros; subst.
    - exact (Not_BoundedIndex_nil idx).
    - simpl in *;
      destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      simpl; eauto.
  Qed.

End ithIndexBound.


  Fixpoint nth_Bounded'
          (n : nat)
          (Bound : list A)
          (lt_n : n < List.length Bound)
          {struct n}
  : A :=
    match n as n' return
          n' < List.length Bound -> A with
      | 0 => match Bound as Bound' return
                   0 < List.length Bound' -> A with
               | nil => fun lt_0 => match (lt_n_0 _ lt_0) with end
               | cons a Bound' => fun lt_0 => a
             end
      | S n => match Bound as Bound' return
                     S n < List.length Bound' -> A with
                 | nil =>
                   fun lt_Sn => match (lt_n_0 _ lt_Sn) with end
                 | cons a Bound' =>
                   fun lt_Sn => @nth_Bounded' n Bound' (lt_S_n _ _ lt_Sn)
               end
    end lt_n.

  Program Fixpoint map_length
          (A B : Type) (f : A -> B) (l : list A)
  : Datatypes.length (map f l) = Datatypes.length l :=
    match l as l' return
          Datatypes.length (map f l') = Datatypes.length l' with
        | nil => eq_refl
        | cons a l' => (fun H => _) (map_length f l')
    end.

  Lemma nth_Bounded_lt_agnostic
  : forall (n : nat)
           (Bound : list A)
           lt lt',
      @nth_Bounded' n Bound lt =
      @nth_Bounded' n Bound lt' .
    induction n;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption
     | simpl; intros]); auto.
  Qed.

  (* Local Obligation Tactic := intros.

  Program Fixpoint map_length_lt
          (As : list A)
          (n : nat)
  : n < List.length (map projAC As) ->
    n < List.length As :=
    match As as As' return
          n < List.length (map projAC As') ->
          n < List.length As' with
      | nil => fun len_n => len_n
      | cons a As' =>
        match n with
          | 0 => (fun HInd len_n => _) (@map_length_lt As' 0)
          | S n => (fun HInd len_n => _ ) (@map_length_lt As' (S n))
        end
    end.
  Next Obligation.
    simpl in *.
    econstructor.
    e
    auto with arith. *)

  Program Definition nth_Bounded
          (Bound : list A)
          (idx : BoundedIndex (map projAC Bound))
  : A := @nth_Bounded' (ibound idx) Bound _.
  Next Obligation.
    generalize (ibound_lt idx); clear.
    rewrite map_length; auto.
  Defined.

  Lemma nth_Bounded_eq
  : forall (n : nat)
           (default_A : A)
           (Bound : list A)
           (lt_n : n < List.length Bound),
      nth_Bounded' Bound lt_n = nth n Bound default_A.
  Proof.
    induction n; (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption
     | simpl; intros]); auto.
  Qed.

  (* Lemma nth_Bounded_eq_nth :
    forall (default_A : A)
           (As : list A)
           (idx : BoundedIndex (map projAC As)),
      nth_Bounded As idx =
      nth (findIndex AC_eq_bool As (bindex _ idx)) As default_A .
  Proof.
    induction As; simpl; intros.
    - eapply Not_BoundedIndex_nil; eauto.
    - unfold AC_eq_bool.
      destruct (AC_eq a (bindex (projAC a :: map projAC As) idx)); auto.
      eapply IHAs.
  Qed.

  Global Arguments nth_Bounded_obligation_1 _ _ _ _ _ _ _ / . *)

  Fixpoint ith_Bounded'
          {B : A -> Type}
          (n : nat)
          (Bound : list A)
          (lt_n : n < Datatypes.length Bound)
          (il : ilist B Bound)
          {struct n}
  : B (nth_Bounded' Bound lt_n) :=
    match n as n' return
          forall (lt_n : n' < Datatypes.length Bound),
            ilist B Bound
            -> B (nth_Bounded' Bound lt_n)
    with
      | 0 => match Bound as Bound' return
                   forall lt_0 : 0 < Datatypes.length Bound',
                     ilist B Bound'
                     -> B (nth_Bounded' Bound' lt_0) with
               | nil => fun lt_0 il =>
                          match (lt_n_0 _ lt_0) with end
               | cons a Bound' => fun lt_0 il => ilist_hd il
             end
      | S n => match Bound as Bound' return
                     forall (lt_Sn : (S n) < Datatypes.length Bound'),
                       ilist B Bound'
                       -> B (nth_Bounded' Bound' lt_Sn) with
                 | nil =>
                   fun lt_Sn il =>
                     match (lt_n_0 _ lt_Sn) with end
                 | cons a Bound' =>
                   fun lt_Sn il =>
                     @ith_Bounded' B n _
                                   (lt_S_n _ _ lt_Sn) (ilist_tail il)
             end
    end lt_n il.

  (* Lemma ith_Bounded_lt
          {B : A -> Type}
  : forall (n : nat)
           (Bound : list A)
           (lt_n lt_n' : n < Datatypes.length Bound)
           (il : ilist B Bound),
      ith_Bounded' lt_n il =
      ith_Bounded' lt_n' il .
  Proof.
    induction n;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl ]); auto.
  Qed. *)

  Program Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx) :=
    @ith_Bounded' B (ibound idx) Bound _ _.

  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_Bounded'; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Lemma ith_Bounded_Sn :
    forall (a : A) b il idx n
           (nth_n : forall a' : C, nth (S n) (map projAC (a :: b)) a' = idx)
           (lt_n : S n < Datatypes.length (map projAC (a :: b))),
      (ith_Bounded (icons a b il)
                   {| bindex := idx;
                      indexb := {| ibound := S n; boundi := nth_n; ibound_lt := lt_n |} |}) =
      ith_Bounded il {| bindex := idx;
                        indexb := (tail_IndexBound idx _ n nth_n lt_n) |}.
  Proof.
    simpl; unfold ith_Bounded. simpl; intros.
    unfold nth_Bounded_obligation_1; simpl.
    unfold ith_Bounded_obligation_1.
    f_equal.
    revert lt_n; clear; induction b; simpl; auto.
    intros.
    unfold map_length_obligation_1; simpl.
    unfold eq_ind, eq_rect; simpl.

    unfold nth_Bounded_obligation_1; destruct b; simpl.
    unfold ith_Bounded_obligation_2, ith_Bounded_obligation_1; simpl.
    unfold map_length_obligation_1, f_equal; simpl.
    unfold ith_Bounded' at 1; simpl.
    unfold map_length, list_ind, list_rect, f_equal; simpl.
    destruct b; simpl; unfold map_length_obligation_1, f_equal; simpl.


    simpl.


  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_Bounded'; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Fixpoint replace_BoundIndex
           {B : A -> Type}
           (As : list A)
           (il : ilist B As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           {struct As} : ilist B As.
  Proof.
    refine (match As as As' return
                  forall (idx : BoundedIndex (map projAC As')),
                    ilist B As'
                  -> B (nth_Bounded As' idx)
                  -> ilist B As' with
              | a :: As' => (fun idx il' new_b' => _)
              | _ => fun idx il' new_b' => inil _
            end idx il new_b).
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As') idx0)).
    exact (icons _ new_b' (ilist_tail il')).
    exact (icons _ (ilist_hd il')
                 (replace_BoundIndex B As' (ilist_tail il')
                                     (BoundIndex_tail idx0 n) new_b')).
  Defined.

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           (idx' : BoundedIndex (map projAC As))
           c_neq,
      AC_eq (nth_Bounded As idx) (bindex _ idx') = right c_neq
      -> ith_Bounded (replace_BoundIndex il idx new_b) idx' =
      ith_Bounded il idx'.
  Proof.
    induction As; intros; subst; auto.
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      try rewrite H in *; simpl; auto.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx')); eauto.
  Qed.

  Lemma ith_replace_BoundIndex_eq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx)),
      ith_Bounded (replace_BoundIndex il idx new_b) idx = new_b.
  Proof.
    induction As; intros; subst.
    - exact (Not_BoundedIndex_nil idx).
    - simpl in *;
      destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      simpl; eauto.
  Qed.

End ithIndexBound. *)
