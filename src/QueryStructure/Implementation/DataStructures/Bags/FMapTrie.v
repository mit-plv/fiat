Require Import
        Coq.FSets.FMapInterface
        Coq.FSets.FMapFacts
        Coq.FSets.FMapAVL
        ADTSynthesis.Common
        ADTSynthesis.Common.List.ListFacts
        ADTSynthesis.Common.List.FlattenList
        ADTSynthesis.Common.FMapExtensions.

Set Implicit Arguments.

Module Raw (X:OrderedType).

Module Import MX := OrderedTypeFacts X.
Module Import PX := KeyOrderedType X.

Definition key := list X.t.

Module XMap := FMapAVL.Make X.
Module XMapFacts := FMapFacts.

Section Elt.
  Variable elt : Type.

  Definition Map := XMap.Raw.tree.

  Inductive Trie :=
  | Node : option elt -> Map Trie -> Trie.

  Definition TrieNode (trie : Trie) :=
    match trie with
      | Node bag tries => bag
    end.

  Definition SubTries (trie : Trie) :=
    match trie with
      | Node bag tries => tries
    end.

  Definition WFMap := XMap.Raw.bst.

  Inductive TrieOK : Trie -> Prop :=
  |NodeOK :
     forall trie,
       WFMap (SubTries trie)
       -> (forall k subtrie,
             XMap.Raw.MapsTo k subtrie (SubTries trie)
             -> TrieOK subtrie)
       -> TrieOK trie.

  
  Lemma SubTrieMapBST 
  : forall o m,
      TrieOK (Node o m)
      -> XMap.Raw.bst m.
  Proof.
    intros; inversion H; eauto.
  Qed.
  
  Hint Resolve SubTrieMapBST.
  
  Lemma SubTrieOK
  : forall trie k subtrie,
      TrieOK trie
      -> XMap.Raw.find k (SubTries trie) = Some subtrie
      -> TrieOK subtrie.
  Proof.
    destruct trie; simpl.
    induction m; simpl in *; intros.
    - discriminate.
    - inversion H; subst.
      case_eq (X.compare k0 k); intros; rewrite H3 in H0.
      + eapply IHm1; eauto.
        econstructor; simpl in *; eauto.
        unfold WFMap in *; eauto.
        inversion H1; subst; eauto.
      + injections; simpl in *.
        eapply (H2 k0); eauto.
      + eapply IHm2; eauto.
        econstructor; simpl in *; eauto.
        inversion H1; subst; eauto.
  Qed.

  Hint Resolve SubTrieOK.
  
  Definition t := Trie.

  (* Emptiness *)
  Definition empty : t := Node None (XMap.Raw.empty Trie).

  Definition is_empty (trie : Trie) :=
    match trie with
      | Node None subtrie => XMap.Raw.is_empty subtrie
      | _ => false
    end.

  Definition Empty (trie : Trie) :=
    TrieNode trie = None
    /\ XMap.Raw.Proofs.Empty (SubTries trie).

  Lemma is_empty_1 :forall m, Empty m -> is_empty m = true.
  Proof.
    unfold Empty, is_empty; intros; subst; intuition eauto.
    destruct m; simpl in *; subst.
    eauto using XMap.Raw.Proofs.is_empty_1.
  Qed.

  Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
  Proof.
    unfold Empty, is_empty; destruct m; destruct o;
    intuition eauto; try congruence.
    simpl; eauto using XMap.Raw.Proofs.is_empty_2.
  Qed.

  (* Membership *)

  Fixpoint mem
           (k : key)
           (trie : Trie)
  : bool :=
    match TrieNode trie with
      | Some _ => true
      | None => 
        match k with 
          | nil => false
          | key :: k' =>
            match XMap.Raw.find key (SubTries trie) with
              | Some subtrie => mem k' subtrie
              | _ => false
            end
        end
    end.

  Inductive In_trie
  : forall (k : key)
           (trie : Trie), Prop :=
  | In_Node : forall k e subtries, In_trie k (Node (Some e) subtries)
  | In_SubTrie :
      forall k keys' e_opt subtries subtrie,
        XMap.Raw.MapsTo k subtrie subtries
        -> In_trie keys' subtrie
        -> In_trie (k :: keys') (Node e_opt subtries).
  
  Definition In := In_trie.

  Lemma mem_1 : forall x m, TrieOK m -> In x m -> mem x m = true.
  Proof.
    induction x; intros; inversion H0; subst; simpl; eauto.
    destruct e_opt; eauto.
    case_eq (XMap.Raw.find a subtries); try congruence; intros.
    - apply XMap.Raw.Proofs.find_1 in H3; eauto.
      rewrite H3 in H1; injections.
      eapply IHx; eauto.
    - apply XMap.Raw.Proofs.find_1 in H3; eauto.
      congruence.
  Qed.

  Lemma mem_2 : forall x m, mem x m = true -> In x m.
  Proof.
    induction x; destruct m; simpl.
    - destruct o; intros.
      + econstructor.
      + discriminate.
    - destruct o; intros.
      + econstructor.
      + case_eq (XMap.Raw.find a m); intros; rewrite H0 in H.
        * econstructor 2; eauto.
          apply XMap.Raw.Proofs.find_2 in H0; eauto.
          eapply IHx; eauto.
        * discriminate.
  Qed.

  Fixpoint find
           (k : key)
           (trie : Trie)
  : option elt :=
    match k with
      | nil => TrieNode trie                        
      | key :: k' =>
        match XMap.Raw.find key (SubTries trie) with
          | Some subtrie =>
            match find k' subtrie with
              | Some e => Some e
              | _ => TrieNode trie
            end
          | _ => TrieNode trie
        end
    end.

  Inductive MapsTo_trie
  : forall (k : key)
           (e : elt)
           (trie : Trie), Prop :=
  | MapsTo_Node : forall e subtries,
                    MapsTo_trie [ ] e (Node (Some e) subtries)
  | MapsTo_In_SubTrie :
      forall key k' e e_opt subtries subtrie,
        XMap.Raw.MapsTo key subtrie subtries
        -> MapsTo_trie k' e subtrie
        -> MapsTo_trie (key :: k') e (Node e_opt subtries)
  | MapsTo_NIn_SubTrie :
      forall key k' e subtries,
        (forall subtrie,
           XMap.Raw.MapsTo key subtrie subtries
           -> ~ In_trie k' subtrie)
        -> MapsTo_trie (key :: k') e (Node (Some e) subtries).

  Definition MapsTo := MapsTo_trie.

  Lemma find_in :
    forall (k : key) (trie : Trie),
      TrieOK trie -> find k trie <> None -> In k trie.
  Proof.
    induction k; destruct trie; simpl; intros.
    - destruct o.
      + econstructor.
      + congruence.
    - destruct o.
      + econstructor.
      + revert H0; case_eq (XMap.Raw.find a m); intros; subst.
        revert H1; case_eq (find k t0); intros; subst.
        econstructor.
        apply XMap.Raw.Proofs.find_2 in H0; eauto.
        eapply IHk; eauto using SubTrieOK; congruence.
        congruence.
        congruence.
  Qed.

  Lemma in_find :
    forall (k : key) (trie : Trie),
      TrieOK trie -> In k trie -> find k trie <> None.
  Proof.
    induction k; destruct trie; simpl; intros;
    inversion H0; subst.
    - congruence.
    - case_eq (XMap.Raw.find a m); intros; subst.
      + case_eq (find k t0); intros; subst; congruence.
      + congruence.
    - apply XMap.Raw.Proofs.find_1 in H4; eauto.
      + rewrite H4.
        eapply IHk in H6; eauto.
        case_eq (find k subtrie); intros; congruence.
  Qed.

  Lemma find_1 :
    forall (k : key) (e : elt) (trie : Trie),
      TrieOK trie -> MapsTo k e trie -> find k trie = Some e.
  Proof.
    induction k; destruct trie; simpl; intros;
    inversion H0; subst.
    - reflexivity.
    - case_eq (XMap.Raw.find a m); intros.
      erewrite IHk; eauto.
      apply XMap.Raw.Proofs.find_1 in H5; eauto.
      rewrite H5 in H1; injections; eauto.
      inversion H; eauto.
      apply XMap.Raw.Proofs.find_1 in H5; eauto.
      rewrite H5 in H1; discriminate.
    - case_eq (XMap.Raw.find a m); intros; eauto.
      case_eq (find k t0); eauto; intros.
      elimtype False; eapply H4.
      apply XMap.Raw.Proofs.find_iff in H1; eauto.
      apply mem_2.
      apply mem_1; eauto using SubTrieOK.
      eapply find_in; eauto using SubTrieOK.
      congruence.
  Qed.
    
  Lemma find_2 
  : forall (k : key) (e : elt) (trie : Trie),
      TrieOK trie
      -> find k trie = Some e -> MapsTo k e trie.
  Proof.
    induction k; destruct trie; simpl; intros; subst.
    - econstructor.
    - revert H0; case_eq (XMap.Raw.find a m); intros.
      + revert H1; case_eq (find k t0); eauto; intros.
        * injections; econstructor.
          apply XMap.Raw.Proofs.find_2 in H0; eauto.
          eapply IHk; eauto.
        * subst; econstructor 3.
          intros; apply XMap.Raw.Proofs.find_1 in H2; eauto.
          rewrite H0 in H2; injections.
          intro; eapply in_find; 
          try eapply SubTrieOK; eauto.
      + subst; econstructor 3.
        intros; apply XMap.Raw.Proofs.find_1 in H1; eauto.
        congruence.
  Qed.
    
  (* Addition *)

  Fixpoint add
           (k : key)
           (e : elt)
           (trie : Trie)
  : Trie :=
    match k with
      | nil => Node (Some e) (SubTries trie)
      | k' :: st' =>
        Node (TrieNode trie)
             
             ((fix list_add (l : list (X.t * Trie)) : list (X.t * Trie) :=
                 match l with
                   | nil => (k', add st' e empty) :: nil
                   | (key', trie') :: l' =>
                     if X.eq_dec k' key' then
                       (key', add st' e trie') :: l'
                     else
                       (key', trie') :: (list_add l')
                 end) (SubTries trie))
    end.

  (* Removal *)
  Fixpoint remove
           (k : key)
           (trie : Trie)
  : Trie :=
    match k with
      | nil => Node None (SubTries trie)
      | k' :: st' =>
        Node (TrieNode trie)
             ((fix list_remove (l : list (X.t * Trie)) : list (X.t * Trie) :=
                 match l with
                   | nil => nil
                   | (key', trie') :: l' =>
                     if X.eq_dec k' key' then
                       (key', remove st' trie') :: l'
                     else
                       (key', trie') :: (list_remove l')
                 end) (SubTries trie))
    end.

  (* Enumeration *)
  Fixpoint elements
           (t : Trie)
  : list elt :=
    match t with
      | Node (Some e) tries =>
        e :: (flatten (List.map (fun kt => elements (snd kt)) tries))
      | Node None tries =>
        flatten (List.map (fun kt => elements (snd kt)) tries)
    end.


  Variables elt' elt'' : Type.

  (* Mapping *)
  Fixpoint map (f : elt -> elt') ->


  Notation eqk := (eqk (elt:=elt)).
  Notation eqke := (eqke (elt:=elt)).
  Notation ltk := (ltk (elt:=elt)).
  Notation MapsTo := (MapsTo (elt:=elt)).
  Notation In := (In (elt:=elt)).
  Notation Sort := (sort ltk).
  Notation Inf := (lelistA (ltk)).


  Print PX.MapsTo.
  Definition Empty (m : t elt) :=
    forall (a : key) (e:elt) , ~ MapsTo a e m.

  Print Empty.

  Lemma empty_1 : Empty empty.
    Hint Resolve empty_1.

Lemma empty_sorted : Sort empty.

is_empty

Definition is_empty (l : t elt) : bool := if l then true else false.

Lemma is_empty_1 :forall m, Empty m -> is_empty m = true.

Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.

mem

Function mem (k : key) (s : t elt) {struct s} : bool :=
 match s with
  | nil => false
  | (k´,_) :: l =>
     match X.compare k k´ with
      | LT _ => false
      | EQ _ => true
      | GT _ => mem k l
     end
 end.

Lemma mem_1 : forall m (Hm:Sort m) x, In x m -> mem x m = true.

Lemma mem_2 : forall m (Hm:Sort m) x, mem x m = true -> In x m.

find

Function find (k:key) (s: t elt) {struct s} : option elt :=
 match s with
  | nil => None
  | (k´,x)::s´ =>
     match X.compare k k´ with
      | LT _ => None
      | EQ _ => Some x
      | GT _ => find k s´
     end
 end.

Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.

Lemma find_1 : forall m (Hm:Sort m) x e, MapsTo x e m -> find x m = Some e.

add

Function add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
 match s with
  | nil => (k,x) :: nil
  | (k´,y) :: l =>
     match X.compare k k´ with
      | LT _ => (k,x)::s
      | EQ _ => (k,x)::l
      | GT _ => (k´,y) :: add k x l
     end
 end.

Lemma add_1 : forall m x y e, X.eq x y -> MapsTo y e (add x e m).

Lemma add_2 : forall m x y e e´,
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e´ m).

Lemma add_3 : forall m x y e e´,
  ~ X.eq x y -> MapsTo y e (add x e´ m) -> MapsTo y e m.

Lemma add_Inf : forall (m:t elt)(x x´:key)(e e´:elt),
  Inf (x´,e´) m -> ltk (x´,e´) (x,e) -> Inf (x´,e´) (add x e m).
Hint Resolve add_Inf.

Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).

remove

Function remove (k : key) (s : t elt) {struct s} : t elt :=
 match s with
  | nil => nil
  | (k´,x) :: l =>
     match X.compare k k´ with
      | LT _ => s
      | EQ _ => l
      | GT _ => (k´,x) :: remove k l
     end
 end.

Lemma remove_1 : forall m (Hm:Sort m) x y, X.eq x y -> ~ In y (remove x m).

Lemma remove_2 : forall m (Hm:Sort m) x y e,
  ~ X.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).

Lemma remove_3 : forall m (Hm:Sort m) x y e,
  MapsTo y e (remove x m) -> MapsTo y e m.

Lemma remove_Inf : forall (m:t elt)(Hm : Sort m)(x x´:key)(e´:elt),
  Inf (x´,e´) m -> Inf (x´,e´) (remove x m).
Hint Resolve remove_Inf.

Lemma remove_sorted : forall m (Hm:Sort m) x, Sort (remove x m).

elements

Definition elements (m: t elt) := m.

Lemma elements_1 : forall m x e,
  MapsTo x e m -> InA eqke (x,e) (elements m).

Lemma elements_2 : forall m x e,
  InA eqke (x,e) (elements m) -> MapsTo x e m.

Lemma elements_3 : forall m (Hm:Sort m), sort ltk (elements m).

Lemma elements_3w : forall m (Hm:Sort m), NoDupA eqk (elements m).

fold

Function fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc:A) {struct m} : A :=
  match m with
   | nil => acc
   | (k,e)::m´ => fold f m´ (f k e acc)
  end.

Lemma fold_1 : forall m (A:Type)(i:A)(f:key->elt->A->A),
  fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

equal

Function equal (cmp:elt->elt->bool)(m m´ : t elt) {struct m} : bool :=
  match m, m´ with
   | nil, nil => true
   | (x,e)::l, (x´,e´)::l´ =>
      match X.compare x x´ with
       | EQ _ => cmp e e´ && equal cmp l l´
       | _ => false
      end
   | _, _ => false
  end.

Definition Equivb cmp m m´ :=
  (forall k, In k m <-> In k m´) /\
  (forall k e e´, MapsTo k e m -> MapsTo k e´ m´ -> cmp e e´ = true).

Lemma equal_1 : forall m (Hm:Sort m) m´ (Hm´: Sort m´) cmp,
  Equivb cmp m m´ -> equal cmp m m´ = true.

Lemma equal_2 : forall m (Hm:Sort m) m´ (Hm:Sort m´) cmp,
  equal cmp m m´ = true -> Equivb cmp m m´.

This lemma isn't part of the spec of Equivb, but is used in FMapAVL

Lemma equal_cons : forall cmp l1 l2 x y, Sort (x::l1) -> Sort (y::l2) ->
  eqk x y -> cmp (snd x) (snd y) = true ->
  (Equivb cmp l1 l2 <-> Equivb cmp (x :: l1) (y :: l2)).

Variable elt´:Type.

map and mapi

Fixpoint map (f:elt -> elt´) (m:t elt) : t elt´ :=
  match m with
   | nil => nil
   | (k,e)::m´ => (k,f e) :: map f m´
  end.

Fixpoint mapi (f: key -> elt -> elt´) (m:t elt) : t elt´ :=
  match m with
   | nil => nil
   | (k,e)::m´ => (k,f k e) :: mapi f m´
  end.

End Elt.
Section Elt2.

Variable elt elt´ : Type.

Specification of map

Lemma map_1 : forall (m:t elt)(x:key)(e:elt)(f:elt->elt´),
  MapsTo x e m -> MapsTo x (f e) (map f m).

Lemma map_2 : forall (m:t elt)(x:key)(f:elt->elt´),
  In x (map f m) -> In x m.

Lemma map_lelistA : forall (m: t elt)(x:key)(e:elt)(e´:elt´)(f:elt->elt´),
  lelistA (@ltk elt) (x,e) m ->
  lelistA (@ltk elt´) (x,e´) (map f m).

Hint Resolve map_lelistA.

Lemma map_sorted : forall (m: t elt)(Hm : sort (@ltk elt) m)(f:elt -> elt´),
  sort (@ltk elt´) (map f m).

Specification of mapi

Lemma mapi_1 : forall (m:t elt)(x:key)(e:elt)(f:key->elt->elt´),
  MapsTo x e m ->
  exists y, X.eq y x /\ MapsTo x (f y e) (mapi f m).

Lemma mapi_2 : forall (m:t elt)(x:key)(f:key->elt->elt´),
  In x (mapi f m) -> In x m.

Lemma mapi_lelistA : forall (m: t elt)(x:key)(e:elt)(f:key->elt->elt´),
  lelistA (@ltk elt) (x,e) m ->
  lelistA (@ltk elt´) (x,f x e) (mapi f m).

Hint Resolve mapi_lelistA.

Lemma mapi_sorted : forall m (Hm : sort (@ltk elt) m)(f: key ->elt -> elt´),
  sort (@ltk elt´) (mapi f m).

End Elt2.
Section Elt3.

map2

Variable elt elt´ elt´´ : Type.
Variable f : option elt -> option elt´ -> option elt´´.

Definition option_cons (A:Type)(k:key)(o:option A)(l:list (key*A)) :=
  match o with
   | Some e => (k,e)::l
   | None => l
  end.

Fixpoint map2_l (m : t elt) : t elt´´ :=
  match m with
   | nil => nil
   | (k,e)::l => option_cons k (f (Some e) None) (map2_l l)
  end.

Fixpoint map2_r (m´ : t elt´) : t elt´´ :=
  match m´ with
   | nil => nil
   | (k,e´)::l´ => option_cons k (f None (Some e´)) (map2_r l´)
  end.

Fixpoint map2 (m : t elt) : t elt´ -> t elt´´ :=
  match m with
   | nil => map2_r
   | (k,e) :: l =>
      fix map2_aux (m´ : t elt´) : t elt´´ :=
        match m´ with
         | nil => map2_l m
         | (k´,e´) :: l´ =>
            match X.compare k k´ with
             | LT _ => option_cons k (f (Some e) None) (map2 l m´)
             | EQ _ => option_cons k (f (Some e) (Some e´)) (map2 l l´)
             | GT _ => option_cons k´ (f None (Some e´)) (map2_aux l´)
            end
        end
  end.

Notation oee´ := (option elt * option elt´)%type.

Fixpoint combine (m : t elt) : t elt´ -> t oee´ :=
  match m with
   | nil => map (fun e´ => (None,Some e´))
   | (k,e) :: l =>
      fix combine_aux (m´:t elt´) : list (key * oee´) :=
        match m´ with
         | nil => map (fun e => (Some e,None)) m
         | (k´,e´) :: l´ =>
            match X.compare k k´ with
             | LT _ => (k,(Some e, None))::combine l m´
             | EQ _ => (k,(Some e, Some e´))::combine l l´
             | GT _ => (k´,(None,Some e´))::combine_aux l´
            end
        end
  end.

Definition fold_right_pair (A B C:Type)(f: A->B->C->C)(l:list (A*B))(i:C) :=
  List.fold_right (fun p => f (fst p) (snd p)) i l.

Definition map2_alt m m´ :=
  let m0 : t oee´ := combine m m´ in
  let m1 : t (option elt´´) := map (fun p => f (fst p) (snd p)) m0 in
  fold_right_pair (option_cons (A:=elt´´)) m1 nil.

Lemma map2_alt_equiv : forall m m´, map2_alt m m´ = map2 m m´.

Lemma combine_lelistA :
  forall m m´ (x:key)(e:elt)(e´:elt´)(e´´:oee´),
  lelistA (@ltk elt) (x,e) m ->
  lelistA (@ltk elt´) (x,e´) m´ ->
  lelistA (@ltk oee´) (x,e´´) (combine m m´).
Hint Resolve combine_lelistA.

Lemma combine_sorted :
  forall m (Hm : sort (@ltk elt) m) m´ (Hm´ : sort (@ltk elt´) m´),
  sort (@ltk oee´) (combine m m´).

Lemma map2_sorted :
  forall m (Hm : sort (@ltk elt) m) m´ (Hm´ : sort (@ltk elt´) m´),
  sort (@ltk elt´´) (map2 m m´).

Definition at_least_one (o:option elt)(o´:option elt´) :=
  match o, o´ with
   | None, None => None
   | _, _ => Some (o,o´)
  end.

Lemma combine_1 :
  forall m (Hm : sort (@ltk elt) m) m´ (Hm´ : sort (@ltk elt´) m´) (x:key),
  find x (combine m m´) = at_least_one (find x m) (find x m´).

Definition at_least_one_then_f (o:option elt)(o´:option elt´) :=
  match o, o´ with
   | None, None => None
   | _, _ => f o o´
  end.

Lemma map2_0 :
  forall m (Hm : sort (@ltk elt) m) m´ (Hm´ : sort (@ltk elt´) m´) (x:key),
  find x (map2 m m´) = at_least_one_then_f (find x m) (find x m´).

Specification of map2

Lemma map2_1 :
  forall m (Hm : sort (@ltk elt) m) m´ (Hm´ : sort (@ltk elt´) m´)(x:key),
  In x m \/ In x m´ ->
  find x (map2 m m´) = f (find x m) (find x m´).

Lemma map2_2 :
  forall m (Hm : sort (@ltk elt) m) m´ (Hm´ : sort (@ltk elt´) m´)(x:key),
  In x (map2 m m´) -> In x m \/ In x m´.

End Elt3.
End Raw.

Module Make (X: OrderedType) <: S with Module E := X.
Module Raw := Raw X.
Module E := X.

Definition key := E.t.

Record slist (elt:Type) :=
  {this :> Raw.t elt; sorted : sort (@Raw.PX.ltk elt) this}.
Definition t (elt:Type) : Type := slist elt.

Section Elt.
 Variable elt elt´ elt´´:Type.

 Implicit Types m : t elt.
 Implicit Types x y : key.
 Implicit Types e : elt.

 Definition empty : t elt := Build_slist (Raw.empty_sorted elt).
 Definition is_empty m : bool := Raw.is_empty m.(this).
 Definition add x e m : t elt := Build_slist (Raw.add_sorted m.(sorted) x e).
 Definition find x m : option elt := Raw.find x m.(this).
 Definition remove x m : t elt := Build_slist (Raw.remove_sorted m.(sorted) x).
 Definition mem x m : bool := Raw.mem x m.(this).
 Definition map f m : t elt´ := Build_slist (Raw.map_sorted m.(sorted) f).
 Definition mapi (f:key->elt->elt´) m : t elt´ := Build_slist (Raw.mapi_sorted m.(sorted) f).
 Definition map2 f m (m´:t elt´) : t elt´´ :=
   Build_slist (Raw.map2_sorted f m.(sorted) m´.(sorted)).
 Definition elements m : list (key*elt) := @Raw.elements elt m.(this).
 Definition cardinal m := length m.(this).
 Definition fold (A:Type)(f:key->elt->A->A) m (i:A) : A := @Raw.fold elt A f m.(this) i.
 Definition equal cmp m m´ : bool := @Raw.equal elt cmp m.(this) m´.(this).

 Definition MapsTo x e m : Prop := Raw.PX.MapsTo x e m.(this).
 Definition In x m : Prop := Raw.PX.In x m.(this).
 Definition Empty m : Prop := Raw.Empty m.(this).

 Definition Equal m m´ := forall y, find y m = find y m´.
 Definition Equiv (eq_elt:elt->elt->Prop) m m´ :=
         (forall k, In k m <-> In k m´) /\
         (forall k e e´, MapsTo k e m -> MapsTo k e´ m´ -> eq_elt e e´).
 Definition Equivb cmp m m´ : Prop := @Raw.Equivb elt cmp m.(this) m´.(this).

 Definition eq_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.eqk elt.
 Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop:= @Raw.PX.eqke elt.
 Definition lt_key : (key*elt) -> (key*elt) -> Prop := @Raw.PX.ltk elt.

 Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.

 Lemma mem_1 : forall m x, In x m -> mem x m = true.
 Lemma mem_2 : forall m x, mem x m = true -> In x m.

 Lemma empty_1 : Empty empty.

 Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
 Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.

 Lemma add_1 : forall m x y e, E.eq x y -> MapsTo y e (add x e m).
 Lemma add_2 : forall m x y e e´, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e´ m).
 Lemma add_3 : forall m x y e e´, ~ E.eq x y -> MapsTo y e (add x e´ m) -> MapsTo y e m.

 Lemma remove_1 : forall m x y, E.eq x y -> ~ In y (remove x m).
 Lemma remove_2 : forall m x y e, ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
 Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.

 Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
 Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.

 Lemma elements_1 : forall m x e, MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
 Lemma elements_2 : forall m x e, InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
 Lemma elements_3 : forall m, sort lt_key (elements m).
 Lemma elements_3w : forall m, NoDupA eq_key (elements m).

 Lemma cardinal_1 : forall m, cardinal m = length (elements m).

 Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

 Lemma equal_1 : forall m m´ cmp, Equivb cmp m m´ -> equal cmp m m´ = true.
 Lemma equal_2 : forall m m´ cmp, equal cmp m m´ = true -> Equivb cmp m m´.

 End Elt.

 Lemma map_1 : forall (elt elt´:Type)(m: t elt)(x:key)(e:elt)(f:elt->elt´),
        MapsTo x e m -> MapsTo x (f e) (map f m).
 Lemma map_2 : forall (elt elt´:Type)(m: t elt)(x:key)(f:elt->elt´),
        In x (map f m) -> In x m.

 Lemma mapi_1 : forall (elt elt´:Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt´), MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
 Lemma mapi_2 : forall (elt elt´:Type)(m: t elt)(x:key)
        (f:key->elt->elt´), In x (mapi f m) -> In x m.

 Lemma map2_1 : forall (elt elt´ elt´´:Type)(m: t elt)(m´: t elt´)
        (x:key)(f:option elt->option elt´->option elt´´),
        In x m \/ In x m´ ->
        find x (map2 f m m´) = f (find x m) (find x m´).
 Lemma map2_2 : forall (elt elt´ elt´´:Type)(m: t elt)(m´: t elt´)
        (x:key)(f:option elt->option elt´->option elt´´),
        In x (map2 f m m´) -> In x m \/ In x m´.

End Make.

Module Make_ord (X: OrderedType)(D : OrderedType) <:
Sord with Module Data := D
        with Module MapS.E := X.

Module Data := D.
Module MapS := Make(X).
Import MapS.

Module MD := OrderedTypeFacts(D).
Import MD.

Definition t := MapS.t D.t.

Definition cmp e e´ := match D.compare e e´ with EQ _ => true | _ => false end.

Fixpoint eq_list (m m´ : list (X.t * D.t)) : Prop :=
  match m, m´ with
   | nil, nil => True
   | (x,e)::l, (x´,e´)::l´ =>
      match X.compare x x´ with
       | EQ _ => D.eq e e´ /\ eq_list l l´
       | _ => False
      end
   | _, _ => False
  end.

Definition eq m m´ := eq_list m.(this) m´.(this).

Fixpoint lt_list (m m´ : list (X.t * D.t)) : Prop :=
  match m, m´ with
   | nil, nil => False
   | nil, _ => True
   | _, nil => False
   | (x,e)::l, (x´,e´)::l´ =>
      match X.compare x x´ with
       | LT _ => True
       | GT _ => False
       | EQ _ => D.lt e e´ \/ (D.eq e e´ /\ lt_list l l´)
      end
  end.

Definition lt m m´ := lt_list m.(this) m´.(this).

Lemma eq_equal : forall m m´, eq m m´ <-> equal cmp m m´ = true.

Lemma eq_1 : forall m m´, Equivb cmp m m´ -> eq m m´.

Lemma eq_2 : forall m m´, eq m m´ -> Equivb cmp m m´.

Lemma eq_refl : forall m : t, eq m m.

Lemma eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.

Lemma eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.

Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.

Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

Ltac cmp_solve := unfold eq, lt; simpl; try Raw.MX.elim_comp; auto.

Definition compare : forall m1 m2, Compare lt eq m1 m2.

End Make_ord.
Navigation

    Standard Library
        Table of contents
        Index

    webmaster xhtml valid CSS valid
