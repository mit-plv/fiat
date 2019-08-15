Require Import
  Bedrock.Word
  Coq.Arith.Arith
  Fiat.QueryStructure.Automation.MasterPlan
  IndexedEnsembles
  Fiat.Common.EnumType
  Coq.Vectors.Vector
  Fiat.Narcissus.Examples.NetworkStack.IPv4Header
  Fiat.Narcissus.Examples.NetworkStack.TCP_Packet
  Fiat.Narcissus.Examples.NetworkStack.UDP_Packet
  Fiat.Narcissus.Examples.Guard.IPTables.
Import VectorNotations.

(* comment-out to use IPTables input *)
Record input :=
  { source: word 16;
    destination: word 16;
    payload: string;
    flag: bool }.

Definition Complete_heading := < "Input" :: input >%Heading.
Definition Complete_topkt (t: @Tuple Complete_heading) := t!"Input".
Definition Complete_totup (i: input) := < "Input" :: i >.
Lemma Complete_inverse :
  forall i, i = Complete_topkt (Complete_totup i).
Proof. reflexivity. Qed.
Lemma Complete_inverse' :
  forall t, t = Complete_totup (Complete_topkt t).
Proof. destruct t. destruct prim_snd. reflexivity. Qed.

Definition PacketHistorySchema (h: Heading) :=
  Query Structure Schema
        [ relation "History" has schema h ]
        enforcing [].
Definition CompletePacketHistorySchema := PacketHistorySchema Complete_heading.

Notation "qs ! R" := (GetRelationBnd qs {| bindex := R; indexb := _ |}) : myqs_scope.
Delimit Scope myqs_scope with myqs.

Open Scope myqs.
Definition Complete_Dropped_qs_equiv (h: Heading) (totup: input -> @Tuple h)
           (r_o: QueryStructure CompletePacketHistorySchema)
           (r_n: QueryStructure (PacketHistorySchema h)) :=
  forall inp, IndexedEnsemble_In r_o!"History" (Complete_totup inp) <->
         IndexedEnsemble_In r_n!"History" (totup inp).
Definition FilterType := forall (h: Heading), (@Tuple h -> input) -> (input -> @Tuple h)
  -> (QueryStructure (PacketHistorySchema h)) -> input -> Comp (option result).
Definition Complete_filter (f: FilterType) :=
  f Complete_heading Complete_topkt Complete_totup.

Definition Complete_Dropped_equiv (h: Heading) (topkt: @Tuple h -> input)
           (totup: input -> @Tuple h) (f: FilterType) :=
  forall r_o r_n, Complete_Dropped_qs_equiv h totup r_o r_n ->
  forall inp, refine (Complete_filter f r_o inp) (f h topkt totup r_n inp).

Definition In_History {h: Heading} (totup: input -> @Tuple h)
           (r: QueryStructure (PacketHistorySchema h)) (p: input) : Prop :=
  IndexedEnsemble_In (r!"History")%myqs (totup p).
Definition flag_true (p: input) : Prop := flag p = true.
Definition and_prop {h: Heading} totup r p := @In_History h totup r p /\ flag_true p.
(* Opaque In_History flag_true. *)

Definition f (h: Heading) (topkt: @Tuple h -> input) (totup: input -> @Tuple h)
           (r: QueryStructure (PacketHistorySchema h)) (inp: input) :=
  If (weqb (wones 16) inp.(source))
  Then ret (Some ACCEPT)
  Else (b <- { b: bool | decides b (exists pre,
                 and_prop totup r pre) };
          if b then ret (Some ACCEPT) else ret (Some DROP)).

(* Definition f (pkt: packet) := andb (weqb (pkt.(destination)) (wones 16))
                                   pkt.(flag). *)


Definition accessor : Type := { t: Type & input -> t }.
Definition acc {T: Type} (t: input -> T) :=
  match t return accessor with _ => (existT _ _ t) end.

Notation "acc1 '//' acc2" :=
  (fun p => (acc2 (acc1 p))) (at level 90, no associativity).

(* Definition acc2head : list (accessor * string) :=
  [ (acc (in_ip4 // TotalLength), "TotalLength");
    (acc (in_ip4 // ID), "Identifier");
    (acc (in_ip4 // DF), "DontFragment");
    (acc (in_ip4 // MF), "MultipleFragments");
    (acc (in_ip4 // FragmentOffset), "FragmentOffset");
    (acc (in_ip4 // TTL), "TTL");
    (acc (in_ip4 // Protocol), "Protocol");
    (acc (in_ip4 // SourceAddress), "SourceAddress");
    (acc (in_ip4 // DestAddress), "DestAddress");
    (acc (in_ip4 // IPv4Header.Options), "Options");
    (acc in_tcp, "optTCPpacket");
    (acc in_udp, "optUDPpacket");
    (acc in_chn, "Chain") ]. *)
Definition acc2head : list (accessor * string) :=
  [ (acc source, "source");
    (acc destination, "destination");
    (acc payload, "payload");
    (acc flag, "flag") ].

Open Scope list_scope.
Ltac for_each_acc' acclist k :=
  match acclist with
  | [] => idtac
  | ?a :: ?tl =>
    let t := (eval cbn in (projT1 (fst a))) in
    let f := (eval cbn in (projT2 (fst a))) in
    let h := (eval cbn in (snd a)) in
    k t f h; for_each_acc' tl k
  end.
Close Scope list_scope.
Ltac for_each_acc k :=
  let a := (eval unfold acc2head in acc2head) in for_each_acc' a k.

Ltac dummy_type x k :=
  match (type of x) with
  | word ?n => k (wzero n)
  | string => k ""
  | bool => k false
  | list ?T => k (@Datatypes.nil T)
  | EnumType ["ICMP"; "TCP"; "UDP"] => k (@Fin.F1 2)
  | option ?T => k (@None T)
  | chain => k INPUT
  end.

Ltac dummy_type' :=
  repeat constructor;
  match goal with
  | [|- word ?n] => apply (wzero n)
  | [|- string] => apply ""
  | [|- ()] => apply tt
  | [|- bool] => apply false
  end.

Ltac change_dummy x :=
  match goal with
  | [|- context c [x]] =>
    let c' := dummy_type x ltac:(fun d => context c [d]) in
    change c'
  end.

Ltac evec_cons x vec :=
  let y := fresh in
  pose (x :: vec) as y; subst vec; rename y into vec.

Ltac change_dummy_else_tuple_heading acc_type acc_fun head :=
  match goal with [ attrs: Vector.t Attribute _, inp: input |- _ ] =>
  let acc_fun_inp := (eval cbv beta in (acc_fun inp)) in
  tryif change_dummy acc_fun_inp then idtac else
    (evec_cons (Build_Attribute head acc_type) attrs;
     match goal with
     | [ ftup: input -> ilist2 _ |- _ ] =>
       let y := fresh in
       pose (fun p => icons2 (head :: acc_fun p)%Component (ftup p)) as y;
       subst ftup; rename y into ftup; cbv beta in ftup
     | _ => pose (fun p => icons2 (head :: acc_fun p)%Component inil2) as ftup
     end)
  end.


Ltac build_topkt' acc_fun head fpkt tup pkt :=
  let y' := fresh in
  let y := (eval unfold fpkt in fpkt) in
  let acc_fun_pkt := (eval cbv beta in (acc_fun pkt)) in
  match y with context c [acc_fun_pkt] =>
    let c' := context c[tup!head] in pose c' as y'
  end;
  clear fpkt; rename y' into fpkt.

Ltac build_topkt heading :=
  evar (tup: @Tuple heading);
  match goal with [ pkt: input, tup: @Tuple heading |- f ?p = _] =>
    pose p as fpkt;
    for_each_acc ltac:(fun acc_type acc_fun head =>
                         try build_topkt' acc_fun head fpkt tup pkt);
    (let fpkt := (eval unfold fpkt in fpkt) in
     let fpkt := (eval pattern tup in fpkt) in
     match fpkt with
     | ?f tup => pose f as topkt
     end);
    clear tup fpkt
  end.

Ltac destruct_packet pkt :=
  pose Build_input as pkt';
  for_each_acc ltac:(fun _ acc_fun _ =>
                       pose (pkt' (acc_fun pkt)) as p; subst pkt';
                       rename p into pkt');
  assert (Hpkt: pkt = pkt') by (destruct pkt; reflexivity);
  subst pkt'; rewrite Hpkt; clear Hpkt.


Ltac comp_inv :=
  match goal with
  | [H: computes_to _ _ |- _] => inversion H; unfold Ensembles.In in *; clear H
  | [H: _ /\ _ |- _] => destruct H
  | [H: ret _ _ |- _] => inversion H; clear H
  | [H: Bind _ _ _ |- _] => inversion H; unfold Ensembles.In in *; clear H
  | [H: Bind2 _ _ _ |- _] => inversion H; unfold Ensembles.In in *; clear H
  end.


Theorem drop_fields:
  exists h (totup: input -> @Tuple h) topkt,
    Complete_Dropped_equiv h topkt totup f.
Proof.
  eexists. eexists. eexists. red. intros r_o r_n Hrpre pkt.
  destruct_packet pkt.

(*  pose Build_input as pkt'. pose Build_IPv4_Packet as pkt'.
  for_each_acc ltac:(fun _ acc_fun _ =>
                       try (pose (pkt' (acc_fun pkt)) as p; subst pkt'; rename p into pkt')).
  pose (i pkt') as tmp; subst pkt'; rename tmp into pkt'.
  for_each_acc ltac:(fun _ acc_fun _ =>
                       try (pose (pkt' (acc_fun pkt)) as p; subst pkt';
                       rename p into pkt')).
  assert (Hpkt: pkt = pkt') by (destruct pkt; destruct in_ip4; reflexivity);
    subst pkt'; rewrite Hpkt; clear Hpkt. subst i. *)

  unfold f.
  match goal with
  | [|- context c [fun p: input => ?cond p]] =>
    idtac c
  end.

  (*destruct_packet pkt.*)
  pose (Vector.nil Attribute) as attrs.

  red in Hrpre. unfold f.
  
  (*  unfold Complete_f. unfold f. unfold Complete_topkt.
  unfold Complete_Dropped_equiv. *)
  Ltac mychange x :=
    match x with
    | context c [flag ?p] =>
      let c' := dummy_type (flag p) ltac:(fun d => context c [d]) in
      mychange c'
    | _ => idtac x
    end.

  match goal with
  | [|- ?P] => mychange P
  end.
  
  {
    intros r_o' r_n' res_o res_n H_o H_n. repeat comp_inv. subst. split.
    - red in H0.
    change_dummy ( pkt).
  for_each_acc change_dummy_else_tuple_heading.

  pose (BuildHeading attrs) as h.
  build_topkt h.
  pose (fun p => (BuildTuple attrs (ftup p))) as totup.
  subst attrs h ftup.
  
  let totup := (eval unfold totup in totup) in
  instantiate (1 := totup).
  let topkt := (eval unfold topkt in topkt) in
  instantiate (1 := topkt).

  reflexivity.
  Unshelve. constructor; cbn; dummy_type'. (* for the cleared evar *)
Defined.

Goal input -> True.
  intros inp.
  let d := (eval unfold drop_fields in drop_fields) in
  match d with
  | ex_intro _ ?h ?p => pose h;
    match p with
    | ex_intro _ ?ftup ?p => pose ftup as totup;
      match p with
      | ex_intro _ ?fpkt ?p => pose fpkt as topkt; pose p as H'
      end
    end
  end;
  assert (H: f inp = f (topkt (totup inp))) by apply H'; clear H'.
  
  destruct e as [h [totup [topkt H]]].
  