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

(* Record packet :=
  { source: word 16;
    destination: word 16;
    payload: string;
    flag: bool }. *)

Definition f (inp: input) :=
  (iptables -A FORWARD --source 18'0'0'0/8 -j ACCEPT) inp.
(* Definition f (pkt: packet) := andb (weqb (pkt.(destination)) (wones 16))
                                   pkt.(flag). *)


Definition accessor : Type := { t: Type & input -> t }.
Definition acc {T: Type} (t: input -> T) :=
  match t return accessor with _ => (existT _ _ t) end.

Notation "acc1 '//' acc2" :=
  (fun p => (acc2 (acc1 p))) (at level 90, no associativity).

Definition acc2head : list (accessor * string) :=
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
    (acc in_chn, "Chain") ].
(* Definition acc2head : list (accessor * string) :=
  [ (acc source, "source");
    (acc destination, "destination");
    (acc payload, "payload");
    (acc flag, "flag") ]. *)

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

(*
Ltac destruct_packet pkt :=
  pose Build_packet as pkt';
  for_each_acc ltac:(fun _ acc_fun _ =>
                       pose (pkt' (acc_fun pkt)) as p; subst pkt';
                       rename p into pkt');
  assert (Hpkt: pkt = pkt') by (destruct pkt; reflexivity);
  subst pkt'; rewrite Hpkt; clear Hpkt.
*)

Theorem drop_fields:
  exists h (totup: input -> @Tuple h) topkt, forall pkt,
  f pkt = f (topkt (totup pkt)).
Proof.
  repeat eexists.
  intros. pose Build_input. pose Build_IPv4_Packet as pkt'.
  for_each_acc ltac:(fun _ acc_fun _ =>
                       try (pose (pkt' (acc_fun pkt)) as p; subst pkt'; rename p into pkt')).
  pose (i pkt') as tmp; subst pkt'; rename tmp into pkt'.
  for_each_acc ltac:(fun _ acc_fun _ =>
                       try (pose (pkt' (acc_fun pkt)) as p; subst pkt';
                       rename p into pkt')).
  assert (Hpkt: pkt = pkt') by (destruct pkt; destruct in_ip4; reflexivity);
  subst pkt'; rewrite Hpkt; clear Hpkt. subst i.

  (*destruct_packet pkt.*)
  pose (Vector.nil Attribute) as attrs.

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
  