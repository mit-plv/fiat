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


(** Definitions **)

(* Complete_ is what you have before you drop any packet fields *)
Definition Complete_heading := < "Input" :: input >%Heading.
Definition Complete_topkt (t: @Tuple Complete_heading) := t!"Input".
Definition Complete_totup (i: input) := < "Input" :: i >.

Definition PacketHistorySchema (h: Heading) :=
  Query Structure Schema
        [ relation "History" has schema h ]
        enforcing [].
Definition Complete_PacketHistorySchema := PacketHistorySchema Complete_heading.
(* for some reason this notation is only predefined for UnConstrQS *)
Notation "qs ! R" := (GetRelationBnd qs {| bindex := R; indexb := _ |}) : myqs_scope.
Delimit Scope myqs_scope with myqs.

(* a Complete_ history is equivalent to a history with dropped fields
   under some function from packets (with all fields) to Tuples (with some fields) *)
Open Scope myqs.
Definition Complete_Dropped_qs_equiv {h: Heading} (totup: input -> @Tuple h)
           (r_o: QueryStructure Complete_PacketHistorySchema)
           (r_n: QueryStructure (PacketHistorySchema h)) :=
  forall inp, IndexedEnsemble_In r_o!"History" (Complete_totup inp) <->
         IndexedEnsemble_In r_n!"History" (totup inp).

(* we want the same filter body to operate on different schemas of history,
   i.e. Complete_ histories and histories with dropped fields,
   so the parameters of a filter include the packet-Tuple conversions *)
Definition FilterType := forall (h: Heading), (@Tuple h -> input) -> (input -> @Tuple h)
  -> (QueryStructure (PacketHistorySchema h)) -> input -> Comp (option result).
Definition Complete_filter (f: FilterType) :=
  f Complete_heading Complete_topkt Complete_totup.

(* given a field-dropped history equivalent to the Complete_ history,
   the filter function should behave the same on all inputs *)
Definition Complete_Dropped_equiv (h: Heading) (topkt: @Tuple h -> input)
           (totup: input -> @Tuple h) (f: FilterType) :=
  forall r_o r_n, Complete_Dropped_qs_equiv totup r_o r_n ->
  forall inp, refine (Complete_filter f r_o inp) (f h topkt totup r_n inp).

(* the theorem below is trivial for any filter if we use packet-Tuple conversion
   functions that keep all the fields, but we want to find conversion functions
   that only keep the required fields, which is what the proof tactics do *)
Definition Drop_Fields (f: FilterType) :=
  exists h (totup: input -> @Tuple h) topkt,
    Complete_Dropped_equiv h topkt totup f.

Definition In_History {h: Heading} (totup: input -> @Tuple h)
           (r: QueryStructure (PacketHistorySchema h)) (p: input) : Prop :=
  IndexedEnsemble_In (r!"History")%myqs (totup p).
Close Scope myqs.


(** Tactics **)

Ltac unfold_Complete_f f :=
  unfold Complete_filter;
  let f' := (eval unfold f in f) in
  assert (Hf: forall h topkt totup r inp,
             f h topkt totup r inp = f' h topkt totup r inp) by reflexivity;
  rewrite Hf; clear Hf.

Ltac refold_Complete_f f :=
  let f' := (eval unfold f in f) in
  assert (Hf: forall h topkt totup r inp,
             f h topkt totup r inp = f' h topkt totup r inp) by reflexivity;
  rewrite <- Hf with _ Complete_topkt _ _ _; clear Hf;
  fold (Complete_filter f).


(* packet field accessor function *)
Definition accessor : Type := { t: Type & input -> t }.
Definition acc {T: Type} (t: input -> T) :=
  match t return accessor with _ => (existT _ _ t) end.
Notation "acc1 '//' acc2" :=
  (fun p => (acc2 (acc1 p))) (at level 90, no associativity).

(* needs to be manually written! *)
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


(* iterate over the accessors *)
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

(* dummy values for each packet field type *)
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

(* how to destruct a packet in-place
   FIXME: needs to be manually written! *)
Ltac destruct_packet pkt :=
  pose Build_input as pkt';
  pose Build_IPv4_Packet as pkt'';
  for_each_acc ltac:(fun _ acc_fun _ =>
                       try (pose (pkt'' (acc_fun pkt)) as p; subst pkt'';
                            rename p into pkt''));
  pose (pkt' pkt'') as p; subst pkt' pkt''; rename p into pkt';
  for_each_acc ltac:(fun _ acc_fun _ =>
                       try (pose (pkt' (acc_fun pkt)) as p; subst pkt';
                            rename p into pkt'));
  assert (Hpkt: pkt = pkt') by
      (destruct pkt as [i1 i2 i3 i4]; destruct i1; reflexivity);
  subst pkt'; rewrite Hpkt; clear Hpkt.


(* tactics for drilling a refine or computes_to *)
Ltac comp_inv :=
  match goal with
  | [H: computes_to (Pick _) _ |- _] => apply Pick_inv in H
  | [H: computes_to _ _ |- _] => inversion H; unfold Ensembles.In in *; clear H
  | [H: _ /\ _ |- _] => destruct H
  | [H: ret _ _ |- _] => inversion H; clear H
  | [H: Bind _ _ _ |- _] => inversion H; unfold Ensembles.In in *; clear H
  | [H: Bind2 _ _ _ |- _] => inversion H; unfold Ensembles.In in *; clear H
  end.

Ltac get_to_the_point_step :=
  match goal with
  | [|- refine (If_Then_Else _ _ _) _] => apply refine_If_Then_Else; [ reflexivity | ]
  | [|- refine (Bind _ _) _] => apply refine_bind; [ | reflexivity ]
  | [|- refine (Pick _) _] =>
    let x := fresh in let Hx := fresh in
    apply refine_pick; intros x Hx; comp_inv
  | [ H: decides ?b _ |- decides ?b _ ] => unfold decides in *; destruct b; cbn in *
  | [ Hqs: Complete_Dropped_qs_equiv _ _ _,
      H: exists x, (In_History _ _ x) /\ _ |- exists x, (In_History _ _ x) /\ _ ] =>
    let x := fresh in let Hx := fresh in
    destruct H as [x [Hhist Hf]]; exists x; split; [ apply Hqs; apply Hhist | ]
  | [ H: ~ _ |- ~ _ ] => intro; apply H
  end.
Ltac get_to_the_point := repeat get_to_the_point_step.


(* tries to change a packet field with the appropriate dummy value,
   without looking inside any existential predicates *)
Ltac change_dummy_flat x pkt :=
  let x_pkt := (eval cbv beta in (x pkt)) in
  match goal with
  | [|- context c [x_pkt]] =>
    let c' := dummy_type x_pkt ltac:(fun d => context c [d]) in
    change c'
  end.

(* 1. change the packet field with dummy at surface level
   2. drill under the refine
   3. try changing the same field with dummy inside the existential predicate
      that talks about historical packets; essentially, what if all packets in
      history had a dummy in that field?
      a. if this succeeds, fail at level 1 so that the match-goal fails at level 0
         so that the outer try clause succeeds and the whole tactic succeeds
      b. if this fails, fail at level 2 so that [...] the whole tactic fails
   4. in any case get_to_the_point has failed so the goal is back to the
      undrilled refine, which lets us test further packet fields at the surface *)
Ltac change_dummy x pkt :=
  change_dummy_flat x pkt;
  try (get_to_the_point;
       match goal with
       | [|- _ ?y] =>
         destruct_packet y; tryif change_dummy_flat x y then fail 1 else fail 2
       end).

(* existential vector constructor *)
Ltac evec_cons x vec :=
  let y := fresh in
  pose (x :: vec) as y; subst vec; rename y into vec.

(* (eventually used with the for_each_acc iterator)
   if the dummy change succeeds, great, otherwise we know that the field
   in question is required by the filter, so add it to the vector of required
   fields and update the packet-to-Tuple function likewise
   (sadly I could not figure out how to build the Tuple-to-packet function here) *)
Ltac change_dummy_else_tuple_heading acc_type acc_fun head :=
  match goal with [ attrs: Vector.t Attribute _, inp: input |- _ ] =>
  idtac "trying" head;
  tryif change_dummy acc_fun inp then idtac else
    (evec_cons (Build_Attribute head acc_type) attrs;
     match goal with
     | [ ftup: input -> ilist2 _ |- _ ] =>
       let y := fresh in
       pose (fun p => icons2 (head :: acc_fun p)%Component (ftup p)) as y;
       subst ftup; rename y into ftup; cbv beta in ftup
     | _ => pose (fun p => icons2 (head :: acc_fun p)%Component inil2) as ftup
     end)
  end.

(* helper for building Tuple-to-packet function; this replaces a field
   accessor with the corresponding Tuple heading *)
Ltac build_topkt' acc_fun head fpkt tup pkt :=
  let y' := fresh in
  let y := (eval unfold fpkt in fpkt) in
  let acc_fun_pkt := (eval cbv beta in (acc_fun pkt)) in
  match y with context c [acc_fun_pkt] =>
    let c' := context c[tup!head] in pose c' as y'
  end;
  clear fpkt; rename y' into fpkt.

(* the goal has been passed through all dummy replacements, and now contains
   an inlined Record of the packet with some literal dummies and some field
   accessors of the original packet; we extract the Record and pass each field
   through the helper tactic above to get a Tuple-to-packet converter *)
Ltac build_topkt heading :=
  assert (tup: @Tuple heading) by (constructor; cbn; dummy_type');
  match goal with
  | [ pkt: input, tup: @Tuple heading |- context [Complete_filter _ _ ?p]] =>
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


(* and finally the master tactic that should be self-evident *)
Ltac solve_drop_fields filter :=
  eexists; eexists; eexists; red; intros r_o r_n Hrpre pkt; destruct_packet pkt;

  unfold_Complete_f filter;
  pose (Vector.nil Attribute) as attrs;
  for_each_acc change_dummy_else_tuple_heading;
  refold_Complete_f filter;

  pose (BuildHeading attrs) as h;
  build_topkt h;
  match goal with
    [ftup: input -> ilist2 _, topkt: Tuple -> input |- _] =>
    pose (fun p => (BuildTuple attrs (ftup p))) as totup;

    subst attrs h ftup;
    (let totup := (eval unfold totup in totup) in
     instantiate (1 := totup));
    (let topkt := (eval unfold topkt in topkt) in
     instantiate (1 := topkt))
  end;

  unfold filter, Complete_filter; get_to_the_point; assumption.


(* a demo *)
Definition flag_true (p: input) : Prop := p.(in_ip4).(DF) = true.
Definition sent_to_me := (iptables -A FORWARD --destination 18'0'0'0/8).(cf_cond).

Notation "'with' r totup ',' 'if' 'historically' cond 'then' iftrue 'else' iffalse" :=
  (b <- { b: bool | decides b (exists pre,
                 In_History totup r pre /\ cond pre) };
     if b then iftrue else iffalse) (at level 65, r at level 9) : filter_scope.
Notation "'<' res '>'" :=
  (ret (Some res)) (at level 64, res at level 63) : filter_scope.

Open Scope filter_scope.
Definition f (h: Heading) (topkt: @Tuple h -> input) (totup: input -> @Tuple h)
           (r: QueryStructure (PacketHistorySchema h)) (inp: input) :=
  If sent_to_me inp
  Then <ACCEPT>
  Else with r totup,
    if historically flag_true then <ACCEPT> else <DROP>.


Theorem mydrop: Drop_Fields f.
Proof. red. Transparent computes_to. solve_drop_fields f. Defined.