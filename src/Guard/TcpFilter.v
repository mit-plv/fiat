Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Fiat.Narcissus.Examples.NetworkStack.IPv4Header.
Require Import Fiat.Narcissus.Examples.NetworkStack.TCP_Packet.
Require Import Fiat.Narcissus.Formats.ByteBuffer.

Definition GuardDataSchema :=
  Query Structure Schema [
    relation "connections" has schema
      <"src_addr" :: string, "src_port" :: nat,
       "dst_addr" :: string, "dst_port" :: nat>
  ] enforcing [].

Notation bytes := { n: nat & ByteBuffer.t n }.

Definition bytes_of_ByteBuffer {n} (bb: ByteBuffer.t n) : bytes :=
  existT _ n bb.

Definition GuardSig : ADTSig := ADTsignature {
  Constructor "Init" : rep,
  Method "ProcessPacket" : rep * bytes -> rep * bool
}.

Definition ACCEPT := true.
Definition REJECT := false.

(* FIXME *)
Definition is_conn_start (pkt: TCP_Packet) : bool := pkt.(SYN).
Definition is_conn_end (pkt: TCP_Packet) : bool := pkt.(FIN).
Definition MAX_OPEN_CONNECTIONS := 50.

Require Import Bedrock.Word.
Require Import Fiat.Narcissus.BinLib.Core.

Definition WrapDecoder {A B C} (f: forall n, ByteBuffer.t n -> option (A * B * C)) :=
  fun (bs: bytes) =>
    match f _ (projT2 bs) with
    | Some (pkt, _, _) => Some pkt
    | None => None
    end.

Definition ipv4_decode :=
  WrapDecoder (@IPv4_decoder_impl).

Definition ipv4Split {A} (k: forall (w1 w2 w3 w4: word 8), A) (addr: word 32) : A :=
  let w1 := split2 24 8 addr in
  let w2 := split1 8 8 (split2 16 16 addr) in
  let w3 := split1 8 16 (split2 8 24 addr) in
  let w4 := split1 8 24 addr in
  k w1 w2 w3 w4.

Definition ipv4ToList :=
  ipv4Split (fun w1 w2 w3 w4 => [w1; w2; w3; w4]).

Definition ipv4ToByteBuffer :=
  ipv4Split (fun w1 w2 w3 w4 => ByteBuffer.of_list [w1; w2; w3; w4]: ByteBuffer.t 4).

Compute (ipv4ToByteBuffer (WO~0~0~0~0~1~1~1~1~0~1~0~1~0~1~0~1~0~0~1~1~0~0~1~1~0~1~1~1~0~1~1~1)).

Definition ipv4ToString (addr: word 32) :=
  List.fold_right
    (fun (w: char) str => String (ascii_of_nat (wordToNat w)) str)
    EmptyString (ipv4ToList addr).

Compute (ipv4ToString (WO~0~0~0~0~1~1~1~1~0~1~0~1~0~1~0~1~0~0~1~1~0~0~1~1~0~1~1~1~0~1~1~1)).

Definition tcp_decode (hdr: IPv4_Packet) :=
  let src := ipv4ToByteBuffer hdr.(SourceAddress) in
  let dst := ipv4ToByteBuffer hdr.(DestAddress) in
  let offset := 20 + 4 * List.length hdr.(IPv4Header.Options) in
  let tcpLen := wordToNat hdr.(TotalLength) - offset in
  fun bs =>
    let bs' := AlignedByteBuffer.bytebuffer_of_bytebuffer_range offset tcpLen (projT2 bs) in
    WrapDecoder (@TCP_decoder_impl src dst (natToWord 16 tcpLen)) bs'.

Definition port_to_nat (port: word 16) :=
  wordToNat port.

Definition GuardSpec : ADT GuardSig := Eval simpl in Def ADT {
  rep := QueryStructure GuardDataSchema,

  Def Constructor0 "Init" : rep := empty,,

  Def Method1 "ProcessPacket" (db : rep) (bs : bytes) : rep * bool :=
    Ifopt ipv4_decode bs as hdr Then
      let src_addr := ipv4ToString hdr.(SourceAddress) in
      let dst_addr := ipv4ToString hdr.(DestAddress) in
      Ifopt tcp_decode hdr bs as pkt Then
        let src_port := port_to_nat (pkt.(SourcePort)) in
        let dst_port := port_to_nat (pkt.(DestPort)) in
        count <- Count (For (conn in db!"connections")
                       Where (conn!"src_addr" = src_addr)
                       Where (conn!"dst_addr" = dst_addr)
                       Return ());
        If is_conn_end pkt Then (
          `(db, _) <- Delete conn from db!"connections"
                       where (conn!"src_addr" = src_addr /\
                              conn!"dst_addr" = dst_addr /\
                              conn!"src_port" = src_port /\
                              conn!"dst_port" = dst_port);
          ret (db, ACCEPT)
        ) Else If count <? MAX_OPEN_CONNECTIONS Then (
          If is_conn_start pkt Then (
            `(db, _) <- Insert <"src_addr" :: src_addr, "src_port" :: src_port,
                               "dst_addr" :: dst_addr, "dst_port" :: dst_port>
                         into db!"connections"; (* FIXME *)
            ret (db, ACCEPT)
          ) Else
            ret (db, ACCEPT)
        ) Else
          ret (db, REJECT)
      Else
        ret (db, REJECT)
    Else
      ret (db, REJECT)

}%methDefParsing.

Notation IndexType sch :=
  (@ilist3 RawSchema (fun sch : RawSchema =>
                        list (string * Attributes (rawSchemaHeading sch)))
           (numRawQSschemaSchemas sch) (qschemaSchemas sch)).

(* Definition empty_index : IndexType GuardDataSchema := *)
(*   {| prim_fst := []; *)
(*      prim_snd := () |}. *)

Definition slow_index : IndexType GuardDataSchema :=
  {| prim_fst := [("EqualityIndex", "src_port" # "connections" ## GuardDataSchema);
                  ("EqualityIndex", "dst_port" # "connections" ## GuardDataSchema)];
     prim_snd := () |}.

Definition fast_index : IndexType GuardDataSchema :=
  {| prim_fst := [("EqualityIndex", "src_addr" # "connections" ## GuardDataSchema);
                  ("EqualityIndex", "dst_addr" # "connections" ## GuardDataSchema)];
     prim_snd := () |}.

Definition indexes := slow_index.

Ltac FindAttributeUses := EqExpressionAttributeCounter.
Ltac BuildEarlyIndex := ltac:(LastCombineCase6 BuildEarlyEqualityIndex).
Ltac BuildLastIndex := ltac:(LastCombineCase5 BuildLastEqualityIndex).
Ltac IndexUse := EqIndexUse.
Ltac createEarlyTerm := createEarlyEqualityTerm.
Ltac createLastTerm := createLastEqualityTerm.
Ltac IndexUse_dep := EqIndexUse_dep.
Ltac createEarlyTerm_dep := createEarlyEqualityTerm_dep.
Ltac createLastTerm_dep := createLastEqualityTerm_dep.
Ltac BuildEarlyBag := BuildEarlyEqualityBag.
Ltac BuildLastBag := BuildLastEqualityBag.
Ltac PickIndex := ltac:(fun makeIndex => let attrlist' := eval compute in indexes in makeIndex attrlist').


Theorem SharpenedGuard :
  FullySharpened GuardSpec.

Proof.
  start sharpening ADT.

  match goal with
  |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
    hone representation using (@DropQSConstraints_AbsR Rep)
  end.

  - apply Constructor_DropQSConstraints.
  - etransitivity; [ eapply refine_If_Opt_Then_Else_Bind | ].
    etransitivity; [ eapply refine_If_Opt_Then_Else | ]; swap 1 3.
    (* setoid_rewrite refine_If_Opt_Then_Else_Bind. *)
    (* setoid_rewrite refine_If_Opt_Then_Else; swap 2 3. *)
    + higher_order_reflexivity.
    + simplify with monad laws.
      refine pick val _; [ | reflexivity ].
      simplify with monad laws; simpl.
      match goal with
      | [ H: DropQSConstraints_AbsR _ _ |- _ ] => red in H; rewrite !H
      end;
        higher_order_reflexivity.
    + intro.
      (* Why not setoid_rewrite? *)
      etransitivity; [ eapply refine_If_Opt_Then_Else_Bind | ].
      etransitivity; [ eapply refine_If_Opt_Then_Else | ]; swap 1 3.
      * higher_order_reflexivity.
      * simplify with monad laws.
        refine pick val _; [ | reflexivity ].
        simplify with monad laws; simpl.
        match goal with
        | [ H: DropQSConstraints_AbsR _ _ |- _ ] => red in H; rewrite !H
        end;
          higher_order_reflexivity.
      * intro.
        simplify with monad laws.

        etransitivity.
        -- setoid_rewrite DropQSConstraintsQuery_In. (* drop_constraints_from_query *)
           try simplify with monad laws; cbv beta; simpl;
             repeat match goal with
                      H : DropQSConstraints_AbsR _ _ |- _ =>
                      unfold DropQSConstraints_AbsR in H; rewrite H
                    end. (*pose_string_hyps; pose_heading_hyps; *)
           finish honing.
        -- etransitivity; [ eapply refine_bind | ]; cycle -1.
           ++ higher_order_reflexivity.
           ++ higher_order_reflexivity.
           ++ intro.
              (* Why not setoid_rewrite? *)
              etransitivity; [ eapply refine_If_Then_Else_Bind | ].
              etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 3.
              ** higher_order_reflexivity.
              ** etransitivity; [ eapply refine_If_Then_Else_Bind | ].
                 etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 3.
                 --- higher_order_reflexivity.
                 --- simplify with monad laws.
                     refine pick val _; [ | reflexivity ].
                     simplify with monad laws; simpl.
                     match goal with
                     | [ H: DropQSConstraints_AbsR _ _ |- _ ] => red in H; rewrite !H
                     end;
                       higher_order_reflexivity.
                 --- etransitivity; [ eapply refine_If_Then_Else_Bind | ].
                     etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 3.
                     +++ higher_order_reflexivity.
                     +++ simplify with monad laws.
                         refine pick val _; [ | reflexivity ].
                         simplify with monad laws; simpl.
                         match goal with
                         | [ H: DropQSConstraints_AbsR _ _ |- _ ] => red in H; rewrite !H
                         end;
                           higher_order_reflexivity.
                     +++ unfold Bind2; simplify with monad laws.
                         simpl.

                         Lemma refine_bind_bind_dep X X' Y Z (f : X -> Comp Y) (g : Y -> Comp Z) (k: X -> X') x
                           : refine (Bind x (fun x0 => Bind (f x0) (fun u => g u)))
                                    (Bind (Bind x (fun x0 => Bind (f x0) (fun u => ret (u, (k x0)))))
                                          (fun x0u => g (fst x0u))).
                         Proof.
                           red; intros.
                           computes_to_inv; subst.
                           eauto using @BindComputes.
                         Qed.

                         Lemma refine_bind_bind_dep' X Y Z (f : X -> Comp Y) (g : Y -> X -> Comp Z) x
                           : refine (Bind x (fun x0 => Bind (f x0) (fun u => g u x0)))
                                    (Bind (Bind x (fun x0 => Bind (f x0) (fun u => ret (u, x0))))
                                          (fun x0u => g (fst x0u) (snd x0u))).
                         Proof.
                           red; intros.
                           computes_to_inv; subst.
                           eauto using @BindComputes.
                         Qed.

                         rewrite refine_bind_bind_dep with (k := snd).
                         setoid_rewrite refine_bind.
                         *** higher_order_reflexivity.
                         *** (* remove trivial insertion checks *)
                           (* Pull out the relation we're inserting into and then
                              rewrite [QSInsertSpec] *)
                           lazymatch goal with
                             H : DropQSConstraints_AbsR _ ?r_n
                             |- context [(QSInsert _ ?R ?n)%QuerySpec] =>
                             let H' := fresh in
                             (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                                after we've drilled under a bind, this tactic will fail because
                                typeclass resolution breaks down. Generalizing and applying gets
                                around this problem for reasons unknown. *)
                             let H' := fresh in
                             pose (@QSInsertSpec_UnConstr_refine_opt _ r_n _ R n H) as H';
                               cbv beta delta [tupleConstraints attrConstraints map app relName schemaHeading] iota in H';
                               simpl in H'; fold_heading_hyps_in H'; fold_string_hyps_in H'; exact H'
                           end.
                         *** intro.
                             finish honing.
              ** unfold Bind2; simplify with monad laws.
                 simpl.
                 rewrite refine_bind_bind_dep with (k := snd).
                 setoid_rewrite refine_bind.

                 --- higher_order_reflexivity.
                 --- (* drop_constraints_from_delete. *)
                   (* Pull out the relation we're inserting into and then
                      rewrite [QSInsertSpec] *)
                   match goal with
                       H : DropQSConstraints_AbsR ?r_o ?r_n
                       |- context [QSDelete ?qs ?R ?P] =>
                       (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                                  after we've drilled under a bind, this tactic will fail because
                                  typeclass resolution breaks down. Generalizing and applying gets
                                  around this problem for reasons unknown. *)
                       let H' := fresh "H'" in
                       pose proof (@QSDeleteSpec_UnConstr_refine_opt
                                     _ r_n R P r_o H) as H';
                         simpl in H'; fold_heading_hyps_in H'; fold_string_hyps_in H';
                         apply H'
                   end.
                 --- intro.
                     finish honing.

  -
    PickIndex ltac:(fun attrlist =>
                      make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex).

    plan CreateTerm EarlyIndex LastIndex makeClause_dep EarlyIndex_dep LastIndex_dep.

    etransitivity; [ eapply refine_If_Opt_Then_Else_Bind | ].
    eapply refine_If_Opt_Then_Else; swap 1 2.
    (* setoid_rewrite refine_If_Opt_Then_Else_Bind. *)
    (* setoid_rewrite refine_If_Opt_Then_Else; swap 2 3. *)
    + simplify with monad laws.
      simpl; refine pick val _; [ | eauto ].
      simplify with monad laws; simpl.
      higher_order_reflexivity.
    + intro.
      (* Why not setoid_rewrite? *)
      etransitivity; [ eapply refine_If_Opt_Then_Else_Bind | ].
      eapply refine_If_Opt_Then_Else; swap 1 2.
      * simplify with monad laws.
        simpl; refine pick val _; [ | eauto ].
        higher_order_reflexivity.
      * intro.
        simplify with monad laws.
        apply refine_bind.
        -- implement_Query IndexUse createEarlyTerm createLastTerm
                           IndexUse_dep createEarlyTerm_dep createLastTerm_dep.
           simpl; repeat first [setoid_rewrite refine_bind_unit
                               | setoid_rewrite refine_bind_bind ];
           cbv beta; simpl.
           finish honing.
        -- intro.
              (* Why not setoid_rewrite? *)
              etransitivity; [ eapply refine_If_Then_Else_Bind | ].
              etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 2.
              ** etransitivity; [ eapply refine_If_Then_Else_Bind | ].
                 etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 2.
                 --- simplify with monad laws.
                     refine pick val _; [ | eauto ].
                     simplify with monad laws; simpl.
                     higher_order_reflexivity.
                 --- etransitivity; [ eapply refine_If_Then_Else_Bind | ].
                     etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 2.
                     +++ simplify with monad laws.
                         refine pick val _; [ | eauto ].
                         simplify with monad laws; simpl.
                         higher_order_reflexivity.
                     +++ unfold Bind2; simplify with monad laws.
                         simpl.
                         insertion IndexUse createEarlyTerm createLastTerm IndexUse_dep createEarlyTerm_dep createLastTerm_dep.
                     +++ higher_order_reflexivity.
                 --- higher_order_reflexivity.
              ** unfold Bind2; simplify with monad laws.
                 simpl.
                 deletion IndexUse createEarlyTerm createLastTerm IndexUse_dep createEarlyTerm_dep createLastTerm_dep.
              ** higher_order_reflexivity.

    + simpl.
      hone representation using eq; simpl; subst.
      * refine pick eq; simplify with monad laws; simpl.
        finish honing.
      * refine pick eq; simplify with monad laws; simpl.
        etransitivity; [ eapply refine_If_Opt_Then_Else_Bind | ].
        eapply refine_If_Opt_Then_Else; swap 1 2.
        -- simplify with monad laws; simpl.
           higher_order_reflexivity.
        -- intro.
           (* Why not setoid_rewrite? *)
           etransitivity; [ eapply refine_If_Opt_Then_Else_Bind | ].
           eapply refine_If_Opt_Then_Else; swap 1 2.
           ++ simplify with monad laws; simpl.
              higher_order_reflexivity.
           ++ intro.
              simplify with monad laws.
              repeat change (true && ?x) with x.
              apply refine_bind.
              ** finish honing.
              ** intro.
                 (* Why not setoid_rewrite? *)
                 etransitivity; [ eapply refine_If_Then_Else_Bind | ].
                 etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 3.
                 --- higher_order_reflexivity.
                 --- repeat rewrite ?map_length, ?app_nil_r.
                     etransitivity; [ eapply refine_If_Then_Else_Bind | ].
                     etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 3.
                     +++ higher_order_reflexivity.
                     +++ simplify with monad laws; simpl.
                         higher_order_reflexivity.
                     +++ etransitivity; [ eapply refine_If_Then_Else_Bind | ].
                         etransitivity; [ eapply refine_If_Then_Else | ]; swap 1 3.
                         *** higher_order_reflexivity.
                         *** simplify with monad laws; simpl.
                             higher_order_reflexivity.
                         *** simplify with monad laws; simpl.
                             higher_order_reflexivity.
                 --- simplify with monad laws; simpl.
                     (* FIXME delete unused bind? *)
                     finish honing.

      *  Implement_Bags BuildEarlyBag BuildLastBag.
Defined.

Definition GuardImpl :=
  Eval simpl in projT1 SharpenedGuard.
