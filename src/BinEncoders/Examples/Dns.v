Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Helpers
               Fiat.BinEncoders.Libraries.Sig
               Fiat.BinEncoders.Libraries.BinCore
               Fiat.BinEncoders.Libraries.FixInt
               Fiat.BinEncoders.Libraries.SteppingList
               Fiat.BinEncoders.Libraries.FixList
               Fiat.BinEncoders.Libraries.FixList2
               Fiat.BinEncoders.Libraries.Char
               Fiat.BinEncoders.Libraries.Bool
               (* Fiat.BinEncoders.Automation.Solver *)
               Coq.Strings.Ascii.

Set Implicit Arguments.

Inductive type_t := A | CNAME | NS | MX.
Inductive class_t := IN | CH | HS.

Record word_t :=
  { word_attr : { s : list ascii | length s < exp2_nat 8 } }.

Definition halt : word_t.
  refine (Build_word_t (exist _ nil _)); rewrite Compare_dec.nat_compare_lt; eauto. Defined.

Definition halt_dec (a : word_t) : {a = halt} + {a <> halt}.
  unfold halt; destruct a as [word word_pf];
  destruct word as [ w ]; destruct w eqn: eq; subst.
  - left; subst; f_equal; eapply sig_equivalence; eauto.
  - right; inversion 1.
Defined. Hint Resolve halt_dec.

Record name_t :=
  { name_attr : { s : list word_t | length s <= 255 /\ forall x, In x s -> x <> halt } }.

Record question_t :=
  { qname  : name_t;
    qtype  : type_t;
    qclass : class_t }.

Record resource_t :=
  { rname  : name_t;
    rtype  : type_t;
    rclass : class_t;
    rttl   : uint 32;
    rdata  : { s : list bool |  length s < exp2_nat 16 } }.

Record packet_t :=
  { pid         : { s : list bool | length s = 16 };
    pmask       : { s : list bool | length s = 16 };
    pquestion   : { s : list question_t | length s < exp2_nat 16 };
    panswer     : { s : list resource_t | length s < exp2_nat 16 };
    pauthority  : { s : list resource_t | length s < exp2_nat 16 };
    padditional : { s : list resource_t | length s < exp2_nat 16 } }.

Definition FixInt_of_type (t : type_t) : {n | (n < exp2 16)%N}.
  refine (match t with
          | A     => exist _ (1%N) _
          | CNAME => exist _ (5%N) _
          | NS    => exist _ (2%N) _
          | MX    => exist _ (15%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Definition FixInt_of_class (c : class_t) : {n | (n < exp2 16)%N}.
  refine (match c with
          | IN => exist _ (1%N) _
          | CH => exist _ (3%N) _
          | HS => exist _ (4%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Definition encode_word (bundle : word_t * bin_t) :=
  FixInt_encode (FixList_getlength (word_attr (fst bundle)),
  FixList_encode Char_encode (word_attr (fst bundle), snd bundle)).

Definition encode_name (bundle : name_t * bin_t) :=
  @SteppingList_encode _ _ halt _ encode_word (name_attr (fst bundle), snd bundle).

Definition encode_question (bundle : question_t * bin_t) :=
  encode_name (qname (fst bundle),
  FixInt_encode (FixInt_of_type (qtype (fst bundle)),
  FixInt_encode (FixInt_of_class (qclass (fst bundle)), snd bundle))).

Definition encode_resource (bundle : resource_t * bin_t) :=
  encode_name (rname (fst bundle),
  FixInt_encode (FixInt_of_type (rtype (fst bundle)),
  FixInt_encode (FixInt_of_class (rclass (fst bundle)),
  FixInt_encode (rttl (fst bundle),
  FixInt_encode (FixList_getlength (rdata (fst bundle)),
  FixList_encode Bool_encode (rdata (fst bundle), snd bundle)))))).

Definition encode_packet (bundle : packet_t * bin_t) :=
  FixList2_encode Bool_encode (pid (fst bundle),
  FixList2_encode Bool_encode (pmask (fst bundle),
  FixInt_encode (FixList_getlength (pquestion (fst bundle)),
  FixInt_encode (FixList_getlength (panswer (fst bundle)),
  FixInt_encode (FixList_getlength (pauthority (fst bundle)),
  FixInt_encode (FixList_getlength (padditional (fst bundle)),
  FixList_encode encode_question (pquestion (fst bundle),
  FixList_encode encode_resource (panswer (fst bundle),
  FixList_encode encode_resource (pauthority (fst bundle),
  FixList_encode encode_resource (padditional (fst bundle), snd bundle)))))))))).

Ltac idtac' :=
  match goal with
    | |- _ => idtac (* I NEED THIS FOR SOME UNKNOWN REASON *)
  end.

Ltac enum_part eq_dec :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func in
    let h := fresh in
      evar (h:func_t);
      unify (fun n => if eq_dec _ n arg then res else h n) func;
      reflexivity
  end.

Ltac enum_finish :=
  simpl;
  match goal with
  | |- ?func ?arg = ?res =>
    let func_t := type of func
    in  unify ((fun _  => res) : func_t) func;
        reflexivity
  end.

Ltac solve_enum :=
  let h := fresh in
  eexists; intros h _; destruct h;
  [ idtac'; enum_part FixInt_eq_dec ..
  | idtac'; enum_finish ].

Global Instance type_to_FixInt_decoder
  : Decoder of FixInt_of_type.
Proof.
  solve_enum.
Defined.

Global Instance class_to_FixInt_decoder
  : Decoder of FixInt_of_class.
Proof.
  solve_enum.
Defined.

Lemma func_unprod :
  forall (A B C : Type) (f : A * B -> C), (fun x => f (fst x, snd x)) = f.
Proof.
  Require Import Coq.Logic.FunctionalExtensionality.
  intuition.
  eapply functional_extensionality; intro x; destruct x; eauto.
Qed.

Ltac solve_predicate :=
  let hdata := fresh
  in  intro hdata; intuition; simpl in *;
    match goal with
    | |- context[ @fst ?a ?b hdata ] => solve [ pattern (@fst a b hdata); eauto ]
    | |- _ => solve [ intuition eauto ]
    | |- ?func _ =>
      let func_t := type of func
      in  solve [ unify ((fun _ => True) : func_t) func; intuition eauto ]
    end.

Ltac solve_unpack' e1 e2 ex proj d_t b_t :=
  match proj with
  | (fun bundle => FixList_getlength _) =>
                   eapply unpacking_decoder with
                    (project:=proj)
                    (encode1:=fun bundle => e1 (ex (fst bundle), snd bundle))
                    (encode2:=e2)
  | (fun bundle => (?proj1 (@?proj2 bundle))) =>
    match type of proj1 with
    | d_t -> _ => eapply unpacking_decoder with
                    (project:=proj)
                    (encode1:=fun bundle => e1 (ex (fst bundle), snd bundle))
                    (encode2:=e2)
    | ?d_t' -> _ => solve_unpack' e1 e2 (fun data : d_t' => ex (proj1 data)) proj2 d_t b_t
    end
  end.

Ltac solve_unpack :=
  match goal with
  | |- decoder _ ?encode =>
    match type of encode with
    | ?d_t * ?b_t -> _ =>
      match goal with
      | |- decoder _ (fun data => ?e1 (@?proj data, @?e2 data)) =>
        match type of e1 with
        | ?o_t * _ -> _ =>
          solve_unpack' e1 e2 (fun data : o_t => data) proj d_t b_t;
          repeat rewrite func_unprod
        end
      end
    end
  end.

Ltac solve_decoder :=
  (eauto with typeclass_instances) ||
  (match goal with
   | |- context [ SteppingList_encode _ ] => eapply SteppingList_decoder; eauto
   | |- context [ FixList_encode _  ] => eapply FixList_decoder
   | |- context [ FixList2_encode _ ] => eapply FixList2_decoder
   end).

Ltac solve_step' :=
  eapply strengthening_decoder; [ solve_decoder; solve_step' | solve_predicate ].

Ltac solve_step :=
  solve_unpack;
  [ solve_step' | solve_predicate | intro ].

Ltac solve_done :=
  let hdata := fresh in
  let hdata' := fresh in
  eexists; intro hdata; destruct hdata as [hdata' ?]; destruct hdata';
  intuition; simpl in *; subst; instantiate (1:=fun b => (_, b)); eauto.

Ltac solve' :=
  match goal with
  | |- decoder _ ?e => unfold e; repeat solve_step; solve_done
  end.

Global Instance word_decoder
  : Decoder of encode_word.
Proof.
  solve'.
Defined.

Global Instance name_decoder
  : Decoder of encode_name.
Proof.
  solve'.
Defined.

Global Instance question_decoder
  : Decoder of encode_question.
Proof.
  solve'.
Defined.

Global Instance resource_decoder
  : Decoder of encode_resource.
Proof.
  solve'.
Defined.

Global Instance packet_decoder
  : Decoder of encode_packet.
Proof.
  solve'.
Defined.

Section Example.
  Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).
  Definition packet1 := [true; true; false; true; true; false; true; true; false; true;
                         false; false; false; false; true; false; false; false; false; false;
                         false; false; false; true; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; true; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; true; true; false; true; true; true; false; true;
                         true; true; false; true; true; true; false; true; true; true;
                         false; true; true; true; false; true; true; true; false; false;
                         false; false; true; true; false; false; false; true; true; false;
                         true; true; true; false; false; true; true; false; true; true;
                         true; true; false; true; true; true; false; false; true; false;
                         false; true; true; true; false; true; false; false; false; true;
                         true; false; true; false; false; false; false; true; true; false;
                         false; true; false; true; false; true; true; false; false; false;
                         false; true; false; true; true; true; false; false; true; true;
                         false; true; true; true; false; true; false; false; false; true;
                         true; false; false; true; false; true; false; true; true; true;
                         false; false; true; false; false; true; true; false; true; true;
                         true; false; false; false; false; false; false; false; true; true;
                         false; true; true; false; false; true; false; true; false; true;
                         true; false; false; true; false; false; false; true; true; true;
                         false; true; false; true; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; true; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; true].
End Example.


Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive ascii => char [
"(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

(* Extraction "extracted.ml" encode_packet packet_decoder. *)