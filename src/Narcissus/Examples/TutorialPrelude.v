Require Export
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.
Require Export
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.BaseFormats
        Fiat.Common.EnumType
        Fiat.Narcissus.Formats.EnumOpt.

Open Scope nat_scope.
Open Scope type_scope.
Open Scope format_scope.
Open Scope vector_scope.
Arguments Datatypes.length {_}.
Notation "x ⋅ y" := (Core.append_word y x) (left associativity, at level 3, format "x ⋅ y").

Definition encoder_impl' {S P}
           (enc: { encoder : (forall sz : nat, AlignedEncodeM (S:=S) sz) & P encoder })
           {sz} r v :=
  projT1 enc sz v 0 r tt.

Arguments encoder_impl' {_ _} _ [_].

Definition decoder_impl' {A P}
           (dec: {decoder : (forall sz : nat, AlignedDecodeM A sz) & P decoder }) {sz} v :=
  projT1 dec sz v 0 tt.

Arguments decoder_impl' {_ _} _ [_].

Notation simplify x :=
  (ltac:(let x := (eval unfold encoder_impl', decoder_impl' in x) in
         let x := (eval simpl in x) in
         (* let x := (eval unfold SetCurrentBytes in x) in *)
         (* let x := (eval simpl in x) in *)
         exact x)) (only parsing).

Definition must {T} : forall (x: option T),
    match x with
    | Some x0 => T
    | None => True
    end.
  destruct x; auto.
Defined.

Ltac shelve_inv ::=
  let H' := fresh in
  let data := fresh in
  intros data H';
  repeat (destruct H'; [ idtac ]); (* !! *)
  match goal with
  | H : ?P data |- ?P_inv' =>
    is_evar P;
    let P_inv' := (eval pattern data in P_inv') in
    let P_inv := match P_inv' with ?P_inv data => P_inv end in
    let new_P_T := type of P in
    makeEvar new_P_T
             ltac:(fun new_P =>
                     unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
  end.

Notation "'format_const' x" := (format_word ◦ (fun _ => x)) (at level 50).


Open Scope AlignedDecodeM.
Open Scope AlignedEncodeM.

Notation "'fail'" := ThrowAlignedDecodeM.

Transparent mult.
Arguments mult: simpl nomatch.

Transparent plus.
Arguments plus: simpl nomatch.

Definition Projection_AlignedEncodeM'
           {S' S'' : Type}
           {cache : Cache}
           {sz}
           (encode : AlignedEncodeM (S := S'') sz)
           (f : S' -> S'')
  : AlignedEncodeM (S := S') sz :=
  fun v idx s' env =>
    encode v idx (f s') env.

Lemma cleanup_aligned_encoder_bind {cache S2}:
  forall (sz : nat) (v : t Core.char sz) idx (r : S2) ch,
  forall (f f' g g': @AlignedEncodeM cache S2 sz),
    (forall v idx r ch, g v idx r ch = g' v idx r ch) ->
    (forall v idx r ch, f v idx r ch = f' v idx r ch) ->
    (AppendAlignedEncodeM f g) v idx r ch =
    (AppendAlignedEncodeM f' g') v idx r ch.
Proof. compute; intros * Hg Hf. rewrite Hf; destruct (f' _ _ _ _); congruence. Qed.

Lemma cleanup_aligned_encoder_distribute {cache S1 S2}:
  forall (sz : nat) (r : S1) (v : t Core.char sz) ch idx,
  forall (f1 f2: @AlignedEncodeM cache S2 sz)
    (g: @AlignedEncodeM cache S1 sz)
    x proj,
    (AppendAlignedEncodeM
       (fun v idx r => f1 v idx (proj r))
       (AppendAlignedEncodeM (fun v idx r => f2 v idx (proj r)) g)) v idx r ch = x ->
    (AppendAlignedEncodeM (fun v idx r => (AppendAlignedEncodeM f1 f2) v idx (proj r)) g) v idx r ch = x.
Proof. compute; intros; destruct (f1 _ _ _ _); [ destruct (f2 _ _ _ _) | ]; congruence. Qed.

Lemma cleanup_aligned_encoder_init {cache S2}:
  forall (sz : nat) (v : t Core.char sz) idx (r : S2) ch,
  forall (f: @AlignedEncodeM cache _ sz)
    (g: @AlignedEncodeM cache S2 sz)
    (h: forall sz, @AlignedEncodeM cache _ sz)
    (h': @AlignedEncodeM cache S2 sz),
    (h' = h sz) ->
    (AppendAlignedEncodeM f g) v idx r ch = h' v idx r ch ->
    (AppendAlignedEncodeM f g) v idx r ch = h sz v idx r ch.
Proof. intros; congruence. Qed.

Lemma cleanup_aligned_encoder_bind_projection {cache S1 S2 sz}:
  forall (f f': @AlignedEncodeM cache S2 sz)
    (h: @AlignedEncodeM cache S1 sz) proj,
    (forall v idx r1 ch, f' v idx (proj r1) ch = h v idx r1 ch) ->
    (forall v idx r2 ch, f v idx r2 ch = f' v idx r2 ch) ->
    forall (v : t Core.char sz) idx (r1: S1) r2 ch,
      r2 = proj r1 ->
      f v idx r2 ch = h v idx r1 ch.
Proof. congruence. Qed.

Ltac eta_reduce :=
  repeat match goal with
           |- context [fun x => @?h x] =>
           change (fun x => ?h x) with h
         end.

Ltac cleanup_single_encoder := simpl.
(*lazymatch goal with
  | [  |- forall v idx s ce, @?f v idx s ce = @?g v idx s ce ] =>
    change (forall v idx s ce, f v idx s ce = g v idx s ce); intros;
    eta_reduce;
    change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx ?cst) with
        (fun (v : Tv) (idx : Tidx) (s : Ts) => f v idx ((const cst) s));
    change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx (?g s)) with
        (Projection_AlignedEncodeM' f g);
    change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx (?g1 (?g2 s))) with
        (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' f g1) g2);
    change (fun (v : ?Tv) (idx : ?Tidx) (s : ?Ts) => ?f v idx (?g1 (?g2 (?g3 s)))) with
        (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' (Projection_AlignedEncodeM' f g1) g2) g3)
  end. *)

Lemma AlignedEncodeList_morphism {cache: Cache} {A: Type}:
  forall (encA encA': forall sz, AlignedEncodeM sz) sz,
    (forall v idx r ch, encA sz v idx r ch = encA' sz v idx r ch) ->
    (forall r v idx ch,
        @AlignedEncodeList cache A encA sz v idx r ch =
        @AlignedEncodeList cache A encA' sz v idx r ch).
Proof.
  intros * Heq; induction r; simpl; intros.
  - reflexivity.
  - rewrite Heq; destruct (encA' _ _ _ _ _); simpl; congruence.
Qed.

Lemma cleanup_aligned_encoder_AlignedEncodeList {cache: Cache} {A: Type}:
  forall (encA encA': forall sz, AlignedEncodeM sz) sz
    (f: AlignedEncodeM sz),
    (forall v idx r ch, encA sz v idx r ch = encA' sz v idx r ch) ->
    (forall r v idx ch,
        @AlignedEncodeList cache A encA' sz v idx r ch = f v idx r ch) ->
    (forall r v idx ch,
        @AlignedEncodeList cache A encA sz v idx r ch = f v idx r ch).
Proof.
  intros; erewrite AlignedEncodeList_morphism; eauto.
Qed.

Ltac exact_computed t :=
  let t' := (eval compute in t) in exact t'.

Ltac derive_clean_encoder_do_postprocess :=
  simpl.
(*repeat change (fun x => ?h x) with h;
  repeat change (wzero ?sz) with (ltac:(let w0 := (eval compute in (wzero sz)) in exact w0));
  repeat ((change (@split1' (S ?sz1) ?sz2 (WS ?b ?w)) with
               (ltac:(exact_computed (@split1' (S sz1) sz2 (WS b w))))) ||
          (change (@split2' (S ?sz1) ?sz2 (WS ?b ?w)) with
               (ltac:(exact_computed (@split2' (S sz1) sz2 (WS b w)))))). *)

Ltac derive_clean_encoder_do_projections_step :=
  lazymatch goal with
  | [ |- _ ?v ?idx ?pkt ?ch = _ ?sz ?v ?idx ?pkt ?ch ] =>
    simple eapply cleanup_aligned_encoder_init
  | [ |- ?enc ?v ?idx (?f _) ?ch = _ ?v ?idx _ ?ch ] =>
    eapply cleanup_aligned_encoder_bind_projection;
    [ .. | higher_order_reflexivity ];
    [ simpl; cleanup_single_encoder; reflexivity | .. ]
  | [ |- _ ?v ?idx ?pkt ?ch = _ ?v ?idx ?pkt ?ch ] =>
    (simple eapply cleanup_aligned_encoder_distribute ||
     (simple eapply cleanup_aligned_encoder_AlignedEncodeList;
      [ .. | higher_order_reflexivity ]) ||
     simple eapply cleanup_aligned_encoder_bind)
  | [ |- forall _, _ ] => intros
  end.

Ltac derive_clean_encoder_do_projections :=
  repeat derive_clean_encoder_do_projections_step;
  repeat higher_order_reflexivity.

Ltac derive_clean_encoder :=
  intros; simpl;
  unfold SetCurrentBytes, Projection_AlignedEncodeM;
  match goal with
  | [ |- _ ?v ?idx ?r ?ch = _ ] => refine (eq_trans (y := (_: AlignedEncodeM _) v idx r ch) _ _)
  end;
  [ derive_clean_encoder_do_projections | derive_clean_encoder_do_postprocess ];
  higher_order_reflexivity.

Notation "x ⋙ y" :=
  (Projection_AlignedEncodeM' y x)
    (at level 80, right associativity,
    format "'[hv  ' x  '/' ⋙  y ']'") : AlignedEncodeM_scope.

Notation "y ≫ z" :=
  (AppendAlignedEncodeM y z)
    (at level 81, right associativity,
     format "'[' y  ≫ '//' z ']'") : AlignedEncodeM_scope.

Compute (split2' 6 2 (natToWord 8 3)).

Notation high_bits n := (split1' n _).
Notation low_bits n := (split2' _ n).

Ltac cleanup_encoder' enc :=
  constr:(ltac:(eexists; derive_clean_encoder)
                     : { g : (forall sz : nat, @AlignedEncodeM _ _ sz)
                             & (forall (sz : nat) (v : Vector.t _ sz) r idx ch,
                                   enc sz v idx r ch = g sz v idx r ch) }).

Notation cleanup_encoder enc :=
  (ltac:(let enc' := cleanup_encoder' enc in
         exact (enc'))) (only parsing).

Record EncoderDecoderPair {A : Type}
       (format : FormatM A ByteString)
       (predicate : A -> Prop) :=
  { enc : CorrectAlignedEncoderFor format;
    dec : CorrectAlignedDecoderFor predicate format }.

Arguments enc {_} [_] [_].
Arguments dec {_} [_] [_].

Ltac derive_encoder_decoder_pair :=
  econstructor;
  [ synthesize_aligned_encoder |
    synthesize_aligned_decoder ].

Notation encoder_impl x :=
  (simplify (encoder_impl' (cleanup_encoder (projT1 x.(enc))))) (only parsing).

Notation decoder_impl x :=
  (simplify (decoder_impl' x.(dec))) (only parsing).
