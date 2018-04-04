Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Common.StringFacts
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.DomainNameOpt
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedString
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedFix
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Narcissus.Stores.DomainNameStore.

Require Import
        Bedrock.Word.

Section AlignedDomainName.

  Import Vectors.VectorDef.VectorNotations.

  Arguments natToWord : simpl never.
  Arguments wordToNat : simpl never.
  Arguments NPeano.div : simpl never.
  Opaque pow2. (* Don't want to be evaluating this. *)

  Lemma split_string_OK
    : forall d,
      ValidDomainName d ->
      (d = (fst (split_string (d)) ++ String "." (snd (split_string (d))))%string \/
       split_string (d) = (d, ""%string)) /\
      ValidLabel (fst (split_string (d))) /\
      (forall label' post' : string,
          d = (label' ++ post')%string ->
          ValidLabel label' -> (String.length label' <= String.length (fst (split_string (d))))%nat).
  Proof.
  Admitted.

  Lemma split_string_ValidDomainName :
    forall d,
      ValidDomainName d ->
      ValidDomainName (snd (split_string d)).
  Proof.
  Admitted.

  Lemma well_founded_string_length'
    : well_founded (fun y r : {a : string & ValidDomainName a} => lt (String.length (projT1 y)) (String.length (projT1 r))%nat).
  Proof.
  Admitted.

  Definition aligned_format_DomainName :=
    Fix well_founded_string_length
        (fun _ : string  =>
           FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : nat & t (word 8) n} * CacheFormat))
        (fun (r : string)
             (y : forall r' : string,
                 lt (String.length r') (String.length r)%nat ->
                 CacheFormat -> {n : nat & t (word 8) n} * CacheFormat)
             (ce : CacheFormat) =>
           match string_dec r "" with
           | left e =>
             (existT (fun n : nat => t (word 8) n) 1 [NToWord 8 (Ascii.N_of_ascii terminal_char)], addE ce 8)
           | right e => (existT (fun n : nat => t (word 8) n)
                                (1 + String.length (fst (split_string r)) +
                                 projT1
                                   (fst
                                      (y
                                         ((snd (split_string r)))
                                         (@split_string_ValidDomainName_length r e)
                                         (Ifopt Ifopt fst ce as m
                                                                  Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                       then Some (natToWord 17 (wordToNat m + 8))
                                                                       else None Else None as m
                                                                                                Then if Compare_dec.lt_dec
                                                                                                          (wordToNat m + 8 * String.length (fst (split_string r)))
                                                                                                          (pow2 17)
                                                                                                     then
                                                                                                       Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                                                                                     else None Else None,
                                                                                              snd ce))))
                                (([natToWord 8 (String.length (let (x0, _) := split_string r in x0))] ++
                                                                                                      StringToBytes (fst (split_string r))) ++
                                                                                                                                            projT2
                                                                                                                                            (fst
                                                                                                                                               (y
                                                                                                                                                  (snd (split_string r))
                                                                                                                                                  (@split_string_ValidDomainName_length r e)
                                                                                                                                                  (Ifopt Ifopt fst ce as m
                                                                                                                                                                           Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                                                then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                                                else None Else None as m
                                                                                                                                                                                                         Then if Compare_dec.lt_dec
                                                                                                                                                                                                                   (wordToNat m + 8 * String.length (fst (split_string r)))
                                                                                                                                                                                                                   (pow2 17)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                                                                                                                                                                                              else None Else None,
                                                                                                                                                                                                       snd ce)))),
                         Ifopt Ifopt fst ce as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None as curPtr
                                                                                                                         Then (fst
                                                                                                                                 (snd
                                                                                                                                    (y
                                                                                                                                       (snd (split_string r))
                                                                                                                                       (@split_string_ValidDomainName_length r e)
                                                                                                                                       (Ifopt Ifopt
                                                                                                                                              fst ce as m
                                                                                                                                                          Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                               then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                               else None Else None as m
                                                                                                                                                                                        Then if Compare_dec.lt_dec
                                                                                                                                                                                                  (wordToNat m + 8 * String.length (fst (split_string r)))
                                                                                                                                                                                                  (pow2 17)
                                                                                                                                                                                             then
                                                                                                                                                                                               Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                                                                                                                                                                             else None Else None,
                                                                                                                                                                                      snd ce))),
                                                                                                                               ((r, curPtr)
                                                                                                                                  :: snd
                                                                                                                                  (snd
                                                                                                                                     (y (snd (split_string r))
                                                                                                                                        (@split_string_ValidDomainName_length r e)
                                                                                                                                        (Ifopt Ifopt
                                                                                                                                               fst ce as m
                                                                                                                                                           Then
                                                                                                                                                           if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                           then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                           else None Else None as m
                                                                                                                                                                                    Then if Compare_dec.lt_dec
                                                                                                                                                                                              (wordToNat m + 8 * String.length (fst (split_string r)))
                                                                                                                                                                                              (pow2 17)
                                                                                                                                                                                         then
                                                                                                                                                                                           Some
                                                                                                                                                                                             (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                                                                                                                                                                         else None Else None,
                                                                                                                                                                                  snd ce))))%list)
                                                                                                                         Else snd
                                                                                                                         (y
                                                                                                                            (snd (split_string r))
                                                                                                                            (@split_string_ValidDomainName_length r e)
                                                                                                                            (Ifopt Ifopt fst ce as m
                                                                                                                                                     Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                          then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                          else None Else None as m
                                                                                                                                                                                   Then if Compare_dec.lt_dec
                                                                                                                                                                                             (wordToNat m + 8 * String.length (fst (split_string r)))
                                                                                                                                                                                             (pow2 17)
                                                                                                                                                                                        then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                                                                                                                                                                        else None Else None,
                                                                                                                                                                                 snd ce)))
           end).

  Lemma refine_If_string_dec {A}
    : forall s s' (t e : Comp A)
             (t' : s = s' -> Comp A)
             (e' : s <> s' -> Comp A),
      (forall e'', refine t (t' e''))
      -> (forall n, refine e (e' n))
      -> refine (If string_dec s s' Then t Else e)
                (match string_dec s s' with
                 | left e'' => t' e''
                 | right n => e' n
                 end).
  Proof.
    intros; destruct (string_dec s s'); auto.
  Qed.

  Lemma align_format_DomainName
    : forall d ce
             (d_OK : ValidDomainName d),
      refine (format_DomainName d ce)
             (ret (build_aligned_ByteString (projT2 (fst (aligned_format_DomainName d ce))),
                   (snd (aligned_format_DomainName d ce)))).
  Proof.
    intros.
    etransitivity.
    eapply (byte_align_Fix_encode_inv ValidDomainName) with
    (lt_A := fun a a' => lt (String.length (projT1 a)) (String.length (projT1 a')));
      eauto using format_body_monotone.
    intros.
    etransitivity.
    match goal with
      |- refine (If_Then_Else (bool_of_sumbool (string_dec ?s ?s')) _ _) _ =>
      subst_refine_evar; eapply (refine_If_string_dec s s');
        let H := fresh in
        intro H; set_refine_evar; try rewrite H; simpl
    end.
    unfold AsciiOpt.format_ascii; rewrite aligned_format_char_eq.
    subst_refine_evar; higher_order_reflexivity.
    refine pick val None; try congruence.
    simplify with monad laws; simpl.
    unfold Bind2.
    refine pick val (split_string (projT1 r)).
    simplify with monad laws.
    unfold format_nat.
    rewrite aligned_format_char_eq.
    simplify with monad laws.
    rewrite format_string_ByteString.
    simplify with monad laws.
    unfold snd at 2; unfold snd at 2.
    unfold fst at 2; unfold fst at 2.
    unfold fst at 2.
    rewrite (H (existT _ _ (split_string_ValidDomainName _ (projT2 r)))
               (@split_string_ValidDomainName_length _ H0)).
    simplify with monad laws.
    Arguments mult : simpl never.
    simpl.
    subst_refine_evar; higher_order_reflexivity.
    auto using addE_addE_plus.
    destruct r; apply split_string_OK.
    simpl; eauto.
    instantiate (1 := (fun (r : {a : string & ValidDomainName a})
                           (y : forall r' : {a : string & ValidDomainName a},
                               lt (String.length (projT1 r')) (String.length (projT1 r))%nat ->
                               CacheFormat -> {n : nat & t (word 8) n} * CacheFormat)
                           (ce : CacheFormat) =>
                         match string_dec (projT1 r) "" with
                         | left _ =>  (existT (fun n : nat => t (word 8) n) 1 [NToWord 8 (Ascii.N_of_ascii terminal_char)], addE ce 8)
                         | right n' =>  (existT (fun n : nat => t (word 8) n)
                                                (1 + String.length (fst (split_string (projT1 r))) +
                                                 projT1
                                                   (fst
                                                      (y
                                                         (existT ValidDomainName
                                                                 (snd (split_string (projT1 r)))
                                                                 (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                                         (@split_string_ValidDomainName_length (projT1 r) n')
                                                         (Ifopt Ifopt fst ce as m
                                                                                  Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                       then Some (natToWord 17 (wordToNat m + 8))
                                                                                       else None Else None as m
                                                                                                                Then if Compare_dec.lt_dec
                                                                                                                          (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                                                                                          (pow2 17)
                                                                                                                     then
                                                                                                                       Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                                                                                                     else None Else None,
                                                                                                              snd ce))))
                                                (([natToWord 8 (String.length (let (x0, _) := split_string (projT1 r) in x0))] ++
                                                                                                                               StringToBytes (fst (split_string (projT1 r)))) ++
                                                                                                                                                                              projT2
                                                                                                                                                                              (fst
                                                                                                                                                                                 (y
                                                                                                                                                                                    (existT ValidDomainName
                                                                                                                                                                                            (snd (split_string (projT1 r)))
                                                                                                                                                                                            (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                                                                                                                                                                    (@split_string_ValidDomainName_length (projT1 r) n')
                                                                                                                                                                                    (Ifopt Ifopt fst ce as m
                                                                                                                                                                                                             Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                                                                                  then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                                                                                  else None Else None as m
                                                                                                                                                                                                                                           Then if Compare_dec.lt_dec
                                                                                                                                                                                                                                                     (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                                                                                                                                                                                                                     (pow2 17)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                                                                                                                                                                                                                                else None Else None,
                                                                                                                                                                                                                                         snd ce)))),
                                         Ifopt Ifopt fst ce as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None as curPtr
                                                                                                                                         Then (fst
                                                                                                                                                 (snd
                                                                                                                                                    (y
                                                                                                                                                       (existT ValidDomainName
                                                                                                                                                               (snd (split_string (projT1 r)))
                                                                                                                                                               (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                                                                                                                                       (@split_string_ValidDomainName_length (projT1 r) n')
                                                                                                                                                       (Ifopt Ifopt
                                                                                                                                                              fst ce as m
                                                                                                                                                                          Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                                               then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                                               else None Else None as m
                                                                                                                                                                                                        Then if Compare_dec.lt_dec
                                                                                                                                                                                                                  (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                                                                                                                                                                                  (pow2 17)
                                                                                                                                                                                                             then
                                                                                                                                                                                                               Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                                                                                                                                                                                             else None Else None,
                                                                                                                                                                                                      snd ce))),
                                                                                                                                               ((projT1 r, curPtr)
                                                                                                                                                  :: snd
                                                                                                                                                  (snd
                                                                                                                                                     (y
                                                                                                                                                        (existT ValidDomainName
                                                                                                                                                                (snd (split_string (projT1 r)))
                                                                                                                                                                (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                                                                                                                                        (@split_string_ValidDomainName_length (projT1 r) n')
                                                                                                                                                        (Ifopt Ifopt
                                                                                                                                                               fst ce as m
                                                                                                                                                                           Then
                                                                                                                                                                           if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                                           then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                                           else None Else None as m
                                                                                                                                                                                                    Then if Compare_dec.lt_dec
                                                                                                                                                                                                              (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                                                                                                                                                                              (pow2 17)
                                                                                                                                                                                                         then
                                                                                                                                                                                                           Some
                                                                                                                                                                                                             (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                                                                                                                                                                                         else None Else None,
                                                                                                                                                                                                  snd ce))))%list)
                                                                                                                                         Else snd
                                                                                                                                         (y
                                                                                                                                            (existT ValidDomainName
                                                                                                                                                    (snd (split_string (projT1 r)))
                                                                                                                                                    (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                                                                                                                            (@split_string_ValidDomainName_length (projT1 r) n')
                                                                                                                                            (Ifopt Ifopt fst ce as m
                                                                                                                                                                     Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                                                                                                                                          then Some (natToWord 17 (wordToNat m + 8))
                                                                                                                                                                          else None Else None as m
                                                                                                                                                                                                   Then if Compare_dec.lt_dec
                                                                                                                                                                                                             (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                                                                                                                                                                             (pow2 17)
                                                                                                                                                                                                        then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                                                                                                                                                                                        else None Else None,
                                                                                                                                                                                                 snd ce))) end)).
    simpl.
    destruct (string_dec (projT1 r) ""); simpl.
    reflexivity.
    rewrite <- !build_aligned_ByteString_append.
    destruct (y (existT ValidDomainName (snd (split_string (projT1 r))) (split_string_ValidDomainName (projT1 r) (projT2 r)))
                (@split_string_ValidDomainName_length (projT1 r) n)
                (Ifopt Ifopt fst ce0 as m
                                          Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17) then Some (natToWord 17 (wordToNat m + 8)) else None
                                                                                                                                                   Else None as m
                                                                                                                                                                  Then if Compare_dec.lt_dec (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))) (pow2 17)
                                                                                                                                                                       then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                                                                                                                                                       else None Else None, snd ce0)); simpl.
    rewrite <- !build_aligned_ByteString_append.
    reflexivity.
    intros; apply functional_extensionality; intros.
    destruct (string_dec (projT1 x0) ""); simpl; try rewrite H; reflexivity.
    instantiate (2 := well_founded_string_length').
    instantiate (1 := d_OK).
    match goal with
      |- context [let (_,_) := ?z in _] =>
      replace z with
      (aligned_format_DomainName d ce)
    end.
    destruct (aligned_format_DomainName d ce); reflexivity.
    simpl. admit.
  Qed.

  (*  Lemma align_format_DomainName
    : forall d ce
      (d_OK : ValidDomainName d),
      refine (format_DomainName d ce)
             (ret (build_aligned_ByteString (projT2 (fst (aligned_format_DomainName d ce))),
                   (snd (aligned_format_DomainName d ce)))).
  Proof.
    intros.
    etransitivity.
    eapply (byte_align_Fix_encode_inv ValidDomainName) with
    (lt_A := fun a a' => lt (String.length (projT1 a)) (String.length (projT1 a')));
      eauto using format_body_monotone.
    intros.
    etransitivity.
    match goal with
      |- refine (If_Then_Else (bool_of_sumbool (string_dec ?s ?s')) _ _) _ =>
      subst_refine_evar; eapply (refine_If_string_dec s s');
        let H := fresh in
        intro H; set_refine_evar; try rewrite H; simpl
    end.
    unfold AsciiOpt.format_ascii; rewrite aligned_format_char_eq.
    subst_refine_evar; higher_order_reflexivity.
    refine pick val None; try congruence.
    simplify with monad laws; simpl.
    unfold Bind2.
    refine pick val (split_string (projT1 r)).
    simplify with monad laws.
    unfold format_nat.
    rewrite aligned_format_char_eq.
    simplify with monad laws.
    rewrite format_string_ByteString.
    simplify with monad laws.
    unfold snd at 2; unfold snd at 2.
    unfold fst at 2; unfold fst at 2.
    unfold fst at 2.
    rewrite (H (exist _ _ (split_string_ValidDomainName _ (projT2 r)))
                   (@split_string_ValidDomainName_length _ H0)).
    simplify with monad laws.
    Arguments mult : simpl never.
    simpl.
    subst_refine_evar; higher_order_reflexivity.
    auto using addE_addE_plus.
    destruct r; apply split_string_OK.
    simpl; eauto.
    instantiate (1 := (fun (r : {a : string & ValidDomainName a})
                     (y : forall r' : {a : string & ValidDomainName a},
                          lt (String.length (projT1 r')) (String.length (projT1 r))%nat ->
                          CacheFormat -> {n : nat & t (word 8) n} * CacheFormat)
                     (ce : CacheFormat) =>
                   match string_dec (projT1 r) "" with
                   | left _ =>  (existT (fun n : nat => t (word 8) n) 1 [NToWord 8 (Ascii.N_of_ascii terminal_char)], addE ce 8)
                   | right n' =>  (existT (fun n : nat => t (word 8) n)
                           (1 + String.length (fst (split_string (projT1 r))) +
                            projT1
                              (fst
                                 (y
                                    (existT ValidDomainName
                                       (snd (split_string (projT1 r)))
                                       (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                    (@split_string_ValidDomainName_length (projT1 r) n')
                                    (Ifopt Ifopt fst ce as m
                                           Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                     Then if Compare_dec.lt_dec
                                               (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                               (pow2 17)
                                          then
                                           Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                          else None Else None,
                                    snd ce))))
                           (([natToWord 8 (String.length (let (x0, _) := split_string (projT1 r) in x0))] ++
                             StringToBytes (fst (split_string (projT1 r)))) ++
                            projT2
                              (fst
                                 (y
                                    (existT ValidDomainName
                                       (snd (split_string (projT1 r)))
                                       (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                    (@split_string_ValidDomainName_length (projT1 r) n')
                                    (Ifopt Ifopt fst ce as m
                                           Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                     Then if Compare_dec.lt_dec
                                               (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                               (pow2 17)
                                          then
                                           Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                          else None Else None,
                                    snd ce)))),
                        Ifopt Ifopt fst ce as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None as curPtr
                        Then (fst
                                (snd
                                   (y
                                      (existT ValidDomainName
                                         (snd (split_string (projT1 r)))
                                         (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                      (@split_string_ValidDomainName_length (projT1 r) n')
                                      (Ifopt Ifopt
                                             fst ce as m
                                             Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                  then Some (natToWord 17 (wordToNat m + 8))
                                                  else None Else None as m
                                       Then if Compare_dec.lt_dec
                                                 (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                 (pow2 17)
                                            then
                                             Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                            else None Else None,
                                      snd ce))),
                             ((projT1 r, curPtr)
                              :: snd
                                   (snd
                                      (y
                                         (existT ValidDomainName
                                            (snd (split_string (projT1 r)))
                                            (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                         (@split_string_ValidDomainName_length (projT1 r) n')
                                         (Ifopt Ifopt
                                                fst ce as m
                                                Then
                                                if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                          Then if Compare_dec.lt_dec
                                                  (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                  (pow2 17)
                                               then
                                                Some
                                                  (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                               else None Else None,
                                         snd ce))))%list)
                        Else snd
                               (y
                                  (existT ValidDomainName
                                     (snd (split_string (projT1 r)))
                                     (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                  (@split_string_ValidDomainName_length (projT1 r) n')
                                  (Ifopt Ifopt fst ce as m
                                         Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                              then Some (natToWord 17 (wordToNat m + 8))
                                              else None Else None as m
                                   Then if Compare_dec.lt_dec
                                             (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                             (pow2 17)
                                        then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                        else None Else None,
                                  snd ce))) end)).
    simpl.
    destruct (string_dec (projT1 r) ""); simpl.
    reflexivity.
    rewrite <- !build_aligned_ByteString_append.
    progress destruct (y (existT ValidDomainName (snd (split_string (projT1 r))) (split_string_ValidDomainName (projT1 r) (projT2 r)))
                (@split_string_ValidDomainName_length (projT1 r) n)
                (Ifopt Ifopt fst ce0 as m
                       Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17) then Some (natToWord 17 (wordToNat m + 8)) else None
                       Else None as m
                 Then if Compare_dec.lt_dec (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))) (pow2 17)
                      then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                      else None Else None, snd ce0)) eqn:?; simpl.
    match goal with
      |- context [y ?A ?B ?C] => set (H4 := y A B C)
    end.
  Admitted.
   (*    rewrite Heqp in H4.
    rewrite <- !build_aligned_ByteString_append.
    reflexivity.
    intros; apply functional_extensionality; intros.
    destruct (string_dec (projT1 x0) ""); simpl; try rewrite H; reflexivity.
    instantiate (2 := well_founded_string_length').
    instantiate (1 := d_OK).
    match goal with
      |- context [let (_,_) := ?z in _] =>
      replace z with
      (aligned_format_DomainName d ce)
    end.
    destruct (aligned_format_DomainName d ce); reflexivity.
    simpl. admit.
  Qed. *) *)



  Lemma byte_align_Fix_encode {A}
        (lt_A : A -> A -> Prop)
        (wf_lt_A : well_founded lt_A)
    : forall
      (body : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat)
              -> FixComp.funType [A; CacheFormat] (ByteString * CacheFormat))
      (body' : forall r : A,
          (forall r' : A, lt_A r' r -> FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat)) ->
          FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat))

      (refine_body_OK : forall (r : A)
                               (x : A -> CacheFormat  ->
                                    Comp (ByteString * CacheFormat))
                               (y : forall r' : A,
                                   lt_A r' r ->
                                   CacheFormat ->
                                   {n : _ & Vector.t (word 8) n} * CacheFormat),
          (forall (a' : A) (wf_r : lt_A a' r) (ce : CacheFormat),
              refine (x a' ce)
                     (ret (let (v, ce') := y a' wf_r ce in
                           (build_aligned_ByteString (projT2 v), ce'))))
          -> forall ce, refine (body x r ce) (ret (let (v, ce') := body' r y ce in
                                                   (build_aligned_ByteString (projT2 v), ce'))))

      (body_monotone : forall rec rec' : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat),
          FixComp.refineFun rec rec' -> FixComp.refineFun (body rec) (body rec'))
      (body'_monotone : forall (x0 : A)
                               (f
                                  g : {y : A | lt_A y x0} ->
                                      CacheFormat ->
                                      {n : nat & t (word 8) n} * (CacheFormat)),
          (forall y : {y : A | lt_A y x0}, f y = g y) ->
          body' x0 (fun (a' : A) (lt_a' : lt_A a' x0) => f (exist (fun a'0 : A => lt_A a'0 x0) a' lt_a')) =
          body' x0 (fun (a' : A) (lt_a' : lt_A a' x0) => g (exist (fun a'0 : A => lt_A a'0 x0) a' lt_a')))
      (a : A) (ce : CacheFormat),
      refine (FixComp.LeastFixedPointFun.LeastFixedPoint body a ce)
             (ret (let (v, ce') := Fix wf_lt_A _ body' a ce in
                   (build_aligned_ByteString (projT2 v), ce'))).
  Proof.
    intros.
    unfold FixComp.LeastFixedPointFun.LeastFixedPoint, respectful_hetero; intros.
    simpl.
    revert ce; pattern a; eapply (well_founded_ind wf_lt_A).
    simpl; intros.
    pose proof (proj1 (Frame.Is_GreatestFixedPoint (O := @FixComp.LeastFixedPointFun.funDefOps [A; CacheFormat] (ByteString * CacheFormat)) _ (body_monotone))); etransitivity.
    eapply H0; eauto.
    destruct (Fix wf_lt_A
                  (fun _ : A =>
                     CacheFormat ->
                     {n : nat & t (word 8) n} * (CacheFormat)) body' x ce) eqn: ?.
    pose proof (Fix_eq _ _ wf_lt_A _ (fun a rec => body' a (fun a' lt_a' => rec (exist (fun a' => lt_A a' a) a' lt_a')))).
    generalize Heqp as Heqp'; intros.
    simpl in H1; unfold Fix_sub, Fix_F_sub in H1; unfold Fix, Fix_F in Heqp.
    rewrite H1 in Heqp; simpl in Heqp; clear H1; eauto.
    etransitivity.
    eapply refine_body_OK.
    instantiate (1 := (fun (a' : A) (_ : lt_A a' x) =>
                         (fix Fix_F_sub (x0 : A) (r : Acc lt_A x0) {struct r} :
                            CacheFormat ->
                            {n : nat & t (word 8) n} * (CacheFormat) :=
                            body' x0 (fun (a'0 : A) (lt_a'0 : lt_A a'0 x0) => Fix_F_sub a'0 (Acc_inv r lt_a'0))) a'
                                                                                                                 (wf_lt_A a'))).
    eapply H; eauto.
    unfold CacheFormat, dns_list_cache.
    rewrite Heqp.
    unfold CacheFormat, dns_list_cache in Heqp'.
    rewrite Heqp'; reflexivity.
  Qed.

  Lemma byte_align_Fix_encode_inv {A}
        (A_OK : A -> Prop)
        (lt_A : _ -> _ -> Prop)
        (wf_lt_A : well_founded lt_A)
    : forall
      (body : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat)
              -> FixComp.funType [A; CacheFormat] (ByteString * CacheFormat))
      (body' : forall r : { a : _ & A_OK a},
          (forall r' : { a : _ & A_OK a},
              lt_A r' r
              -> FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat)) ->
          FixComp.LeastFixedPointFun.cfunType [CacheFormat] ({n : _ & Vector.t (word 8) n} * CacheFormat))
      (refine_body_OK : forall (r : { a : _ & A_OK a})
                               (x : A -> CacheFormat ->
                                    Comp (ByteString * CacheFormat))
                               (y : forall r' : { a : _ & A_OK a},
                                   lt_A r' r ->
                                   CacheFormat ->
                                   {n : _ & Vector.t (word 8) n} * CacheFormat),
          (forall (a' : { a : _ & A_OK a}) (wf_r : lt_A a' r) (ce : CacheFormat),
              refine (x (projT1 a') ce)
                     (ret (let (v, ce') := y a' wf_r ce in
                           (build_aligned_ByteString (projT2 v), ce'))))
          -> forall ce, refine (body x (projT1 r) ce) (ret (let (v, ce') := body' r y ce in
                                                            (build_aligned_ByteString (projT2 v), ce'))))

      (body_monotone : forall rec rec' : FixComp.funType [A; CacheFormat] (ByteString * CacheFormat),
          FixComp.refineFun rec rec' -> FixComp.refineFun (body rec) (body rec'))
      (body'_monotone : forall (x0 : { a : _ & A_OK a})
                               (f
                                  g : {y : { a : _ & A_OK a} | lt_A y x0} ->
                                      CacheFormat ->
                                      {n : nat & t (word 8) n} * (CacheFormat)),
          (forall y : {y : { a : _ & A_OK a} | lt_A y x0}, f y = g y) ->
          body' x0 (fun (a' : { a : _ & A_OK a}) (lt_a' : lt_A a' x0) => f (exist (fun a'0 : { a : _ & A_OK a} => lt_A a'0 x0) a' lt_a')) =
          body' x0 (fun (a' : { a : _ & A_OK a}) (lt_a' : lt_A a' x0) => g (exist (fun a'0 : { a : _ & A_OK a} => lt_A a'0 x0) a' lt_a')))
      (a : A) (ce : CacheFormat) (a_OK : A_OK a),
      refine (FixComp.LeastFixedPointFun.LeastFixedPoint body a ce)
             (ret (let (v, ce') := Fix wf_lt_A _ body' (existT _ _ a_OK) ce in
                   (build_aligned_ByteString (projT2 v), ce'))).
  Proof.
    (*intros. (* 8.4 script *)
    unfold FixComp.LeastFixedPointFun.LeastFixedPoint, respectful_hetero; intros.
    simpl.
    replace a with (projT1 (existT _ a a_OK)) at 1.
    revert ce; pattern (existT _ a a_OK); eapply (well_founded_ind wf_lt_A).
    simpl; intros.
    pose proof (proj1 (Frame.Is_GreatestFixedPoint (O := @FixComp.LeastFixedPointFun.funDefOps [A; CacheFormat] (ByteString * CacheFormat)) _ (body_monotone))); etransitivity.
    eapply H0; eauto.
    destruct ( Fix wf_lt_A
                   (fun _ : {a0 : A & A_OK a0} =>
                      CacheFormat ->
                      {n : nat & t (word 8) n} * (CacheFormat)) body' x ce) eqn: ?.
    pose proof (Fix_eq _ _ wf_lt_A _ (fun a rec => body' a (fun a' lt_a' => rec (exist (fun a' => lt_A a' a) a' lt_a')))).
    simpl in H1; unfold Fix_sub, Fix_F_sub in H1; unfold Fix, Fix_F in Heqp.
    generalize Heqp as Heqp'; intros.
    rewrite H1 in Heqp; simpl in Heqp; clear H1; eauto.
    etransitivity.
    eapply refine_body_OK.
    instantiate (1 := fun (a' : {a0 : A & A_OK a0}) (_ : lt_A a' x) =>
                        (fix Fix_F_sub (x0 : {a0 : A & A_OK a0}) (r : Acc lt_A x0) {struct r} :
                           CacheFormat ->
                           {n : nat & t (word 8) n} * (CacheFormat) :=
                           body' x0 (fun (a'0 : {a0 : A & A_OK a0}) (lt_a'0 : lt_A a'0 x0) => Fix_F_sub a'0 (Acc_inv r lt_a'0))) a'
                                                                                                                                 (wf_lt_A a')).
    eapply H; eauto.
    unfold CacheFormat, dns_list_cache, Fix, Fix_F in *.
    rewrite Heqp, Heqp'.
    reflexivity.
    reflexivity.
  Qed. *)
  intros. 
    unfold FixComp.LeastFixedPointFun.LeastFixedPoint, respectful_hetero; intros.
    simpl.
    replace a with (projT1 (existT (fun a0 : A => A_OK a0) a a_OK)) at 1 by reflexivity.
    revert ce; pattern (existT (fun a0 : A => A_OK a0) a a_OK); eapply (well_founded_ind wf_lt_A).
    simpl; intros.
    pose proof (proj1 (Frame.Is_GreatestFixedPoint (O := @FixComp.LeastFixedPointFun.funDefOps [A; CacheFormat] (ByteString * CacheFormat)) _ (body_monotone))); etransitivity.
    eapply H0; eauto.
    destruct (Fix wf_lt_A
               (fun _ : {a0 : A & A_OK a0} =>
                CacheFormat ->
                {n : nat & t (word 8) n} * (CacheFormat)) body' x ce) eqn: ?.
    pose proof (Fix_eq _ _ wf_lt_A _ (fun a rec => body' a (fun a' lt_a' => rec (exist (fun a' => lt_A a' a) a' lt_a')))).
    simpl in H1; unfold Fix_sub, Fix_F_sub in H1; unfold Fix, Fix_F in Heqp.
    rewrite H1 in Heqp; simpl in Heqp; clear H1; eauto.
    etransitivity.
    eapply refine_body_OK.
    instantiate (1 := fun (a' : {a0 : A & A_OK a0}) (_ : lt_A a' x) =>
            (fix Fix_F_sub (x0 : {a0 : A & A_OK a0}) (r : Acc lt_A x0) {struct r} :
               CacheFormat ->
               {n : nat & t (word 8) n} * (CacheFormat) :=
               body' x0 (fun (a'0 : {a0 : A & A_OK a0}) (lt_a'0 : lt_A a'0 x0) => Fix_F_sub a'0 (Acc_inv r lt_a'0))) a'
              (wf_lt_A a')).
    simpl; intros; rewrite H; eauto;  reflexivity.
    admit.
    (*rewrite Heqp; try reflexivity. *)
  Qed.

  Lemma AlignedFormatDomainNameThenC
    : (forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m)) ->
      forall (numBytes : nat)
             (d : DomainName)
             (ce ce' : CacheFormat)
             (c : CacheFormat -> Comp (ByteString * CacheFormat))
             (v : t Core.char numBytes),
        ValidDomainName d ->
        refine (c (snd (aligned_format_DomainName d ce))) (ret (build_aligned_ByteString v, ce')) ->
        refine ((format_DomainName d ThenC c) ce)
               (ret (build_aligned_ByteString ((projT2 (fst (aligned_format_DomainName d ce))) ++ v), ce')).
  Proof.
    unfold compose at 1, Bind2; intros.
    rewrite align_format_DomainName; eauto.
    simplify with monad laws.
    simpl; rewrite H1.
    simplify with monad laws; simpl.
    rewrite build_aligned_ByteString_append; reflexivity.
  Qed.

  Lemma AlignedFormatDomainNameDoneC
    : (forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m)) ->
      forall (d : DomainName)
             (ce : CacheFormat),
        ValidDomainName d ->
        refine ((format_DomainName d DoneC) ce)
               (ret (build_aligned_ByteString (projT2 (fst (aligned_format_DomainName d ce))),
                     snd (aligned_format_DomainName d ce))).
  Proof.
    unfold compose at 1, Bind2; intros.
    rewrite align_format_DomainName; eauto.
    simplify with monad laws.
    simpl.
    replace ByteString_id with (build_aligned_ByteString (Vector.nil _)).
    simpl.
    rewrite <- build_aligned_ByteString_append.
    rewrite Vector_append_nil_r'; simpl.
    repeat f_equiv.
    eapply ByteString_f_equal; simpl; eauto.
    eapply ByteString_f_equal; simpl;
      try instantiate (1 := eq_refl _); reflexivity.
    Grab Existential Variables.
    reflexivity.
  Qed.

  Arguments Guarded_Vector_split : simpl never.

  Arguments addD : simpl never.

  Lemma rec_aligned_decode_DomainName_OK
    : forall (x : nat) (x0 : t (word 8) x),
      (le 1 x) ->
      ~ (lt (x - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 x x0))))%nat ->
      (lt (x - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 x x0))) x)%nat.
  Proof.
    clear; intros; omega.
  Qed.

  Definition byte_aligned_decode_DomainName {sz}
             (b : Vector.t (word 8) sz)
             (cd : CacheDecode) :=
    let body :=
        fun n0
            (rec' : forall x : nat,
                (lt x n0)%nat ->
                t Core.char x -> CacheDecode -> option (DomainName * {n1 : nat & t Core.char n1} * CacheDecode))
            b cd =>
          match Compare_dec.le_dec 1 n0 with
          | left e1 =>
            match wlt_dec (natToWord 8 191) (Vector.hd (Guarded_Vector_split 1 n0 b)) with
            | left e =>
              if match n0 - 1 with
                 | 0 => false
                 | S _ => true
                 end
              then
                match
                  association_list_find_first (snd cd)
                                              (exist (wlt (natToWord 8 191)) (Vector.hd (Guarded_Vector_split 1 n0 b)) e,
                                               Vector.hd (Guarded_Vector_split 1 (n0 - 1) (Vector.tl (Guarded_Vector_split 1 n0 b))))
                with
                | Some ""%string => None
                | Some (String _ _ as domain) =>
                  Some
                    (domain,
                     existT (fun n => Vector.t (word 8) n) _ (Vector.tl (Guarded_Vector_split 1 (n0 - 1) (Vector.tl (Guarded_Vector_split 1 n0 b)))),
                     addD (addD cd 8) 8)
                | None => None
                end
              else None
            | right n1 =>
              if bool_of_sumbool (wlt_dec (Vector.hd (Guarded_Vector_split 1 n0 b)) (natToWord 8 64))
              then
                match weq (Vector.hd (Guarded_Vector_split 1 n0 b)) (wzero 8) with
                | in_left => Some (""%string, existT (fun n => Vector.t (word 8) n) _ (Vector.tl (Guarded_Vector_split 1 n0 b)), addD cd 8)
                | right n2 =>
                  (fun a_neq0 : Vector.hd (Guarded_Vector_split 1 n0 b) <> wzero 8 =>
                     match Compare_dec.lt_dec (n0 - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b))) with
                     | left e => (fun _ : lt (n0 - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))%nat => None) e
                     | right n3 =>
                       (fun a_neq1 : ~ lt (n0 - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))%nat =>
                          Ifopt index 0 "."
                                (BytesToString
                                   (fst
                                      (Vector_split (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                    (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                    (Guarded_Vector_split
                                                       (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                       (n0 - 1) (Vector.tl (Guarded_Vector_split 1 n0 b)))))) as a8 Then
                                                                                                                    (fun _ : nat => None) a8
                                                                                                                    Else (`(d, s, c) <- rec' (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                           (rec_aligned_decode_DomainName_OK n0 b e1 n3)
                                                                                                                           (snd
                                                                                                                              (Vector_split
                                                                                                                                 (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                 (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                 (Guarded_Vector_split
                                                                                                                                    (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                    (n0 - 1)
                                                                                                                                    (Vector.tl (Guarded_Vector_split 1 n0 b)))))
                                                                                                                           (addD (addD cd 8) (8 * wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b))));
                                                                                                                            If string_dec d ""
                                                                                                                               Then Some
                                                                                                                               (BytesToString
                                                                                                                                  (fst
                                                                                                                                     (Vector_split
                                                                                                                                        (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                        (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                        (Guarded_Vector_split
                                                                                                                                           (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                           (n0 - 1)
                                                                                                                                           (Vector.tl (Guarded_Vector_split 1 n0 b))))),
                                                                                                                                s,
                                                                                                                                Ifopt Ifopt fst cd as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None
                                                                                                                                   as curPtr
                                                                                                                                        Then (fst c,
                                                                                                                                              ((curPtr,
                                                                                                                                                BytesToString
                                                                                                                                                  (fst
                                                                                                                                                     (Vector_split
                                                                                                                                                        (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                        (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                        (Guarded_Vector_split
                                                                                                                                                           (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                           (n0 - 1)
                                                                                                                                                           (Vector.tl (Guarded_Vector_split 1 n0 b)))))) ::
                                                                                                                                                                                                         snd c)%list) Else c)
                                                                                                                               Else Some
                                                                                                                               ((BytesToString
                                                                                                                                   (fst
                                                                                                                                      (Vector_split
                                                                                                                                         (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                         (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                         (Guarded_Vector_split
                                                                                                                                            (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                            (n0 - 1)
                                                                                                                                            (Vector.tl (Guarded_Vector_split 1 n0 b))))) ++
                                                                                                                                   String "." d)%string,
                                                                                                                                s,
                                                                                                                                Ifopt Ifopt fst cd as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None
                                                                                                                                   as curPtr
                                                                                                                                        Then (fst c,
                                                                                                                                              ((curPtr,
                                                                                                                                                (BytesToString
                                                                                                                                                   (fst
                                                                                                                                                      (Vector_split
                                                                                                                                                         (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                         (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                         (Guarded_Vector_split
                                                                                                                                                            (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                            (n0 - 1)
                                                                                                                                                            (Vector.tl (Guarded_Vector_split 1 n0 b))))) ++
                                                                                                                                                   String "." d)%string) ::
                                                                                                                                                                         snd c)%list) Else c))) n3
                     end) n2
                end
              else None
            end
          | right e => None
          end in
    Fix Wf_nat.lt_wf (fun m : nat => Vector.t (word 8) m -> CacheDecode -> option (_ * { n : _ & Vector.t _ n} * CacheDecode)) body sz b cd.

  Lemma byte_align_decode_DomainName {sz}
    : forall (b : Vector.t (word 8) sz) cd,
      decode_DomainName(build_aligned_ByteString b) cd =
      Ifopt byte_aligned_decode_DomainName b cd as p Then
                                                     (match p with
                                                      | (a, b', cd') => Some (a, build_aligned_ByteString (projT2 b'), cd')
                                                      end)
                                                     Else None.
  Proof.
  Admitted.
  (*(* 8.4 script *)
    unfold If_Opt_Then_Else,decode_DomainName,
    byte_aligned_decode_DomainName; simpl; intros.
    eapply (@optimize_Fix dns_list_cache).
    Focus 3.
    etransitivity.
    simpl; intros.
    erewrite ByteAlign_Decode_w_Measure_le with (m := 1)
                                                  (dec_a' := Vector.hd)
                                                  (f := fun cd => addD cd 8);
      try (intros; unfold decode_word; rewrite aligned_decode_char_eq;
           reflexivity).
    Focus 2.
    intros; assert (n = 0) by omega; subst.
    revert b1; clear.
    apply case0; reflexivity.
    set_refine_evar.
    etransitivity;
      [eapply (@If_sumbool_Then_Else_DecodeBindOpt _ _ _ _ _ dns_list_cache) | ]; simpl.

    apply optimize_under_match; intros.
    simpl.

    apply optimize_under_match; intros.
    simpl.
    erewrite ByteAlign_Decode_w_Measure_le with (m := 1)
                                                  (dec_a' := Vector.hd)
                                                  (f := fun cd => addD cd 8);
      try (intros; unfold decode_word; rewrite aligned_decode_char_eq;
           reflexivity).
    Focus 2.
    intros; assert (n - 1 = 0) by omega.
    revert b1; rewrite H3; clear.
    apply case0; reflexivity.
    set_refine_evar.
    simpl.
    etransitivity;
      [eapply (@If_sumbool_Then_Else_DecodeBindOpt _ _ _ _ _ dns_list_cache) | ]; simpl.
    apply optimize_under_match; intros.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    eapply Solver.optimize_under_if_bool.
    apply optimize_under_match.
    simpl.
    intros; higher_order_reflexivity.
    intros.
    simpl.
    2: reflexivity.
    2: reflexivity.
    2: simpl.
    erewrite ByteAlign_Decode_w_Measure_lt with (m := (wordToNat (Vector.hd (Guarded_Vector_split 1 n b0)))) (m_OK := n_eq_0_lt _ a_neq0).
    Focus 3.

    intros.
    rewrite decode_string_aligned_ByteString.
    repeat f_equal.
    higher_order_reflexivity.
    higher_order_reflexivity.
    apply addD_addD_plus.
    etransitivity;
      [eapply (@If_sumbool_Then_Else_DecodeBindOpt _ _ _ _ _ dns_list_cache) | ]; simpl.
    etransitivity.
    apply optimize_under_match; intros.
    subst_refine_evar; simpl; higher_order_reflexivity.
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    subst_refine_evar; simpl; higher_order_reflexivity.
    apply optimize_under_match; intros.
    simpl; higher_order_reflexivity.
    unfold LetIn.
    apply optimize_under_if_opt.
    intros; higher_order_reflexivity.
    eapply optimize_under_DecodeBindOpt2_both.
    unfold lt_B_Guarded_Vector_split; simpl.
    intros; apply H with (b_lt' := rec_aligned_decode_DomainName_OK _ _ a_eq a_neq1).
    apply H2.
    intros; eapply H0; eauto.
    intros; simpl.
    higher_order_reflexivity.
    intros; eauto using decode_string_aligned_ByteString_overflow.
    destruct n; eauto.
    destruct (wlt_dec (natToWord 8 191) (Vector.hd (Guarded_Vector_split 1 (S n) b0)));
      eauto.
    find_if_inside; eauto.
    simpl.
    find_if_inside; eauto.
    destruct n; try omega; simpl; eauto.
    match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    clear; induction s; simpl; eauto.
    destruct n; simpl; auto; try omega.
    match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    find_if_inside; simpl; eauto.
  Admitted.
  match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- (Ifopt ?c as a Then _ Else _) = _ => destruct c as [ ? | ]; simpl; eauto
    end.
    match goal with
      |- DecodeBindOpt2 ?z _ = _ => destruct z as [ [ [? ?] ?] | ]; simpl; eauto
    end.
    find_if_inside; simpl; eauto.
    simpl; intros; apply functional_extensionality; intros.
    f_equal.
    simpl; intros; repeat (apply functional_extensionality; intros).
    destruct (wlt_dec (natToWord 8 191) x1).
    reflexivity.
    destruct (wlt_dec x1 (natToWord 8 64)); simpl.
    destruct (weq x1 (wzero 8)); eauto.
    match goal with
      |- DecodeBindOpt2 ?z _ = _ => destruct z as [ [ [? ?] ?] | ]; simpl; eauto
    end.
    match goal with
      |- (Ifopt ?c as a Then _ Else _) = _ => destruct c as [ ? | ]; simpl; eauto
    end.
    rewrite H.
    reflexivity.
    eauto.
    simpl; intros; apply functional_extensionality; intros.
    f_equal.
    simpl; intros; repeat (apply functional_extensionality; intros).
    match goal with
      |- match ?z with _ => _ end = match ?z' with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- match ?z with _ => _ end = match ?z' with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    find_if_inside; simpl.
    find_if_inside; simpl; eauto.
    match goal with
      |- match ?z with _ => _ end = match ?z' with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- (Ifopt ?c as a Then _ Else _) = _ => destruct c as [ ? | ]; simpl; eauto
    end.
    rewrite H; reflexivity.
    eauto.
  Qed. *)

End AlignedDomainName.
