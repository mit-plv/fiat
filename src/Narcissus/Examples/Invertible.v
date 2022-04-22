(*+ Examples of invertible functions/relations *)
(* When the format uses composition to intorudce porjections (in the
general sense), we use the invertibility of the function/relation to
recover the encoded object.  *)

Require Import Fiat.Narcissus.Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Formats.Reorder.
Require Import 
        Coq.Sorting.Permutation.
Require Import Fiat.Narcissus.Automation.Invertible.

(*For finite types *)
Require Import Coq.Logic.FinFun.

Set Warnings "-local-declaration".
Set Nested Proofs Allowed.


Module Revert.
  (* revert words is it's own invers. *)
  
  
Fixpoint wreverse {sz} (w : word sz) : word sz :=
  match w with
  | WO          => WO
  | WS b n rest => append_bit b (wreverse rest)
  end.


(* Prove the inversion lemmas and create an instance of the inversible class *)
Lemma wreverse_lemma1
: forall {sz} (b : bool) (w : word sz),
  wreverse (append_bit b w) = WS b (wreverse w).
Proof.
  induction w. simpl. reflexivity.
  simpl. rewrite IHw. simpl. reflexivity.
Qed.
Theorem inverse_wreverse
: forall sz (s v : word sz),
  wreverse s = v  ->  s = wreverse v.
Proof.
  intros. rewrite <- H. clear H v.
  induction s.
  simpl. reflexivity. 
  simpl. rewrite wreverse_lemma1. rewrite <- IHs. reflexivity.
Qed.

Instance CInv_wreverse (sz:nat): ConditionallyInvertible (@wreverse sz) (constant True) wreverse .
Proof.
  constructor; intros.
  rewrite <- (inverse_wreverse _ a); reflexivity.
Qed.
Opaque wreverse.


Record sensor_msg := { firstW: word 8; secondW: word 16 }.

Let format_int_reverse : FormatM sensor_msg ByteString :=
     format_word ◦ wreverse (sz:=8) ◦ firstW
  ++ format_word ◦ wreverse (sz:=16) ◦ secondW.
 
Let enc_dec_automatic:
  EncoderDecoderPair format_int_reverse (constant True).
Proof. derive_encoder_decoder_pair. Defined.

End Revert.

 


Module Nat.
  (* Elements using coq nats. The function natToWord is ony invertible
  as long as the number is bownded. *)

  Instance CInv_natToWord (n:nat): ConditionallyInvertible (natToWord n) (fun x => x < pow2 n) (@wordToNat n).
  Proof. constructor; intros. apply wordToNat_natToWord_idempotent.
         apply Nomega.Nlt_in. rewrite Nnat.Nat2N.id, Npow2_nat.
         assumption.
  Qed.


  (* project from nat *)
  Record sensor_msg :=
    { stationID: nat; data: word 16 }.

  Let format :=
        format_word ◦ natToWord 8 ∘ stationID
                    ++ format_word ◦ data.

  Let invariant (msg:sensor_msg):= stationID msg < pow2 8.
  Let enc_dec_nat : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.  Defined.

  Let encode := encoder_impl enc_dec_nat.
  Let decode := decoder_impl enc_dec_nat.

End Nat.

Module FinT.
  (* Elements using finite types `Fin.t`. Works just like for `nat`,
  but with a little more type dependance. *)

  (*We define the inverse and two possible inversion classes*)

  Definition word2Fin {n sz:nat} (w: word sz): Fin.t (S n).
  Proof.
    apply (@Fin.of_nat_lt (min (wordToNat w) n) (S n)).
    lia.
  Defined.
  
  Instance CInv_finToWord (n sz:nat):
    ConditionallyInvertible (@fin2Word (S n) sz) (fun a => Fin2Restrict.f2n a < pow2 sz) (@word2Fin n sz).
  Proof. constructor; intros.
         unfold word2Fin, fin2Word.
         match goal with
           |- @Fin2Restrict.n2f ?a ?b ?c = _ =>
             (*forget c: TODO: make tactic*)
             remember c as X eqn:HH; clear HH
         end.
         revert X; rewrite wordToNat_natToWord_idempotent.
         - intros.
           apply Fin2Restrict.f2n_inj.
           rewrite Fin2Restrict.f2n_n2f.
           rewrite min_l; auto.
           pose proof (Fin2Restrict.f2n_ok a). lia.
         - eapply Nomega.Nlt_in.
           rewrite Npow2_nat,Nnat.Nat2N.id.
           assumption.
  Qed.
    
  Instance CInv_finToWord' (n sz:nat):
    ConditionallyInvertible (@fin2Word (S n) sz) (fun a => (S n) < pow2 sz) (@word2Fin n sz).
  Proof. constructor; intros.
         unfold word2Fin, fin2Word.
         match goal with
           |- @Fin2Restrict.n2f ?a ?b ?c = _ =>
             (*forget c: TODO: make tactic*)
             remember c as X eqn:HH; clear HH
         end.
         revert X; rewrite wordToNat_natToWord_idempotent.
         - intros.
           apply Fin2Restrict.f2n_inj.
           rewrite Fin2Restrict.f2n_n2f.
           rewrite min_l; auto.
           pose proof (Fin2Restrict.f2n_ok a). lia.
         - eapply Nomega.Nlt_in.
           rewrite Npow2_nat,Nnat.Nat2N.id.
           etransitivity. eapply Fin2Restrict.f2n_ok.
           assumption.
  Qed.

  
  Record sensor_msg :=
    { stationID: Fin.t 16; data: word 16 }.
  
  Let format :=
        format_word ◦ (fin2Word 8 ∘ stationID) ++ format_word ◦ data.

  Let invariant (msg:sensor_msg):= Fin2Restrict.f2n (stationID msg) < pow2 8.
  
  
  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  (* In this case the bownd comes from the size of the `Fin.t`. The
  invariant is trivial (and could be removed in an extra step). *)
  Let enc_dec'' : EncoderDecoderPair format (fun _ => 16 < pow2 8).
  Proof. derive_encoder_decoder_pair. Defined.

End FinT.

Module Split.
  Import Revert.
  Opaque wreverse.
  
  (* `split1`, `split2` don't seem to have inverses. They don't even
  map the entire input! But with a the help of the predicated P we
  can encode the other part of the input and make it "invertible". *)
  
  Instance CInv_split1 (sz1 sz2: nat) w1:
    ConditionallyInvertible (split2 sz1 sz2) (fun w => split1 sz1 sz2 w = w1) (@Word.combine sz1 w1 sz2).
  Proof.
    constructor; intros.
    rewrite <- H.
    apply Word.combine_split.
  Qed.


Let format_int16 : FormatM (word 16) ByteString :=
     format_word ◦ wreverse (sz:=8) ◦ split1 8 8
  ++ format_word ◦ wreverse (sz:=8) ◦ split2 8 8.

Let enc_dec_automatic:
  EncoderDecoderPair format_int16 (constant True).
  Proof. derive_encoder_decoder_pair. Defined.



(*Then we can combine multiple applications of split *)
  Let format_int24 : FormatM (word 24) ByteString :=
     format_word ◦ wreverse (sz:=8) ◦ split1 8 16
  ++ format_word ◦ wreverse (sz:=8) ◦ split1 8 8 ◦ split2 8 16
  ++ format_word ◦ wreverse (sz:=8) ◦ split2 8 8 ◦ split2 8 16.

  Let enc_dec_automatic24: EncoderDecoderPair format_int24 (constant True).
  Proof. derive_encoder_decoder_pair. Defined.

  
Let format_int32 : FormatM (word 32) ByteString :=
     format_word ◦ wreverse (sz:=8) ◦ split1 8 8 ◦ split1 16 16
  ++ format_word ◦ wreverse (sz:=8) ◦ split2 8 8 ◦ split1 16 16
  ++ format_word ◦ wreverse (sz:=8) ◦ split1 8 8 ◦ split2 16 16
  ++ format_word ◦ wreverse (sz:=8) ◦ split2 8 8 ◦ split2 16 16.

Let enc_dec_automatic32:
  EncoderDecoderPair format_int32 (constant True).
  Proof. derive_encoder_decoder_pair. Defined.
  
End Split.
