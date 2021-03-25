Require Import
        Coq.ZArith.ZArith
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs.

Section LaxTerminalFormat.

  Context {S : Type}. (* Source type *)
  Context {T : Type}. (* Target type *)
  Context {cache : Cache}. (* State type *)
  Context {monoid : Monoid T}. (* Target type is a monoid *)

  Definition LaxTerminal_Format
    : FormatM (S * T) T :=
    fun st env => ret (snd st, env).

  Definition LaxTerminal_Decode
             (s : S)
    : DecodeM (S * T) T :=
    fun t env => Some (s, t, env).

  Definition LaxTerminal_Encode
    : EncodeM (S * T) T :=
    fun st env => Some (snd st, env).

  Lemma CorrectEncoder_LaxTerminal
    : CorrectEncoder LaxTerminal_Format LaxTerminal_Encode.
  Proof.
    unfold CorrectEncoder, LaxTerminal_Format, LaxTerminal_Encode;
      split; intros.
    -  injections;
         repeat computes_to_econstructor; eauto using measure_mempty.
    - discriminate.
  Qed.

End LaxTerminalFormat.

Notation "'?*'" := (LaxTerminal_Format) (at level 99) : format_scope.
