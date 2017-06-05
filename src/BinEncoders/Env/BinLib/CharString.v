Require Import
        Bedrock.Word
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Lib2.CInt
        compcert.lib.Integers.

Import Byte.

Record ByteString :=
  { padding : nat;
    front : word padding;
    paddingOK : (padding < 8)%nat;
    numBytes : nat;
    byteString : Vector.t byte numBytes (* The bytestring. *)
  }.

Definition length_ByteString (bs : ByteString) := numBytes bs.

Definition wordToByte (w : word 8) : byte :=
  repr (BinInt.Z.of_N (wordToN w)).

Definition byteToWord (i : byte) : word 8 :=
  match intval i with
  | 0%Z => wzero 8
  | Zpos p => posToWord 8 p
  | _ => wzero 8
  end.

Definition ByteString_enqueue
         (b : bool)
         (bs : ByteString)
  : ByteString.
  refine (if (eq_nat_dec (padding bs) 7) then
            {| front := WO;
               byteString := Vector.append (byteString bs)
                                           (Vector.cons _ (wordToByte (WS b _)) _ (@Vector.nil _)) |}
  else
    {| front := WS b (front bs);
       padding := S (padding bs);
       byteString := byteString bs |}).
  abstract omega.
  abstract (pose proof (front bs) as w; generalize dependent (padding bs);
            intros ?? w; subst; exact w).
  abstract (pose proof (paddingOK bs); omega).
Defined.

Fixpoint word_dequeue {sz}
           (w : word (S sz))
  : bool * word sz :=
  match sz return word (S sz) -> bool * word sz with
  | 0 => fun w => (whd w, WO)
  | S sz' =>
    fun w => let (b, w') := word_dequeue (wtl w) in
             (b, WS (whd w) w')
  end w.

Fixpoint CharList_dequeue
         {numBytes}
         (l : Vector.t byte (S numBytes))
  : bool * (Vector.t byte numBytes) * word 7 :=
  let (b, w') := word_dequeue (byteToWord (Vector.hd l)) in
  match numBytes return
        Vector.t byte (S numBytes) -> _ with
  | S numBytes' =>
    fun l =>
      match CharList_dequeue (Vector.tl l) with
      | (b', l'', tail) =>
        (b, Vector.cons _ (wordToByte (WS b' w')) _ l'', tail)
      end
  | 0 => fun _ => (b, Vector.nil _, w')
  end l.

Definition ByteString_dequeue
         (bs : ByteString)
  : option (bool * ByteString).
  refine (match padding bs as n return
                word n
                -> (n < 8)%nat
                -> _ with
          | 0 =>
            match numBytes bs as nb return
                  Vector.t byte nb
                  -> _ with
            | S n' =>
              fun l _ _ =>
                match CharList_dequeue l with
                | (b', l'', tail) =>
                  Some (b', {| front := tail;
                               byteString := l'' |})
                end
            | _ => fun _ _ _ => None
            end (byteString bs)
          | S n =>
            fun front' lt_n =>
              match numBytes bs as nb return
                    Vector.t byte nb
                    -> _ with
              | S n' =>
                fun l =>
                  match CharList_dequeue l with
                  | (b', l'', tail) =>
                    let (b, w') := word_dequeue front' in
                    Some (b', {| front := w';
                                 byteString := Vector.append l''
                                                             (Vector.cons _ (wordToByte (WS b tail)) _ (@Vector.nil _))
                              |})
                  end
              | _ => fun _ =>
                       let (b, w') := word_dequeue front' in
                       Some (b, {| front := w';
                                   byteString := Vector.nil _ |})
              end (byteString bs)
          end (front bs) (paddingOK bs)).
  abstract omega.
  abstract omega.
  abstract omega.
Defined.

Fixpoint ByteString_enqueue_word
           {n}
           (w : word n)
           (bs : ByteString) :=
  match n return word n -> ByteString with
  | 0 => fun _ => bs
  | S n' => fun w =>
              (ByteString_enqueue (whd w) (ByteString_enqueue_word (wtl w) bs))
  end w.

Definition ByteString_enqueue_char (bs : ByteString) (b : byte)
  := ByteString_enqueue_word (byteToWord b) bs.

Definition ByteString_enqueue_ByteString
           (bs bs' : ByteString)
  : ByteString :=
  let bs'' := Vector.fold_left ByteString_enqueue_char bs (byteString bs') in
  ByteString_enqueue_word (front bs') bs''.

Definition ByteString_id : ByteString.
  refine {| front := WO; byteString := Vector.nil _ |}.
  abstract omega.
Defined.

Definition ByteStringQueueTransformer : Transformer ByteString.
Proof.
  refine {| transform := ByteString_enqueue_ByteString;
            bin_measure := length_ByteString;
            transform_id := ByteString_id |}.
  admit.
  admit.
  admit.
  admit.
Defined.

Instance ByteString_QueueTransformerOpt
  : QueueTransformerOpt ByteStringQueueTransformer bool.
Proof.
refine {| B_measure f := 1;
          enqueue_opt := ByteString_enqueue;
          dequeue_opt := ByteString_dequeue |}.
Proof.
  - abstract eauto.
  - simpl. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Defined.
