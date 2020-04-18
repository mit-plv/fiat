Require Import Bedrock.Examples.AutoSep.


Inductive request :=
| Echo (_ : W)
| Add (_ _ : W).

Definition encode (req : request) : list W :=
  match req with
    | Echo w => $0 :: w :: nil
    | Add w1 w2 => $1 :: w1 :: w2 :: nil
  end.

Definition reply (req : request) : W :=
  match req with
    | Echo w => w
    | Add w1 w2 => w1 ^+ w2
  end.

Definition mainS := SPEC("req", "len") reserving 3
  Al req,
  PRE[V] [| V "len" = length (encode req) |] * array (encode req) (V "req")
  POST[R] [| R = reply req |] * array (encode req) (V "req").

Definition m := bmodule "m" {{
  bfunction "main"("req", "len", "pos", "x", "y") [mainS]
    "pos" <- 0;;
    Match "req" Size "len" Position "pos" {
      Case (0 ++ "x")
        Return "x"
      end;;
      Case (1 ++ "x" ++ "y")
        Return "x" + "y"
      end
    } Default {
      Fail
    }
  end
}}.

Ltac encode_case :=
  match goal with
    | [ H : context[match encode ?E with nil => _ | _ => _ end] |- _ ] =>
      destruct E; simpl in *; intuition (try discriminate)
  end.

Theorem mOk : moduleOk m.
  vcgen; abstract (parse0; post; evaluate auto_ext;
    repeat (parse1 auto; try encode_case; reveal_slots; evaluate auto_ext); sep_auto; parse2).
Qed.
