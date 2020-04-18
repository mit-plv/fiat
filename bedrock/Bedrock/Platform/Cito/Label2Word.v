Set Implicit Arguments.

Require Import Bedrock.Memory Bedrock.Word.
Require Import Bedrock.Platform.Cito.GLabel Bedrock.Platform.Cito.ConvertLabel.

Section stn.

  Variable Domain : glabel -> Prop.

  Variable l2w : glabel -> option W.

  Definition stn_injective :=
    forall lbl1 lbl2 p,
      Domain lbl1 ->
      Domain lbl2 ->
      l2w lbl1 = Some p ->
      l2w lbl2 = Some p ->
      lbl1 = lbl2.

  Definition is_label_map_to_word lbl p :=
    match l2w lbl with
      | Some p' =>
        if weq p p' then
          true
        else
          false
      | None => false
    end.

  Definition is_label_map_to_word' A p (x : glabel * A) := is_label_map_to_word (fst x) p.

  Definition find_by_word A m (p : W) : option A :=
    match List.find (is_label_map_to_word' p) m with
      | Some (_, a) => Some a
      | None => None
    end.

End stn.
