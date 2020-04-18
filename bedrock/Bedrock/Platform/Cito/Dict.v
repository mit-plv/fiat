Require Import Bedrock.Platform.Sets.

Set Implicit Arguments.

Module Type KEY.
  Parameter key : Type.
  Parameter eq_dec : forall x y : key, {x = y} + {x <> y}.
End KEY.

Module Type DATA.
  Parameter data : Type.
End DATA.

Module Dict (MKey : KEY) (MData : DATA).

  Import MKey MData.

  Module SetKey : S with Definition A := key.
    Definition A := key.
    Definition eq_dec := eq_dec.
  End SetKey.
  Module MSet := Make SetKey.

  Definition map := key -> data.

  Definition dict := (MSet.set * map)%type.

  Definition upd_map (m : map) k v k' :=
    if eq_dec k' k then v else m k'.

  Definition keys (d : dict) := fst d.

  Definition mem (d : dict) (k : key) := fst d k.

  Definition sel (d : dict) (k : key) := snd d k.

  Definition upd (d : dict) k v := (MSet.add (fst d) k, upd_map (snd d) k v).

  Definition remove (d : dict) (k : key) := (MSet.del (fst d) k, snd d).

  Lemma sel_upd_eq : forall m k v k', k' = k ->  sel (upd m k v) k' = v.
    intros; unfold sel, upd, upd_map; simpl; destruct (eq_dec k' k); intuition.
  Qed.

  Lemma sel_upd_ne : forall m k v k', k' <> k -> sel (upd m k v) k' = sel m k'.
    intros; unfold sel, upd, upd_map; simpl; destruct (eq_dec k' k); intuition.
  Qed.

End Dict.
