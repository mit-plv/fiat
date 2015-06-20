Lemma option_map_None A B (f : A -> B) x
: option_map f x = None <-> x = None.
Proof.
  destruct x; simpl; split; intros; trivial; congruence.
Qed.

Lemma option_rect_option_map {A B P} (f : A -> B) (x : option A) a b
: option_rect P a b (option_map f x) = option_rect (fun k => P (option_map f k)) (fun k => a (f k)) b x.
Proof.
  destruct x; simpl; reflexivity.
Qed.
