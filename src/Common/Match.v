Set Implicit Arguments.

Definition pull_match_sumbool_dep {L R A B} (P : forall b : sumbool L R, A b -> B b)
           (a : forall x, A (left x))
           (a' : forall x, A (right x))
           b
: P b (match b return A b with
         | left x => a x
         | right x => a' x
       end)
  = match b return B b with
      | left x => P _ (a x)
      | right x => P _ (a' x)
    end.
Proof. destruct b; reflexivity. Defined.

Definition pull_match_sumbool {L R : Prop} {A B} (P : A -> B) (a : L -> A) (a' : R -> A) (b : sumbool L R)
: P (match b with
       | left x => a x
       | right x => a' x
     end)
  = match b with
      | left x => P (a x)
      | right x => P (a' x)
    end
  := pull_match_sumbool_dep (fun _ => P) a a' b.

Definition pull_match_bool_dep {A B} (P : forall b : bool, A b -> B b) (a : A true) (a' : A false)
           (b : bool)
: P b (if b as b return A b then a else a') =
  if b as b return B b then P _ a else P _ a'
  := match b with true => eq_refl | false => eq_refl end.

Definition pull_match_bool {A B} (P : A -> B) (a a' : A) (b : bool)
: P (if b then a else a') = if b then P a else P a'
  := pull_match_bool_dep (fun _ => P) a a' b.

Definition pull_bool_rect_dep {A B} (P : forall b : bool, A b -> B b) (a : A true) (a' : A false)
           (b : bool)
: P b (bool_rect A a a' b) = bool_rect B (P _ a) (P _ a') b
  := match b with true => eq_refl | false => eq_refl end.

Definition pull_bool_rect {A B} (P : A -> B) (a a' : A) (b : bool)
: P (bool_rect (fun _ => A) a a' b) = bool_rect (fun _ => B) (P a) (P a') b
  := pull_bool_rect_dep (fun _ => P) a a' b.

Definition pull_option_rect_dep {T A B} (P : forall x : option T, A x -> B x) (a : forall x, A (Some x)) (a' : A None)
           (x : option T)
: P x (option_rect A a a' x) = option_rect B (fun x => P _ (a x)) (P _ a') x
  := match x with Some _ => eq_refl | None => eq_refl end.

Definition pull_option_rect {T A B} (P : A -> B) (a : T -> A) (a' : A) (x : option T)
: P (option_rect (fun _ => A) a a' x) = option_rect (fun _ => B) (fun x => P (a x)) (P a') x
  := pull_option_rect_dep (fun _ => P) a a' x.
