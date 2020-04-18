Require Import Bedrock.Word.

Definition B := word 8.
Definition W := word 32.

Section mem_ops.
  Variable addr mem : Type.
  Variable footprint_w : addr -> addr * addr * addr * addr.

  Variable mem_get : mem -> addr -> option B.

  Definition mem_get_word (implode : B * B * B * B -> W) (p : addr) (m : mem)
    : option W :=
    let '(a,b,c,d) := footprint_w p in
    match mem_get m a , mem_get m b , mem_get m c , mem_get m d with
      | Some a , Some b , Some c , Some d =>
        Some (implode (a,b,c,d))
      | _ , _ , _ , _ => None
    end.

  Variable mem_set : mem -> addr -> B -> option mem.

  Definition mem_set_word (explode : W -> B * B * B * B) (p : addr) (v : W)
    (m : mem) : option mem :=
    let '(a,b,c,d) := footprint_w p in
    let '(av,bv,cv,dv) := explode v in
    match mem_set m d dv with
      | Some m => match mem_set m c cv with
                    | Some m => match mem_set m b bv with
                                  | Some m => mem_set m a av
                                  | None => None
                                end
                    | None => None
                  end
      | None => None
    end.

End mem_ops.
