Require Import Bedrock.Bedrock.


Import DefineStructured.

Section Lambda.
  Variable imports : LabelMap.t assert.
  Hypothesis imports_global : importsGlobal imports.
  Variable modName : string.

  Variable body : cmd imports modName.
  Variable precondition : assert.

  Hint Extern 1 (_ < _)%N => nomega.
  Hint Extern 1 (not (@eq LabelMap.key _ _)) => lomega.
  Hint Extern 1 (@eq LabelMap.key _ _ -> False) => lomega.
  Hint Extern 1 (LabelMap.MapsTo _ _ _) => apply imps_exit.

  Transparent evalInstrs.

  Definition Lambda__ : cmd imports modName.
    red; refine (fun pre =>
      let cout := body precondition in
      {|
        Postcondition := (fun st => Ex st', Ex fp,
          [| evalInstrs (fst st) st' (Assign Rp (RvImm fp) :: nil) = Some (snd st) |]
          /\ pre (fst st, st')
          /\ Cptr fp precondition)%PropX;
      VerifCond := (forall specs st, ~interp specs (cout.(Postcondition) st))
        :: cout.(VerifCond);
      Generate := fun Base Exit =>
        let cg := Generate cout (Nsucc (Nsucc Base)) Base in
        {|
          Entry := 1;
          Blocks := (cout.(Postcondition),
            (nil, Uncond (RvLabel (modName, Local Base))))
          :: (pre, (Assign Rp (RvLabel (modName,
            Local (Nsucc (Nsucc Base) + cg.(Entry)))) :: nil,
            Uncond (RvLabel (modName, Local Exit))))
          :: cg.(Blocks)
        |}
      |}); abstract (struct;
        repeat match goal with
                 | [ H : forall k v, _
                     |- context[match Labels _ ?k with None => _
                                  | _ => _ end] ] =>
                   edestruct (H k); eauto; intuition;
                     match goal with
                       | [ H : _ = _ |- _ ] => rewrite H
                     end
               end; repeat esplit; eauto; propxFo; eauto).
  Defined.

End Lambda.

Definition Lambda_ (vars : list string) (pre : spec) (Body : chunk) : chunk := fun ns res =>
  Structured nil (fun im mn H =>
    Lambda__ im H mn
    (toCmd ($[Sp+0] <- Rp;;
      (fun _ _ =>
        Structured nil (fun im mn _ => Structured.Assert_ im mn
          (Precondition pre (Some vars))));;
      (fun ns res => Body ns (res - (List.length vars - List.length (Formals pre)))%nat))%SP mn H vars (Reserved pre))
    (Precondition pre None)).

Notation "rv <-- 'Lambda' () [ p ] b 'end'" :=
  (Seq (Lambda_ nil p b) (Assign' rv Rp))
  (no associativity, at level 95) : SP_scope.

Notation "rv <-- 'Lambda' ( x1 , .. , xN ) [ p ] b 'end'" :=
  (Seq (Lambda_ (cons x1 (.. (cons xN nil) ..)) p b) (Assign' rv Rp))
  (no associativity, at level 95) : SP_scope.
