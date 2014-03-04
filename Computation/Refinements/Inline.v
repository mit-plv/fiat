Require Import Common.
Require Import Computation.Core Computation.Monad Computation.SetoidMorphisms.

Section inline.
  Context `{LookupContext}.

  Lemma refineEquiv_call (name : names) A (P : (dom name -> Comp (cod name)) -> Comp A)
        `{pr : Proper _
                      ((pointwise_relation _ (@refine _ _ _)) ==> (@refine _ _ _))%signature
                      P}
  : refineEquiv (P (Call name))
                (P (lookup name)).
  Proof.
    split;
    apply pr;
    repeat first [ intro
                 | assumption
                 | inversion_by computes_to_inv
                 | econstructor ].
  Qed.

  Fixpoint inline_once (should_inline : names -> bool) {A} (c : Comp A)
  : { c' : Comp A | refineEquiv c c' }.
  Proof.
    refine match c as c in (Comp A) return { c' : Comp A | refineEquiv c c' } with
             | Call f v => existT _ (if should_inline f then lookup f v else Call f v) _
             | Bind _ _ v f => let v' := @inline_once should_inline _ v in
                               let f' := (fun v => @inline_once should_inline _ (f v)) in
                               existT _ (Bind (projT1 v') (fun v => projT1 (f' v))) _
             | c' => existT (refineEquiv c') c' (reflexivity _)
           end.
    - clearbodies; clear inline_once; abstract (apply refineEquiv_bind; try intro; apply projT2).
    - clearbodies; clear inline_once.
      abstract (destruct (should_inline f);
                repeat first [ reflexivity
                             | apply refineEquiv_call with (P := fun f => f _)
                             | progress apply_hyp
                             | intro ]).
  Defined.

  Fixpoint inline_n should_inline {A} (c : Comp A) (n : nat)
  : { c' : Comp A | refineEquiv c c' }
    := match n with
         | 0 => existT (refineEquiv c) c (reflexivity _)
         | S n' => let c'p := inline_once should_inline c in
                   let c''p := inline_n should_inline (projT1 c'p) n' in
                   existT _ (projT1 c''p) (transitivity (projT2 c'p) (projT2 c''p))
       end.
End inline.
