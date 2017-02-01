Require Import Fiat.Common
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement.Core
        Coq.Sets.Ensembles.

Generalizable All Variables.
Set Implicit Arguments.

Section sMethodRefinement.

  (** Old and new representations **)
  Variables oldRep newRep : Type.

  (* Type of state (heaps in the case of ByteString ADT). *)
  Variable ST : Type.

  (** Abstraction Relation *)
  Variable AbsR : oldRep -> newRep -> ST -> Prop.

  Definition sMethodType
             (arity : nat)
             (rep : Type)
             (dom : list Type)
             (cod : option Type)
    := methodType arity rep (ST :: dom)
                   match cod with
                   | Some T => Some (prod ST T)
                   | None => Some ST
                   end.

  Fixpoint sRefineMethod''
           {dom : list Type}
           {cod : option Type}
    : methodType' oldRep dom cod
      -> methodType'
           newRep dom
           match cod with
           | Some T => Some (prod ST T)
           | None => Some ST
           end
      -> Prop :=
    match dom return
          methodType' oldRep dom cod
          -> methodType'
               newRep dom
               match cod with
               | Some T => Some (prod ST T)
               | None => Some ST
               end
          -> Prop
    with
    | nil =>
      match cod return
            methodType' oldRep [] cod
            -> methodType'
                 newRep []
                 match cod with
                 | Some T => Some (prod ST T)
                 | None => Some ST
                 end
            -> Prop
      with
      | Some cod' =>
        fun oldMethod newMethod =>
            refine (r_o' <- oldMethod;
                  `(r_n', s') <- {r_n_s | AbsR (fst r_o') (fst r_n_s) (snd r_n_s)};
                  ret (r_n', (s', snd r_o')))
                   newMethod
      | _ =>
        fun oldMethod newMethod =>
            refine (r_o' <- oldMethod;
                      {r_n_s | AbsR r_o' (fst r_n_s) (snd r_n_s)})
                   newMethod
      end
    | cons D dom' =>
      fun oldMethod newMethod =>
        forall d : D,
          @sRefineMethod'' dom' cod (oldMethod d)
                         (newMethod d)
    end.

  Fixpoint sRefineMethod'
           (arity : nat)
           (s : ST)
           {dom : list Type}
           {cod : option Type}
           (oldMethod : methodType arity oldRep dom cod)
           (newMethod : sMethodType arity newRep dom cod)
    : Prop
    :=
      match arity return methodType arity oldRep dom cod
                         -> sMethodType arity newRep dom cod
                         -> Prop with
      | 0 => fun oldMethod newMethod =>
               @sRefineMethod'' dom cod oldMethod (newMethod s)
      | S arity' =>
        fun oldMethod newMethod =>
          forall r_o r_n,
            AbsR r_o r_n s ->
            sRefineMethod' arity' s (oldMethod r_o) (newMethod r_n)
      end oldMethod newMethod.

  Definition sRefineMethod
             {arity : nat}
             {dom : list Type}
             {cod : option Type}
             (oldMethod : methodType arity oldRep dom cod)
             (newMethod : sMethodType arity newRep dom cod)
    : Prop := forall s : ST, sRefineMethod' arity s oldMethod newMethod.

End sMethodRefinement.

Definition sSig (ST : Type) (Sig : ADTSig) : ADTSig :=
  {| MethodIndex := MethodIndex Sig;
     MethodDomCod idx :=
       (fst (fst (MethodDomCod Sig idx)),
        cons ST (snd (fst (MethodDomCod Sig idx))),
        match (snd (MethodDomCod Sig idx)) with
          | Some T => Some (prod ST T)
          | None => Some ST
          end) |}.

Definition sADT (ST : Type) (Sig : ADTSig) :=
  ADT (sSig ST Sig).

Record refine_sADT {Sig}
       (ST : Type)
       (A : ADT Sig)
       (B : sADT ST Sig) :=
  refines_sADT {
      sAbsR : _;
      sADTRefinementPreservesMethods
      : forall idx : MethodIndex Sig,
          @sRefineMethod
            (Rep A) (Rep B) ST sAbsR
            (fst (fst (MethodDomCod Sig idx)))
            (snd (fst (MethodDomCod Sig idx)))
            (snd (MethodDomCod Sig idx))
            (Methods A idx)
            (Methods B idx) }.
