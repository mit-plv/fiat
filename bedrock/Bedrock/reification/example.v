(* Declare ML Module "plugin". *)

(*
Declare ML Module "extlib".
Declare ML Module "reif".

Section PartialApply.

  Fixpoint funtype (ls : list Type) (r : Type) : Type :=
    match ls with
      | nil => r
      | cons a b => a -> funtype b r
    end.

  Fixpoint apply_ls (ls : list Type) (T : Type) (R : T -> Type) (V : T)
    : funtype ls (forall x : T, R x) -> funtype ls (R V) :=
    match ls with
      | nil => fun F => F V
      | cons a b => fun F => fun x : a => apply_ls b T R V (F x)
    end.
End PartialApply.

Require Import List.

Ltac refl_app cc e :=
  match e with
    | (fun _ => _) =>
      let rec getTypes As :=
        match As with
          | tt => constr:(@nil Type)
          | (?A, ?B) =>
            match type of A with
              | _ -> ?TT =>
                let r := getTypes B in
                constr:((TT : Type) :: r)
            end
        end
      in
      let rec papply cc F T Tb Ts As :=
        match T with
          | ?T1 -> ?TT =>
            match Ts with
              | ?T :: ?T' =>
                match As with
                  | (?A, ?A') =>
                    let cc' f Ts As :=
                      let Ts' := constr:((T : Type) :: Ts) in
                      let As' := constr:((A, As)) in
                      cc f Ts' As'
                    in
                    let Tb := constr:((T:Type) :: Tb) in
                    papply cc' F TT Tb T' A'
                end
            end
          | forall x : ?T1, @?T2 x =>
            match Ts with
              | _ :: ?T' =>
                match As with
                  | ((fun _ => ?A), ?A') =>
                    let TT' := eval simpl in (T2 A) in
                    let f' := eval simpl in (@apply_ls Tb T1 T2 A F) in
                    papply cc f' TT' Tb T' A'
                end
            end
          | _ =>
            cc F Ts As
        end
      in
      match e with
        | fun x => ?F (@?A x) (@?B x) (@?C x) (@?D x) (@?E x) =>
          let As := constr:((A,(B,(C,(D,(E,tt)))))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) (@?B x) (@?C x) (@?D x) =>
          let As := constr:((A,(B,(C,(D,tt))))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) (@?B x) (@?C x) =>
          let As := constr:((A,(B,(C,tt)))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) (@?B x) =>
          let As := constr:((A,(B,tt))) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F (@?A x) =>
          let As := constr:((A,tt)) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
        | fun x => ?F =>
          let As := constr:(tt) in
          let Ts := getTypes As in
          let Tf := type of F in
          let Tb := constr:(@nil Type) in
          papply cc F Tf Tb Ts As
      end
    | _ =>
      let rec refl cc e As :=
        match e with
          | ?A ?B =>
            let Ta := type of A in
            match Ta with
              | _ -> ?TT =>
                let As := constr:((B, As)) in
                let Tb := type of B in
                let cc f Ts args :=
                  let Ts' := constr:(List.app Ts (cons (Tb : Type) nil)) in
                  cc f Ts' args
                in
                refl cc A As
              | forall x : ?T1, @?T2 x =>
                let cc f Ts args :=
                  let Tb  := type of B in
                  let f'  := eval simpl in (@apply_ls Ts T1 T2 B f) in
                  cc f' Ts args
                in
                refl cc A As
              end
          | _ =>
            let Ts := constr:(@nil Type) in
            cc e Ts As
        end
        in
        let b := constr:(tt) in
        refl cc e b
  end.


Ltac cc1 x ts args :=
  idtac "$$$ plugin" x ts args.
Ltac cc2 x ts args :=
  idtac "$$$ ltac" x ts args.

Definition tutu (x : Type) ( y : x ) (s : Type) (z : nat) (z2 : nat) (u : x) := 1.
Goal tutu bool true nat 3 3  false = 2.
  match goal with
      |- ?l = _ =>  refl_app_cps l cc1
  end.
  match goal with
      |- ?l = _ =>  refl_app cc2 l
  end.
Abort.

Definition bar : forall ( x: Type), nat -> forall (y : Type), x -> y -> x := fun _ _ _ e _ => e.

Definition bar2 : forall ( x: Type), nat -> forall (y : Type), nat -> forall (z : Type),  x -> y -> z -> z. Admitted.

Goal forall a b c d e, bar a b c d e = d.
intros.
  match goal with
      |- ?l = _ => refl_app_cps l cc1
  end.
  match goal with
      |- ?l = _ =>  refl_app cc2 l
  end.
Abort.

Goal forall Hx Hy Hz a b c d e, bar2 Hx a Hy b Hz c d e = e.
intros.
match goal with
    |- ?l = _ => refl_app_cps l cc1
end.
match goal with
    |- ?l = _ =>  refl_app cc2 l
end.

Abort.


Goal (fun x => x + x) = (fun x => 2).
match goal with
    |- ?l = _ => refl_app_cps l cc1
end.
match goal with
    |- ?l = _ =>  refl_app cc2 l
end.
Abort.

Variable A B : Type.
Definition test1 (stn : A) (sm : B) : B. Admitted.
Goal  forall a b, test1 a b = b. intros.
match goal with |- ?l = _  => refl_app_cps l cc1 end.
match goal with |- ?l = _  => refl_app cc2 l end.
Abort.

Definition test2 : A * B -> B. Admitted.
Goal  (fun x y => test2 (x, y)) = (fun _ b => b). intros.
match goal with |- ?l = _  => refl_app cc2 l end.
match goal with |- ?l = _  => refl_app_cps l cc1 end.
Abort.
Require Import String.
Require Bedrock. Require ReifyExpr.
Definition test_dep_0 (n : nat) (arg : bool) := True.
Definition test_dep (n : nat) (arg : bool) := n = 0 -> arg = arg.
Goal True.
reify_expr (test_dep_0 1 true).
reify_expr (test_dep 1 true).
Abort.
(* Require Bedrock. Require ReifyExpr.  *)
(* Goal True.  *)
(* reify_expr (forall (x : bool), x = x).  *)
(* reify_expr (1). *)
(* reify_expr (fun (x : nat )=> x).  *)
(* reify_expr (1 + 3).  *)
(* reify_expr (1 + 3 = 2 + 2).  *)
(* reify_expr (not (1 + 3 = 2 + 2)).  *)
(* reify_expr (not (1 + 3 = 2 + 2)).  *)
(* reify_expr ((1 + 3 = 2 + 2) -> False).  *)
(* (* Time reify_expr ((1 + 1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 +1 + 3 = 2 + 2) -> False).  *) *)
(* reify_expr (fun n => n + n = n + n).  *)
(* reify_expr (fun x => negb (negb x) = x). *)
(* Abort.  *)
(* Require Import Bedrock.SepIL. Import SEP.  *)
(* Locate SEP.Emp.  *)
(* Axiom types : list Type.  *)
(* Axiom pc : Type.  *)
(* Notation "a * b" := (@star pc pc types  a b) (only parsing).  *)
(* Notation "0" := (@emp pc pc types ) (only parsing).  *)
(* Notation "'Ex' x , p" := (@ex pc pc types _ (fun x => p)). *)
(* Notation "'Ex' x : T , p" := (@ex pc pc types T (fun x => p)) . *)
(* Notation "[| P |]" := (@inj pc pc types (@PropX.Inj pc pc types  P )).  *)
(* Require Import IL.  *)
(* Variable st : state.  *)
(* Goal True.  *)
(* reify_expr (Regs st Rp). *)
(* reify_sexpr (0 ).  *)
(* reify_sexpr (0 * 0 * 0).  *)
(* reify_sexpr ( [| 1 + 1 = 2 |] * 0 * [| 12 = 6 + 6 |] ). *)
(* reify_sexpr ( [| 1 + 1 = 2 |] * 0 * [| 12 = 6 + 6 |] ).  *)
(* reify_sexpr ( Ex x, [| x = 1|]).  *)
(* reify_sexpr ( Ex x, Ex y, Ex z, [| x = y + z|]).  *)
(* reify_sexpr ( Ex x, [| x = 1|]).  *)
(* reify_sexpr ( Ex x : bool, Ex y, Ex z, [| (if x then 1 else 2) = y + z|]).  *)
(* reify_sexpr ( Ex x: bool, [| (if x then true else false) = x|]).  *)
(* reify_sexpr ( Ex x:bool, Ex y : bool, [| (if x then y else false) = andb x y|]).  *)
(* reify_sexpr ( Ex x:bool, Ex y : nat, [| (if x then y else y) = y|]).  *)
(* Fail reify_sexpr (Ex x : (bool -> bool), [| x true = false |]).  *)
(* evar (x : nat); let s := eval simpl in (Ex y : nat, [|x = y|] * [| S x = S y|]) in reify_sexpr s ; clear x.   *)
(* Abort.  *)

(* Goal forall P,    *)
(*        P( Ex x : bool, [|negb (negb x) = false |]). *)
(* intros.   *)
(* assert (forall x, false = (x && negb x)%bool). admit.  *)
(* Require Import Setoid. erewrite H.  *)
(* match goal with  *)
(*     |- P ?l =>  *)
(*       reify_sexpr l *)
(* end.  *)
(* Abort.  *)

(* Goal True.  *)
(* Ltac t f := *)
(* match f with  *)
(*   | (fun x => @?B x) => idtac 1 B;  *)
(*       refl_app ltac:(fun x y z => idtac x y z) B *)
(*   | (fun x => _) => idtac 2 *)
(* end.  *)

(* t ((fun x => (if (x : bool) then true else false))).  *)
(* Abort.  *)
*)
