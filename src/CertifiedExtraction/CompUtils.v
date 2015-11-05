Require Import
        Computation.Core.
Require Export
        CertifiedExtraction.HintDBs
        CertifiedExtraction.Core.
Require Import
        Bedrock.Memory
        Bedrock.Platform.Facade.DFacade.

(* Definition WrapComp_W {av} (cmp: Comp W) := *)
(*   fun (a: Value av) => match a with *)
(*                     | SCA a => cmp ↝ a *)
(*                     | _ => False *)
(*                     end. *)

(* Definition WrapCons_W {av} key (cmp: W -> Comp W) tail : (. *)
  
(*   fun (a: Value av) => match a with *)
(*                     | SCA a => Cons key (cmp a) tail *)
(*                     | _ => Nil *)
(*                     end. *)

(* Definition WrapComp_Generic `{FacadeWrapper (Value av) A} (cmp: Comp A) := *)
(*   fun (a: Value av) => match (unwrap a) with *)
(*                     | Some a => cmp ↝ a *)
(*                     | None => False *)
(*                     end. *)

(* Definition WrapCons_Generic `{FacadeWrapper (Value av) A} key (cmp: A -> Comp (Value av)) tail := *)
(*   fun (a: Value av) => match (unwrap a) with *)
(*                     | Some a => Cons key (cmp a) tail *)
(*                     | _ => Nil *)
(*                     end. *)

(* Definition WrappedCons {av A} Wrapper (key: option string) (cmp: A -> Comp (Value av)) (tail: Value av -> Telescope av) *)
(*   : Value av -> Telescope av := *)
(*   Wrapper key cmp tail. *)

Definition AlwaysComputesToSCA {av} (v: Comp (Value av)) :=
  forall vv, v ↝ vv -> is_adt vv = false.
