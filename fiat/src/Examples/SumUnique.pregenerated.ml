let failwith _ = Obj.magic 0

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f0 = function
| Some a -> Some (f0 a)
| None -> None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (x, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| y::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m6 =
  match l with
  | [] -> m6
  | a::l1 -> a::(app l1 m6)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, p) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (x0, h) -> h

type 'a sumor =
| Inleft of 'a
| Inright

type 'a exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val plus : nat -> nat -> nat **)

let rec plus n0 m6 =
  match n0 with
  | O -> m6
  | S p -> S (plus p m6)

(** val mult : nat -> nat -> nat **)

let rec mult n0 m6 =
  match n0 with
  | O -> O
  | S p -> plus m6 (mult p m6)

(** val minus : nat -> nat -> nat **)

let rec minus n0 m6 =
  match n0 with
  | O -> n0
  | S k ->
    (match m6 with
     | O -> n0
     | S l -> minus k l)

(** val max : nat -> nat -> nat **)

let rec max n0 m6 =
  match n0 with
  | O -> m6
  | S n' ->
    (match m6 with
     | O -> n0
     | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n0 m6 =
  match n0 with
  | O -> O
  | S n' ->
    (match m6 with
     | O -> O
     | S m' -> S (min n' m'))

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f0 x =
  match n0 with
  | O -> x
  | S n' -> f0 (nat_iter n' f0 x)

(** val eq_nat_dec : nat -> nat -> bool **)

let rec eq_nat_dec n0 m6 =
  match n0 with
  | O ->
    (match m6 with
     | O -> true
     | S m7 -> false)
  | S n1 ->
    (match m6 with
     | O -> false
     | S m7 -> eq_nat_dec n1 m7)

(** val zerop : nat -> bool **)

let zerop = function
| O -> true
| S n1 -> false

(** val lt_eq_lt_dec : nat -> nat -> bool sumor **)

let rec lt_eq_lt_dec n0 m6 =
  match n0 with
  | O ->
    (match m6 with
     | O -> Inleft false
     | S m7 -> Inleft true)
  | S n1 ->
    (match m6 with
     | O -> Inright
     | S m7 -> lt_eq_lt_dec n1 m7)

(** val nat_compare : nat -> nat -> comparison **)

let rec nat_compare n0 m6 =
  match n0 with
  | O ->
    (match m6 with
     | O -> Eq
     | S n1 -> Lt)
  | S n' ->
    (match m6 with
     | O -> Gt
     | S m' -> nat_compare n' m')

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n0 m6 =
  match n0 with
  | O ->
    (match m6 with
     | O -> true
     | S n1 -> false)
  | S n1 ->
    (match m6 with
     | O -> false
     | S m7 -> beq_nat n1 m7)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module type DecidableTypeOrig = 
 sig 
  type t 
  
  val eq_dec : t -> t -> bool
 end

module type MiniDecidableType = 
 sig 
  type t 
  
  val eq_dec : t -> t -> bool
 end

module Make_UDT = 
 functor (M:MiniDecidableType) ->
 struct 
  type t = M.t
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    M.eq_dec
 end

module type EqLtLe = 
 sig 
  type t 
 end

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> bool
 end

module type OrderedType' = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> bool
 end

module OT_to_Full = 
 functor (O:OrderedType') ->
 struct 
  type t = O.t
  
  (** val compare : t -> t -> comparison **)
  
  let compare =
    O.compare
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    O.eq_dec
 end

module MakeOrderTac = 
 functor (O:EqLtLe) ->
 functor (P:sig 
  
 end) ->
 struct 
  
 end

module OT_to_OrderTac = 
 functor (OT:OrderedType) ->
 struct 
  module OTF = OT_to_Full(OT)
  
  module TO = 
   struct 
    type t = OTF.t
    
    (** val compare : t -> t -> comparison **)
    
    let compare =
      OTF.compare
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts = 
 functor (O:OrderedType') ->
 struct 
  module OrderTac = OT_to_OrderTac(O)
  
  (** val eq_dec : O.t -> O.t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val lt_dec : O.t -> O.t -> bool **)
  
  let lt_dec x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> true
     | _ -> false)
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x y =
    if eq_dec x y then true else false
 end

module Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f0 f1 f2 = function
  | IsNul -> f0
  | IsPos x -> f1 x
  | IsNeg -> f2
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f0 f1 f2 = function
  | IsNul -> f0
  | IsPos x -> f1 x
  | IsNeg -> f2
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f0 x =
    match n0 with
    | XI n' -> f0 (iter n' f0 (iter n' f0 x))
    | XO n' -> iter n' f0 (iter n' f0 x)
    | XH -> f0 x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)
  
  let sqrtrem_step f0 g = function
  | Pair (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f0 r) in
       if leb s' r'
       then Pair ((XI s), (sub_mask r' s'))
       else Pair ((XO s), (IsPos r'))
     | _ -> Pair ((XO s), (sub_mask (g (f0 XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> (positive, mask) prod **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos XH)))
  | XH -> Pair (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b0 =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b0 with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b0)
          | XO b1 -> gcdn n1 a b1
          | XH -> XH)
       | XO a0 ->
         (match b0 with
          | XI p -> gcdn n1 a0 b0
          | XO b1 -> XO (gcdn n1 a0 b1)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b0 =
    gcdn (plus (size_nat a) (size_nat b0)) a b0
  
  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)
  
  let rec ggcdn n0 a b0 =
    match n0 with
    | O -> Pair (XH, (Pair (a, b0)))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b0 with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n1 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n1 (sub a' b') b0 in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b1 ->
            let Pair (g, p) = ggcdn n1 a b1 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b0 with
          | XI p ->
            let Pair (g, p0) = ggcdn n1 a0 b0 in
            let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
          | XO b1 -> let Pair (g, p) = ggcdn n1 a0 b1 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b0))))
  
  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)
  
  let ggcd a b0 =
    ggcdn (plus (size_nat a) (size_nat b0)) a b0
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> positive **)
  
  let rec of_nat = function
  | O -> XH
  | S x ->
    (match x with
     | O -> XH
     | S n1 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> positive **)
  
  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f0 f1 f2 = function
  | IsNul -> f0
  | IsPos x -> f1 x
  | IsNeg -> f2
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f0 f1 f2 = function
  | IsNul -> f0
  | IsPos x -> f1 x
  | IsNeg -> f2
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f0 x =
    match n0 with
    | XI n' -> f0 (iter n' f0 (iter n' f0 x))
    | XO n' -> iter n' f0 (iter n' f0 x)
    | XH -> f0 x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH
  
  (** val compare_cont : positive -> positive -> comparison -> comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q Gt
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q Lt
       | XO q -> compare_cont p q r
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)
  
  (** val compare : positive -> positive -> comparison **)
  
  let compare x y =
    compare_cont x y Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> eqb p0 q0
       | _ -> false)
    | XO p0 ->
      (match q with
       | XO q0 -> eqb p0 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive, mask)
      prod -> (positive, mask) prod **)
  
  let sqrtrem_step f0 g = function
  | Pair (s, y) ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f0 r) in
       if leb s' r'
       then Pair ((XI s), (sub_mask r' s'))
       else Pair ((XO s), (IsPos r'))
     | _ -> Pair ((XO s), (sub_mask (g (f0 XH)) (XO (XO XH)))))
  
  (** val sqrtrem : positive -> (positive, mask) prod **)
  
  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos (XO XH))))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> Pair (XH, (IsPos XH)))
  | XH -> Pair (XH, IsNul)
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b0 =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b0 with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b0)
          | XO b1 -> gcdn n1 a b1
          | XH -> XH)
       | XO a0 ->
         (match b0 with
          | XI p -> gcdn n1 a0 b0
          | XO b1 -> XO (gcdn n1 a0 b1)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b0 =
    gcdn (plus (size_nat a) (size_nat b0)) a b0
  
  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)
  
  let rec ggcdn n0 a b0 =
    match n0 with
    | O -> Pair (XH, (Pair (a, b0)))
    | S n1 ->
      (match a with
       | XI a' ->
         (match b0 with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n1 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n1 (sub a' b') b0 in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b1 ->
            let Pair (g, p) = ggcdn n1 a b1 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b0 with
          | XI p ->
            let Pair (g, p0) = ggcdn n1 a0 b0 in
            let Pair (aa, bb) = p0 in Pair (g, (Pair ((XO aa), bb)))
          | XO b1 -> let Pair (g, p) = ggcdn n1 a0 b1 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b0))))
  
  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)
  
  let ggcd a b0 =
    ggcdn (plus (size_nat a) (size_nat b0)) a b0
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p0 n')
    | XO p0 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p0 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p0 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p0 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p0 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> positive **)
  
  let rec of_nat = function
  | O -> XH
  | S x ->
    (match x with
     | O -> XH
     | S n1 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> positive **)
  
  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
  
  (** val eq_dec : positive -> positive -> bool **)
  
  let rec eq_dec p y0 =
    match p with
    | XI p0 ->
      (match y0 with
       | XI p1 -> eq_dec p0 p1
       | _ -> false)
    | XO p0 ->
      (match y0 with
       | XO p1 -> eq_dec p0 p1
       | _ -> false)
    | XH ->
      (match y0 with
       | XH -> true
       | _ -> false)
  
  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let rec peano_rect a f0 p =
    let f2 =
      peano_rect (f0 XH a) (fun p0 x -> f0 (succ (XO p0)) (f0 (XO p0) x))
    in
    (match p with
     | XI q -> f0 (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)
  
  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rect f0 f1 p = function
  | PeanoOne -> f0
  | PeanoSucc (p1, p2) -> f1 p1 p2 (coq_PeanoView_rect f0 f1 p1 p2)
  
  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rec f0 f1 p = function
  | PeanoOne -> f0
  | PeanoSucc (p1, p2) -> f1 p1 p2 (coq_PeanoView_rec f0 f1 p1 p2)
  
  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0), (peanoView_xO p0 q0))))
  
  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0), (peanoView_xI p0 q0))))
  
  (** val peanoView : positive -> coq_PeanoView **)
  
  let rec peanoView = function
  | XI p0 -> peanoView_xI p0 (peanoView p0)
  | XO p0 -> peanoView_xO p0 (peanoView p0)
  | XH -> PeanoOne
  
  (** val coq_PeanoView_iter :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_iter a f0 p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f0 p0 (coq_PeanoView_iter a f0 p0 q0)
  
  (** val eqb_spec : positive -> positive -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq : comparison -> comparison -> comparison **)
  
  let switch_Eq c = function
  | Eq -> c
  | x -> x
  
  (** val mask2cmp : mask -> comparison **)
  
  let mask2cmp = function
  | IsNul -> Eq
  | IsPos p0 -> Gt
  | IsNeg -> Lt
  
  (** val leb_spec0 : positive -> positive -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : positive -> positive -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n0 m6 compat hl hr =
      let c = compSpec2Type n0 m6 (compare n0 m6) in
      (match c with
       | CompGtT -> compat n0 (max n0 m6) __ (hl __)
       | _ -> compat m6 (max n0 m6) __ (hr __))
    
    (** val max_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m6 x x0 x1 =
      max_case_strong n0 m6 x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : positive -> positive -> bool **)
    
    let max_dec n0 m6 =
      max_case n0 m6 (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n0 m6 compat hl hr =
      let c = compSpec2Type n0 m6 (compare n0 m6) in
      (match c with
       | CompGtT -> compat m6 (min n0 m6) __ (hr __)
       | _ -> compat n0 (min n0 m6) __ (hl __))
    
    (** val min_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1) ->
        'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m6 x x0 x1 =
      min_case_strong n0 m6 x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : positive -> positive -> bool **)
    
    let min_dec n0 m6 =
      min_case n0 m6 (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m6 x x0 =
    Private_Dec.max_case_strong n0 m6 (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m6 x x0 =
    max_case_strong n0 m6 (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : positive -> positive -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m6 x x0 =
    Private_Dec.min_case_strong n0 m6 (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m6 x x0 =
    min_case_strong n0 m6 (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : positive -> positive -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t = n
  
  (** val zero : n **)
  
  let zero =
    N0
  
  (** val one : n **)
  
  let one =
    Npos XH
  
  (** val two : n **)
  
  let two =
    Npos (XO XH)
  
  (** val succ_double : n -> n **)
  
  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val double : n -> n **)
  
  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val succ : n -> n **)
  
  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)
  
  (** val pred : n -> n **)
  
  let pred = function
  | N0 -> N0
  | Npos p -> Coq_Pos.pred_N p
  
  (** val succ_pos : n -> positive **)
  
  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p
  
  (** val add : n -> n -> n **)
  
  let add n0 m6 =
    match n0 with
    | N0 -> m6
    | Npos p ->
      (match m6 with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))
  
  (** val sub : n -> n -> n **)
  
  let sub n0 m6 =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m6 with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))
  
  (** val mul : n -> n -> n **)
  
  let mul n0 m6 =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m6 with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))
  
  (** val compare : n -> n -> comparison **)
  
  let compare n0 m6 =
    match n0 with
    | N0 ->
      (match m6 with
       | N0 -> Eq
       | Npos m' -> Lt)
    | Npos n' ->
      (match m6 with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')
  
  (** val eqb : n -> n -> bool **)
  
  let rec eqb n0 m6 =
    match n0 with
    | N0 ->
      (match m6 with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m6 with
       | N0 -> false
       | Npos q -> Coq_Pos.eqb p q)
  
  (** val leb : n -> n -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : n -> n -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val min : n -> n -> n **)
  
  let min n0 n' =
    match compare n0 n' with
    | Gt -> n'
    | _ -> n0
  
  (** val max : n -> n -> n **)
  
  let max n0 n' =
    match compare n0 n' with
    | Gt -> n0
    | _ -> n'
  
  (** val div2 : n -> n **)
  
  let div2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos p
     | XO p -> Npos p
     | XH -> N0)
  
  (** val even : n -> bool **)
  
  let even = function
  | N0 -> true
  | Npos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : n -> bool **)
  
  let odd n0 =
    negb (even n0)
  
  (** val pow : n -> n -> n **)
  
  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 ->
    (match n0 with
     | N0 -> N0
     | Npos q -> Npos (Coq_Pos.pow q p0))
  
  (** val square : n -> n **)
  
  let square = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.square p)
  
  (** val log2 : n -> n **)
  
  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)
  
  (** val size : n -> n **)
  
  let size = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.size p)
  
  (** val size_nat : n -> nat **)
  
  let size_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.size_nat p
  
  (** val pos_div_eucl : positive -> n -> (n, n) prod **)
  
  let rec pos_div_eucl a b0 =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b0 in
      let r' = succ_double r in
      if leb b0 r'
      then Pair ((succ_double q), (sub r' b0))
      else Pair ((double q), r')
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b0 in
      let r' = double r in
      if leb b0 r'
      then Pair ((succ_double q), (sub r' b0))
      else Pair ((double q), r')
    | XH ->
      (match b0 with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))
  
  (** val div_eucl : n -> n -> (n, n) prod **)
  
  let div_eucl a b0 =
    match a with
    | N0 -> Pair (N0, N0)
    | Npos na ->
      (match b0 with
       | N0 -> Pair (N0, a)
       | Npos p -> pos_div_eucl na b0)
  
  (** val div : n -> n -> n **)
  
  let div a b0 =
    fst (div_eucl a b0)
  
  (** val modulo : n -> n -> n **)
  
  let modulo a b0 =
    snd (div_eucl a b0)
  
  (** val gcd : n -> n -> n **)
  
  let gcd a b0 =
    match a with
    | N0 -> b0
    | Npos p ->
      (match b0 with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))
  
  (** val ggcd : n -> n -> (n, (n, n) prod) prod **)
  
  let ggcd a b0 =
    match a with
    | N0 -> Pair (b0, (Pair (N0, (Npos XH))))
    | Npos p ->
      (match b0 with
       | N0 -> Pair (a, (Pair ((Npos XH), N0)))
       | Npos q ->
         let Pair (g, p0) = Coq_Pos.ggcd p q in
         let Pair (aa, bb) = p0 in
         Pair ((Npos g), (Pair ((Npos aa), (Npos bb)))))
  
  (** val sqrtrem : n -> (n, n) prod **)
  
  let sqrtrem = function
  | N0 -> Pair (N0, N0)
  | Npos p ->
    let Pair (s, m6) = Coq_Pos.sqrtrem p in
    (match m6 with
     | Coq_Pos.IsPos r -> Pair ((Npos s), (Npos r))
     | _ -> Pair ((Npos s), N0))
  
  (** val sqrt : n -> n **)
  
  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.sqrt p)
  
  (** val coq_lor : n -> n -> n **)
  
  let coq_lor n0 m6 =
    match n0 with
    | N0 -> m6
    | Npos p ->
      (match m6 with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))
  
  (** val coq_land : n -> n -> n **)
  
  let coq_land n0 m6 =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m6 with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)
  
  (** val ldiff : n -> n -> n **)
  
  let rec ldiff n0 m6 =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m6 with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)
  
  (** val coq_lxor : n -> n -> n **)
  
  let coq_lxor n0 m6 =
    match n0 with
    | N0 -> m6
    | Npos p ->
      (match m6 with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)
  
  (** val shiftl_nat : n -> nat -> n **)
  
  let shiftl_nat a n0 =
    nat_iter n0 double a
  
  (** val shiftr_nat : n -> nat -> n **)
  
  let shiftr_nat a n0 =
    nat_iter n0 div2 a
  
  (** val shiftl : n -> n -> n **)
  
  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)
  
  (** val shiftr : n -> n -> n **)
  
  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter p div2 a
  
  (** val testbit_nat : n -> nat -> bool **)
  
  let testbit_nat = function
  | N0 -> (fun x -> false)
  | Npos p -> Coq_Pos.testbit_nat p
  
  (** val testbit : n -> n -> bool **)
  
  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
  
  (** val to_nat : n -> nat **)
  
  let to_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.to_nat p
  
  (** val of_nat : nat -> n **)
  
  let of_nat = function
  | O -> N0
  | S n' -> Npos (Coq_Pos.of_succ_nat n')
  
  (** val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f0 x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f0 x
  
  (** val eq_dec : n -> n -> bool **)
  
  let eq_dec n0 m6 =
    match n0 with
    | N0 ->
      (match m6 with
       | N0 -> true
       | Npos p -> false)
    | Npos x ->
      (match m6 with
       | N0 -> false
       | Npos p0 -> Coq_Pos.eq_dec x p0)
  
  (** val discr : n -> positive sumor **)
  
  let discr = function
  | N0 -> Inright
  | Npos p -> Inleft p
  
  (** val binary_rect :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n0 =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p ->
       let rec f1 = function
       | XI p1 -> fS2' p1 (f1 p1)
       | XO p1 -> f2' p1 (f1 p1)
       | XH -> fS2 N0 f0
       in f1 p)
  
  (** val binary_rec :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rect f0 f1 n0 =
    let f' = fun p -> f1 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f1 N0 f0) f' p)
  
  (** val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : n -> n -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : n -> n -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : n -> n **)
  
  let sqrt_up a =
    match compare N0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> N0
  
  (** val log2_up : n -> n **)
  
  let log2_up a =
    match compare (Npos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> N0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : n -> n -> n **)
  
  let lcm a b0 =
    mul a (div b0 (gcd a b0))
  
  (** val eqb_spec : n -> n -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> n **)
  
  let b2n = function
  | true -> Npos XH
  | false -> N0
  
  (** val setbit : n -> n -> n **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Npos XH) n0)
  
  (** val clearbit : n -> n -> n **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Npos XH) n0)
  
  (** val ones : n -> n **)
  
  let ones n0 =
    pred (shiftl (Npos XH) n0)
  
  (** val lnot : n -> n -> n **)
  
  let lnot a n0 =
    coq_lxor a (ones n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m6 compat hl hr =
      let c = compSpec2Type n0 m6 (compare n0 m6) in
      (match c with
       | CompGtT -> compat n0 (max n0 m6) __ (hl __)
       | _ -> compat m6 (max n0 m6) __ (hr __))
    
    (** val max_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m6 x x0 x1 =
      max_case_strong n0 m6 x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : n -> n -> bool **)
    
    let max_dec n0 m6 =
      max_case n0 m6 (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m6 compat hl hr =
      let c = compSpec2Type n0 m6 (compare n0 m6) in
      (match c with
       | CompGtT -> compat m6 (min n0 m6) __ (hr __)
       | _ -> compat n0 (min n0 m6) __ (hl __))
    
    (** val min_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m6 x x0 x1 =
      min_case_strong n0 m6 x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : n -> n -> bool **)
    
    let min_dec n0 m6 =
      min_case n0 m6 (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m6 x x0 =
    Private_Dec.max_case_strong n0 m6 (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m6 x x0 =
    max_case_strong n0 m6 (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : n -> n -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m6 x x0 =
    Private_Dec.min_case_strong n0 m6 (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m6 x x0 =
    min_case_strong n0 m6 (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : n -> n -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val div0 : nat -> nat **)

let rec div0 = function
| O -> O
| S n1 ->
  (match n1 with
   | O -> O
   | S n' -> S (div0 n'))

(** val leb0 : nat -> nat -> bool **)

let rec leb0 n0 m6 =
  match n0 with
  | O -> true
  | S n' ->
    (match m6 with
     | O -> false
     | S m' -> leb0 n' m')

(** val ltb0 : nat -> nat -> bool **)

let ltb0 n0 m6 =
  leb0 (S n0) m6

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default1 = function
| [] -> default1
| x::l0 -> x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| a::m6 -> m6

(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y::l0 -> let s = h y a in if s then true else in_dec h a l0

(** val nth_error : 'a1 list -> nat -> 'a1 exc **)

let rec nth_error l = function
| O ->
  (match l with
   | [] -> error
   | x::l0 -> value x)
| S n1 ->
  (match l with
   | [] -> error
   | a::l0 -> nth_error l0 n1)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | [] -> l'
  | a::l0 -> rev_append l0 (a::l')

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| [] -> []
| a::t0 -> (f0 a)::(map f0 t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f0 l a0 =
  match l with
  | [] -> a0
  | b0::t0 -> fold_left f0 t0 (f0 a0 b0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f0 a0 = function
| [] -> a0
| b0::t0 -> f0 b0 (fold_right f0 a0 t0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f0 = function
| [] -> true
| a::l0 -> if f0 a then forallb f0 l0 else false

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f0 = function
| [] -> []
| x::l0 -> if f0 x then x::(filter f0 l0) else filter f0 l0

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f0 = function
| [] -> None
| x::tl0 -> if f0 x then Some x else find f0 tl0

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  match n0 with
  | O -> []
  | S n1 ->
    (match l with
     | [] -> []
     | a::l0 -> a::(firstn n1 l0))

module Z = 
 struct 
  type t = z
  
  (** val zero : z **)
  
  let zero =
    Z0
  
  (** val one : z **)
  
  let one =
    Zpos XH
  
  (** val two : z **)
  
  let two =
    Zpos (XO XH)
  
  (** val double : z -> z **)
  
  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)
  
  (** val succ_double : z -> z **)
  
  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)
  
  (** val pred_double : z -> z **)
  
  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)
  
  (** val pos_sub : positive -> positive -> z **)
  
  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)
  
  (** val add : z -> z -> z **)
  
  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))
  
  (** val opp : z -> z **)
  
  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0
  
  (** val succ : z -> z **)
  
  let succ x =
    add x (Zpos XH)
  
  (** val pred : z -> z **)
  
  let pred x =
    add x (Zneg XH)
  
  (** val sub : z -> z -> z **)
  
  let sub m6 n0 =
    add m6 (opp n0)
  
  (** val mul : z -> z -> z **)
  
  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))
  
  (** val pow_pos : z -> positive -> z **)
  
  let pow_pos z0 n0 =
    Coq_Pos.iter n0 (mul z0) (Zpos XH)
  
  (** val pow : z -> z -> z **)
  
  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg p -> Z0
  
  (** val square : z -> z **)
  
  let square = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_Pos.square p)
  | Zneg p -> Zpos (Coq_Pos.square p)
  
  (** val compare : z -> z -> comparison **)
  
  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos y' -> Lt
       | Zneg y' -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)
  
  (** val sgn : z -> z **)
  
  let sgn = function
  | Z0 -> Z0
  | Zpos p -> Zpos XH
  | Zneg p -> Zneg XH
  
  (** val leb : z -> z -> bool **)
  
  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true
  
  (** val ltb : z -> z -> bool **)
  
  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false
  
  (** val geb : z -> z -> bool **)
  
  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true
  
  (** val gtb : z -> z -> bool **)
  
  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false
  
  (** val eqb : z -> z -> bool **)
  
  let rec eqb x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos p ->
      (match y with
       | Zpos q -> Coq_Pos.eqb p q
       | _ -> false)
    | Zneg p ->
      (match y with
       | Zneg q -> Coq_Pos.eqb p q
       | _ -> false)
  
  (** val max : z -> z -> z **)
  
  let max n0 m6 =
    match compare n0 m6 with
    | Lt -> m6
    | _ -> n0
  
  (** val min : z -> z -> z **)
  
  let min n0 m6 =
    match compare n0 m6 with
    | Gt -> m6
    | _ -> n0
  
  (** val abs : z -> z **)
  
  let abs = function
  | Zneg p -> Zpos p
  | x -> x
  
  (** val abs_nat : z -> nat **)
  
  let abs_nat = function
  | Z0 -> O
  | Zpos p -> Coq_Pos.to_nat p
  | Zneg p -> Coq_Pos.to_nat p
  
  (** val abs_N : z -> n **)
  
  let abs_N = function
  | Z0 -> N0
  | Zpos p -> Npos p
  | Zneg p -> Npos p
  
  (** val to_nat : z -> nat **)
  
  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O
  
  (** val to_N : z -> n **)
  
  let to_N = function
  | Zpos p -> Npos p
  | _ -> N0
  
  (** val of_nat : nat -> z **)
  
  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)
  
  (** val of_N : n -> z **)
  
  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p
  
  (** val to_pos : z -> positive **)
  
  let to_pos = function
  | Zpos p -> p
  | _ -> XH
  
  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f0 x =
    match n0 with
    | Zpos p -> Coq_Pos.iter p f0 x
    | _ -> x
  
  (** val pos_div_eucl : positive -> z -> (z, z) prod **)
  
  let rec pos_div_eucl a b0 =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b0 in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b0
      then Pair ((mul (Zpos (XO XH)) q), r')
      else Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b0))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b0 in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b0
      then Pair ((mul (Zpos (XO XH)) q), r')
      else Pair ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b0))
    | XH ->
      if leb (Zpos (XO XH)) b0
      then Pair (Z0, (Zpos XH))
      else Pair ((Zpos XH), Z0)
  
  (** val div_eucl : z -> z -> (z, z) prod **)
  
  let div_eucl a b0 =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a' ->
      (match b0 with
       | Z0 -> Pair (Z0, Z0)
       | Zpos p -> pos_div_eucl a' b0
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (add b0 r))))
    | Zneg a' ->
      (match b0 with
       | Z0 -> Pair (Z0, Z0)
       | Zpos p ->
         let Pair (q, r) = pos_div_eucl a' b0 in
         (match r with
          | Z0 -> Pair ((opp q), Z0)
          | _ -> Pair ((opp (add q (Zpos XH))), (sub b0 r)))
       | Zneg b' ->
         let Pair (q, r) = pos_div_eucl a' (Zpos b') in Pair (q, (opp r)))
  
  (** val div : z -> z -> z **)
  
  let div a b0 =
    let Pair (q, x) = div_eucl a b0 in q
  
  (** val modulo : z -> z -> z **)
  
  let modulo a b0 =
    let Pair (x, r) = div_eucl a b0 in r
  
  (** val quotrem : z -> z -> (z, z) prod **)
  
  let quotrem a b0 =
    match a with
    | Z0 -> Pair (Z0, Z0)
    | Zpos a0 ->
      (match b0 with
       | Z0 -> Pair (Z0, a)
       | Zpos b1 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b1) in
         Pair ((of_N q), (of_N r))
       | Zneg b1 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b1) in
         Pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b0 with
       | Z0 -> Pair (Z0, a)
       | Zpos b1 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b1) in
         Pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b1 ->
         let Pair (q, r) = N.pos_div_eucl a0 (Npos b1) in
         Pair ((of_N q), (opp (of_N r))))
  
  (** val quot : z -> z -> z **)
  
  let quot a b0 =
    fst (quotrem a b0)
  
  (** val rem : z -> z -> z **)
  
  let rem a b0 =
    snd (quotrem a b0)
  
  (** val even : z -> bool **)
  
  let even = function
  | Z0 -> true
  | Zpos p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  | Zneg p ->
    (match p with
     | XO p0 -> true
     | _ -> false)
  
  (** val odd : z -> bool **)
  
  let odd = function
  | Z0 -> false
  | Zpos p ->
    (match p with
     | XO p0 -> false
     | _ -> true)
  | Zneg p ->
    (match p with
     | XO p0 -> false
     | _ -> true)
  
  (** val div2 : z -> z **)
  
  let div2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)
  
  (** val quot2 : z -> z **)
  
  let quot2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p ->
    (match p with
     | XH -> Z0
     | _ -> Zneg (Coq_Pos.div2 p))
  
  (** val log2 : z -> z **)
  
  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0
  
  (** val sqrtrem : z -> (z, z) prod **)
  
  let sqrtrem = function
  | Zpos p ->
    let Pair (s, m6) = Coq_Pos.sqrtrem p in
    (match m6 with
     | Coq_Pos.IsPos r -> Pair ((Zpos s), (Zpos r))
     | _ -> Pair ((Zpos s), Z0))
  | _ -> Pair (Z0, Z0)
  
  (** val sqrt : z -> z **)
  
  let sqrt = function
  | Zpos p -> Zpos (Coq_Pos.sqrt p)
  | _ -> Z0
  
  (** val gcd : z -> z -> z **)
  
  let gcd a b0 =
    match a with
    | Z0 -> abs b0
    | Zpos a0 ->
      (match b0 with
       | Z0 -> abs a
       | Zpos b1 -> Zpos (Coq_Pos.gcd a0 b1)
       | Zneg b1 -> Zpos (Coq_Pos.gcd a0 b1))
    | Zneg a0 ->
      (match b0 with
       | Z0 -> abs a
       | Zpos b1 -> Zpos (Coq_Pos.gcd a0 b1)
       | Zneg b1 -> Zpos (Coq_Pos.gcd a0 b1))
  
  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)
  
  let ggcd a b0 =
    match a with
    | Z0 -> Pair ((abs b0), (Pair (Z0, (sgn b0))))
    | Zpos a0 ->
      (match b0 with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b1 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b1 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b1 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b1 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b0 with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b1 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b1 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b1 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b1 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))
  
  (** val testbit : z -> z -> bool **)
  
  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg p -> false
  
  (** val shiftl : z -> z -> z **)
  
  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter p (mul (Zpos (XO XH))) a
  | Zneg p -> Coq_Pos.iter p div2 a
  
  (** val shiftr : z -> z -> z **)
  
  let shiftr a n0 =
    shiftl a (opp n0)
  
  (** val coq_lor : z -> z -> z **)
  
  let coq_lor a b0 =
    match a with
    | Z0 -> b0
    | Zpos a0 ->
      (match b0 with
       | Z0 -> a
       | Zpos b1 -> Zpos (Coq_Pos.coq_lor a0 b1)
       | Zneg b1 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b1) (Npos a0))))
    | Zneg a0 ->
      (match b0 with
       | Z0 -> a
       | Zpos b1 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b1)))
       | Zneg b1 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b1))))
  
  (** val coq_land : z -> z -> z **)
  
  let coq_land a b0 =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b0 with
       | Z0 -> Z0
       | Zpos b1 -> of_N (Coq_Pos.coq_land a0 b1)
       | Zneg b1 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b1)))
    | Zneg a0 ->
      (match b0 with
       | Z0 -> Z0
       | Zpos b1 -> of_N (N.ldiff (Npos b1) (Coq_Pos.pred_N a0))
       | Zneg b1 ->
         Zneg
           (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b1))))
  
  (** val ldiff : z -> z -> z **)
  
  let ldiff a b0 =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b0 with
       | Z0 -> a
       | Zpos b1 -> of_N (Coq_Pos.ldiff a0 b1)
       | Zneg b1 -> of_N (N.coq_land (Npos a0) (Coq_Pos.pred_N b1)))
    | Zneg a0 ->
      (match b0 with
       | Z0 -> a
       | Zpos b1 ->
         Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Npos b1)))
       | Zneg b1 -> of_N (N.ldiff (Coq_Pos.pred_N b1) (Coq_Pos.pred_N a0)))
  
  (** val coq_lxor : z -> z -> z **)
  
  let coq_lxor a b0 =
    match a with
    | Z0 -> b0
    | Zpos a0 ->
      (match b0 with
       | Z0 -> a
       | Zpos b1 -> of_N (Coq_Pos.coq_lxor a0 b1)
       | Zneg b1 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b1))))
    | Zneg a0 ->
      (match b0 with
       | Z0 -> a
       | Zpos b1 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b1)))
       | Zneg b1 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b1)))
  
  (** val eq_dec : z -> z -> bool **)
  
  let eq_dec x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos x0 ->
      (match y with
       | Zpos p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
    | Zneg x0 ->
      (match y with
       | Zneg p0 -> Coq_Pos.eq_dec x0 p0
       | _ -> false)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : z -> z -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : z -> z -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module IsTotal = 
     struct 
      
     end
    
    module Tac = 
     struct 
      
     end
   end
  
  (** val sqrt_up : z -> z **)
  
  let sqrt_up a =
    match compare Z0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Z0
  
  (** val log2_up : z -> z **)
  
  let log2_up a =
    match compare (Zpos XH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> Z0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : z -> z -> z **)
      
      let div =
        quot
      
      (** val modulo : z -> z -> z **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : z -> z -> z **)
  
  let lcm a b0 =
    abs (mul a (div b0 (gcd a b0)))
  
  (** val eqb_spec : z -> z -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> z **)
  
  let b2z = function
  | true -> Zpos XH
  | false -> Z0
  
  (** val setbit : z -> z -> z **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Zpos XH) n0)
  
  (** val clearbit : z -> z -> z **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Zpos XH) n0)
  
  (** val lnot : z -> z **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : z -> z **)
  
  let ones n0 =
    pred (shiftl (Zpos XH) n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m6 compat hl hr =
      let c = compSpec2Type n0 m6 (compare n0 m6) in
      (match c with
       | CompGtT -> compat n0 (max n0 m6) __ (hl __)
       | _ -> compat m6 (max n0 m6) __ (hr __))
    
    (** val max_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m6 x x0 x1 =
      max_case_strong n0 m6 x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : z -> z -> bool **)
    
    let max_dec n0 m6 =
      max_case n0 m6 (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m6 compat hl hr =
      let c = compSpec2Type n0 m6 (compare n0 m6) in
      (match c with
       | CompGtT -> compat m6 (min n0 m6) __ (hr __)
       | _ -> compat n0 (min n0 m6) __ (hl __))
    
    (** val min_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m6 x x0 x1 =
      min_case_strong n0 m6 x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : z -> z -> bool **)
    
    let min_dec n0 m6 =
      min_case n0 m6 (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m6 x x0 =
    Private_Dec.max_case_strong n0 m6 (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m6 x x0 =
    max_case_strong n0 m6 (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : z -> z -> bool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m6 x x0 =
    Private_Dec.min_case_strong n0 m6 (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m6 x x0 =
    min_case_strong n0 m6 (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : z -> z -> bool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val z_gt_dec : z -> z -> bool **)

let z_gt_dec x y =
  match Z.compare x y with
  | Gt -> true
  | _ -> false

(** val z_ge_dec : z -> z -> bool **)

let z_ge_dec x y =
  match Z.compare x y with
  | Lt -> false
  | _ -> true

(** val z_gt_le_dec : z -> z -> bool **)

let z_gt_le_dec x y =
  z_gt_dec x y

(** val z_ge_lt_dec : z -> z -> bool **)

let z_ge_lt_dec x y =
  z_ge_dec x y

(** val zero0 : char **)

let zero0 = '\000'

(** val one0 : char **)

let one0 = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | O -> zero0
    | S n' ->
      (match p with
       | XI p' -> shift true (loop n' p')
       | XO p' -> shift false (loop n' p')
       | XH -> one0)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero0
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b0::l' ->
  N.add (if b0 then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[])))))))))
    a

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s s0 =
  match s with
  | [] ->
    (match s0 with
     | [] -> true
     | a::s1 -> false)
  | a::s1 ->
    (match s0 with
     | [] -> false
     | a0::s2 -> if (=) a a0 then string_dec s1 s2 else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val prefix : char list -> char list -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | [] -> true
  | a::s1' ->
    (match s2 with
     | [] -> false
     | b0::s2' -> if (=) a b0 then prefix s1' s2' else false)

type 'a eqDec = 'a -> 'a -> bool

(** val equiv_dec : 'a1 eqDec -> 'a1 -> 'a1 -> bool **)

let equiv_dec eqDec0 =
  eqDec0

type ('a, 'b) hlist =
| HNil
| HCons of 'a * 'a list * 'b * ('a, 'b) hlist

(** val hlist_hd : 'a1 -> 'a1 list -> ('a1, 'a2) hlist -> 'a2 **)

let hlist_hd t0 ls = function
| HNil -> Obj.magic Tt
| HCons (x0, ls0, x, h) -> x

(** val hlist_tl :
    'a1 -> 'a1 list -> ('a1, 'a2) hlist -> ('a1, 'a2) hlist **)

let hlist_tl t0 ls = function
| HNil -> Obj.magic Tt
| HCons (x0, ls0, b0, x) -> x

type word =
| WO
| WS of bool * nat * word

(** val wordToNat : nat -> word -> nat **)

let rec wordToNat sz = function
| WO -> O
| WS (b0, n0, w') ->
  if b0
  then S (mult (wordToNat n0 w') (S (S O)))
  else mult (wordToNat n0 w') (S (S O))

(** val mod2 : nat -> bool **)

let rec mod2 = function
| O -> false
| S n1 ->
  (match n1 with
   | O -> true
   | S n' -> mod2 n')

(** val natToWord : nat -> nat -> word **)

let rec natToWord sz n0 =
  match sz with
  | O -> WO
  | S sz' -> WS ((mod2 n0), sz', (natToWord sz' (div0 n0)))

(** val wordToN : nat -> word -> n **)

let rec wordToN sz = function
| WO -> N0
| WS (b0, n0, w') ->
  if b0
  then N.succ (N.mul (Npos (XO XH)) (wordToN n0 w'))
  else N.mul (Npos (XO XH)) (wordToN n0 w')

(** val wzero : nat -> word **)

let wzero sz =
  natToWord sz O

(** val wzero' : nat -> word **)

let rec wzero' = function
| O -> WO
| S sz' -> WS (false, sz', (wzero' sz'))

(** val posToWord : nat -> positive -> word **)

let rec posToWord sz p =
  match sz with
  | O -> WO
  | S sz' ->
    (match p with
     | XI p' -> WS (true, sz', (posToWord sz' p'))
     | XO p' -> WS (false, sz', (posToWord sz' p'))
     | XH -> WS (true, sz', (wzero' sz')))

(** val nToWord : nat -> n -> word **)

let nToWord sz = function
| N0 -> wzero' sz
| Npos p -> posToWord sz p

(** val npow2 : nat -> n **)

let rec npow2 = function
| O -> Npos XH
| S n' -> N.mul (Npos (XO XH)) (npow2 n')

(** val pow2 : nat -> nat **)

let rec pow2 = function
| O -> S O
| S n' -> mult (S (S O)) (pow2 n')

(** val whd : nat -> word -> bool **)

let whd sz = function
| WO -> Obj.magic Tt
| WS (b0, n0, w1) -> b0

(** val wtl : nat -> word -> word **)

let wtl sz = function
| WO -> Obj.magic Tt
| WS (b0, n0, w') -> w'

(** val weq : nat -> word -> word -> bool **)

let rec weq sz x y =
  match x with
  | WO -> true
  | WS (b0, n0, x') ->
    if bool_dec b0 (whd n0 y) then weq n0 x' (wtl n0 y) else false

(** val weqb : nat -> word -> word -> bool **)

let rec weqb sz x x0 =
  match x with
  | WO -> true
  | WS (b0, n0, x') ->
    if eqb b0 (whd n0 x0) then weqb n0 x' (wtl n0 x0) else false

(** val combine : nat -> word -> nat -> word -> word **)

let rec combine sz1 w0 sz2 w' =
  match w0 with
  | WO -> w'
  | WS (b0, n0, w'0) -> WS (b0, (plus n0 sz2), (combine n0 w'0 sz2 w'))

(** val split2 : nat -> nat -> word -> word **)

let rec split2 sz1 sz2 w0 =
  match sz1 with
  | O -> w0
  | S sz1' ->
    split2 sz1' sz2
      (wtl
        (let rec plus0 n0 m6 =
           match n0 with
           | O -> m6
           | S p -> S (plus0 p m6)
         in plus0 sz1' sz2) w0)

(** val wneg : nat -> word -> word **)

let wneg sz x =
  nToWord sz (N.sub (npow2 sz) (wordToN sz x))

(** val wordBin : (n -> n -> n) -> nat -> word -> word -> word **)

let wordBin f0 sz x y =
  nToWord sz (f0 (wordToN sz x) (wordToN sz y))

(** val wplus : nat -> word -> word -> word **)

let wplus =
  wordBin N.add

(** val wmult : nat -> word -> word -> word **)

let wmult =
  wordBin N.mul

(** val wminus : nat -> word -> word -> word **)

let wminus sz x y =
  wplus sz x (wneg sz y)

(** val wlt_dec : nat -> word -> word -> bool **)

let wlt_dec sz l r =
  match N.compare (wordToN sz l) (wordToN sz r) with
  | Lt -> true
  | _ -> false

type b = word

type w = word

module type Heap = 
 sig 
  type addr 
  
  type mem 
  
  val mem_get : mem -> addr -> b option
  
  val mem_set : mem -> addr -> b -> mem option
  
  val footprint_w : addr -> (((addr, addr) prod, addr) prod, addr) prod
  
  val addr_dec : addr -> addr -> bool
  
  val all_addr : addr list
 end

module HeapTheory = 
 functor (B:Heap) ->
 struct 
  type smem' = (B.addr, b option) hlist
  
  (** val smem_emp' : B.addr list -> smem' **)
  
  let rec smem_emp' = function
  | [] -> HNil
  | a::b0 -> HCons (a, b0, None, (smem_emp' b0))
  
  (** val join' : B.addr list -> smem' -> smem' -> smem' **)
  
  let rec join' dom x x0 =
    match dom with
    | [] -> HNil
    | a::b0 ->
      HCons (a, b0,
        (match hlist_hd a b0 x with
         | Some x1 -> Some x1
         | None -> hlist_hd a b0 x0),
        (join' b0 (hlist_tl a b0 x) (hlist_tl a b0 x0)))
  
  (** val relevant' : B.addr list -> smem' -> B.addr list **)
  
  let rec relevant' ls x =
    match ls with
    | [] -> []
    | a::b0 ->
      (match hlist_hd a b0 x with
       | Some b1 -> a::(relevant' b0 (hlist_tl a b0 x))
       | None -> relevant' b0 (hlist_tl a b0 x))
  
  (** val smem_get' : B.addr list -> B.addr -> smem' -> b option **)
  
  let rec smem_get' dom x x0 =
    match dom with
    | [] -> None
    | a::b0 ->
      if B.addr_dec a x
      then hlist_hd a b0 x0
      else smem_get' b0 x (hlist_tl a b0 x0)
  
  (** val smem_set' : B.addr list -> B.addr -> b -> smem' -> smem' option **)
  
  let rec smem_set' dom x x0 x1 =
    match dom with
    | [] -> None
    | a::b0 ->
      if B.addr_dec a x
      then (match hlist_hd a b0 x1 with
            | Some b1 -> Some (HCons (a, b0, (Some x0), (hlist_tl a b0 x1)))
            | None -> None)
      else (match smem_set' b0 x x0 (hlist_tl a b0 x1) with
            | Some tl0 -> Some (HCons (a, b0, (hlist_hd a b0 x1), tl0))
            | None -> None)
  
  type smem = smem'
  
  (** val smem_emp : smem **)
  
  let smem_emp =
    smem_emp' B.all_addr
  
  (** val smem_get : B.addr -> smem' -> b option **)
  
  let smem_get =
    smem_get' B.all_addr
  
  (** val smem_set : B.addr -> b -> smem' -> smem' option **)
  
  let smem_set =
    smem_set' B.all_addr
  
  (** val smem_get_word :
      ((((b, b) prod, b) prod, b) prod -> w) -> B.addr -> smem -> w option **)
  
  let smem_get_word implode0 p m6 =
    let Pair (p0, d) = B.footprint_w p in
    let Pair (p1, c) = p0 in
    let Pair (a, b0) = p1 in
    (match smem_get a m6 with
     | Some a0 ->
       (match smem_get b0 m6 with
        | Some b1 ->
          (match smem_get c m6 with
           | Some c0 ->
             (match smem_get d m6 with
              | Some d0 ->
                Some (implode0 (Pair ((Pair ((Pair (a0, b1)), c0)), d0)))
              | None -> None)
           | None -> None)
        | None -> None)
     | None -> None)
  
  (** val smem_set_word :
      (w -> (((b, b) prod, b) prod, b) prod) -> B.addr -> w -> smem -> smem
      option **)
  
  let smem_set_word explode0 p v m6 =
    let Pair (p0, d) = B.footprint_w p in
    let Pair (p1, c) = p0 in
    let Pair (a, b0) = p1 in
    let Pair (p2, dv) = explode0 v in
    let Pair (p3, cv) = p2 in
    let Pair (av, bv) = p3 in
    (match smem_set d dv m6 with
     | Some m7 ->
       (match smem_set c cv m7 with
        | Some m8 ->
          (match smem_set b0 bv m8 with
           | Some m9 -> smem_set a av m9
           | None -> None)
        | None -> None)
     | None -> None)
  
  (** val join : smem -> smem -> smem **)
  
  let join m6 m7 =
    join' B.all_addr m6 m7
  
  (** val relevant : smem -> B.addr list **)
  
  let relevant sm =
    relevant' B.all_addr sm
  
  (** val coq_EqDec_addr : B.addr eqDec **)
  
  let coq_EqDec_addr =
    B.addr_dec
  
  (** val cons_not_in : 'a1 -> 'a1 list -> 'a1 list -> 'a2 **)
  
  let cons_not_in =
    failwith "AXIOM TO BE REALIZED"
  
  (** val memoryIn' : B.mem -> B.addr list -> smem' **)
  
  let rec memoryIn' m6 = function
  | [] -> HNil
  | l::ls0 -> HCons (l, ls0, (B.mem_get m6 l), (memoryIn' m6 ls0))
  
  (** val memoryIn : B.mem -> smem **)
  
  let memoryIn m6 =
    memoryIn' m6 B.all_addr
 end

module Coq__1 = struct 
 type ('pc, 'state) propX =
 | Inj of __ list
 | Cptr of __ list * 'pc * ('state -> ('pc, 'state) propX)
 | And of __ list * ('pc, 'state) propX * ('pc, 'state) propX
 | Or of __ list * ('pc, 'state) propX * ('pc, 'state) propX
 | Imply of __ list * ('pc, 'state) propX * ('pc, 'state) propX
 | Forall of __ list * (__ -> ('pc, 'state) propX)
 | Exists of __ list * (__ -> ('pc, 'state) propX)
 | Var0 of __ list * __
 | Lift of __ list * ('pc, 'state) propX
 | ForallX of __ list * ('pc, 'state) propX
 | ExistsX of __ list * ('pc, 'state) propX
end
type ('pc, 'state) propX = ('pc, 'state) Coq__1.propX =
| Inj of __ list
| Cptr of __ list * 'pc * ('state -> ('pc, 'state) propX)
| And of __ list * ('pc, 'state) propX * ('pc, 'state) propX
| Or of __ list * ('pc, 'state) propX * ('pc, 'state) propX
| Imply of __ list * ('pc, 'state) propX * ('pc, 'state) propX
| Forall of __ list * (__ -> ('pc, 'state) propX)
| Exists of __ list * (__ -> ('pc, 'state) propX)
| Var0 of __ list * __
| Lift of __ list * ('pc, 'state) propX
| ForallX of __ list * ('pc, 'state) propX
| ExistsX of __ list * ('pc, 'state) propX

type ('pc, 'state) propX0 = ('pc, 'state) propX

type ('pc, 'state) spec = 'state -> ('pc, 'state) propX0

module type SepTheoryX = 
 sig 
  module H : 
   Heap
  
  type ('pcType, 'stateType) hprop 
  
  module HT : 
   sig 
    type smem' = (H.addr, b option) hlist
    
    val smem_emp' : H.addr list -> smem'
    
    val join' : H.addr list -> smem' -> smem' -> smem'
    
    val relevant' : H.addr list -> smem' -> H.addr list
    
    val smem_get' : H.addr list -> H.addr -> smem' -> b option
    
    val smem_set' : H.addr list -> H.addr -> b -> smem' -> smem' option
    
    type smem = smem'
    
    val smem_emp : smem
    
    val smem_get : H.addr -> smem' -> b option
    
    val smem_set : H.addr -> b -> smem' -> smem' option
    
    val smem_get_word :
      ((((b, b) prod, b) prod, b) prod -> w) -> H.addr -> smem -> w option
    
    val smem_set_word :
      (w -> (((b, b) prod, b) prod, b) prod) -> H.addr -> w -> smem -> smem
      option
    
    val join : smem -> smem -> smem
    
    val relevant : smem -> H.addr list
    
    val coq_EqDec_addr : H.addr eqDec
    
    val cons_not_in : 'a1 -> 'a1 list -> 'a1 list -> 'a2
    
    val memoryIn' : H.mem -> H.addr list -> smem'
    
    val memoryIn : H.mem -> smem
   end
  
  type settings 
  
  val inj : __ list -> ('a1, 'a2) propX -> ('a1, 'a2) hprop
  
  val emp : __ list -> ('a1, 'a2) hprop
  
  val star :
    __ list -> ('a1, 'a2) hprop -> ('a1, 'a2) hprop -> ('a1, 'a2) hprop
  
  val ex : __ list -> ('a3 -> ('a1, 'a2) hprop) -> ('a1, 'a2) hprop
  
  val hptsto : __ list -> H.addr -> b -> ('a1, 'a2) hprop
 end

module SepTheoryX_Rewrites = 
 functor (ST:SepTheoryX) ->
 struct 
  
 end

module SepTheoryX_Ext = 
 functor (ST:SepTheoryX) ->
 struct 
  module ST_RW = SepTheoryX_Rewrites(ST)
  
  type 'range functionTypeD = __
  
  (** val existsEach :
      __ list -> 'a3 list -> (('a3, 'a4) sigT list -> ('a1, 'a2) ST.hprop) ->
      ('a1, 'a2) ST.hprop **)
  
  let existsEach sos ts f0 =
    ST.ex sos (fun env0 -> ST.star sos (ST.inj sos (Inj sos)) (f0 env0))
 end

type label' =
| Global of char list
| Local of n

type label = (char list, label') prod

(** val natToW : nat -> w **)

let natToW n0 =
  natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) n0

type reg =
| Sp
| Rp
| Rv

type loc =
| Reg of reg
| Imm of w
| Indir of reg * w

type lvalue =
| LvReg of reg
| LvMem of loc
| LvMem8 of loc

type rvalue =
| RvLval of lvalue
| RvImm of w
| RvLabel of label

type binop =
| Plus
| Minus
| Times

type instr =
| Assign of lvalue * rvalue
| Binop of lvalue * rvalue * binop * rvalue

type test =
| Eq0
| Ne
| Lt0
| Le

type jmp =
| Uncond of rvalue
| Cond of rvalue * test * rvalue * label * label

type block = (instr list, jmp) prod

type mem0 = w -> b option

type settings0 = { implode : ((((b, b) prod, b) prod, b) prod -> w);
                   explode : (w -> (((b, b) prod, b) prod, b) prod);
                   labels : (label -> w option) }

(** val labels : settings0 -> label -> w option **)

let labels x = x.labels

(** val readByte : mem0 -> w -> b option **)

let readByte m6 a =
  m6 a

(** val writeByte : mem0 -> w -> b -> mem0 option **)

let writeByte m6 p v =
  match m6 p with
  | Some b0 ->
    Some (fun p' ->
      if weq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
           p' p
      then Some v
      else m6 p')
  | None -> None

type state = { regs : (reg -> w); mem1 : mem0 }

(** val regs : state -> reg -> w **)

let regs x = x.regs

(** val mem1 : state -> mem0 **)

let mem1 x = x.mem1

(** val wtoB : w -> b **)

let wtoB =
  split2 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))) (S (S (S (S (S (S (S (S O))))))))

(** val btoW : b -> w **)

let btoW =
  combine (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S O))))))))))))))))))))))))
    (wzero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S O))))))))))))))))))))))))) (S (S (S (S (S (S (S (S O))))))))

(** val evalBinop : binop -> w -> w -> w **)

let evalBinop = function
| Plus ->
  wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
| Minus ->
  wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
| Times ->
  wmult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))

(** val wltb : w -> w -> bool **)

let wltb w1 w2 =
  if wlt_dec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) w1
       w2
  then true
  else false

(** val weqb0 : w -> w -> bool **)

let weqb0 w1 w2 =
  weqb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) w1 w2

(** val wneb : w -> w -> bool **)

let wneb w1 w2 =
  if weq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) w1 w2
  then false
  else true

(** val wleb : w -> w -> bool **)

let wleb w1 w2 =
  if weq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) w1 w2
  then true
  else if wlt_dec (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) w1 w2
       then true
       else false

(** val evalTest : test -> w -> w -> bool **)

let evalTest = function
| Eq0 -> weqb0
| Ne -> wneb
| Lt0 -> wltb
| Le -> wleb

module Make = 
 functor (H':Heap) ->
 struct 
  module H = H'
  
  module HT = HeapTheory(H)
  
  type settings = settings0
  
  type ('pcType, 'stateType) hprop =
    settings -> HT.smem -> ('pcType, 'stateType) propX
  
  (** val inj : __ list -> ('a1, 'a2) propX -> ('a1, 'a2) hprop **)
  
  let inj sos p x m6 =
    And (sos, p, (Inj sos))
  
  (** val emp : __ list -> ('a1, 'a2) hprop **)
  
  let emp sos =
    inj sos (Inj sos)
  
  (** val star :
      __ list -> ('a1, 'a2) hprop -> ('a1, 'a2) hprop -> ('a1, 'a2) hprop **)
  
  let star sos l r s m6 =
    Exists (sos, (fun ml -> Exists (sos, (fun mr -> And (sos, (Inj sos), (And
      (sos, (Obj.magic l s ml), (Obj.magic r s mr))))))))
  
  (** val ex : __ list -> ('a3 -> ('a1, 'a2) hprop) -> ('a1, 'a2) hprop **)
  
  let ex sos p s h =
    Exists (sos, (fun t0 -> Obj.magic p t0 s h))
  
  (** val hptsto : __ list -> H.addr -> b -> ('a1, 'a2) hprop **)
  
  let hptsto sos p v s h =
    Inj sos
 end

(** val fold_left_2_opt :
    ('a1 -> 'a3 -> 'a2 -> 'a2 option) -> 'a1 list -> 'a3 list -> 'a2 -> 'a2
    option **)

let rec fold_left_2_opt f0 ls ls' acc =
  match ls with
  | [] ->
    (match ls' with
     | [] -> Some acc
     | v::l -> None)
  | x::xs ->
    (match ls' with
     | [] -> None
     | y::ys ->
       (match f0 x y acc with
        | Some acc0 -> fold_left_2_opt f0 xs ys acc0
        | None -> None))

(** val all2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec all2 f0 xs ys =
  match xs with
  | [] ->
    (match ys with
     | [] -> true
     | y::l -> false)
  | x::xs0 ->
    (match ys with
     | [] -> false
     | y::ys0 -> if f0 x y then all2 f0 xs0 ys0 else false)

(** val allb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec allb p = function
| [] -> true
| x::ls' -> if p x then allb p ls' else false

type type0 =
  __ -> __ -> bool
  (* singleton inductive, whose constructor was Typ *)

type impl = __

(** val eqb0 : type0 -> impl -> impl -> bool **)

let eqb0 t0 =
  t0

type tvar =
| TvProp
| TvType of nat

type tvarD = __

(** val emptySet_type : type0 **)

let emptySet_type x y =
  assert false (* absurd case *)

type 'range functionTypeD0 = __

type signature = { domain : tvar list; range : tvar;
                   denotation : tvarD functionTypeD0 }

(** val domain : type0 list -> signature -> tvar list **)

let domain _ x = x.domain

(** val range : type0 list -> signature -> tvar **)

let range _ x = x.range

(** val denotation : type0 list -> signature -> tvarD functionTypeD0 **)

let denotation _ x = x.denotation

(** val default_signature : type0 list -> signature **)

let default_signature types4 =
  { domain = []; range = TvProp; denotation = (Obj.magic __) }

type functions = signature list

type variables = tvar list

type func = nat

type var = nat

type uvar = nat

type expr =
| Const of tvar * tvarD
| Var of var
| Func of func * expr list
| Equal of tvar * expr * expr
| Not of expr
| UVar of uvar

type exprs = expr list

(** val eqDec_tvar : tvar eqDec **)

let eqDec_tvar x y =
  match x with
  | TvProp ->
    (match y with
     | TvProp -> true
     | TvType n0 -> false)
  | TvType x0 ->
    (match y with
     | TvProp -> false
     | TvType n0 -> eq_nat_dec x0 n0)

(** val tvar_seqb : tvar -> tvar -> bool **)

let tvar_seqb x y =
  match x with
  | TvProp ->
    (match y with
     | TvProp -> true
     | TvType n0 -> false)
  | TvType x0 ->
    (match y with
     | TvProp -> false
     | TvType y0 -> beq_nat x0 y0)

type env = (tvar, tvarD) sigT list

(** val lookupAs : type0 list -> env -> tvar -> nat -> tvarD option **)

let lookupAs types4 ls t0 i =
  match nth_error ls i with
  | Some tv ->
    if equiv_dec eqDec_tvar (projT1 tv) t0 then Some (projT2 tv) else None
  | None -> None

(** val applyD :
    type0 list -> (expr -> tvar -> tvarD option) -> tvar list -> expr list ->
    'a1 functionTypeD0 -> 'a1 option **)

let rec applyD types4 exprD0 domain0 xs x =
  match domain0 with
  | [] ->
    (match xs with
     | [] -> Some (Obj.magic x)
     | e::l -> None)
  | t0::ts ->
    (match xs with
     | [] -> None
     | e::es ->
       (match exprD0 e t0 with
        | Some v -> applyD types4 exprD0 ts es (Obj.magic x v)
        | None -> None))

(** val exprD :
    type0 list -> functions -> env -> env -> expr -> tvar -> tvarD option **)

let rec exprD types4 funcs meta_env var_env e t0 =
  match e with
  | Const (t', c) -> if equiv_dec eqDec_tvar t' t0 then Some c else None
  | Var x -> lookupAs types4 var_env t0 x
  | Func (f0, xs) ->
    (match nth_error funcs f0 with
     | Some f1 ->
       if equiv_dec eqDec_tvar f1.range t0
       then applyD types4 (exprD types4 funcs meta_env var_env) f1.domain xs
              f1.denotation
       else None
     | None -> None)
  | Equal (t', e1, e2) ->
    (match t0 with
     | TvProp ->
       (match exprD types4 funcs meta_env var_env e1 t' with
        | Some v1 ->
          (match exprD types4 funcs meta_env var_env e2 t' with
           | Some v2 -> Some (Obj.magic __)
           | None -> None)
        | None -> None)
     | TvType n0 -> None)
  | Not e1 ->
    (match t0 with
     | TvProp ->
       (match exprD types4 funcs meta_env var_env e1 TvProp with
        | Some x -> Obj.magic (fun _ -> Some __) x
        | None -> None)
     | TvType n0 -> None)
  | UVar x -> lookupAs types4 meta_env t0 x

type tenv = tvar list

type tsignature = { tDomain : tvar list; tRange : tvar }

(** val tDomain : tsignature -> tvar list **)

let tDomain x = x.tDomain

(** val tRange : tsignature -> tvar **)

let tRange x = x.tRange

type tfunctions = tsignature list

(** val is_well_typed :
    type0 list -> tfunctions -> tenv -> tenv -> expr -> tvar -> bool **)

let rec is_well_typed types4 tfuncs tmeta_env tvar_env e t0 =
  match e with
  | Const (t', t1) -> tvar_seqb t' t0
  | Var x ->
    (match nth_error tvar_env x with
     | Some t' -> tvar_seqb t0 t'
     | None -> false)
  | Func (f0, xs) ->
    (match nth_error tfuncs f0 with
     | Some f1 ->
       if tvar_seqb t0 f1.tRange
       then all2 (is_well_typed types4 tfuncs tmeta_env tvar_env) xs
              f1.tDomain
       else false
     | None -> false)
  | Equal (t', e1, e2) ->
    (match t0 with
     | TvProp ->
       if is_well_typed types4 tfuncs tmeta_env tvar_env e1 t'
       then is_well_typed types4 tfuncs tmeta_env tvar_env e2 t'
       else false
     | TvType n0 -> false)
  | Not e1 ->
    (match t0 with
     | TvProp -> is_well_typed types4 tfuncs tmeta_env tvar_env e1 TvProp
     | TvType n0 -> false)
  | UVar x ->
    (match nth_error tmeta_env x with
     | Some t' -> tvar_seqb t0 t'
     | None -> false)

(** val mentionsU : type0 list -> uvar -> expr -> bool **)

let rec mentionsU types4 uv = function
| Func (f0, args) ->
  let rec anyb = function
  | [] -> false
  | l::ls0 -> if mentionsU types4 uv l then true else anyb ls0
  in anyb args
| Equal (t0, l, r) ->
  if mentionsU types4 uv l then true else mentionsU types4 uv r
| Not e0 -> mentionsU types4 uv e0
| UVar n0 -> beq_nat uv n0
| _ -> false

(** val get_Eq : type0 list -> tvar -> tvarD -> tvarD -> bool **)

let get_Eq types4 = function
| TvProp -> Obj.magic (fun _ _ -> false)
| TvType t1 ->
  (match nth_error types4 t1 with
   | Some t2 -> eqb0 t2
   | None -> (fun x y -> assert false (* absurd case *)))

(** val const_seqb : type0 list -> tvar -> tvar -> tvarD -> tvarD -> bool **)

let const_seqb types4 t0 t' =
  match t0 with
  | TvProp -> Obj.magic (fun _ x -> false)
  | TvType x ->
    (match t' with
     | TvProp -> (fun x0 -> Obj.magic (fun _ -> false))
     | TvType y ->
       if eq_nat_dec x y
       then (match nth_error types4 x with
             | Some t1 -> eqb0 t1
             | None -> (fun x0 x1 -> false))
       else (fun x0 x1 -> false))

(** val expr_seq_dec : type0 list -> expr -> expr -> bool **)

let rec expr_seq_dec types4 a b0 =
  match a with
  | Const (t0, c) ->
    (match b0 with
     | Const (t', c') -> const_seqb types4 t0 t' c c'
     | _ -> false)
  | Var x ->
    (match b0 with
     | Var y -> beq_nat x y
     | _ -> false)
  | Func (x, xs) ->
    (match b0 with
     | Func (y, ys) ->
       if beq_nat x y
       then let rec seq_dec' a0 b1 =
              match a0 with
              | [] ->
                (match b1 with
                 | [] -> true
                 | y0::l -> false)
              | x0::xs0 ->
                (match b1 with
                 | [] -> false
                 | y0::ys0 ->
                   if expr_seq_dec types4 x0 y0
                   then seq_dec' xs0 ys0
                   else false)
            in seq_dec' xs ys
       else false
     | _ -> false)
  | Equal (t1, e1, f1) ->
    (match b0 with
     | Equal (t2, e2, f2) ->
       if if tvar_seqb t1 t2 then expr_seq_dec types4 e1 e2 else false
       then expr_seq_dec types4 f1 f2
       else false
     | _ -> false)
  | Not e1 ->
    (match b0 with
     | Not e2 -> expr_seq_dec types4 e1 e2
     | _ -> false)
  | UVar x ->
    (match b0 with
     | UVar y -> beq_nat x y
     | _ -> false)

(** val liftExpr : type0 list -> nat -> nat -> nat -> nat -> expr -> expr **)

let rec liftExpr types4 ua ub a b0 e = match e with
| Const (t0, t1) -> e
| Var x -> Var (if ltb0 x a then x else plus b0 x)
| Func (f0, xs) -> Func (f0, (map (liftExpr types4 ua ub a b0) xs))
| Equal (t0, e1, e2) ->
  Equal (t0, (liftExpr types4 ua ub a b0 e1),
    (liftExpr types4 ua ub a b0 e2))
| Not e1 -> Not (liftExpr types4 ua ub a b0 e1)
| UVar x -> UVar (if ltb0 x ua then x else plus ub x)

(** val exprSubstU : type0 list -> nat -> nat -> nat -> expr -> expr **)

let rec exprSubstU types4 a b0 c = function
| Const (t0, t1) -> Const (t0, t1)
| Var x ->
  if ltb0 x a
  then Var x
  else if ltb0 x b0
       then UVar (minus (plus c x) a)
       else Var (minus (plus x a) b0)
| Func (f0, args) -> Func (f0, (map (exprSubstU types4 a b0 c) args))
| Equal (t0, e1, e2) ->
  Equal (t0, (exprSubstU types4 a b0 c e1), (exprSubstU types4 a b0 c e2))
| Not e1 -> Not (exprSubstU types4 a b0 c e1)
| UVar x -> if ltb0 x c then UVar x else UVar (minus (plus x b0) a)

module type SepExpr = 
 sig 
  module ST : 
   SepTheoryX
  
  type predicate = { coq_SDomain : tvar list;
                     coq_SDenotation : (tvarD, tvarD) ST.hprop functionTypeD0 }
  
  val predicate_rect :
    type0 list -> tvar -> tvar -> (tvar list -> (tvarD, tvarD) ST.hprop
    functionTypeD0 -> 'a1) -> predicate -> 'a1
  
  val predicate_rec :
    type0 list -> tvar -> tvar -> (tvar list -> (tvarD, tvarD) ST.hprop
    functionTypeD0 -> 'a1) -> predicate -> 'a1
  
  val coq_SDomain : type0 list -> tvar -> tvar -> predicate -> tvar list
  
  val coq_SDenotation :
    type0 list -> tvar -> tvar -> predicate -> (tvarD, tvarD) ST.hprop
    functionTypeD0
  
  type predicates = predicate list
  
  val coq_Default_predicate : type0 list -> tvar -> tvar -> predicate
  
  type sexpr =
  | Emp
  | Inj of expr
  | Star of sexpr * sexpr
  | Exists of tvar * sexpr
  | Func of func * expr list
  | Const of (tvarD, tvarD) ST.hprop
  
  val sexpr_rect :
    type0 list -> tvar -> tvar -> 'a1 -> (expr -> 'a1) -> (sexpr -> 'a1 ->
    sexpr -> 'a1 -> 'a1) -> (tvar -> sexpr -> 'a1 -> 'a1) -> (func -> expr
    list -> 'a1) -> ((tvarD, tvarD) ST.hprop -> 'a1) -> sexpr -> 'a1
  
  val sexpr_rec :
    type0 list -> tvar -> tvar -> 'a1 -> (expr -> 'a1) -> (sexpr -> 'a1 ->
    sexpr -> 'a1 -> 'a1) -> (tvar -> sexpr -> 'a1 -> 'a1) -> (func -> expr
    list -> 'a1) -> ((tvarD, tvarD) ST.hprop -> 'a1) -> sexpr -> 'a1
  
  type tpredicate = tvar list
  
  type tpredicates = tpredicate list
  
  val typeof_pred : type0 list -> tvar -> tvar -> predicate -> tpredicate
  
  val typeof_preds : type0 list -> tvar -> tvar -> predicates -> tpredicates
  
  val coq_WellTyped_sexpr :
    type0 list -> tvar -> tvar -> tfunctions -> tpredicates -> tenv -> tenv
    -> sexpr -> bool
  
  val liftSExpr :
    type0 list -> tvar -> tvar -> nat -> nat -> nat -> nat -> sexpr -> sexpr
  
  val sexprD :
    type0 list -> tvar -> tvar -> functions -> predicates -> env -> env ->
    sexpr -> (tvarD, tvarD) ST.hprop
  
  val existsEach : type0 list -> tvar -> tvar -> tvar list -> sexpr -> sexpr
 end

module SepExprFacts = 
 functor (SE:SepExpr) ->
 struct 
  module SEP_FACTS = SepTheoryX_Rewrites(SE.ST)
 end

module Coq_Make = 
 functor (ST':SepTheoryX) ->
 struct 
  module ST = ST'
  
  type predicate = { coq_SDomain : tvar list;
                     coq_SDenotation : (tvarD, tvarD) ST.hprop functionTypeD0 }
  
  (** val predicate_rect :
      type0 list -> tvar -> tvar -> (tvar list -> (tvarD, tvarD) ST.hprop
      functionTypeD0 -> 'a1) -> predicate -> 'a1 **)
  
  let predicate_rect types4 pcType stateType f0 p =
    let { coq_SDomain = x; coq_SDenotation = x0 } = p in f0 x x0
  
  (** val predicate_rec :
      type0 list -> tvar -> tvar -> (tvar list -> (tvarD, tvarD) ST.hprop
      functionTypeD0 -> 'a1) -> predicate -> 'a1 **)
  
  let predicate_rec types4 pcType stateType f0 p =
    let { coq_SDomain = x; coq_SDenotation = x0 } = p in f0 x x0
  
  (** val coq_SDomain :
      type0 list -> tvar -> tvar -> predicate -> tvar list **)
  
  let coq_SDomain types4 pcType stateType p =
    p.coq_SDomain
  
  (** val coq_SDenotation :
      type0 list -> tvar -> tvar -> predicate -> (tvarD, tvarD) ST.hprop
      functionTypeD0 **)
  
  let coq_SDenotation types4 pcType stateType p =
    p.coq_SDenotation
  
  type predicates = predicate list
  
  (** val coq_Default_predicate : type0 list -> tvar -> tvar -> predicate **)
  
  let coq_Default_predicate types4 pcType stateType =
    { coq_SDomain = []; coq_SDenotation = (Obj.magic (ST.emp [])) }
  
  type sexpr =
  | Emp
  | Inj of expr
  | Star of sexpr * sexpr
  | Exists of tvar * sexpr
  | Func of func * expr list
  | Const of (tvarD, tvarD) ST.hprop
  
  (** val sexpr_rect :
      type0 list -> tvar -> tvar -> 'a1 -> (expr -> 'a1) -> (sexpr -> 'a1 ->
      sexpr -> 'a1 -> 'a1) -> (tvar -> sexpr -> 'a1 -> 'a1) -> (func -> expr
      list -> 'a1) -> ((tvarD, tvarD) ST.hprop -> 'a1) -> sexpr -> 'a1 **)
  
  let rec sexpr_rect types4 pcType stateType f0 f1 f2 f3 f4 f5 = function
  | Emp -> f0
  | Inj e -> f1 e
  | Star (s0, s1) ->
    f2 s0 (sexpr_rect types4 pcType stateType f0 f1 f2 f3 f4 f5 s0) s1
      (sexpr_rect types4 pcType stateType f0 f1 f2 f3 f4 f5 s1)
  | Exists (t0, s0) ->
    f3 t0 s0 (sexpr_rect types4 pcType stateType f0 f1 f2 f3 f4 f5 s0)
  | Func (f6, l) -> f4 f6 l
  | Const h -> f5 h
  
  (** val sexpr_rec :
      type0 list -> tvar -> tvar -> 'a1 -> (expr -> 'a1) -> (sexpr -> 'a1 ->
      sexpr -> 'a1 -> 'a1) -> (tvar -> sexpr -> 'a1 -> 'a1) -> (func -> expr
      list -> 'a1) -> ((tvarD, tvarD) ST.hprop -> 'a1) -> sexpr -> 'a1 **)
  
  let rec sexpr_rec types4 pcType stateType f0 f1 f2 f3 f4 f5 = function
  | Emp -> f0
  | Inj e -> f1 e
  | Star (s0, s1) ->
    f2 s0 (sexpr_rec types4 pcType stateType f0 f1 f2 f3 f4 f5 s0) s1
      (sexpr_rec types4 pcType stateType f0 f1 f2 f3 f4 f5 s1)
  | Exists (t0, s0) ->
    f3 t0 s0 (sexpr_rec types4 pcType stateType f0 f1 f2 f3 f4 f5 s0)
  | Func (f6, l) -> f4 f6 l
  | Const h -> f5 h
  
  type tpredicate = tvar list
  
  type tpredicates = tpredicate list
  
  (** val typeof_pred :
      type0 list -> tvar -> tvar -> predicate -> tpredicate **)
  
  let typeof_pred types4 pcType stateType =
    coq_SDomain types4 pcType stateType
  
  (** val typeof_preds :
      type0 list -> tvar -> tvar -> predicates -> tpredicates **)
  
  let typeof_preds types4 pcType stateType =
    map (typeof_pred types4 pcType stateType)
  
  (** val coq_WellTyped_sexpr :
      type0 list -> tvar -> tvar -> tfunctions -> tpredicates -> tenv -> tenv
      -> sexpr -> bool **)
  
  let rec coq_WellTyped_sexpr types4 pcType stateType funcs preds tU tG = function
  | Inj e -> is_well_typed types4 funcs tU tG e TvProp
  | Star (l, r) ->
    if coq_WellTyped_sexpr types4 pcType stateType funcs preds tU tG l
    then coq_WellTyped_sexpr types4 pcType stateType funcs preds tU tG r
    else false
  | Exists (t0, e) ->
    coq_WellTyped_sexpr types4 pcType stateType funcs preds tU (t0::tG) e
  | Func (f0, args) ->
    (match nth_error preds f0 with
     | Some ts -> all2 (is_well_typed types4 funcs tU tG) args ts
     | None -> false)
  | _ -> true
  
  (** val sexprD :
      type0 list -> tvar -> tvar -> functions -> predicates -> env -> env ->
      sexpr -> (tvarD, tvarD) ST.hprop **)
  
  let rec sexprD types4 pcType stateType funcs sfuncs meta_env var_env = function
  | Emp -> ST.emp []
  | Inj p ->
    (match exprD types4 funcs meta_env var_env p TvProp with
     | Some x -> Obj.magic (fun _ -> ST.inj [] (Coq__1.Inj [])) x
     | None -> ST.inj [] (Coq__1.Inj []))
  | Star (l, r) ->
    ST.star []
      (sexprD types4 pcType stateType funcs sfuncs meta_env var_env l)
      (sexprD types4 pcType stateType funcs sfuncs meta_env var_env r)
  | Exists (t0, b0) ->
    ST.ex [] (fun x ->
      sexprD types4 pcType stateType funcs sfuncs meta_env ((ExistT (t0,
        x))::var_env) b0)
  | Func (f0, b0) ->
    (match nth_error sfuncs f0 with
     | Some f' ->
       (match applyD types4 (exprD types4 funcs meta_env var_env)
                (coq_SDomain types4 pcType stateType f') b0
                (coq_SDenotation types4 pcType stateType f') with
        | Some p -> p
        | None -> ST.inj [] (Coq__1.Inj []))
     | None -> ST.inj [] (Coq__1.Inj []))
  | Const p -> p
  
  (** val existsEach :
      type0 list -> tvar -> tvar -> tvar list -> sexpr -> sexpr **)
  
  let rec existsEach types4 pcType stateType ls x =
    match ls with
    | [] -> x
    | t0::ts -> Exists (t0, (existsEach types4 pcType stateType ts x))
  
  (** val liftSExpr :
      type0 list -> tvar -> tvar -> nat -> nat -> nat -> nat -> sexpr ->
      sexpr **)
  
  let rec liftSExpr types4 pcType stateType ua ub a b0 = function
  | Inj p -> Inj (liftExpr types4 ua ub a b0 p)
  | Star (l, r) ->
    Star ((liftSExpr types4 pcType stateType ua ub a b0 l),
      (liftSExpr types4 pcType stateType ua ub a b0 r))
  | Exists (t0, s0) ->
    Exists (t0, (liftSExpr types4 pcType stateType ua ub (S a) b0 s0))
  | Func (f0, args) -> Func (f0, (map (liftExpr types4 ua ub a b0) args))
  | x -> x
 end

(** val findA : ('a1 -> bool) -> ('a1, 'a2) prod list -> 'a2 option **)

let rec findA f0 = function
| [] -> None
| p::l0 -> let Pair (a, b0) = p in if f0 a then Some b0 else findA f0 l0

type 'x compare0 =
| LT
| EQ
| GT

module type MiniOrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare0
 end

module type Coq_OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare0
  
  val eq_dec : t -> t -> bool
 end

module MOT_to_OT = 
 functor (O:MiniOrderedType) ->
 struct 
  type t = O.t
  
  (** val compare : t -> t -> t compare0 **)
  
  let compare =
    O.compare
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    match compare x y with
    | EQ -> true
    | _ -> false
 end

module Coq_OrderedTypeFacts = 
 functor (O:Coq_OrderedType) ->
 struct 
  module TO = 
   struct 
    type t = O.t
   end
  
  module IsTO = 
   struct 
    
   end
  
  module OrderTac = MakeOrderTac(TO)(IsTO)
  
  (** val eq_dec : O.t -> O.t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val lt_dec : O.t -> O.t -> bool **)
  
  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType = 
 functor (O:Coq_OrderedType) ->
 struct 
  module MO = Coq_OrderedTypeFacts(O)
 end

module type DecidableType = 
 DecidableTypeOrig

module type WS = 
 sig 
  module E : 
   DecidableType
  
  type key = E.t
  
  type 'x t 
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val find : key -> 'a1 t -> 'a1 option
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Raw = 
 functor (X:Coq_OrderedType) ->
 struct 
  module MX = Coq_OrderedTypeFacts(X)
  
  module PX = KeyOrderedType(X)
  
  type key = X.t
  
  type 'elt t = (X.t, 'elt) prod list
  
  (** val empty : 'a1 t **)
  
  let empty =
    []
  
  (** val is_empty : 'a1 t -> bool **)
  
  let is_empty = function
  | [] -> true
  | x::x0 -> false
  
  (** val mem : key -> 'a1 t -> bool **)
  
  let rec mem k = function
  | [] -> false
  | p::l ->
    let Pair (k', e) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)
  
  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
     * 'elt coq_R_mem
  
  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rect k f0 f1 f2 f3 s b0 = function
  | R_mem_0 s0 -> f0 s0 __
  | R_mem_1 (s0, k', _x, l) -> f1 s0 k' _x l __ __ __
  | R_mem_2 (s0, k', _x, l) -> f2 s0 k' _x l __ __ __
  | R_mem_3 (s0, k', _x, l, res, r0) ->
    f3 s0 k' _x l __ __ __ res r0 (coq_R_mem_rect k f0 f1 f2 f3 l res r0)
  
  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2 **)
  
  let rec coq_R_mem_rec k f0 f1 f2 f3 s b0 = function
  | R_mem_0 s0 -> f0 s0 __
  | R_mem_1 (s0, k', _x, l) -> f1 s0 k' _x l __ __ __
  | R_mem_2 (s0, k', _x, l) -> f2 s0 k' _x l __ __ __
  | R_mem_3 (s0, k', _x, l, res, r0) ->
    f3 s0 k' _x l __ __ __ res r0 (coq_R_mem_rec k f0 f1 f2 f3 l res r0)
  
  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let mem_rect =
    failwith "AXIOM TO BE REALIZED"
  
  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let mem_rec k =
    mem_rect k
  
  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)
  
  let coq_R_mem_correct x x0 res =
    let princ = fun x1 -> mem_rect x1 in
    Obj.magic princ x (fun y _ z0 _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ z0 _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ z0 _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 z0 _ -> R_mem_3 (y, y0, y1, y2, (mem x y2),
      (y6 (mem x y2) __))) x0 res __
  
  (** val find : key -> 'a1 t -> 'a1 option **)
  
  let rec find k = function
  | [] -> None
  | p::s' ->
    let Pair (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')
  
  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
     * 'elt coq_R_find
  
  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)
  
  let rec coq_R_find_rect k f0 f1 f2 f3 s o = function
  | R_find_0 s0 -> f0 s0 __
  | R_find_1 (s0, k', x, s') -> f1 s0 k' x s' __ __ __
  | R_find_2 (s0, k', x, s') -> f2 s0 k' x s' __ __ __
  | R_find_3 (s0, k', x, s', res, r0) ->
    f3 s0 k' x s' __ __ __ res r0 (coq_R_find_rect k f0 f1 f2 f3 s' res r0)
  
  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)
  
  let rec coq_R_find_rec k f0 f1 f2 f3 s o = function
  | R_find_0 s0 -> f0 s0 __
  | R_find_1 (s0, k', x, s') -> f1 s0 k' x s' __ __ __
  | R_find_2 (s0, k', x, s') -> f2 s0 k' x s' __ __ __
  | R_find_3 (s0, k', x, s', res, r0) ->
    f3 s0 k' x s' __ __ __ res r0 (coq_R_find_rec k f0 f1 f2 f3 s' res r0)
  
  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let find_rect =
    failwith "AXIOM TO BE REALIZED"
  
  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let find_rec k =
    find_rect k
  
  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)
  
  let coq_R_find_correct x x0 res =
    let princ = fun x1 -> find_rect x1 in
    Obj.magic princ x (fun y _ z0 _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ z0 _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ z0 _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 z0 _ -> R_find_3 (y, y0, y1, y2, (find x y2),
      (y6 (find x y2) __))) x0 res __
  
  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let rec add k x s = match s with
  | [] -> (Pair (k, x))::[]
  | p::l ->
    let Pair (k', y) = p in
    (match X.compare k k' with
     | LT -> (Pair (k, x))::s
     | EQ -> (Pair (k, x))::l
     | GT -> (Pair (k', y))::(add k x l))
  
  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_add
  
  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add ->
      'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rect k x f0 f1 f2 f3 s t0 = function
  | R_add_0 s0 -> f0 s0 __
  | R_add_1 (s0, k', y, l) -> f1 s0 k' y l __ __ __
  | R_add_2 (s0, k', y, l) -> f2 s0 k' y l __ __ __
  | R_add_3 (s0, k', y, l, res, r0) ->
    f3 s0 k' y l __ __ __ res r0 (coq_R_add_rect k x f0 f1 f2 f3 l res r0)
  
  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add ->
      'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)
  
  let rec coq_R_add_rec k x f0 f1 f2 f3 s t0 = function
  | R_add_0 s0 -> f0 s0 __
  | R_add_1 (s0, k', y, l) -> f1 s0 k' y l __ __ __
  | R_add_2 (s0, k', y, l) -> f2 s0 k' y l __ __ __
  | R_add_3 (s0, k', y, l, res, r0) ->
    f3 s0 k' y l __ __ __ res r0 (coq_R_add_rec k x f0 f1 f2 f3 l res r0)
  
  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
      'a2 **)
  
  let add_rect =
    failwith "AXIOM TO BE REALIZED"
  
  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
      'a2 **)
  
  let add_rec k x =
    add_rect k x
  
  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)
  
  let coq_R_add_correct x x0 x1 res =
    add_rect x x0 (fun y _ z0 _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ z0 _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ z0 _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 z0 _ -> R_add_3 (y, y0, y1, y2,
      (add x x0 y2), (y6 (add x x0 y2) __))) x1 res __
  
  (** val remove : key -> 'a1 t -> 'a1 t **)
  
  let rec remove k s = match s with
  | [] -> []
  | p::l ->
    let Pair (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (Pair (k', x))::(remove k l))
  
  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_remove
  
  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rect k f0 f1 f2 f3 s t0 = function
  | R_remove_0 s0 -> f0 s0 __
  | R_remove_1 (s0, k', x, l) -> f1 s0 k' x l __ __ __
  | R_remove_2 (s0, k', x, l) -> f2 s0 k' x l __ __ __
  | R_remove_3 (s0, k', x, l, res, r0) ->
    f3 s0 k' x l __ __ __ res r0 (coq_R_remove_rect k f0 f1 f2 f3 l res r0)
  
  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)
  
  let rec coq_R_remove_rec k f0 f1 f2 f3 s t0 = function
  | R_remove_0 s0 -> f0 s0 __
  | R_remove_1 (s0, k', x, l) -> f1 s0 k' x l __ __ __
  | R_remove_2 (s0, k', x, l) -> f2 s0 k' x l __ __ __
  | R_remove_3 (s0, k', x, l, res, r0) ->
    f3 s0 k' x l __ __ __ res r0 (coq_R_remove_rec k f0 f1 f2 f3 l res r0)
  
  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let remove_rect =
    failwith "AXIOM TO BE REALIZED"
  
  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)
  
  let remove_rec k =
    remove_rect k
  
  (** val coq_R_remove_correct :
      key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)
  
  let coq_R_remove_correct x x0 res =
    let princ = fun x1 -> remove_rect x1 in
    Obj.magic princ x (fun y _ z0 _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ z0 _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ z0 _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 z0 _ -> R_remove_3 (y, y0, y1, y2,
      (remove x y2), (y6 (remove x y2) __))) x0 res __
  
  (** val elements : 'a1 t -> 'a1 t **)
  
  let elements m6 =
    m6
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let rec fold f0 m6 acc =
    match m6 with
    | [] -> acc
    | p::m' -> let Pair (k, e) = p in fold f0 m' (f0 k e acc)
  
  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
  | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a * X.t * 'elt
     * (X.t, 'elt) prod list * 'a * ('elt, 'a) coq_R_fold
  
  (** val coq_R_fold_rect :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key ->
      'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold ->
      'a2 **)
  
  let rec coq_R_fold_rect f0 f1 f2 m6 acc a = function
  | R_fold_0 (f3, m7, acc0) -> Obj.magic f0 __ f3 m7 acc0 __
  | R_fold_1 (f3, m7, acc0, k, e, m', res, r0) ->
    Obj.magic f1 __ f3 m7 acc0 k e m' __ res r0
      (coq_R_fold_rect f0 f1 f3 m' (f3 k e acc0) res r0)
  
  (** val coq_R_fold_rec :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key ->
      'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold ->
      'a2 **)
  
  let rec coq_R_fold_rec f0 f1 f2 m6 acc a = function
  | R_fold_0 (f3, m7, acc0) -> Obj.magic f0 __ f3 m7 acc0 __
  | R_fold_1 (f3, m7, acc0, k, e, m', res, r0) ->
    Obj.magic f1 __ f3 m7 acc0 k e m' __ res r0
      (coq_R_fold_rec f0 f1 f3 m' (f3 k e acc0) res r0)
  
  (** val fold_rect :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t
      -> 'a3 -> 'a2 **)
  
  let fold_rect =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rec :
      (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) -> (__ ->
      (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t
      -> 'a3 -> 'a2 **)
  
  let fold_rec f0 f1 f2 m6 acc =
    fold_rect f0 f1 f2 m6 acc
  
  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)
  
  let coq_R_fold_correct x0 x1 x2 res =
    let princ = fun x x3 -> fold_rect x x3 in
    Obj.magic princ (fun _ y0 y1 y2 _ z0 _ -> R_fold_0 (y0, y1, y2))
      (fun _ y0 y1 y2 y3 y4 y5 _ y7 z0 _ -> R_fold_1 (y0, y1, y2, y3, y4, y5,
      (fold y0 y5 (y0 y3 y4 y2)), (y7 (fold y0 y5 (y0 y3 y4 y2)) __))) x0 x1
      x2 res __
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let rec equal cmp0 m6 m' =
    match m6 with
    | [] ->
      (match m' with
       | [] -> true
       | p::l -> false)
    | p::l ->
      let Pair (x, e) = p in
      (match m' with
       | [] -> false
       | p0::l' ->
         let Pair (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> if cmp0 e e' then equal cmp0 l l' else false
          | _ -> false))
  
  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
  
  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
      'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
      __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ ->
      __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
      'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)
  
  let rec coq_R_equal_rect cmp0 f0 f1 f2 f3 m6 m' b0 = function
  | R_equal_0 (m7, m'0) -> f0 m7 m'0 __ __
  | R_equal_1 (m7, m'0, x, e, l, x', e', l', res, r0) ->
    f1 m7 m'0 x e l __ x' e' l' __ __ __ res r0
      (coq_R_equal_rect cmp0 f0 f1 f2 f3 l l' res r0)
  | R_equal_2 (m7, m'0, x, e, l, x', e', l', _x) ->
    f2 m7 m'0 x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m7, m'0, _x, _x0) -> f3 m7 m'0 _x __ _x0 __ __
  
  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
      'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list ->
      __ -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ ->
      __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
      'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)
  
  let rec coq_R_equal_rec cmp0 f0 f1 f2 f3 m6 m' b0 = function
  | R_equal_0 (m7, m'0) -> f0 m7 m'0 __ __
  | R_equal_1 (m7, m'0, x, e, l, x', e', l', res, r0) ->
    f1 m7 m'0 x e l __ x' e' l' __ __ __ res r0
      (coq_R_equal_rec cmp0 f0 f1 f2 f3 l l' res r0)
  | R_equal_2 (m7, m'0, x, e, l, x', e', l', _x) ->
    f2 m7 m'0 x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m7, m'0, _x, _x0) -> f3 m7 m'0 _x __ _x0 __ __
  
  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
      t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
      'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
      'a2 **)
  
  let equal_rect =
    failwith "AXIOM TO BE REALIZED"
  
  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
      t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
      'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
      'a2 **)
  
  let equal_rec cmp0 =
    equal_rect cmp0
  
  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)
  
  let coq_R_equal_correct x x0 x1 res =
    equal_rect x (fun y y0 _ _ z0 _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 z0 _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal x y3 y7), (y11 (equal x y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ z0 _ -> R_equal_2 (y, y0, y1,
      y2, y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ z0 _ -> R_equal_3 (y,
      y0, y1, y3)) x0 x1 res __
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let rec map f0 = function
  | [] -> []
  | p::m' -> let Pair (k, e) = p in (Pair (k, (f0 e)))::(map f0 m')
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let rec mapi f0 = function
  | [] -> []
  | p::m' -> let Pair (k, e) = p in (Pair (k, (f0 k e)))::(mapi f0 m')
  
  (** val option_cons :
      key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list **)
  
  let option_cons k o l =
    match o with
    | Some e -> (Pair (k, e))::l
    | None -> l
  
  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)
  
  let rec map2_l f0 = function
  | [] -> []
  | p::l ->
    let Pair (k, e) = p in option_cons k (f0 (Some e) None) (map2_l f0 l)
  
  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)
  
  let rec map2_r f0 = function
  | [] -> []
  | p::l' ->
    let Pair (k, e') = p in option_cons k (f0 None (Some e')) (map2_r f0 l')
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let rec map2 f0 m6 = match m6 with
  | [] -> map2_r f0
  | p::l ->
    let Pair (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f0 m6
    | p0::l' ->
      let Pair (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f0 (Some e) None) (map2 f0 l m')
       | EQ -> option_cons k (f0 (Some e) (Some e')) (map2 f0 l l')
       | GT -> option_cons k' (f0 None (Some e')) (map2_aux l'))
    in map2_aux
  
  (** val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t **)
  
  let rec combine m6 = match m6 with
  | [] -> map (fun e' -> Pair (None, (Some e')))
  | p::l ->
    let Pair (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> Pair ((Some e0), None)) m6
    | p0::l' ->
      let Pair (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (Pair (k, (Pair ((Some e), None))))::(combine l m')
       | EQ -> (Pair (k, (Pair ((Some e), (Some e')))))::(combine l l')
       | GT -> (Pair (k', (Pair (None, (Some e')))))::(combine_aux l'))
    in combine_aux
  
  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3 **)
  
  let fold_right_pair f0 l i =
    fold_right (fun p -> f0 (fst p) (snd p)) i l
  
  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
      'a3) prod list **)
  
  let map2_alt f0 m6 m' =
    let m7 = combine m6 m' in
    let m8 = map (fun p -> f0 (fst p) (snd p)) m7 in
    fold_right_pair option_cons m8 []
  
  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option **)
  
  let at_least_one o o' =
    match o with
    | Some e -> Some (Pair (o, o'))
    | None ->
      (match o' with
       | Some e -> Some (Pair (o, o'))
       | None -> None)
  
  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)
  
  let at_least_one_then_f f0 o o' =
    match o with
    | Some e -> f0 o o'
    | None ->
      (match o' with
       | Some e -> f0 o o'
       | None -> None)
 end

module type Int = 
 sig 
  type t 
  
  val i2z : t -> z
  
  val _0 : t
  
  val _1 : t
  
  val _2 : t
  
  val _3 : t
  
  val plus : t -> t -> t
  
  val opp : t -> t
  
  val minus : t -> t -> t
  
  val mult : t -> t -> t
  
  val max : t -> t -> t
  
  val gt_le_dec : t -> t -> bool
  
  val ge_lt_dec : t -> t -> bool
  
  val eq_dec : t -> t -> bool
 end

module Z_as_Int = 
 struct 
  type t = z
  
  (** val _0 : z **)
  
  let _0 =
    Z0
  
  (** val _1 : z **)
  
  let _1 =
    Zpos XH
  
  (** val _2 : z **)
  
  let _2 =
    Zpos (XO XH)
  
  (** val _3 : z **)
  
  let _3 =
    Zpos (XI XH)
  
  (** val plus : z -> z -> z **)
  
  let plus =
    Z.add
  
  (** val opp : z -> z **)
  
  let opp =
    Z.opp
  
  (** val minus : z -> z -> z **)
  
  let minus =
    Z.sub
  
  (** val mult : z -> z -> z **)
  
  let mult =
    Z.mul
  
  (** val max : z -> z -> z **)
  
  let max =
    Z.max
  
  (** val gt_le_dec : z -> z -> bool **)
  
  let gt_le_dec =
    z_gt_le_dec
  
  (** val ge_lt_dec : z -> z -> bool **)
  
  let ge_lt_dec =
    z_ge_lt_dec
  
  (** val eq_dec : z -> z -> bool **)
  
  let eq_dec =
    Z.eq_dec
  
  (** val i2z : t -> z **)
  
  let i2z n0 =
    n0
 end

module Coq_Raw = 
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct 
  type key = X.t
  
  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t
  
  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)
  
  let rec tree_rect f0 f1 = function
  | Leaf -> f0
  | Node (t1, k, e, t2, t3) ->
    f1 t1 (tree_rect f0 f1 t1) k e t2 (tree_rect f0 f1 t2) t3
  
  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)
  
  let rec tree_rec f0 f1 = function
  | Leaf -> f0
  | Node (t1, k, e, t2, t3) ->
    f1 t1 (tree_rec f0 f1 t1) k e t2 (tree_rec f0 f1 t2) t3
  
  (** val height : 'a1 tree -> I.t **)
  
  let height = function
  | Leaf -> I._0
  | Node (t0, k, e, t1, h) -> h
  
  (** val cardinal : 'a1 tree -> nat **)
  
  let rec cardinal = function
  | Leaf -> O
  | Node (l, k, e, r, t0) -> S (plus (cardinal l) (cardinal r))
  
  (** val empty : 'a1 tree **)
  
  let empty =
    Leaf
  
  (** val is_empty : 'a1 tree -> bool **)
  
  let is_empty = function
  | Leaf -> true
  | Node (t0, k, e, t1, t2) -> false
  
  (** val mem : X.t -> 'a1 tree -> bool **)
  
  let rec mem x = function
  | Leaf -> false
  | Node (l, y, e, r, t0) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)
  
  (** val find : X.t -> 'a1 tree -> 'a1 option **)
  
  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, t0) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)
  
  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let create l x e r =
    Node (l, x, e, r, (I.plus (I.max (height l) (height r)) I._1))
  
  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let assert_false =
    create
  
  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.plus hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, t0) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, t1) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.plus hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, t0) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, t1) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r
  
  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))
  
  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod **)
  
  let rec remove_min l x d r =
    match l with
    | Leaf -> Pair (r, (Pair (x, d)))
    | Node (ll, lx, ld, lr, lh) ->
      let Pair (l', m6) = remove_min ll lx ld lr in Pair ((bal l' x d r), m6)
  
  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, k, e, t1, t2) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, h2) ->
         let Pair (s2', p) = remove_min l2 x2 d2 r2 in
         let Pair (x, d) = p in bal s1 x d s2')
  
  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)
  
  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, h) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))
  
  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)
  
  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.plus rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.plus lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)
  
  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }
  
  (** val triple_rect :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2 **)
  
  let triple_rect f0 t0 =
    let { t_left = x; t_opt = x0; t_right = x1 } = t0 in f0 x x0 x1
  
  (** val triple_rec :
      ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2 **)
  
  let triple_rec f0 t0 =
    let { t_left = x; t_opt = x0; t_right = x1 } = t0 in f0 x x0 x1
  
  (** val t_left : 'a1 triple -> 'a1 tree **)
  
  let t_left t0 =
    t0.t_left
  
  (** val t_opt : 'a1 triple -> 'a1 option **)
  
  let t_opt t0 =
    t0.t_opt
  
  (** val t_right : 'a1 triple -> 'a1 tree **)
  
  let t_right t0 =
    t0.t_right
  
  (** val split : X.t -> 'a1 tree -> 'a1 triple **)
  
  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, h) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })
  
  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)
  
  let concat m6 m7 =
    match m6 with
    | Leaf -> m7
    | Node (t0, k, e, t1, t2) ->
      (match m7 with
       | Leaf -> m6
       | Node (l2, x2, d2, r2, t3) ->
         let Pair (m2', xd) = remove_min l2 x2 d2 r2 in
         join m6 (fst xd) (snd xd) m2')
  
  (** val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list **)
  
  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, t0) ->
    elements_aux ((Pair (x, d))::(elements_aux acc r)) l
  
  (** val elements : 'a1 tree -> (key, 'a1) prod list **)
  
  let elements m6 =
    elements_aux [] m6
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
  
  let rec fold f0 m6 a =
    match m6 with
    | Leaf -> a
    | Node (l, x, d, r, t0) -> fold f0 r (f0 x d (fold f0 l a))
  
  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration
  
  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)
  
  let rec enumeration_rect f0 f1 = function
  | End -> f0
  | More (k, e0, t0, e1) -> f1 k e0 t0 e1 (enumeration_rect f0 f1 e1)
  
  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)
  
  let rec enumeration_rec f0 f1 = function
  | End -> f0
  | More (k, e0, t0, e1) -> f1 k e0 t0 e1 (enumeration_rec f0 f1 e1)
  
  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)
  
  let rec cons m6 e =
    match m6 with
    | Leaf -> e
    | Node (l, x, d, r, h) -> cons l (More (x, d, r, e))
  
  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)
  
  let equal_more cmp0 x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp0 d1 d2 then cont (cons r2 e3) else false
     | _ -> false)
  
  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)
  
  let rec equal_cont cmp0 m6 cont e2 =
    match m6 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, t0) ->
      equal_cont cmp0 l1 (equal_more cmp0 x1 d1 (equal_cont cmp0 r1 cont)) e2
  
  (** val equal_end : 'a1 enumeration -> bool **)
  
  let equal_end = function
  | End -> true
  | More (k, e, t0, e0) -> false
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)
  
  let equal cmp0 m6 m7 =
    equal_cont cmp0 m6 equal_end (cons m7 End)
  
  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)
  
  let rec map f0 = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f0 l), x, (f0 d), (map f0 r), h)
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)
  
  let rec mapi f0 = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f0 l), x, (f0 x d), (mapi f0 r), h)
  
  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)
  
  let rec map_option f0 = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) ->
    (match f0 x d with
     | Some d' -> join (map_option f0 l) x d' (map_option f0 r)
     | None -> concat (map_option f0 l) (map_option f0 r))
  
  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)
  
  let rec map2_opt f0 mapl mapr m6 m7 =
    match m6 with
    | Leaf -> mapr m7
    | Node (l1, x1, d1, r1, h1) ->
      (match m7 with
       | Leaf -> mapl m6
       | Node (t0, k, y, t1, t2) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m7 in
         (match f0 x1 d1 o2 with
          | Some e ->
            join (map2_opt f0 mapl mapr l1 l2') x1 e
              (map2_opt f0 mapl mapr r1 r2')
          | None ->
            concat (map2_opt f0 mapl mapr l1 l2')
              (map2_opt f0 mapl mapr r1 r2')))
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)
  
  let map2 f0 =
    map2_opt (fun x d o -> f0 (Some d) o)
      (map_option (fun x d -> f0 (Some d) None))
      (map_option (fun x d' -> f0 None (Some d')))
  
  module Proofs = 
   struct 
    module MX = Coq_OrderedTypeFacts(X)
    
    module PX = KeyOrderedType(X)
    
    module L = Raw(X)
    
    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    
    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)
    
    let rec coq_R_mem_rect x f0 f1 f2 f3 m6 b0 = function
    | R_mem_0 m7 -> f0 m7 __
    | R_mem_1 (m7, l, y, _x, r0, _x0, res, r1) ->
      f1 m7 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rect x f0 f1 f2 f3 l res r1)
    | R_mem_2 (m7, l, y, _x, r0, _x0) -> f2 m7 l y _x r0 _x0 __ __ __
    | R_mem_3 (m7, l, y, _x, r0, _x0, res, r1) ->
      f3 m7 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rect x f0 f1 f2 f3 r0 res r1)
    
    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)
    
    let rec coq_R_mem_rec x f0 f1 f2 f3 m6 b0 = function
    | R_mem_0 m7 -> f0 m7 __
    | R_mem_1 (m7, l, y, _x, r0, _x0, res, r1) ->
      f1 m7 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rec x f0 f1 f2 f3 l res r1)
    | R_mem_2 (m7, l, y, _x, r0, _x0) -> f2 m7 l y _x r0 _x0 __ __ __
    | R_mem_3 (m7, l, y, _x, r0, _x0, res, r1) ->
      f3 m7 l y _x r0 _x0 __ __ __ res r1
        (coq_R_mem_rec x f0 f1 f2 f3 r0 res r1)
    
    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    
    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)
    
    let rec coq_R_find_rect x f0 f1 f2 f3 m6 o = function
    | R_find_0 m7 -> f0 m7 __
    | R_find_1 (m7, l, y, d, r0, _x, res, r1) ->
      f1 m7 l y d r0 _x __ __ __ res r1
        (coq_R_find_rect x f0 f1 f2 f3 l res r1)
    | R_find_2 (m7, l, y, d, r0, _x) -> f2 m7 l y d r0 _x __ __ __
    | R_find_3 (m7, l, y, d, r0, _x, res, r1) ->
      f3 m7 l y d r0 _x __ __ __ res r1
        (coq_R_find_rect x f0 f1 f2 f3 r0 res r1)
    
    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)
    
    let rec coq_R_find_rec x f0 f1 f2 f3 m6 o = function
    | R_find_0 m7 -> f0 m7 __
    | R_find_1 (m7, l, y, d, r0, _x, res, r1) ->
      f1 m7 l y d r0 _x __ __ __ res r1
        (coq_R_find_rec x f0 f1 f2 f3 l res r1)
    | R_find_2 (m7, l, y, d, r0, _x) -> f2 m7 l y d r0 _x __ __ __
    | R_find_3 (m7, l, y, d, r0, _x, res, r1) ->
      f3 m7 l y d r0 _x __ __ __ res r1
        (coq_R_find_rec x f0 f1 f2 f3 r0 res r1)
    
    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
    
    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)
    
    let coq_R_bal_rect f0 f1 f2 f3 f4 f5 f6 f7 f8 l x d r t0 = function
    | R_bal_0 (x0, x1, x2, x3) -> f0 x0 x1 x2 x3 __ __ __
    | R_bal_1 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f1 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f2 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f3 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_4 (x0, x1, x2, x3) -> f4 x0 x1 x2 x3 __ __ __ __ __
    | R_bal_5 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f5 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_6 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f6 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f7 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13
        __
    | R_bal_8 (x0, x1, x2, x3) -> f8 x0 x1 x2 x3 __ __ __ __
    
    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)
    
    let coq_R_bal_rec f0 f1 f2 f3 f4 f5 f6 f7 f8 l x d r t0 = function
    | R_bal_0 (x0, x1, x2, x3) -> f0 x0 x1 x2 x3 __ __ __
    | R_bal_1 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f1 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_2 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f2 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_3 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f3 x0 x1 x2 x3 __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13 __
    | R_bal_4 (x0, x1, x2, x3) -> f4 x0 x1 x2 x3 __ __ __ __ __
    | R_bal_5 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f5 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __
    | R_bal_6 (x0, x1, x2, x3, x4, x5, x6, x7, x8) ->
      f6 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ __
    | R_bal_7 (x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) ->
      f7 x0 x1 x2 x3 __ __ __ __ x4 x5 x6 x7 x8 __ __ __ x9 x10 x11 x12 x13
        __
    | R_bal_8 (x0, x1, x2, x3) -> f8 x0 x1 x2 x3 __ __ __ __
    
    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    
    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)
    
    let rec coq_R_add_rect x d f0 f1 f2 f3 m6 t0 = function
    | R_add_0 m7 -> f0 m7 __
    | R_add_1 (m7, l, y, d', r0, h, res, r1) ->
      f1 m7 l y d' r0 h __ __ __ res r1
        (coq_R_add_rect x d f0 f1 f2 f3 l res r1)
    | R_add_2 (m7, l, y, d', r0, h) -> f2 m7 l y d' r0 h __ __ __
    | R_add_3 (m7, l, y, d', r0, h, res, r1) ->
      f3 m7 l y d' r0 h __ __ __ res r1
        (coq_R_add_rect x d f0 f1 f2 f3 r0 res r1)
    
    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)
    
    let rec coq_R_add_rec x d f0 f1 f2 f3 m6 t0 = function
    | R_add_0 m7 -> f0 m7 __
    | R_add_1 (m7, l, y, d', r0, h, res, r1) ->
      f1 m7 l y d' r0 h __ __ __ res r1
        (coq_R_add_rec x d f0 f1 f2 f3 l res r1)
    | R_add_2 (m7, l, y, d', r0, h) -> f2 m7 l y d' r0 h __ __ __
    | R_add_3 (m7, l, y, d', r0, h, res, r1) ->
      f3 m7 l y d' r0 h __ __ __ res r1
        (coq_R_add_rec x d f0 f1 f2 f3 r0 res r1)
    
    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree, (key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt tree * (key, 'elt) prod
    
    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 **)
    
    let rec coq_R_remove_min_rect f0 f1 l x d r p = function
    | R_remove_min_0 (l0, x0, d0, r1) -> f0 l0 x0 d0 r1 __
    | R_remove_min_1 (l0, x0, d0, r1, ll, lx, ld, lr, _x, res, r2, l', m6) ->
      f1 l0 x0 d0 r1 ll lx ld lr _x __ res r2
        (coq_R_remove_min_rect f0 f1 ll lx ld lr res r2) l' m6 __
    
    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 **)
    
    let rec coq_R_remove_min_rec f0 f1 l x d r p = function
    | R_remove_min_0 (l0, x0, d0, r1) -> f0 l0 x0 d0 r1 __
    | R_remove_min_1 (l0, x0, d0, r1, ll, lx, ld, lr, _x, res, r2, l', m6) ->
      f1 l0 x0 d0 r1 ll lx ld lr _x __ res r2
        (coq_R_remove_min_rec f0 f1 ll lx ld lr res r2) l' m6 __
    
    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key, 'elt) prod * key * 'elt
    
    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)
    
    let coq_R_merge_rect f0 f1 f2 s1 s2 t0 = function
    | R_merge_0 (x, x0) -> f0 x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f1 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f2 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __
    
    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)
    
    let coq_R_merge_rec f0 f1 f2 s1 s2 t0 = function
    | R_merge_0 (x, x0) -> f0 x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f1 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f2 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __
    
    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    
    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)
    
    let rec coq_R_remove_rect x f0 f1 f2 f3 m6 t0 = function
    | R_remove_0 m7 -> f0 m7 __
    | R_remove_1 (m7, l, y, d, r0, _x, res, r1) ->
      f1 m7 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rect x f0 f1 f2 f3 l res r1)
    | R_remove_2 (m7, l, y, d, r0, _x) -> f2 m7 l y d r0 _x __ __ __
    | R_remove_3 (m7, l, y, d, r0, _x, res, r1) ->
      f3 m7 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rect x f0 f1 f2 f3 r0 res r1)
    
    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)
    
    let rec coq_R_remove_rec x f0 f1 f2 f3 m6 t0 = function
    | R_remove_0 m7 -> f0 m7 __
    | R_remove_1 (m7, l, y, d, r0, _x, res, r1) ->
      f1 m7 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rec x f0 f1 f2 f3 l res r1)
    | R_remove_2 (m7, l, y, d, r0, _x) -> f2 m7 l y d r0 _x __ __ __
    | R_remove_3 (m7, l, y, d, r0, _x, res, r1) ->
      f3 m7 l y d r0 _x __ __ __ res r1
        (coq_R_remove_rec x f0 f1 f2 f3 r0 res r1)
    
    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key, 'elt) prod
    
    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2 **)
    
    let coq_R_concat_rect f0 f1 f2 m6 m7 t0 = function
    | R_concat_0 (x, x0) -> f0 x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f1 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __
    
    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_concat -> 'a2 **)
    
    let coq_R_concat_rec f0 f1 f2 m6 m7 t0 = function
    | R_concat_0 (x, x0) -> f0 x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f1 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __
    
    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    
    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)
    
    let rec coq_R_split_rect x f0 f1 f2 f3 m6 t0 = function
    | R_split_0 m7 -> f0 m7 __
    | R_split_1 (m7, l, y, d, r0, _x, res, r1, ll, o, rl) ->
      f1 m7 l y d r0 _x __ __ __ res r1
        (coq_R_split_rect x f0 f1 f2 f3 l res r1) ll o rl __
    | R_split_2 (m7, l, y, d, r0, _x) -> f2 m7 l y d r0 _x __ __ __
    | R_split_3 (m7, l, y, d, r0, _x, res, r1, rl, o, rr) ->
      f3 m7 l y d r0 _x __ __ __ res r1
        (coq_R_split_rect x f0 f1 f2 f3 r0 res r1) rl o rr __
    
    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)
    
    let rec coq_R_split_rec x f0 f1 f2 f3 m6 t0 = function
    | R_split_0 m7 -> f0 m7 __
    | R_split_1 (m7, l, y, d, r0, _x, res, r1, ll, o, rl) ->
      f1 m7 l y d r0 _x __ __ __ res r1
        (coq_R_split_rec x f0 f1 f2 f3 l res r1) ll o rl __
    | R_split_2 (m7, l, y, d, r0, _x) -> f2 m7 l y d r0 _x __ __ __
    | R_split_3 (m7, l, y, d, r0, _x, res, r1, rl, o, rr) ->
      f3 m7 l y d r0 _x __ __ __ res r1
        (coq_R_split_rec x f0 f1 f2 f3 r0 res r1) rl o rr __
    
    type ('elt, 'elt') coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt' * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
       * ('elt, 'elt') coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt' tree * ('elt, 'elt') coq_R_map_option * 'elt' tree
       * ('elt, 'elt') coq_R_map_option
    
    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)
    
    let rec coq_R_map_option_rect f0 f1 f2 f3 m6 t0 = function
    | R_map_option_0 m7 -> f1 m7 __
    | R_map_option_1 (m7, l, x, d, r0, _x, d', res0, r1, res, r2) ->
      f2 m7 l x d r0 _x __ d' __ res0 r1
        (coq_R_map_option_rect f0 f1 f2 f3 l res0 r1) res r2
        (coq_R_map_option_rect f0 f1 f2 f3 r0 res r2)
    | R_map_option_2 (m7, l, x, d, r0, _x, res0, r1, res, r2) ->
      f3 m7 l x d r0 _x __ __ res0 r1
        (coq_R_map_option_rect f0 f1 f2 f3 l res0 r1) res r2
        (coq_R_map_option_rect f0 f1 f2 f3 r0 res r2)
    
    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)
    
    let rec coq_R_map_option_rec f0 f1 f2 f3 m6 t0 = function
    | R_map_option_0 m7 -> f1 m7 __
    | R_map_option_1 (m7, l, x, d, r0, _x, d', res0, r1, res, r2) ->
      f2 m7 l x d r0 _x __ d' __ res0 r1
        (coq_R_map_option_rec f0 f1 f2 f3 l res0 r1) res r2
        (coq_R_map_option_rec f0 f1 f2 f3 r0 res r2)
    | R_map_option_2 (m7, l, x, d, r0, _x, res0, r1, res, r2) ->
      f3 m7 l x d r0 _x __ __ res0 r1
        (coq_R_map_option_rec f0 f1 f2 f3 l res0 r1) res r2
        (coq_R_map_option_rec f0 f1 f2 f3 r0 res r2)
    
    type ('elt, 'elt', 'elt'') coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'elt' tree
    | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt' tree * key * 'elt' * 'elt' tree * I.t
       * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt' tree * key * 'elt' * 'elt' tree * I.t
       * 'elt' tree * 'elt' option * 'elt' tree * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
       * ('elt, 'elt', 'elt'') coq_R_map2_opt
    
    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)
    
    let rec coq_R_map2_opt_rect f0 mapl mapr f1 f2 f3 f4 m6 m7 t0 = function
    | R_map2_opt_0 (m8, m9) -> f1 m8 m9 __
    | R_map2_opt_1 (m8, m9, l1, x1, d1, r1, _x) ->
      f2 m8 m9 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m8, m9, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, res0, r0, res, r2) ->
      f3 m8 m9 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        res0 r0 (coq_R_map2_opt_rect f0 mapl mapr f1 f2 f3 f4 l1 l2' res0 r0)
        res r2 (coq_R_map2_opt_rect f0 mapl mapr f1 f2 f3 f4 r1 r2' res r2)
    | R_map2_opt_3 (m8, m9, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', res0, r0, res, r2) ->
      f4 m8 m9 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ res0
        r0 (coq_R_map2_opt_rect f0 mapl mapr f1 f2 f3 f4 l1 l2' res0 r0) res
        r2 (coq_R_map2_opt_rect f0 mapl mapr f1 f2 f3 f4 r1 r2' res r2)
    
    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)
    
    let rec coq_R_map2_opt_rec f0 mapl mapr f1 f2 f3 f4 m6 m7 t0 = function
    | R_map2_opt_0 (m8, m9) -> f1 m8 m9 __
    | R_map2_opt_1 (m8, m9, l1, x1, d1, r1, _x) ->
      f2 m8 m9 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m8, m9, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, res0, r0, res, r2) ->
      f3 m8 m9 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        res0 r0 (coq_R_map2_opt_rec f0 mapl mapr f1 f2 f3 f4 l1 l2' res0 r0)
        res r2 (coq_R_map2_opt_rec f0 mapl mapr f1 f2 f3 f4 r1 r2' res r2)
    | R_map2_opt_3 (m8, m9, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', res0, r0, res, r2) ->
      f4 m8 m9 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ res0
        r0 (coq_R_map2_opt_rec f0 mapl mapr f1 f2 f3 f4 l1 l2' res0 r0) res
        r2 (coq_R_map2_opt_rec f0 mapl mapr f1 f2 f3 f4 r1 r2' res r2)
    
    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)
    
    let fold' f0 s =
      L.fold f0 (elements s)
    
    (** val flatten_e : 'a1 enumeration -> (key, 'a1) prod list **)
    
    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) ->
      (Pair (x, e0))::(app (elements t0) (flatten_e r))
   end
 end

module IntMake = 
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct 
  module E = X
  
  module Raw = Coq_Raw(I)(X)
  
  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)
  
  (** val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2 **)
  
  let bst_rect f0 b0 =
    f0 b0 __
  
  (** val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2 **)
  
  let bst_rec f0 b0 =
    f0 b0 __
  
  (** val this : 'a1 bst -> 'a1 Raw.tree **)
  
  let this b0 =
    b0
  
  type 'elt t = 'elt bst
  
  type key = E.t
  
  (** val empty : 'a1 t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : 'a1 t -> bool **)
  
  let is_empty m6 =
    Raw.is_empty (this m6)
  
  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)
  
  let add x e m6 =
    Raw.add x e (this m6)
  
  (** val remove : key -> 'a1 t -> 'a1 t **)
  
  let remove x m6 =
    Raw.remove x (this m6)
  
  (** val mem : key -> 'a1 t -> bool **)
  
  let mem x m6 =
    Raw.mem x (this m6)
  
  (** val find : key -> 'a1 t -> 'a1 option **)
  
  let find x m6 =
    Raw.find x (this m6)
  
  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let map f0 m6 =
    Raw.map f0 (this m6)
  
  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)
  
  let mapi f0 m6 =
    Raw.mapi f0 (this m6)
  
  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)
  
  let map2 f0 m6 m' =
    Raw.map2 f0 (this m6) (this m')
  
  (** val elements : 'a1 t -> (key, 'a1) prod list **)
  
  let elements m6 =
    Raw.elements (this m6)
  
  (** val cardinal : 'a1 t -> nat **)
  
  let cardinal m6 =
    Raw.cardinal (this m6)
  
  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)
  
  let fold f0 m6 i =
    Raw.fold f0 (this m6) i
  
  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)
  
  let equal cmp0 m6 m' =
    Raw.equal cmp0 (this m6) (this m')
 end

module Coq0_Make = 
 functor (X:Coq_OrderedType) ->
 IntMake(Z_as_Int)(X)

module WFacts_fun = 
 functor (E:DecidableType) ->
 functor (M:sig 
  type key = E.t
  
  type 'x t 
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val find : key -> 'a1 t -> 'a1 option
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct 
  (** val eqb : E.t -> E.t -> bool **)
  
  let eqb x y =
    if E.eq_dec x y then true else false
  
  (** val coq_In_dec : 'a1 M.t -> M.key -> bool **)
  
  let coq_In_dec =
    failwith "AXIOM TO BE REALIZED"
  
  (** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)
  
  let option_map f0 = function
  | Some a -> Some (f0 a)
  | None -> None
 end

module WFacts = 
 functor (M:WS) ->
 WFacts_fun(M.E)(M)

module Facts = WFacts

module WProperties_fun = 
 functor (E:DecidableType) ->
 functor (M:sig 
  type key = E.t
  
  type 'x t 
  
  val empty : 'a1 t
  
  val is_empty : 'a1 t -> bool
  
  val add : key -> 'a1 -> 'a1 t -> 'a1 t
  
  val find : key -> 'a1 t -> 'a1 option
  
  val remove : key -> 'a1 t -> 'a1 t
  
  val mem : key -> 'a1 t -> bool
  
  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
  
  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
  
  val elements : 'a1 t -> (key, 'a1) prod list
  
  val cardinal : 'a1 t -> nat
  
  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
  
  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct 
  module F = WFacts_fun(E)(M)
  
  (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3 **)
  
  let uncurry f0 p =
    f0 (fst p) (snd p)
  
  (** val of_list : (M.key, 'a1) prod list -> 'a1 M.t **)
  
  let of_list l =
    fold_right (uncurry M.add) M.empty l
  
  (** val to_list : 'a1 M.t -> (M.key, 'a1) prod list **)
  
  let to_list x =
    M.elements x
  
  (** val fold_rec :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> __ ->
      'a3) -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> 'a1 M.t -> __ -> __ -> __ ->
      'a3 -> 'a3) -> 'a3 **)
  
  let fold_rec =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rec_bis :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> ('a1 M.t -> 'a1 M.t
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t
      -> __ -> __ -> 'a3 -> 'a3) -> 'a3 **)
  
  let fold_rec_bis =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rec_nodep :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 M.t -> 'a3 -> (M.key -> 'a1
      -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)
  
  let fold_rec_nodep =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rec_weak :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 M.t -> 'a1 M.t -> 'a2 -> __
      -> 'a3 -> 'a3) -> 'a3 -> (M.key -> 'a1 -> 'a2 -> 'a1 M.t -> __ -> 'a3
      -> 'a3) -> 'a1 M.t -> 'a3 **)
  
  let fold_rec_weak =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rel :
      (M.key -> 'a1 -> 'a2 -> 'a2) -> (M.key -> 'a1 -> 'a3 -> 'a3) -> 'a2 ->
      'a3 -> 'a1 M.t -> 'a4 -> (M.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 ->
      'a4) -> 'a4 **)
  
  let fold_rel =
    failwith "AXIOM TO BE REALIZED"
  
  (** val map_induction :
      ('a1 M.t -> __ -> 'a2) -> ('a1 M.t -> 'a1 M.t -> 'a2 -> M.key -> 'a1 ->
      __ -> __ -> 'a2) -> 'a1 M.t -> 'a2 **)
  
  let map_induction =
    failwith "AXIOM TO BE REALIZED"
  
  (** val map_induction_bis :
      ('a1 M.t -> 'a1 M.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.key -> 'a1 -> 'a1
      M.t -> __ -> 'a2 -> 'a2) -> 'a1 M.t -> 'a2 **)
  
  let map_induction_bis =
    failwith "AXIOM TO BE REALIZED"
  
  (** val cardinal_inv_2 : 'a1 M.t -> nat -> (M.key, 'a1) prod **)
  
  let cardinal_inv_2 =
    failwith "AXIOM TO BE REALIZED"
  
  (** val cardinal_inv_2b : 'a1 M.t -> (M.key, 'a1) prod **)
  
  let cardinal_inv_2b =
    failwith "AXIOM TO BE REALIZED"
  
  (** val filter : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t **)
  
  let filter f0 m6 =
    M.fold (fun k e m7 -> if f0 k e then M.add k e m7 else m7) m6 M.empty
  
  (** val for_all : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool **)
  
  let for_all f0 m6 =
    M.fold (fun k e b0 -> if f0 k e then b0 else false) m6 true
  
  (** val exists_ : (M.key -> 'a1 -> bool) -> 'a1 M.t -> bool **)
  
  let exists_ f0 m6 =
    M.fold (fun k e b0 -> if f0 k e then true else b0) m6 false
  
  (** val partition :
      (M.key -> 'a1 -> bool) -> 'a1 M.t -> ('a1 M.t, 'a1 M.t) prod **)
  
  let partition f0 m6 =
    Pair ((filter f0 m6), (filter (fun k e -> negb (f0 k e)) m6))
  
  (** val update : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)
  
  let update m6 m7 =
    M.fold M.add m7 m6
  
  (** val restrict : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)
  
  let restrict m6 m7 =
    filter (fun k x -> M.mem k m7) m6
  
  (** val diff : 'a1 M.t -> 'a1 M.t -> 'a1 M.t **)
  
  let diff m6 m7 =
    filter (fun k x -> negb (M.mem k m7)) m6
  
  (** val coq_Partition_In :
      'a1 M.t -> 'a1 M.t -> 'a1 M.t -> M.key -> bool **)
  
  let coq_Partition_In m6 m7 m8 k =
    F.coq_In_dec m7 k
  
  (** val update_dec : 'a1 M.t -> 'a1 M.t -> M.key -> 'a1 -> bool **)
  
  let update_dec m6 m' k e =
    F.coq_In_dec m' k
  
  (** val filter_dom : (M.key -> bool) -> 'a1 M.t -> 'a1 M.t **)
  
  let filter_dom f0 =
    filter (fun k x -> f0 k)
  
  (** val filter_range : ('a1 -> bool) -> 'a1 M.t -> 'a1 M.t **)
  
  let filter_range f0 =
    filter (fun x -> f0)
  
  (** val for_all_dom : (M.key -> bool) -> 'a1 M.t -> bool **)
  
  let for_all_dom f0 =
    for_all (fun k x -> f0 k)
  
  (** val for_all_range : ('a1 -> bool) -> 'a1 M.t -> bool **)
  
  let for_all_range f0 =
    for_all (fun x -> f0)
  
  (** val exists_dom : (M.key -> bool) -> 'a1 M.t -> bool **)
  
  let exists_dom f0 =
    exists_ (fun k x -> f0 k)
  
  (** val exists_range : ('a1 -> bool) -> 'a1 M.t -> bool **)
  
  let exists_range f0 =
    exists_ (fun x -> f0)
  
  (** val partition_dom :
      (M.key -> bool) -> 'a1 M.t -> ('a1 M.t, 'a1 M.t) prod **)
  
  let partition_dom f0 =
    partition (fun k x -> f0 k)
  
  (** val partition_range :
      ('a1 -> bool) -> 'a1 M.t -> ('a1 M.t, 'a1 M.t) prod **)
  
  let partition_range f0 =
    partition (fun x -> f0)
 end

module WProperties = 
 functor (M:WS) ->
 WProperties_fun(M.E)(M)

module Properties = WProperties

module Ordered_nat = 
 struct 
  type t = nat
  
  (** val compare : t -> t -> nat compare0 **)
  
  let compare x y =
    match nat_compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT
  
  (** val eq_dec : nat -> nat -> bool **)
  
  let eq_dec x y =
    if beq_nat x y then true else false
 end

module IntMap = Coq0_Make(Ordered_nat)

module MoreFMapFacts = 
 functor (FM:WS) ->
 struct 
  module PROPS = WProperties_fun(FM.E)(FM)
  
  module FACTS = WFacts_fun(FM.E)(FM)
  
  (** val union : 'a1 FM.t -> 'a1 FM.t -> 'a1 FM.t **)
  
  let union x =
    FM.fold (fun k v a -> FM.add k v a) x
 end

module Coq1_Make = 
 functor (FM:WS) ->
 struct 
  module FACTS = WFacts_fun(FM.E)(FM)
  
  module PROPS = WProperties_fun(FM.E)(FM)
  
  module MFACTS = MoreFMapFacts(FM)
  
  type 't mmap = 't list FM.t
  
  (** val empty : 'a1 mmap **)
  
  let empty =
    FM.empty
  
  (** val mmap_add : FM.key -> 'a1 -> 'a1 mmap -> 'a1 mmap **)
  
  let mmap_add k v m6 =
    match FM.find k m6 with
    | Some v' -> FM.add k (v::v') m6
    | None -> FM.add k (v::[]) m6
  
  (** val mmap_extend : FM.key -> 'a1 list -> 'a1 mmap -> 'a1 mmap **)
  
  let mmap_extend k v m6 =
    match FM.find k m6 with
    | Some v' -> FM.add k (app v v') m6
    | None -> FM.add k v m6
  
  (** val mmap_join : 'a1 mmap -> 'a1 mmap -> 'a1 mmap **)
  
  let mmap_join x =
    FM.fold mmap_extend x
  
  (** val mmap_map : ('a1 -> 'a2) -> 'a1 mmap -> 'a2 mmap **)
  
  let mmap_map f0 =
    FM.map (map f0)
  
  (** val mmap_mapi : (FM.key -> 'a1 -> 'a2) -> 'a1 mmap -> 'a2 mmap **)
  
  let mmap_mapi f0 =
    FM.mapi (fun k -> map (f0 k))
 end

module FM = IntMap

module MM = Coq1_Make(FM)

module type SepHeap = 
 sig 
  module SE : 
   SepExpr
  
  type coq_SHeap = { impures : exprs MM.mmap; pures : expr list;
                     other : (tvarD, tvarD) SE.ST.hprop list }
  
  val coq_SHeap_rect :
    type0 list -> tvar -> tvar -> (exprs MM.mmap -> expr list -> (tvarD,
    tvarD) SE.ST.hprop list -> 'a1) -> coq_SHeap -> 'a1
  
  val coq_SHeap_rec :
    type0 list -> tvar -> tvar -> (exprs MM.mmap -> expr list -> (tvarD,
    tvarD) SE.ST.hprop list -> 'a1) -> coq_SHeap -> 'a1
  
  val impures : type0 list -> tvar -> tvar -> coq_SHeap -> exprs MM.mmap
  
  val pures : type0 list -> tvar -> tvar -> coq_SHeap -> expr list
  
  val other :
    type0 list -> tvar -> tvar -> coq_SHeap -> (tvarD, tvarD) SE.ST.hprop
    list
  
  val coq_WellTyped_sheap :
    type0 list -> tvar -> tvar -> tfunctions -> SE.tpredicates -> tenv ->
    tenv -> coq_SHeap -> bool
  
  val coq_WellTyped_impures :
    type0 list -> tfunctions -> SE.tpredicates -> tenv -> tenv -> exprs
    MM.mmap -> bool
  
  val sheapD : type0 list -> tvar -> tvar -> coq_SHeap -> SE.sexpr
  
  val coq_SHeap_empty : type0 list -> tvar -> tvar -> coq_SHeap
  
  val star_SHeap :
    type0 list -> tvar -> tvar -> coq_SHeap -> coq_SHeap -> coq_SHeap
  
  val liftSHeap :
    type0 list -> tvar -> tvar -> nat -> nat -> nat -> nat -> coq_SHeap ->
    coq_SHeap
  
  val applySHeap :
    type0 list -> tvar -> tvar -> (expr -> expr) -> coq_SHeap -> coq_SHeap
  
  val hash :
    type0 list -> tvar -> tvar -> SE.sexpr -> (variables, coq_SHeap) prod
  
  val impuresD : type0 list -> tvar -> tvar -> exprs MM.mmap -> SE.sexpr
  
  val starred :
    type0 list -> tvar -> tvar -> ('a1 -> SE.sexpr) -> 'a1 list -> SE.sexpr
    -> SE.sexpr
 end

module Coq2_Make = 
 functor (SE__1:SepExpr) ->
 struct 
  module SE = SE__1
  
  module ST = SE__1.ST
  
  module SE_FACTS = SepExprFacts(SE__1)
  
  type coq_SHeap = { impures : exprs MM.mmap; pures : expr list;
                     other : (tvarD, tvarD) ST.hprop list }
  
  (** val coq_SHeap_rect :
      type0 list -> tvar -> tvar -> (exprs MM.mmap -> expr list -> (tvarD,
      tvarD) ST.hprop list -> 'a1) -> coq_SHeap -> 'a1 **)
  
  let coq_SHeap_rect types4 pcType stateType f0 s =
    let { impures = x; pures = x0; other = x1 } = s in f0 x x0 x1
  
  (** val coq_SHeap_rec :
      type0 list -> tvar -> tvar -> (exprs MM.mmap -> expr list -> (tvarD,
      tvarD) ST.hprop list -> 'a1) -> coq_SHeap -> 'a1 **)
  
  let coq_SHeap_rec types4 pcType stateType f0 s =
    let { impures = x; pures = x0; other = x1 } = s in f0 x x0 x1
  
  (** val impures :
      type0 list -> tvar -> tvar -> coq_SHeap -> exprs MM.mmap **)
  
  let impures types4 pcType stateType s =
    s.impures
  
  (** val pures : type0 list -> tvar -> tvar -> coq_SHeap -> expr list **)
  
  let pures types4 pcType stateType s =
    s.pures
  
  (** val other :
      type0 list -> tvar -> tvar -> coq_SHeap -> (tvarD, tvarD) ST.hprop list **)
  
  let other types4 pcType stateType s =
    s.other
  
  (** val coq_SHeap_empty : type0 list -> tvar -> tvar -> coq_SHeap **)
  
  let coq_SHeap_empty types4 pcType stateType =
    { impures = MM.empty; pures = []; other = [] }
  
  (** val liftSHeap :
      type0 list -> tvar -> tvar -> nat -> nat -> nat -> nat -> coq_SHeap ->
      coq_SHeap **)
  
  let liftSHeap types4 pcType stateType ua ub a b0 s =
    { impures =
      (MM.mmap_map (map (liftExpr types4 ua ub a b0))
        (impures types4 pcType stateType s)); pures =
      (map (liftExpr types4 ua ub a b0) (pures types4 pcType stateType s));
      other = (other types4 pcType stateType s) }
  
  (** val star_SHeap :
      type0 list -> tvar -> tvar -> coq_SHeap -> coq_SHeap -> coq_SHeap **)
  
  let star_SHeap types4 pcType stateType l r =
    { impures =
      (MM.mmap_join (impures types4 pcType stateType l)
        (impures types4 pcType stateType r)); pures =
      (app (pures types4 pcType stateType l)
        (pures types4 pcType stateType r)); other =
      (app (other types4 pcType stateType l)
        (other types4 pcType stateType r)) }
  
  (** val hash :
      type0 list -> tvar -> tvar -> SE__1.sexpr -> (variables, coq_SHeap)
      prod **)
  
  let rec hash types4 pcType stateType = function
  | SE__1.Emp -> Pair ([], (coq_SHeap_empty types4 pcType stateType))
  | SE__1.Inj p ->
    Pair ([], { impures = MM.empty; pures = (p::[]); other = [] })
  | SE__1.Star (l, r) ->
    let Pair (vl, hl) = hash types4 pcType stateType l in
    let Pair (vr, hr) = hash types4 pcType stateType r in
    let nr = length vr in
    Pair ((app vl vr),
    (star_SHeap types4 pcType stateType
      (liftSHeap types4 pcType stateType O O O nr hl)
      (liftSHeap types4 pcType stateType O O nr (length vl) hr)))
  | SE__1.Exists (t0, b0) ->
    let Pair (v, b1) = hash types4 pcType stateType b0 in Pair ((t0::v), b1)
  | SE__1.Func (f0, a) ->
    Pair ([], { impures = (MM.mmap_add f0 a MM.empty); pures = []; other =
      [] })
  | SE__1.Const c ->
    Pair ([], { impures = MM.empty; pures = []; other = (c::[]) })
  
  (** val starred :
      type0 list -> tvar -> tvar -> ('a1 -> SE__1.sexpr) -> 'a1 list ->
      SE__1.sexpr -> SE__1.sexpr **)
  
  let starred types4 pcType stateType f0 ls base =
    fold_right (fun x a ->
      match a with
      | SE__1.Emp -> f0 x
      | _ -> SE__1.Star ((f0 x), a)) base ls
  
  (** val sheapD : type0 list -> tvar -> tvar -> coq_SHeap -> SE__1.sexpr **)
  
  let sheapD types4 pcType stateType h =
    let a =
      starred types4 pcType stateType (fun x -> SE__1.Const x)
        (other types4 pcType stateType h) SE__1.Emp
    in
    let a0 =
      starred types4 pcType stateType (fun x -> SE__1.Inj x)
        (pures types4 pcType stateType h) a
    in
    FM.fold (fun k ->
      starred types4 pcType stateType (fun x -> SE__1.Func (k, x)))
      (impures types4 pcType stateType h) a0
  
  (** val coq_WellTyped_impures :
      type0 list -> tfunctions -> SE__1.tpredicates -> tenv -> tenv -> exprs
      MM.mmap -> bool **)
  
  let coq_WellTyped_impures types4 tf tp tU tG imps =
    FM.fold (fun p argss acc ->
      if acc
      then (match argss with
            | [] -> true
            | y::l ->
              (match nth_error tp p with
               | Some ts ->
                 allb (fun args ->
                   all2 (is_well_typed types4 tf tU tG) args ts) argss
               | None -> false))
      else false) imps true
  
  (** val coq_WellTyped_sheap :
      type0 list -> tvar -> tvar -> tfunctions -> SE__1.tpredicates -> tenv
      -> tenv -> coq_SHeap -> bool **)
  
  let coq_WellTyped_sheap types4 pcType stateType tf tp tU tG h =
    if coq_WellTyped_impures types4 tf tp tU tG
         (impures types4 pcType stateType h)
    then allb (fun e -> is_well_typed types4 tf tU tG e TvProp)
           (pures types4 pcType stateType h)
    else false
  
  (** val sheapD' :
      type0 list -> tvar -> tvar -> coq_SHeap -> SE__1.sexpr **)
  
  let sheapD' types4 pcType stateType h =
    SE__1.Star
      ((FM.fold (fun k ->
         starred types4 pcType stateType (fun x -> SE__1.Func (k, x)))
         (impures types4 pcType stateType h) SE__1.Emp), (SE__1.Star
      ((starred types4 pcType stateType (fun x -> SE__1.Inj x)
         (pures types4 pcType stateType h) SE__1.Emp),
      (starred types4 pcType stateType (fun x -> SE__1.Const x)
        (other types4 pcType stateType h) SE__1.Emp))))
  
  (** val impuresD :
      type0 list -> tvar -> tvar -> exprs MM.mmap -> SE__1.sexpr **)
  
  let impuresD types4 pcType stateType imp =
    FM.fold (fun k ls acc -> SE__1.Star
      ((starred types4 pcType stateType (fun x -> SE__1.Func (k, x)) ls
         SE__1.Emp), acc)) imp SE__1.Emp
  
  (** val internal_True_rew : 'a1 -> 'a1 **)
  
  let internal_True_rew f0 =
    f0
  
  (** val applySHeap :
      type0 list -> tvar -> tvar -> (expr -> expr) -> coq_SHeap -> coq_SHeap **)
  
  let applySHeap types4 pcType stateType f0 sh =
    { impures = (MM.mmap_map (map f0) (impures types4 pcType stateType sh));
      pures = (map f0 (pures types4 pcType stateType sh)); other =
      (other types4 pcType stateType sh) }
 end

module SepHeapFacts = 
 functor (SH:SepHeap) ->
 struct 
  module SEP_FACTS = SepExprFacts(SH.SE)
  
  (** val sheapSubstU :
      type0 list -> tvar -> tvar -> nat -> nat -> nat -> SH.coq_SHeap ->
      SH.coq_SHeap **)
  
  let sheapSubstU types4 pcT stT a b0 c =
    SH.applySHeap types4 pcT stT (exprSubstU types4 a b0 c)
 end

(** val allWordsUpto : nat -> nat -> word list **)

let rec allWordsUpto width = function
| O -> []
| S init' -> (natToWord width init')::(allWordsUpto width init')

(** val allWords_def : nat -> word list **)

let allWords_def width =
  allWordsUpto width (pow2 width)

(** val memoryInUpto :
    nat -> nat -> (word -> b option) -> (word, b option) hlist **)

let rec memoryInUpto width init m6 =
  match init with
  | O -> HNil
  | S init' ->
    let w0 = natToWord width init' in
    let v = m6 w0 in
    HCons ((natToWord width init'), (allWordsUpto width init'), v,
    (memoryInUpto width init' m6))

(** val memoryIn_def :
    nat -> (word -> b option) -> (word, b option) hlist **)

let memoryIn_def width =
  memoryInUpto width (pow2 width)

module type ALL_WORDS = 
 sig 
  val allWords : nat -> word list
  
  val memoryIn : nat -> (word -> b option) -> (word, b option) hlist
 end

module AllWords = 
 struct 
  (** val allWords : nat -> word list **)
  
  let allWords =
    fun _ -> []
  
  (** val memoryIn : nat -> (word -> b option) -> (word, b option) hlist **)
  
  let memoryIn =
    memoryIn_def
 end

module BedrockHeap = 
 struct 
  type addr = w
  
  type mem = mem0
  
  (** val mem_get : mem0 -> w -> b option **)
  
  let mem_get =
    readByte
  
  (** val mem_set : mem0 -> w -> b -> mem0 option **)
  
  let mem_set =
    writeByte
  
  (** val footprint_w :
      addr -> (((addr, addr) prod, addr) prod, addr) prod **)
  
  let footprint_w p =
    Pair ((Pair ((Pair (p,
      (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) p
        (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))) (S O))))),
      (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) p
        (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))) (S (S O)))))),
      (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) p
        (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))) (S (S (S O))))))
  
  (** val addr_dec : word -> word -> bool **)
  
  let addr_dec =
    weq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
  
  (** val all_addr : word list **)
  
  let all_addr =
    AllWords.allWords (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))
 end

module ST = Make(BedrockHeap)

(** val memoryIn0 : mem0 -> ST.HT.smem **)

let memoryIn0 =
  ST.HT.memoryIn

type hpropB = (w, (ST.settings, state) prod) ST.hprop

type hProp = hpropB

(** val empB : __ list -> hpropB **)

let empB sos =
  ST.emp sos

(** val injB : __ list -> hpropB **)

let injB sos =
  ST.inj sos (Inj sos)

(** val ptsto8 : __ list -> w -> b -> hpropB **)

let ptsto8 sos =
  ST.hptsto sos

(** val ptsto32 : __ list -> w -> w -> hpropB **)

let ptsto32 sos a v stn sm =
  Inj sos

(** val starB : __ list -> hpropB -> hpropB -> hpropB **)

let starB sos =
  ST.star sos

(** val ptsto32m : __ list -> w -> nat -> w list -> hpropB **)

let rec ptsto32m sos a offset = function
| [] -> empB sos
| v::vs' ->
  (match vs' with
   | [] ->
     ptsto32 sos
       (match offset with
        | O -> a
        | S n0 ->
          wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) a
            (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) offset)) v
   | w0::l ->
     starB sos
       (ptsto32 sos
         (match offset with
          | O -> a
          | S n0 ->
            wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) a
              (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))) offset)) v)
       (ptsto32m sos a (plus (S (S (S (S O)))) offset) vs'))

(** val exB : __ list -> ('a1 -> hpropB) -> hpropB **)

let exB sos p =
  ST.ex sos p

(** val hvarB :
    __ list -> ((ST.settings, ST.HT.smem) prod -> (w, (ST.settings, state)
    prod) propX) -> hpropB **)

let hvarB sos x stn sm =
  x (Pair (stn, sm))

(** val lift1 : __ list -> hpropB -> hpropB **)

let lift1 sos p a b0 =
  Lift (sos, (p a b0))

(** val lift : __ list -> hProp -> hpropB **)

let rec lift sos p =
  match sos with
  | [] -> p
  | _::sos' -> lift1 sos' (lift sos' p)

(** val sepFormula_def :
    __ list -> hpropB -> (ST.settings, state) prod -> (w, (ST.settings,
    state) prod) propX **)

let sepFormula_def sos p st0 =
  p (fst st0) (memoryIn0 (snd st0).mem1)

module type SEP_FORMULA = 
 sig 
  val sepFormula :
    __ list -> hpropB -> (ST.settings, state) prod -> (w, (ST.settings,
    state) prod) propX
 end

module SepFormula = 
 struct 
  (** val sepFormula :
      __ list -> hpropB -> (ST.settings, state) prod -> (w, (ST.settings,
      state) prod) propX **)
  
  let sepFormula =
    sepFormula_def
 end

module SEP = Coq_Make(ST)

module SH = Coq2_Make(SEP)

(** val string_lt : char list -> char list -> bool **)

let rec string_lt s1 s2 =
  match s1 with
  | [] ->
    (match s2 with
     | [] -> false
     | a::s -> true)
  | a1::s1' ->
    (match s2 with
     | [] -> false
     | a2::s2' ->
       (match N.compare (n_of_ascii a1) (n_of_ascii a2) with
        | Eq -> string_lt s1' s2'
        | Lt -> true
        | Gt -> false))

(** val label'_lt : label' -> label' -> bool **)

let label'_lt l1 l2 =
  match l1 with
  | Global s1 ->
    (match l2 with
     | Global s2 -> string_lt s1 s2
     | Local n0 -> true)
  | Local n1 ->
    (match l2 with
     | Global s -> false
     | Local n2 ->
       (match N.compare n1 n2 with
        | Lt -> true
        | _ -> false))

(** val label'_eq : label' -> label' -> bool **)

let label'_eq x y =
  match x with
  | Global x0 ->
    (match y with
     | Global s0 -> string_dec x0 s0
     | Local n0 -> false)
  | Local x0 ->
    (match y with
     | Global s -> false
     | Local n0 -> N.eq_dec x0 n0)

module LabelKey = 
 struct 
  type t = label
  
  (** val compare' : t -> t -> comparison **)
  
  let compare' x y =
    if string_lt (fst x) (fst y)
    then Lt
    else if string_dec (fst x) (fst y)
         then if label'_lt (snd x) (snd y)
              then Lt
              else if label'_eq (snd x) (snd y) then Eq else Gt
         else Gt
  
  (** val compare : t -> t -> label compare0 **)
  
  let compare x y =
    match compare' x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    if string_dec (fst x) (fst y) then label'_eq (snd x) (snd y) else false
 end

module LabelMap = Coq0_Make(LabelKey)

module MakeListOrdering = 
 functor (O:OrderedType) ->
 struct 
  module MO = OrderedTypeFacts(O)
 end

module MakeRaw = 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct 
  type elt = X.t
  
  type tree =
  | Leaf
  | Node of I.t * tree * X.t * tree
  
  (** val empty : tree **)
  
  let empty =
    Leaf
  
  (** val is_empty : tree -> bool **)
  
  let is_empty = function
  | Leaf -> true
  | Node (t1, t2, t3, t4) -> false
  
  (** val mem : X.t -> tree -> bool **)
  
  let rec mem x = function
  | Leaf -> false
  | Node (t1, l, k, r) ->
    (match X.compare x k with
     | Eq -> true
     | Lt -> mem x l
     | Gt -> mem x r)
  
  (** val min_elt : tree -> elt option **)
  
  let rec min_elt = function
  | Leaf -> None
  | Node (t1, l, x, r) ->
    (match l with
     | Leaf -> Some x
     | Node (t2, t3, t4, t5) -> min_elt l)
  
  (** val max_elt : tree -> elt option **)
  
  let rec max_elt = function
  | Leaf -> None
  | Node (t1, l, x, r) ->
    (match r with
     | Leaf -> Some x
     | Node (t2, t3, t4, t5) -> max_elt r)
  
  (** val choose : tree -> elt option **)
  
  let choose =
    min_elt
  
  (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)
  
  let rec fold f0 t0 base =
    match t0 with
    | Leaf -> base
    | Node (t1, l, x, r) -> fold f0 r (f0 x (fold f0 l base))
  
  (** val elements_aux : X.t list -> tree -> X.t list **)
  
  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (t0, l, x, r) -> elements_aux (x::(elements_aux acc r)) l
  
  (** val elements : tree -> X.t list **)
  
  let elements =
    elements_aux []
  
  (** val rev_elements_aux : X.t list -> tree -> X.t list **)
  
  let rec rev_elements_aux acc = function
  | Leaf -> acc
  | Node (t0, l, x, r) -> rev_elements_aux (x::(rev_elements_aux acc l)) r
  
  (** val rev_elements : tree -> X.t list **)
  
  let rev_elements =
    rev_elements_aux []
  
  (** val cardinal : tree -> nat **)
  
  let rec cardinal = function
  | Leaf -> O
  | Node (t0, l, t1, r) -> S (plus (cardinal l) (cardinal r))
  
  (** val maxdepth : tree -> nat **)
  
  let rec maxdepth = function
  | Leaf -> O
  | Node (t0, l, t1, r) -> S (max (maxdepth l) (maxdepth r))
  
  (** val mindepth : tree -> nat **)
  
  let rec mindepth = function
  | Leaf -> O
  | Node (t0, l, t1, r) -> S (min (mindepth l) (mindepth r))
  
  (** val for_all : (elt -> bool) -> tree -> bool **)
  
  let rec for_all f0 = function
  | Leaf -> true
  | Node (t0, l, x, r) ->
    if if f0 x then for_all f0 l else false then for_all f0 r else false
  
  (** val exists_ : (elt -> bool) -> tree -> bool **)
  
  let rec exists_ f0 = function
  | Leaf -> false
  | Node (t0, l, x, r) ->
    if if f0 x then true else exists_ f0 l then true else exists_ f0 r
  
  type enumeration =
  | End
  | More of elt * tree * enumeration
  
  (** val cons : tree -> enumeration -> enumeration **)
  
  let rec cons s e =
    match s with
    | Leaf -> e
    | Node (t0, l, x, r) -> cons l (More (x, r, e))
  
  (** val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison **)
  
  let compare_more x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match X.compare x1 x2 with
     | Eq -> cont (cons r2 e3)
     | x -> x)
  
  (** val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison **)
  
  let rec compare_cont s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (t0, l1, x1, r1) ->
      compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
  
  (** val compare_end : enumeration -> comparison **)
  
  let compare_end = function
  | End -> Eq
  | More (e, t0, e0) -> Lt
  
  (** val compare : tree -> tree -> comparison **)
  
  let compare s1 s2 =
    compare_cont s1 compare_end (cons s2 End)
  
  (** val equal : tree -> tree -> bool **)
  
  let equal s1 s2 =
    match compare s1 s2 with
    | Eq -> true
    | _ -> false
  
  (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)
  
  let rec subsetl subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (t0, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl subset_l1 x1 l2
     | Gt -> if mem x1 r2 then subset_l1 s2 else false)
  
  (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)
  
  let rec subsetr subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (t0, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr subset_r1 x1 r2)
  
  (** val subset : tree -> tree -> bool **)
  
  let rec subset s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (t0, l1, x1, r1) ->
      (match s2 with
       | Leaf -> false
       | Node (t1, l2, x2, r2) ->
         (match X.compare x1 x2 with
          | Eq -> if subset l1 l2 then subset r1 r2 else false
          | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
          | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))
  
  type t = tree
  
  (** val height : t -> I.t **)
  
  let height = function
  | Leaf -> I._0
  | Node (h, t0, t1, t2) -> h
  
  (** val singleton : X.t -> tree **)
  
  let singleton x =
    Node (I._1, Leaf, x, Leaf)
  
  (** val create : t -> X.t -> t -> tree **)
  
  let create l x r =
    Node ((I.plus (I.max (height l) (height r)) I._1), l, x, r)
  
  (** val assert_false : t -> X.t -> t -> tree **)
  
  let assert_false =
    create
  
  (** val bal : t -> X.t -> t -> tree **)
  
  let bal l x r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.plus hr I._2)
    then (match l with
          | Leaf -> assert_false l x r
          | Node (t0, ll, lx, lr) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx (create lr x r)
            else (match lr with
                  | Leaf -> assert_false l x r
                  | Node (t1, lrl, lrx, lrr) ->
                    create (create ll lx lrl) lrx (create lrr x r)))
    else if I.gt_le_dec hr (I.plus hl I._2)
         then (match r with
               | Leaf -> assert_false l x r
               | Node (t0, rl, rx, rr) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false l x r
                       | Node (t1, rll, rlx, rlr) ->
                         create (create l x rll) rlx (create rlr rx rr)))
         else create l x r
  
  (** val add : X.t -> tree -> tree **)
  
  let rec add x = function
  | Leaf -> Node (I._1, Leaf, x, Leaf)
  | Node (h, l, y, r) ->
    (match X.compare x y with
     | Eq -> Node (h, l, y, r)
     | Lt -> bal (add x l) y r
     | Gt -> bal l y (add x r))
  
  (** val join : tree -> elt -> t -> t **)
  
  let rec join l = match l with
  | Leaf -> add
  | Node (lh, ll, lx, lr) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add x l
      | Node (rh, rl, rx, rr) ->
        if I.gt_le_dec lh (I.plus rh I._2)
        then bal ll lx (join lr x r)
        else if I.gt_le_dec rh (I.plus lh I._2)
             then bal (join_aux rl) rx rr
             else create l x r
      in join_aux)
  
  (** val remove_min : tree -> elt -> t -> (t, elt) prod **)
  
  let rec remove_min l x r =
    match l with
    | Leaf -> Pair (r, x)
    | Node (lh, ll, lx, lr) ->
      let Pair (l', m6) = remove_min ll lx lr in Pair ((bal l' x r), m6)
  
  (** val merge : tree -> tree -> tree **)
  
  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, t1, t2, t3) ->
      (match s2 with
       | Leaf -> s1
       | Node (t4, l2, x2, r2) ->
         let Pair (s2', m6) = remove_min l2 x2 r2 in bal s1 m6 s2')
  
  (** val remove : X.t -> tree -> tree **)
  
  let rec remove x = function
  | Leaf -> Leaf
  | Node (t0, l, y, r) ->
    (match X.compare x y with
     | Eq -> merge l r
     | Lt -> bal (remove x l) y r
     | Gt -> bal l y (remove x r))
  
  (** val concat : tree -> tree -> tree **)
  
  let concat s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, t1, t2, t3) ->
      (match s2 with
       | Leaf -> s1
       | Node (t4, l2, x2, r2) ->
         let Pair (s2', m6) = remove_min l2 x2 r2 in join s1 m6 s2')
  
  type triple = { t_left : t; t_in : bool; t_right : t }
  
  (** val t_left : triple -> t **)
  
  let t_left t0 =
    t0.t_left
  
  (** val t_in : triple -> bool **)
  
  let t_in t0 =
    t0.t_in
  
  (** val t_right : triple -> t **)
  
  let t_right t0 =
    t0.t_right
  
  (** val split : X.t -> tree -> triple **)
  
  let rec split x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (t0, l, y, r) ->
    (match X.compare x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b0; t_right = rl } = split x l in
       { t_left = ll; t_in = b0; t_right = (join rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b0; t_right = rr } = split x r in
       { t_left = (join l y rl); t_in = b0; t_right = rr })
  
  (** val inter : tree -> tree -> tree **)
  
  let rec inter s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (t0, l1, x1, r1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (t1, t2, t3, t4) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then join (inter l1 l2') x1 (inter r1 r2')
         else concat (inter l1 l2') (inter r1 r2'))
  
  (** val diff : tree -> tree -> tree **)
  
  let rec diff s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (t0, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t1, t2, t3, t4) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then concat (diff l1 l2') (diff r1 r2')
         else join (diff l1 l2') x1 (diff r1 r2'))
  
  (** val union : tree -> tree -> tree **)
  
  let rec union s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (t0, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (t1, t2, t3, t4) ->
         let { t_left = l2'; t_in = x; t_right = r2' } = split x1 s2 in
         join (union l1 l2') x1 (union r1 r2'))
  
  (** val filter : (elt -> bool) -> tree -> tree **)
  
  let rec filter f0 = function
  | Leaf -> Leaf
  | Node (t0, l, x, r) ->
    let l' = filter f0 l in
    let r' = filter f0 r in if f0 x then join l' x r' else concat l' r'
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let rec partition f0 = function
  | Leaf -> Pair (Leaf, Leaf)
  | Node (t0, l, x, r) ->
    let Pair (l1, l2) = partition f0 l in
    let Pair (r1, r2) = partition f0 r in
    if f0 x
    then Pair ((join l1 x r1), (concat l2 r2))
    else Pair ((concat l1 r1), (join l2 x r2))
  
  (** val ltb_tree : X.t -> tree -> bool **)
  
  let rec ltb_tree x = function
  | Leaf -> true
  | Node (t0, l, y, r) ->
    (match X.compare x y with
     | Gt -> if ltb_tree x l then ltb_tree x r else false
     | _ -> false)
  
  (** val gtb_tree : X.t -> tree -> bool **)
  
  let rec gtb_tree x = function
  | Leaf -> true
  | Node (t0, l, y, r) ->
    (match X.compare x y with
     | Lt -> if gtb_tree x l then gtb_tree x r else false
     | _ -> false)
  
  (** val isok : tree -> bool **)
  
  let rec isok = function
  | Leaf -> true
  | Node (t0, l, x, r) ->
    if if if isok l then isok r else false then ltb_tree x l else false
    then gtb_tree x r
    else false
  
  module MX = OrderedTypeFacts(X)
  
  type coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * I.t * tree * X.t * tree
  | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_min_elt
  
  type coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * I.t * tree * X.t * tree
  | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t * 
     tree * elt option * coq_R_max_elt
  
  module L = MakeListOrdering(X)
  
  (** val flatten_e : enumeration -> elt list **)
  
  let rec flatten_e = function
  | End -> []
  | More (x, t0, r) -> x::(app (elements t0) (flatten_e r))
  
  type coq_R_bal =
  | R_bal_0 of t * X.t * t
  | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t
     * tree
  | R_bal_4 of t * X.t * t
  | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t
     * tree
  | R_bal_8 of t * X.t * t
  
  type coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree
     * (t, elt) prod * coq_R_remove_min * t * elt
  
  type coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * I.t * tree * X.t * tree
  | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt
  
  type coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * I.t * tree * X.t * tree
  | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * elt
  
  type coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * I.t * tree * X.t * tree
  | R_inter_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  
  type coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * I.t * tree * X.t * tree
  | R_diff_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  
  type coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * I.t * tree * X.t * tree
  | R_union_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree * 
     X.t * tree * t * bool * t * tree * coq_R_union * tree * coq_R_union
 end

module Coq_IntMake = 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct 
  module Raw = MakeRaw(I)(X)
  
  module E = 
   struct 
    type t = X.t
    
    (** val compare : t -> t -> comparison **)
    
    let compare =
      X.compare
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  type elt = X.t
  
  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> Raw.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    Raw.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    Raw.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    Raw.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    Raw.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    Raw.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    Raw.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    Raw.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    Raw.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    Raw.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    Raw.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    Raw.elements (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    Raw.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f0 s =
    Raw.fold f0 (this s)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    Raw.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f0 s =
    Raw.filter f0 (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f0 s =
    Raw.for_all f0 (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f0 s =
    Raw.exists_ f0 (this s)
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition f0 s =
    let p = Raw.partition f0 (this s) in Pair ((fst p), (snd p))
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    let b0 = Raw.equal s s' in if b0 then true else false
  
  (** val compare : t -> t -> comparison **)
  
  let compare s s' =
    Raw.compare (this s) (this s')
  
  (** val min_elt : t -> elt option **)
  
  let min_elt s =
    Raw.min_elt (this s)
  
  (** val max_elt : t -> elt option **)
  
  let max_elt s =
    Raw.max_elt (this s)
 end

module type OrderedTypeOrig = 
 Coq_OrderedType

module Update_OT = 
 functor (O:OrderedTypeOrig) ->
 struct 
  type t = O.t
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    O.eq_dec
  
  (** val compare : O.t -> O.t -> comparison **)
  
  let compare x y =
    match O.compare x y with
    | LT -> Lt
    | EQ -> Eq
    | GT -> Gt
 end

module Coq0_IntMake = 
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct 
  module X' = Update_OT(X)
  
  module MSet = Coq_IntMake(I)(X')
  
  type elt = X.t
  
  type t = MSet.t
  
  (** val empty : t **)
  
  let empty =
    MSet.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty =
    MSet.is_empty
  
  (** val mem : elt -> t -> bool **)
  
  let mem =
    MSet.mem
  
  (** val add : elt -> t -> t **)
  
  let add =
    MSet.add
  
  (** val singleton : elt -> t **)
  
  let singleton =
    MSet.singleton
  
  (** val remove : elt -> t -> t **)
  
  let remove =
    MSet.remove
  
  (** val union : t -> t -> t **)
  
  let union =
    MSet.union
  
  (** val inter : t -> t -> t **)
  
  let inter =
    MSet.inter
  
  (** val diff : t -> t -> t **)
  
  let diff =
    MSet.diff
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec =
    MSet.eq_dec
  
  (** val equal : t -> t -> bool **)
  
  let equal =
    MSet.equal
  
  (** val subset : t -> t -> bool **)
  
  let subset =
    MSet.subset
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold x x0 x1 =
    MSet.fold x x0 x1
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all =
    MSet.for_all
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ =
    MSet.exists_
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter =
    MSet.filter
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition =
    MSet.partition
  
  (** val cardinal : t -> nat **)
  
  let cardinal =
    MSet.cardinal
  
  (** val elements : t -> elt list **)
  
  let elements =
    MSet.elements
  
  (** val choose : t -> elt option **)
  
  let choose =
    MSet.choose
  
  module MF = 
   struct 
    (** val eqb : X.t -> X.t -> bool **)
    
    let eqb x y =
      if MSet.E.eq_dec x y then true else false
   end
  
  (** val min_elt : t -> elt option **)
  
  let min_elt =
    MSet.min_elt
  
  (** val max_elt : t -> elt option **)
  
  let max_elt =
    MSet.max_elt
  
  (** val compare : t -> t -> t compare0 **)
  
  let compare s s' =
    let c = compSpec2Type s s' (MSet.compare s s') in
    (match c with
     | CompEqT -> EQ
     | CompLtT -> LT
     | CompGtT -> GT)
  
  module E = 
   struct 
    type t = X.t
    
    (** val compare : t -> t -> t compare0 **)
    
    let compare =
      X.compare
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
 end

module Coq3_Make = 
 functor (X:Coq_OrderedType) ->
 Coq0_IntMake(Z_as_Int)(X)

module StringKey = 
 struct 
  type t = char list
  
  (** val compare' : t -> t -> comparison **)
  
  let compare' x y =
    if string_lt x y then Lt else if string_dec x y then Eq else Gt
  
  (** val compare : t -> t -> t compare0 **)
  
  let compare x y =
    match compare' x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    string_dec x y
 end

module StringSet = Coq3_Make(StringKey)

type assert0 = (w, (settings0, state) prod) spec

type module0 = { imports : assert0 LabelMap.t;
                 blocks : (assert0, block) prod LabelMap.t;
                 exports : assert0 LabelMap.t; modules : StringSet.t }

(** val imports : module0 -> assert0 LabelMap.t **)

let imports x = x.imports

(** val blocks : module0 -> (assert0, block) prod LabelMap.t **)

let blocks x = x.blocks

(** val exports : module0 -> assert0 LabelMap.t **)

let exports x = x.exports

(** val modules : module0 -> StringSet.t **)

let modules x = x.modules

(** val union0 : 'a1 LabelMap.t -> 'a1 LabelMap.t -> 'a1 LabelMap.t **)

let union0 mp1 mp2 =
  LabelMap.fold LabelMap.add mp1 mp2

(** val diff0 : 'a1 LabelMap.t -> 'a2 LabelMap.t -> 'a1 LabelMap.t **)

let diff0 mp1 mp2 =
  LabelMap.fold (fun k v mp ->
    if LabelMap.mem k mp2 then mp else LabelMap.add k v mp) mp1
    LabelMap.empty

(** val link : module0 -> module0 -> module0 **)

let link m6 m7 =
  { imports =
    (union0 (diff0 m6.imports m7.exports) (diff0 m7.imports m6.exports));
    blocks = (union0 m6.blocks m7.blocks); exports =
    (union0 m6.exports m7.exports); modules =
    (StringSet.union m6.modules m7.modules) }

type codeGen = { entry : n; blocks0 : (assert0, block) prod list }

(** val entry :
    assert0 LabelMap.t -> char list -> assert0 -> n -> n -> assert0 -> __
    list -> codeGen -> n **)

let entry _ _ _ _ _ _ _ x = x.entry

(** val blocks0 :
    assert0 LabelMap.t -> char list -> assert0 -> n -> n -> assert0 -> __
    list -> codeGen -> (assert0, block) prod list **)

let blocks0 _ _ _ _ _ _ _ x = x.blocks0

type codeOut = { postcondition : assert0; verifCond : __ list;
                 generate : (n -> n -> codeGen) }

(** val postcondition :
    assert0 LabelMap.t -> char list -> assert0 -> codeOut -> assert0 **)

let postcondition _ _ _ x = x.postcondition

(** val verifCond :
    assert0 LabelMap.t -> char list -> assert0 -> codeOut -> __ list **)

let verifCond _ _ _ x = x.verifCond

(** val generate :
    assert0 LabelMap.t -> char list -> assert0 -> codeOut -> n -> n ->
    codeGen **)

let generate _ _ _ x = x.generate

type cmd = assert0 -> codeOut

(** val straightline_ :
    assert0 LabelMap.t -> char list -> instr list -> cmd **)

let straightline_ imports3 modName is pre =
  { postcondition = (fun stn_st -> Exists ([], (fun st' -> And ([],
    (Obj.magic pre (Pair ((fst stn_st), st'))), (Inj []))))); verifCond =
    (__::[]); generate = (fun base exit -> { entry = N0; blocks0 = ((Pair
    (pre, (Pair (is, (Uncond (RvLabel (Pair (modName, (Local
    exit)))))))))::[]) }) }

(** val seq_ : assert0 LabelMap.t -> char list -> cmd -> cmd -> cmd **)

let seq_ imports3 modName c1 c2 pre =
  let cout1 = c1 pre in
  let cout2 = c2 cout1.postcondition in
  { postcondition = cout2.postcondition; verifCond =
  (app cout1.verifCond cout2.verifCond); generate = (fun base exit ->
  let cg2 = cout2.generate base exit in
  let numBlocks = N.of_nat (length cg2.blocks0) in
  let cg1 = cout1.generate (N.add base numBlocks) (N.add base cg2.entry) in
  { entry = (N.add numBlocks cg1.entry); blocks0 =
  (app cg2.blocks0 cg1.blocks0) }) }

(** val diverge_ : assert0 LabelMap.t -> char list -> cmd **)

let diverge_ imports3 modName pre =
  { postcondition = (fun x -> Inj []); verifCond = []; generate =
    (fun base exit -> { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Uncond
    (RvLabel (Pair (modName, (Local base)))))))))::[]) }) }

(** val skip_ : assert0 LabelMap.t -> char list -> cmd **)

let skip_ imports3 modName pre =
  { postcondition = pre; verifCond = []; generate = (fun base exit ->
    { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Uncond (RvLabel (Pair
    (modName, (Local exit)))))))))::[]) }) }

(** val assert_ : assert0 LabelMap.t -> char list -> assert0 -> cmd **)

let assert_ imports3 modName post2 pre =
  { postcondition = post2; verifCond = (__::[]); generate = (fun base exit ->
    { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Uncond (RvLabel (Pair
    (modName, (Local exit)))))))))::[]) }) }

(** val if_ :
    assert0 LabelMap.t -> char list -> rvalue -> test -> rvalue -> cmd -> cmd
    -> cmd **)

let if_ imports3 modName rv1 t0 rv2 then0 else0 pre =
  let cout1 = then0 (fun stn_st -> And ([], (pre stn_st), (Inj []))) in
  let cout2 = else0 (fun stn_st -> And ([], (pre stn_st), (Inj []))) in
  { postcondition = (fun stn_st -> Or ([], (cout1.postcondition stn_st),
  (cout2.postcondition stn_st))); verifCond =
  (__::(app cout1.verifCond cout2.verifCond)); generate = (fun base exit ->
  let base' = N.succ (N.succ (N.succ base)) in
  let cg1 = cout1.generate base' (N.succ base) in
  let base'' = N.add base' (N.of_nat (length cg1.blocks0)) in
  let cg2 = cout2.generate base'' (N.succ (N.succ base)) in
  { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Cond (rv1, t0, rv2, (Pair
  (modName, (Local (N.add base' cg1.entry)))), (Pair (modName, (Local
  (N.add base'' cg2.entry))))))))))::((Pair (cout1.postcondition, (Pair ([],
  (Uncond (RvLabel (Pair (modName, (Local exit)))))))))::((Pair
  (cout2.postcondition, (Pair ([], (Uncond (RvLabel (Pair (modName, (Local
  exit)))))))))::(app cg1.blocks0 cg2.blocks0)))) }) }

(** val while_ :
    assert0 LabelMap.t -> char list -> assert0 -> rvalue -> test -> rvalue ->
    cmd -> cmd **)

let while_ imports3 modName inv0 rv1 t0 rv2 body5 pre =
  let cout = body5 (fun stn_st -> And ([], (inv0 stn_st), (Inj []))) in
  { postcondition = (fun stn_st -> And ([], (inv0 stn_st), (Inj [])));
  verifCond = (__::(__::(__::cout.verifCond))); generate = (fun base exit ->
  let base' = N.succ (N.succ (N.succ base)) in
  let cg = cout.generate base' (N.succ (N.succ base)) in
  { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Uncond (RvLabel (Pair
  (modName, (Local (N.succ base))))))))))::((Pair (inv0, (Pair ([], (Cond
  (rv1, t0, rv2, (Pair (modName, (Local (N.add base' cg.entry)))), (Pair
  (modName, (Local exit)))))))))::((Pair (cout.postcondition, (Pair ([],
  (Uncond (RvLabel (Pair (modName, (Local
  (N.succ base))))))))))::cg.blocks0))) }) }

(** val goto_ : assert0 LabelMap.t -> char list -> label -> cmd **)

let goto_ imports3 modName f0 pre =
  { postcondition = (fun x -> Inj []); verifCond = (__::[]); generate =
    (fun base exit -> { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Uncond
    (RvLabel f0))))))::[]) }) }

(** val call_ :
    assert0 LabelMap.t -> char list -> label -> assert0 -> cmd **)

let call_ imports3 modName f0 afterCall pre =
  { postcondition = afterCall; verifCond = (__::[]); generate =
    (fun base exit -> { entry = N0; blocks0 = ((Pair (pre, (Pair (((Assign
    ((LvReg Rp), (RvLabel (Pair (modName, (Local exit))))))::[]), (Uncond
    (RvLabel f0))))))::[]) }) }

(** val iGoto : assert0 LabelMap.t -> char list -> rvalue -> cmd **)

let iGoto imports3 modName rv pre =
  { postcondition = (fun x -> Inj []); verifCond = (__::[]); generate =
    (fun base exit -> { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Uncond
    rv)))))::[]) }) }

(** val iCall_ :
    assert0 LabelMap.t -> char list -> rvalue -> assert0 -> cmd **)

let iCall_ imports3 modName rv afterCall pre =
  { postcondition = afterCall; verifCond = (__::[]); generate =
    (fun base exit -> { entry = N0; blocks0 = ((Pair (pre, (Pair (((Assign
    ((LvReg Rp), (RvLabel (Pair (modName, (Local exit))))))::[]), (Uncond
    rv)))))::[]) }) }

type import = ((char list, char list) prod, assert0) prod

type function0 =
  ((char list, assert0) prod, assert0 LabelMap.t -> __ -> cmd) prod

(** val importsMap : import list -> assert0 LabelMap.t **)

let importsMap imports3 =
  fold_left (fun m6 p ->
    let Pair (y, pre) = p in
    let Pair (modl, f0) = y in LabelMap.add (Pair (modl, (Global f0))) pre m6)
    imports3 LabelMap.empty

(** val fullImports :
    import list -> char list -> function0 list -> assert0 LabelMap.t **)

let fullImports imports3 modName functions2 =
  fold_left (fun m6 p ->
    let Pair (y, y0) = p in
    let Pair (f0, pre) = y in
    LabelMap.add (Pair (modName, (Global f0))) pre m6) functions2
    (importsMap imports3)

(** val buildLocals :
    char list -> (assert0, block) prod list -> n -> (assert0, block) prod
    LabelMap.t **)

let buildLocals modName bls base =
  snd
    (fold_left (fun b_m p ->
      let Pair (b0, m6) = b_m in
      Pair ((N.succ b0), (LabelMap.add (Pair (modName, (Local b0))) p m6)))
      bls (Pair (base, LabelMap.empty)))

(** val blocks1 :
    import list -> char list -> function0 list -> function0 list -> n ->
    (assert0, block) prod LabelMap.t **)

let rec blocks1 imports3 modName functions2 fs0 base =
  match fs0 with
  | [] -> LabelMap.empty
  | f0::fs' ->
    let Pair (p, c) = f0 in
    let Pair (f1, pre) = p in
    let cout = c (fullImports imports3 modName functions2) __ pre in
    let cg = cout.generate (N.succ base) base in
    LabelMap.add (Pair (modName, (Global f1))) (Pair (pre, (Pair ([], (Uncond
      (RvLabel (Pair (modName, (Local (N.add (N.succ base) cg.entry))))))))))
      (LabelMap.add (Pair (modName, (Local base))) (Pair (cout.postcondition,
        (Pair ([], (Uncond (RvLabel (Pair (modName, (Local base)))))))))
        (union0 (buildLocals modName cg.blocks0 (N.succ base))
          (blocks1 imports3 modName functions2 fs'
            (N.add (N.succ base) (N.of_nat (length cg.blocks0))))))

(** val exps : char list -> function0 list -> assert0 LabelMap.t **)

let rec exps modName = function
| [] -> LabelMap.empty
| f0::fs' ->
  let Pair (p, c) = f0 in
  let Pair (f1, pre) = p in
  LabelMap.add (Pair (modName, (Global f1))) pre (exps modName fs')

(** val bmodule_ : import list -> char list -> function0 list -> module0 **)

let bmodule_ imports3 modName functions2 =
  { imports = (importsMap imports3); blocks =
    (blocks1 imports3 modName functions2 functions2 (Npos XH)); exports =
    (exps modName functions2); modules = (StringSet.singleton modName) }

type 't repr = { footprint : 't option list; default : 't }

(** val footprint : 'a1 repr -> 'a1 option list **)

let footprint x = x.footprint

(** val default : 'a1 repr -> 'a1 **)

let default x = x.default

(** val nil_Repr : 'a1 -> 'a1 repr **)

let nil_Repr d =
  { footprint = []; default = d }

(** val listToRepr : 'a1 list -> 'a1 -> 'a1 repr **)

let listToRepr ls d =
  { footprint = (map (fun x -> Some x) ls); default = d }

(** val repr0 : 'a1 repr -> 'a1 list -> 'a1 list **)

let repr0 l =
  let { footprint = f0; default = d } = l in
  let rec repr' d0 ls x =
    match ls with
    | [] -> x
    | o::ls0 ->
      (match o with
       | Some v -> v::(repr' d0 ls0 (tl x))
       | None ->
         (match x with
          | [] -> d0
          | a::l0 -> a)::(repr' d0 ls0 (tl x)))
  in repr' d f0

type proverT = { summarize : (exprs -> __); learn : (__ -> exprs -> __);
                 prove : (__ -> expr -> bool) }

type facts = __

(** val summarize : type0 list -> proverT -> exprs -> facts **)

let summarize _ x = x.summarize

(** val learn : type0 list -> proverT -> facts -> exprs -> facts **)

let learn _ x = x.learn

(** val prove : type0 list -> proverT -> facts -> expr -> bool **)

let prove _ x = x.prove

type proverT_correct =
| Build_ProverT_correct

(** val composite_ProverT : type0 list -> proverT -> proverT -> proverT **)

let composite_ProverT types4 pl pr =
  { summarize = (fun hyps ->
    Obj.magic (Pair ((pl.summarize hyps), (pr.summarize hyps)))); learn =
    (fun facts0 hyps ->
    let Pair (fl, fr) = Obj.magic facts0 in
    Obj.magic (Pair ((pl.learn fl hyps), (pr.learn fr hyps)))); prove =
    (fun facts0 goal ->
    let Pair (fl, fr) = Obj.magic facts0 in
    if pl.prove fl goal then true else pr.prove fr goal) }

type quant =
| QAll of variables * quant
| QEx of variables * quant
| QBase

module SymbolicEvaluator = 
 functor (SH__1:SepHeap) ->
 struct 
  module SEP = SH__1.SE
  
  module ST = SEP.ST
  
  type 'symState coq_LearnHook =
    proverT -> variables -> variables -> 'symState -> facts -> expr list ->
    ('symState, quant) prod
  
  (** val coq_LearnHook_correct_rect :
      type0 list -> tvar -> tvar -> 'a1 coq_LearnHook -> functions ->
      SEP.predicates -> (__ -> 'a2) -> 'a2 **)
  
  let coq_LearnHook_correct_rect types_ pcT stT l funcs preds f0 =
    f0 __
  
  (** val coq_LearnHook_correct_rec :
      type0 list -> tvar -> tvar -> 'a1 coq_LearnHook -> functions ->
      SEP.predicates -> (__ -> 'a2) -> 'a2 **)
  
  let coq_LearnHook_correct_rec types_ pcT stT l funcs preds f0 =
    f0 __
  
  module LearnHookDefault = 
   struct 
    (** val coq_LearnHook_default : type0 list -> 'a1 coq_LearnHook **)
    
    let coq_LearnHook_default types4 p x x0 x1 x2 x3 =
      Pair (x1, QBase)
   end
  
  type coq_MemEvaluator = { sread_word : (proverT -> facts -> expr ->
                                         SH__1.coq_SHeap -> expr option);
                            swrite_word : (proverT -> facts -> expr -> expr
                                          -> SH__1.coq_SHeap ->
                                          SH__1.coq_SHeap option);
                            sread_byte : (proverT -> facts -> expr ->
                                         SH__1.coq_SHeap -> expr option);
                            swrite_byte : (proverT -> facts -> expr -> expr
                                          -> SH__1.coq_SHeap ->
                                          SH__1.coq_SHeap option) }
  
  (** val coq_MemEvaluator_rect :
      type0 list -> tvar -> tvar -> ((proverT -> facts -> expr ->
      SH__1.coq_SHeap -> expr option) -> (proverT -> facts -> expr -> expr ->
      SH__1.coq_SHeap -> SH__1.coq_SHeap option) -> (proverT -> facts -> expr
      -> SH__1.coq_SHeap -> expr option) -> (proverT -> facts -> expr -> expr
      -> SH__1.coq_SHeap -> SH__1.coq_SHeap option) -> 'a1) ->
      coq_MemEvaluator -> 'a1 **)
  
  let coq_MemEvaluator_rect types4 pcT stT f0 m6 =
    let { sread_word = x; swrite_word = x0; sread_byte = x1; swrite_byte =
      x2 } = m6
    in
    f0 x x0 x1 x2
  
  (** val coq_MemEvaluator_rec :
      type0 list -> tvar -> tvar -> ((proverT -> facts -> expr ->
      SH__1.coq_SHeap -> expr option) -> (proverT -> facts -> expr -> expr ->
      SH__1.coq_SHeap -> SH__1.coq_SHeap option) -> (proverT -> facts -> expr
      -> SH__1.coq_SHeap -> expr option) -> (proverT -> facts -> expr -> expr
      -> SH__1.coq_SHeap -> SH__1.coq_SHeap option) -> 'a1) ->
      coq_MemEvaluator -> 'a1 **)
  
  let coq_MemEvaluator_rec types4 pcT stT f0 m6 =
    let { sread_word = x; swrite_word = x0; sread_byte = x1; swrite_byte =
      x2 } = m6
    in
    f0 x x0 x1 x2
  
  (** val sread_word :
      type0 list -> tvar -> tvar -> coq_MemEvaluator -> proverT -> facts ->
      expr -> SH__1.coq_SHeap -> expr option **)
  
  let sread_word types4 pcT stT m6 =
    m6.sread_word
  
  (** val swrite_word :
      type0 list -> tvar -> tvar -> coq_MemEvaluator -> proverT -> facts ->
      expr -> expr -> SH__1.coq_SHeap -> SH__1.coq_SHeap option **)
  
  let swrite_word types4 pcT stT m6 =
    m6.swrite_word
  
  (** val sread_byte :
      type0 list -> tvar -> tvar -> coq_MemEvaluator -> proverT -> facts ->
      expr -> SH__1.coq_SHeap -> expr option **)
  
  let sread_byte types4 pcT stT m6 =
    m6.sread_byte
  
  (** val swrite_byte :
      type0 list -> tvar -> tvar -> coq_MemEvaluator -> proverT -> facts ->
      expr -> expr -> SH__1.coq_SHeap -> SH__1.coq_SHeap option **)
  
  let swrite_byte types4 pcT stT m6 =
    m6.swrite_byte
  
  type 'stn_st coq_MemEvaluator_correct =
  | Build_MemEvaluator_correct
  
  (** val coq_MemEvaluator_correct_rect :
      type0 list -> tvar -> tvar -> coq_MemEvaluator -> functions ->
      SEP.predicates -> tvar -> tvar -> ('a1 -> tvarD -> tvarD option) ->
      ('a1 -> tvarD -> tvarD -> 'a1 option) -> ('a1 -> tvarD -> tvarD option)
      -> ('a1 -> tvarD -> tvarD -> 'a1 option) -> (__ -> __ -> __ -> __ ->
      'a2) -> 'a2 **)
  
  let coq_MemEvaluator_correct_rect types4 pcT stT eval funcs preds ptrT valT readWord writeWord readByte0 writeByte0 f0 =
    f0 __ __ __ __
  
  (** val coq_MemEvaluator_correct_rec :
      type0 list -> tvar -> tvar -> coq_MemEvaluator -> functions ->
      SEP.predicates -> tvar -> tvar -> ('a1 -> tvarD -> tvarD option) ->
      ('a1 -> tvarD -> tvarD -> 'a1 option) -> ('a1 -> tvarD -> tvarD option)
      -> ('a1 -> tvarD -> tvarD -> 'a1 option) -> (__ -> __ -> __ -> __ ->
      'a2) -> 'a2 **)
  
  let coq_MemEvaluator_correct_rec types4 pcT stT eval funcs preds ptrT valT readWord writeWord readByte0 writeByte0 f0 =
    f0 __ __ __ __
  
  type coq_MemEvaluatorPackage = { coq_MemEvalTypes : type0 repr;
                                   coq_MemEvalFuncs : (type0 list ->
                                                      signature repr);
                                   coq_MemEvalPreds : (type0 list ->
                                                      SEP.predicate repr);
                                   coq_MemEval : (type0 list ->
                                                 coq_MemEvaluator) }
  
  (** val coq_MemEvaluatorPackage_rect :
      type0 repr -> tvar -> tvar -> tvar -> tvar -> (type0 list -> tvarD ->
      tvarD -> tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD ->
      tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD option) ->
      (type0 list -> tvarD -> tvarD -> tvarD -> tvarD option) -> (type0 repr
      -> (type0 list -> signature repr) -> (type0 list -> SEP.predicate repr)
      -> (type0 list -> coq_MemEvaluator) -> __ -> 'a1) ->
      coq_MemEvaluatorPackage -> 'a1 **)
  
  let coq_MemEvaluatorPackage_rect tr pc0 st0 ptr val0 read write readByte0 writeByte0 f0 m6 =
    let { coq_MemEvalTypes = x; coq_MemEvalFuncs = x0; coq_MemEvalPreds = x1;
      coq_MemEval = x2 } = m6
    in
    f0 x x0 x1 x2 __
  
  (** val coq_MemEvaluatorPackage_rec :
      type0 repr -> tvar -> tvar -> tvar -> tvar -> (type0 list -> tvarD ->
      tvarD -> tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD ->
      tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD option) ->
      (type0 list -> tvarD -> tvarD -> tvarD -> tvarD option) -> (type0 repr
      -> (type0 list -> signature repr) -> (type0 list -> SEP.predicate repr)
      -> (type0 list -> coq_MemEvaluator) -> __ -> 'a1) ->
      coq_MemEvaluatorPackage -> 'a1 **)
  
  let coq_MemEvaluatorPackage_rec tr pc0 st0 ptr val0 read write readByte0 writeByte0 f0 m6 =
    let { coq_MemEvalTypes = x; coq_MemEvalFuncs = x0; coq_MemEvalPreds = x1;
      coq_MemEval = x2 } = m6
    in
    f0 x x0 x1 x2 __
  
  (** val coq_MemEvalTypes :
      type0 repr -> tvar -> tvar -> tvar -> tvar -> (type0 list -> tvarD ->
      tvarD -> tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD ->
      tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD option) ->
      (type0 list -> tvarD -> tvarD -> tvarD -> tvarD option) ->
      coq_MemEvaluatorPackage -> type0 repr **)
  
  let coq_MemEvalTypes tr pc0 st0 ptr val0 read write readByte0 writeByte0 m6 =
    m6.coq_MemEvalTypes
  
  (** val coq_MemEvalFuncs :
      type0 repr -> tvar -> tvar -> tvar -> tvar -> (type0 list -> tvarD ->
      tvarD -> tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD ->
      tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD option) ->
      (type0 list -> tvarD -> tvarD -> tvarD -> tvarD option) ->
      coq_MemEvaluatorPackage -> type0 list -> signature repr **)
  
  let coq_MemEvalFuncs tr pc0 st0 ptr val0 read write readByte0 writeByte0 m6 =
    m6.coq_MemEvalFuncs
  
  (** val coq_MemEvalPreds :
      type0 repr -> tvar -> tvar -> tvar -> tvar -> (type0 list -> tvarD ->
      tvarD -> tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD ->
      tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD option) ->
      (type0 list -> tvarD -> tvarD -> tvarD -> tvarD option) ->
      coq_MemEvaluatorPackage -> type0 list -> SEP.predicate repr **)
  
  let coq_MemEvalPreds tr pc0 st0 ptr val0 read write readByte0 writeByte0 m6 =
    m6.coq_MemEvalPreds
  
  (** val coq_MemEval :
      type0 repr -> tvar -> tvar -> tvar -> tvar -> (type0 list -> tvarD ->
      tvarD -> tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD ->
      tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD option) ->
      (type0 list -> tvarD -> tvarD -> tvarD -> tvarD option) ->
      coq_MemEvaluatorPackage -> type0 list -> coq_MemEvaluator **)
  
  let coq_MemEval tr pc0 st0 ptr val0 read write readByte0 writeByte0 m6 =
    m6.coq_MemEval
  
  module Default = 
   struct 
    (** val smemeval_read_word_default :
        type0 list -> tvar -> tvar -> proverT -> facts -> expr ->
        SH__1.coq_SHeap -> expr option **)
    
    let smemeval_read_word_default types4 pcT stT prover x x0 x1 =
      None
    
    (** val smemeval_write_word_default :
        type0 list -> tvar -> tvar -> proverT -> facts -> expr -> expr ->
        SH__1.coq_SHeap -> SH__1.coq_SHeap option **)
    
    let smemeval_write_word_default types4 pcT stT prover x x0 x1 x2 =
      None
    
    (** val coq_MemEvaluator_default :
        type0 list -> tvar -> tvar -> coq_MemEvaluator **)
    
    let coq_MemEvaluator_default types4 pcT stT =
      { sread_word = (smemeval_read_word_default types4 pcT stT);
        swrite_word = (smemeval_write_word_default types4 pcT stT);
        sread_byte = (smemeval_read_word_default types4 pcT stT);
        swrite_byte = (smemeval_write_word_default types4 pcT stT) }
    
    (** val package :
        type0 repr -> tvar -> tvar -> tvar -> tvar -> (type0 list -> tvarD ->
        tvarD -> tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD ->
        tvarD option) -> (type0 list -> tvarD -> tvarD -> tvarD option) ->
        (type0 list -> tvarD -> tvarD -> tvarD -> tvarD option) ->
        coq_MemEvaluatorPackage **)
    
    let package tr pcT stT ptr val0 y z0 a b0 =
      { coq_MemEvalTypes = (nil_Repr emptySet_type); coq_MemEvalFuncs =
        (fun ts ->
        nil_Repr
          (default_signature (repr0 tr (repr0 (nil_Repr emptySet_type) ts))));
        coq_MemEvalPreds = (fun ts ->
        nil_Repr
          (SEP.coq_Default_predicate
            (repr0 tr (repr0 (nil_Repr emptySet_type) ts)) pcT stT));
        coq_MemEval = (fun ts ->
        coq_MemEvaluator_default
          (repr0 tr (repr0 (nil_Repr emptySet_type) ts)) pcT stT) }
   end
  
  module PredEval = 
   struct 
    module SF = SepExprFacts(SEP)
    
    type coq_MemEvalPred = { pred_read_word : (proverT -> facts -> exprs ->
                                              expr -> expr option);
                             pred_write_word : (proverT -> facts -> exprs ->
                                               expr -> expr -> exprs option);
                             pred_read_byte : (proverT -> facts -> exprs ->
                                              expr -> expr option);
                             pred_write_byte : (proverT -> facts -> exprs ->
                                               expr -> expr -> exprs option) }
    
    (** val coq_MemEvalPred_rect :
        type0 list -> ((proverT -> facts -> exprs -> expr -> expr option) ->
        (proverT -> facts -> exprs -> expr -> expr -> exprs option) ->
        (proverT -> facts -> exprs -> expr -> expr option) -> (proverT ->
        facts -> exprs -> expr -> expr -> exprs option) -> 'a1) ->
        coq_MemEvalPred -> 'a1 **)
    
    let coq_MemEvalPred_rect types4 f0 m6 =
      let { pred_read_word = x; pred_write_word = x0; pred_read_byte = x1;
        pred_write_byte = x2 } = m6
      in
      f0 x x0 x1 x2
    
    (** val coq_MemEvalPred_rec :
        type0 list -> ((proverT -> facts -> exprs -> expr -> expr option) ->
        (proverT -> facts -> exprs -> expr -> expr -> exprs option) ->
        (proverT -> facts -> exprs -> expr -> expr option) -> (proverT ->
        facts -> exprs -> expr -> expr -> exprs option) -> 'a1) ->
        coq_MemEvalPred -> 'a1 **)
    
    let coq_MemEvalPred_rec types4 f0 m6 =
      let { pred_read_word = x; pred_write_word = x0; pred_read_byte = x1;
        pred_write_byte = x2 } = m6
      in
      f0 x x0 x1 x2
    
    (** val pred_read_word :
        type0 list -> coq_MemEvalPred -> proverT -> facts -> exprs -> expr ->
        expr option **)
    
    let pred_read_word types4 m6 =
      m6.pred_read_word
    
    (** val pred_write_word :
        type0 list -> coq_MemEvalPred -> proverT -> facts -> exprs -> expr ->
        expr -> exprs option **)
    
    let pred_write_word types4 m6 =
      m6.pred_write_word
    
    (** val pred_read_byte :
        type0 list -> coq_MemEvalPred -> proverT -> facts -> exprs -> expr ->
        expr option **)
    
    let pred_read_byte types4 m6 =
      m6.pred_read_byte
    
    (** val pred_write_byte :
        type0 list -> coq_MemEvalPred -> proverT -> facts -> exprs -> expr ->
        expr -> exprs option **)
    
    let pred_write_byte types4 m6 =
      m6.pred_write_byte
    
    (** val coq_MemEvalPred_correct_rect :
        type0 list -> tvar -> tvar -> tvar -> tvar -> ('a1 -> tvarD -> tvarD
        option) -> ('a1 -> tvarD -> tvarD -> 'a1 option) -> ('a1 -> tvarD ->
        tvarD option) -> ('a1 -> tvarD -> tvarD -> 'a1 option) ->
        coq_MemEvalPred -> SEP.predicate -> functions -> (__ -> __ -> __ ->
        __ -> 'a2) -> 'a2 **)
    
    let coq_MemEvalPred_correct_rect types4 pcT stT ptrT valT readWord writeWord readByte0 writeByte0 me predicate0 funcs f0 =
      f0 __ __ __ __
    
    (** val coq_MemEvalPred_correct_rec :
        type0 list -> tvar -> tvar -> tvar -> tvar -> ('a1 -> tvarD -> tvarD
        option) -> ('a1 -> tvarD -> tvarD -> 'a1 option) -> ('a1 -> tvarD ->
        tvarD option) -> ('a1 -> tvarD -> tvarD -> 'a1 option) ->
        coq_MemEvalPred -> SEP.predicate -> functions -> (__ -> __ -> __ ->
        __ -> 'a2) -> 'a2 **)
    
    let coq_MemEvalPred_correct_rec types4 pcT stT ptrT valT readWord writeWord readByte0 writeByte0 me predicate0 funcs f0 =
      f0 __ __ __ __
    
    (** val fold_args :
        type0 list -> (exprs -> 'a1 option) -> exprs list -> 'a1 option **)
    
    let rec fold_args types4 f0 = function
    | [] -> None
    | a::b0 ->
      (match f0 a with
       | Some r -> Some r
       | None -> fold_args types4 f0 b0)
    
    (** val fold_args_update :
        type0 list -> (exprs -> exprs option) -> exprs list -> exprs list
        option **)
    
    let rec fold_args_update types4 f_upd = function
    | [] -> None
    | a::b0 ->
      (match f_upd a with
       | Some r -> Some (r::b0)
       | None ->
         (match fold_args_update types4 f_upd b0 with
          | Some b1 -> Some (a::b1)
          | None -> None))
    
    (** val coq_MemEvalPred_to_MemEvaluator :
        type0 list -> tvar -> tvar -> coq_MemEvalPred -> nat ->
        coq_MemEvaluator **)
    
    let coq_MemEvalPred_to_MemEvaluator types4 pcT stT mep predIndex =
      { sread_word = (fun p f0 p0 h ->
        let impures0 = SH__1.impures types4 pcT stT h in
        let argss = FM.find predIndex impures0 in
        (match argss with
         | Some argss0 ->
           fold_args types4 (fun args ->
             pred_read_word types4 mep p f0 args p0) argss0
         | None -> None)); swrite_word = (fun p f0 p0 v h ->
        let impures0 = SH__1.impures types4 pcT stT h in
        let argss = FM.find predIndex impures0 in
        (match argss with
         | Some argss0 ->
           (match fold_args_update types4 (fun args ->
                    pred_write_word types4 mep p f0 args p0 v) argss0 with
            | Some argss1 ->
              Some { SH__1.impures = (FM.add predIndex argss1 impures0);
                SH__1.pures = (SH__1.pures types4 pcT stT h); SH__1.other =
                (SH__1.other types4 pcT stT h) }
            | None -> None)
         | None -> None)); sread_byte = (fun p f0 p0 h ->
        let impures0 = SH__1.impures types4 pcT stT h in
        let argss = FM.find predIndex impures0 in
        (match argss with
         | Some argss0 ->
           fold_args types4 (fun args ->
             pred_read_byte types4 mep p f0 args p0) argss0
         | None -> None)); swrite_byte = (fun p f0 p0 v h ->
        let impures0 = SH__1.impures types4 pcT stT h in
        let argss = FM.find predIndex impures0 in
        (match argss with
         | Some argss0 ->
           (match fold_args_update types4 (fun args ->
                    pred_write_byte types4 mep p f0 args p0 v) argss0 with
            | Some argss1 ->
              Some { SH__1.impures = (FM.add predIndex argss1 impures0);
                SH__1.pures = (SH__1.pures types4 pcT stT h); SH__1.other =
                (SH__1.other types4 pcT stT h) }
            | None -> None)
         | None -> None)) }
   end
  
  module Composite = 
   struct 
    (** val coq_MemEvaluator_composite :
        type0 list -> tvar -> tvar -> coq_MemEvaluator -> coq_MemEvaluator ->
        coq_MemEvaluator **)
    
    let coq_MemEvaluator_composite types4 pcT stT l r =
      { sread_word = (fun p f0 e h ->
        match sread_word types4 pcT stT l p f0 e h with
        | Some v -> Some v
        | None -> sread_word types4 pcT stT r p f0 e h); swrite_word =
        (fun p f0 p0 v h ->
        match swrite_word types4 pcT stT l p f0 p0 v h with
        | Some v0 -> Some v0
        | None -> swrite_word types4 pcT stT r p f0 p0 v h); sread_byte =
        (fun p f0 e h ->
        match sread_byte types4 pcT stT l p f0 e h with
        | Some v -> Some v
        | None -> sread_byte types4 pcT stT r p f0 e h); swrite_byte =
        (fun p f0 p0 v h ->
        match swrite_byte types4 pcT stT l p f0 p0 v h with
        | Some v0 -> Some v0
        | None -> swrite_byte types4 pcT stT r p f0 p0 v h) }
   end
 end

module type CoreEnv = 
 sig 
  val core : type0 repr
  
  val pc : tvar
  
  val st : tvar
 end

module Coq4_Make = 
 functor (SEP':SepExpr) ->
 functor (CE':CoreEnv) ->
 struct 
  module SEP = SEP'
  
  module CE = CE'
  
  type coq_TypeEnv = { coq_Types : type0 repr;
                       coq_Funcs : (type0 list -> signature repr);
                       coq_Preds : (type0 list -> SEP.predicate repr) }
  
  (** val coq_TypeEnv_rect :
      (type0 repr -> (type0 list -> signature repr) -> (type0 list ->
      SEP.predicate repr) -> 'a1) -> coq_TypeEnv -> 'a1 **)
  
  let coq_TypeEnv_rect f0 t0 =
    let { coq_Types = x; coq_Funcs = x0; coq_Preds = x1 } = t0 in f0 x x0 x1
  
  (** val coq_TypeEnv_rec :
      (type0 repr -> (type0 list -> signature repr) -> (type0 list ->
      SEP.predicate repr) -> 'a1) -> coq_TypeEnv -> 'a1 **)
  
  let coq_TypeEnv_rec f0 t0 =
    let { coq_Types = x; coq_Funcs = x0; coq_Preds = x1 } = t0 in f0 x x0 x1
  
  (** val coq_Types : coq_TypeEnv -> type0 repr **)
  
  let coq_Types t0 =
    t0.coq_Types
  
  (** val coq_Funcs : coq_TypeEnv -> type0 list -> signature repr **)
  
  let coq_Funcs t0 =
    t0.coq_Funcs
  
  (** val coq_Preds : coq_TypeEnv -> type0 list -> SEP.predicate repr **)
  
  let coq_Preds t0 =
    t0.coq_Preds
  
  (** val applyTypes : coq_TypeEnv -> type0 list -> type0 list **)
  
  let applyTypes tE ls =
    repr0 CE.core (repr0 (coq_Types tE) ls)
  
  (** val applyFuncs :
      coq_TypeEnv -> type0 list -> functions -> functions **)
  
  let applyFuncs tE ts ls =
    repr0 (coq_Funcs tE ts) ls
  
  (** val applyPreds :
      coq_TypeEnv -> type0 list -> SEP.predicates -> SEP.predicates **)
  
  let applyPreds tE ts ls =
    repr0 (coq_Preds tE ts) ls
  
  (** val applyTypes_red : coq_TypeEnv -> type0 list -> type0 list **)
  
  let applyTypes_red tE ls =
    let { coq_Types = ts; coq_Funcs = funcs; coq_Preds = preds } = tE in
    repr0 CE.core (repr0 ts ls)
  
  (** val applyFuncs_red :
      coq_TypeEnv -> type0 list -> functions -> functions **)
  
  let applyFuncs_red tE ts ls =
    let { coq_Types = ts'; coq_Funcs = fs0; coq_Preds = preds } = tE in
    repr0 (fs0 ts) ls
  
  (** val applyPreds_red :
      coq_TypeEnv -> type0 list -> SEP.predicates -> SEP.predicates **)
  
  let applyPreds_red tE ts ls =
    let { coq_Types = ts'; coq_Funcs = funcs; coq_Preds = ps } = tE in
    repr0 (ps ts) ls
 end

(** val reg_seq : reg -> reg -> bool **)

let reg_seq l r =
  match l with
  | Sp ->
    (match r with
     | Sp -> true
     | _ -> false)
  | Rp ->
    (match r with
     | Rp -> true
     | _ -> false)
  | Rv ->
    (match r with
     | Rv -> true
     | _ -> false)

(** val w_seq : w -> w -> bool **)

let w_seq l r =
  weqb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) l r

(** val bedrock_type_W : type0 **)

let bedrock_type_W =
  Obj.magic w_seq

(** val bedrock_type_setting_X_state : type0 **)

let bedrock_type_setting_X_state x y =
  false

(** val bedrock_type_state : type0 **)

let bedrock_type_state x y =
  false

(** val bedrock_type_reg : type0 **)

let bedrock_type_reg =
  Obj.magic reg_seq

(** val bedrock_type_nat : type0 **)

let bedrock_type_nat =
  Obj.magic beq_nat

(** val bedrock_types_r : type0 repr **)

let bedrock_types_r =
  { footprint =
    (map (fun x -> Some x)
      (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::[]))))));
    default = emptySet_type }

(** val wplus_r : type0 list -> signature **)

let wplus_r types' =
  { domain = ((TvType O)::((TvType O)::[])); range = (TvType O); denotation =
    (Obj.magic
      (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) }

(** val wminus_r : type0 list -> signature **)

let wminus_r types' =
  { domain = ((TvType O)::((TvType O)::[])); range = (TvType O); denotation =
    (Obj.magic
      (wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) }

(** val wmult_r : type0 list -> signature **)

let wmult_r types' =
  { domain = ((TvType O)::((TvType O)::[])); range = (TvType O); denotation =
    (Obj.magic
      (wmult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) }

(** val regs_r : type0 list -> signature **)

let regs_r types' =
  { domain = ((TvType (S (S O)))::((TvType (S (S (S O))))::[])); range =
    (TvType O); denotation = (Obj.magic regs) }

(** val wlt_r : type0 list -> signature **)

let wlt_r types' =
  { domain = ((TvType O)::((TvType O)::[])); range = TvProp; denotation =
    (Obj.magic __) }

(** val natToW_r : type0 list -> signature **)

let natToW_r types' =
  { domain = ((TvType (S (S (S (S O)))))::[]); range = (TvType O);
    denotation = (Obj.magic natToW) }

(** val bedrock_funcs_r : type0 list -> signature repr **)

let bedrock_funcs_r types' =
  { footprint =
    (map (fun x -> Some x)
      ((wplus_r (repr0 bedrock_types_r types'))::((wminus_r
                                                    (repr0 bedrock_types_r
                                                      types'))::((wmult_r
                                                                   (repr0
                                                                    bedrock_types_r
                                                                    types'))::(
      (regs_r (repr0 bedrock_types_r types'))::((wlt_r
                                                  (repr0 bedrock_types_r
                                                    types'))::((natToW_r
                                                                 (repr0
                                                                   bedrock_types_r
                                                                   types'))::[])))))));
    default = (default_signature (repr0 bedrock_types_r types')) }

module BedrockCoreEnv = 
 struct 
  (** val core : type0 repr **)
  
  let core =
    { footprint =
      (map (fun x -> Some x)
        (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::[]))))));
      default = emptySet_type }
  
  (** val pc : tvar **)
  
  let pc =
    TvType O
  
  (** val st : tvar **)
  
  let st =
    TvType (S O)
 end

module MEVAL = SymbolicEvaluator(SH)

(** val array : w list -> w -> hProp **)

let array ws p =
  ptsto32m [] p O ws

(** val div4 : nat -> nat option **)

let rec div4 = function
| O -> Some O
| S n1 ->
  (match n1 with
   | O -> None
   | S n2 ->
     (match n2 with
      | O -> None
      | S n3 ->
        (match n3 with
         | O -> None
         | S n' ->
           (match div4 n' with
            | Some n'' -> Some (S n'')
            | None -> None))))

(** val selN : w list -> nat -> w **)

let rec selN ws n0 =
  match ws with
  | [] ->
    wzero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
  | w0::ws' ->
    (match n0 with
     | O -> w0
     | S n' -> selN ws' n')

(** val sel : w list -> w -> w **)

let sel ws a =
  selN ws
    (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) a)

(** val updN : w list -> nat -> w -> w list **)

let rec updN ws n0 v =
  match ws with
  | [] -> []
  | w0::ws' ->
    (match n0 with
     | O -> v::ws'
     | S n' -> w0::(updN ws' n' v))

(** val upd : w list -> w -> w -> w list **)

let upd ws a v =
  updN ws
    (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) a) v

(** val bedrock_type_listW : type0 **)

let bedrock_type_listW x y =
  false

(** val types_r : type0 repr **)

let types_r =
  { footprint = ((Some bedrock_type_W)::((Some
    bedrock_type_setting_X_state)::(None::(None::((Some
    bedrock_type_nat)::((Some bedrock_type_listW)::[])))))); default =
    emptySet_type }

(** val types : type0 list -> type0 list **)

let types types' =
  repr0 types_r types'

(** val deref : type0 list -> expr -> (expr, expr) prod option **)

let deref types' = function
| Func (f0, l) ->
  (match f0 with
   | O ->
     (match l with
      | [] -> None
      | base::l0 ->
        (match l0 with
         | [] -> None
         | offset::l1 ->
           (match l1 with
            | [] ->
              (match offset with
               | Func (f1, l2) ->
                 (match f1 with
                  | O -> None
                  | S n0 ->
                    (match n0 with
                     | O -> None
                     | S n1 ->
                       (match n1 with
                        | O ->
                          (match l2 with
                           | [] -> None
                           | e0::l3 ->
                             (match e0 with
                              | Func (f2, l4) ->
                                (match f2 with
                                 | O -> None
                                 | S n2 ->
                                   (match n2 with
                                    | O -> None
                                    | S n3 ->
                                      (match n3 with
                                       | O -> None
                                       | S n4 ->
                                         (match n4 with
                                          | O -> None
                                          | S n5 ->
                                            (match n5 with
                                             | O -> None
                                             | S n6 ->
                                               (match n6 with
                                                | O ->
                                                  (match l4 with
                                                   | [] -> None
                                                   | e1::l5 ->
                                                     (match e1 with
                                                      | Const (t0, k) ->
                                                        (match l5 with
                                                         | [] ->
                                                           (match l3 with
                                                            | [] -> None
                                                            | offset0::l6 ->
                                                              (match l6 with
                                                               | [] ->
                                                                 (match t0 with
                                                                  | TvProp ->
                                                                    Obj.magic
                                                                    (fun _ ->
                                                                    None) k
                                                                  | TvType n7 ->
                                                                    (match n7 with
                                                                    | O ->
                                                                    None
                                                                    | S n8 ->
                                                                    (match n8 with
                                                                    | O ->
                                                                    None
                                                                    | S n9 ->
                                                                    (match n9 with
                                                                    | O ->
                                                                    None
                                                                    | S n10 ->
                                                                    (match n10 with
                                                                    | O ->
                                                                    None
                                                                    | S n11 ->
                                                                    (match n11 with
                                                                    | O ->
                                                                    (match 
                                                                    Obj.magic
                                                                    k with
                                                                    | O ->
                                                                    None
                                                                    | S n12 ->
                                                                    (match n12 with
                                                                    | O ->
                                                                    None
                                                                    | S n13 ->
                                                                    (match n13 with
                                                                    | O ->
                                                                    None
                                                                    | S n14 ->
                                                                    (match n14 with
                                                                    | O ->
                                                                    None
                                                                    | S n15 ->
                                                                    (match n15 with
                                                                    | O ->
                                                                    Some
                                                                    (Pair
                                                                    (base,
                                                                    offset0))
                                                                    | S n16 ->
                                                                    None)))))
                                                                    | S n12 ->
                                                                    None))))))
                                                               | e2::l7 ->
                                                                 None))
                                                         | e2::l6 -> None)
                                                      | _ -> None))
                                                | S n7 -> None))))))
                              | _ -> None))
                        | S n2 ->
                          (match n2 with
                           | O -> None
                           | S n3 ->
                             (match n3 with
                              | O -> None
                              | S n4 ->
                                (match n4 with
                                 | O ->
                                   (match l2 with
                                    | [] -> None
                                    | e0::l3 ->
                                      (match e0 with
                                       | Const (t0, k) ->
                                         (match l3 with
                                          | [] ->
                                            (match t0 with
                                             | TvProp ->
                                               Obj.magic (fun _ -> None) k
                                             | TvType n5 ->
                                               (match n5 with
                                                | O -> None
                                                | S n6 ->
                                                  (match n6 with
                                                   | O -> None
                                                   | S n7 ->
                                                     (match n7 with
                                                      | O -> None
                                                      | S n8 ->
                                                        (match n8 with
                                                         | O -> None
                                                         | S n9 ->
                                                           (match n9 with
                                                            | O ->
                                                              (match 
                                                               div4
                                                                 (Obj.magic
                                                                   k) with
                                                               | Some k' ->
                                                                 Some (Pair
                                                                   (base,
                                                                   (Func ((S
                                                                   (S (S (S
                                                                   (S O))))),
                                                                   ((Const
                                                                   ((TvType
                                                                   (S (S (S
                                                                   (S O))))),
                                                                   (Obj.magic
                                                                    k')))::[])))))
                                                               | None -> None)
                                                            | S n10 -> None))))))
                                          | e1::l4 -> None)
                                       | _ -> None))
                                 | S n5 -> None))))))
               | _ -> None)
            | e0::l2 -> None)))
   | S n0 -> None)
| _ -> None

(** val sym_read :
    type0 list -> proverT -> facts -> expr list -> expr -> expr option **)

let sym_read types' prover summ args p =
  match args with
  | [] -> None
  | ws::l ->
    (match l with
     | [] -> None
     | p'::l0 ->
       (match l0 with
        | [] ->
          (match deref types' p with
           | Some p0 ->
             let Pair (base, offset) = p0 in
             if if prover.prove summ (Equal ((TvType O), p', base))
                then prover.prove summ (Func ((S (S (S (S O)))),
                       (offset::((Func ((S (S (S (S (S O))))), ((Func ((S (S
                       (S (S (S (S O)))))), (ws::[])))::[])))::[]))))
                else false
             then Some (Func ((S (S (S (S (S (S (S O))))))),
                    (ws::(offset::[]))))
             else None
           | None -> None)
        | e::l1 -> None))

(** val sym_write :
    type0 list -> proverT -> facts -> expr list -> expr -> expr -> expr list
    option **)

let sym_write types' prover summ args p v =
  match args with
  | [] -> None
  | ws::l ->
    (match l with
     | [] -> None
     | p'::l0 ->
       (match l0 with
        | [] ->
          (match deref types' p with
           | Some p0 ->
             let Pair (base, offset) = p0 in
             if if prover.prove summ (Equal ((TvType O), p', base))
                then prover.prove summ (Func ((S (S (S (S O)))),
                       (offset::((Func ((S (S (S (S (S O))))), ((Func ((S (S
                       (S (S (S (S O)))))), (ws::[])))::[])))::[]))))
                else false
             then Some ((Func ((S (S (S (S (S (S (S (S O)))))))),
                    (ws::(offset::(v::[])))))::(p'::[]))
             else None
           | None -> None)
        | e::l1 -> None))

(** val memEval : type0 list -> MEVAL.PredEval.coq_MemEvalPred **)

let memEval types' =
  { MEVAL.PredEval.pred_read_word = (sym_read types');
    MEVAL.PredEval.pred_write_word = (sym_write types');
    MEVAL.PredEval.pred_read_byte = (fun p facts0 args p0 -> None);
    MEVAL.PredEval.pred_write_byte = (fun p facts0 args p0 v -> None) }

(** val memEvaluator : type0 list -> MEVAL.coq_MemEvaluator **)

let memEvaluator types' =
  { MEVAL.sread_word = (fun p f0 p0 h ->
    match FM.find (S O) h.SH.impures with
    | Some argss ->
      MEVAL.PredEval.fold_args (types types') (fun args ->
        (memEval types').MEVAL.PredEval.pred_read_word p f0 args p0) argss
    | None -> None); MEVAL.swrite_word = (fun p f0 p0 v h ->
    match FM.find (S O) h.SH.impures with
    | Some argss ->
      (match MEVAL.PredEval.fold_args_update (types types') (fun args ->
               (memEval types').MEVAL.PredEval.pred_write_word p f0 args p0 v)
               argss with
       | Some argss0 ->
         Some { SH.impures = (FM.add (S O) argss0 h.SH.impures); SH.pures =
           h.SH.pures; SH.other = h.SH.other }
       | None -> None)
    | None -> None); MEVAL.sread_byte = (fun p f0 p0 h ->
    match FM.find (S O) h.SH.impures with
    | Some argss ->
      MEVAL.PredEval.fold_args (types types') (fun args ->
        (memEval types').MEVAL.PredEval.pred_read_byte p f0 args p0) argss
    | None -> None); MEVAL.swrite_byte = (fun p f0 p0 v h ->
    match FM.find (S O) h.SH.impures with
    | Some argss ->
      (match MEVAL.PredEval.fold_args_update (types types') (fun args ->
               (memEval types').MEVAL.PredEval.pred_write_byte p f0 args p0 v)
               argss with
       | Some argss0 ->
         Some { SH.impures = (FM.add (S O) argss0 h.SH.impures); SH.pures =
           h.SH.pures; SH.other = h.SH.other }
       | None -> None)
    | None -> None) }

(** val allocated : w -> nat -> nat -> hProp **)

let rec allocated base offset = function
| O -> empB []
| S len' ->
  starB []
    (exB [] (fun v ->
      ptsto32 []
        (match offset with
         | O -> base
         | S n0 ->
           wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))) base
             (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               O)))))))))))))))))))))))))))))))) offset)) v))
    (allocated base (plus (S (S (S (S O)))) offset) len')

type vals = char list -> w

(** val toArray : char list list -> vals -> w list **)

let toArray ns vs =
  map vs ns

(** val locals : char list list -> vals -> nat -> w -> hProp **)

let locals ns vs avail p =
  starB [] (starB [] (injB []) (array (toArray ns vs) p))
    (allocated
      (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) p
        (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))
          (mult (length ns) (S (S (S (S O))))))) O avail)

(** val ascii_eq : char -> char -> bool **)

let ascii_eq a1 a2 =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b1 c1 d1 e1 f1 g1 h1 i1 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b2 c2 d2 e2 f2 g2 h2 i2 ->
      if if if if if if if eqb b1 b2 then eqb c1 c2 else false
                     then eqb d1 d2
                     else false
                  then eqb e1 e2
                  else false
               then eqb f1 f2
               else false
            then eqb g1 g2
            else false
         then eqb h1 h2
         else false
      then eqb i1 i2
      else false)
      a2)
    a1

(** val string_eq : char list -> char list -> bool **)

let rec string_eq s1 s2 =
  match s1 with
  | [] ->
    (match s2 with
     | [] -> true
     | a::s -> false)
  | a1::s1' ->
    (match s2 with
     | [] -> false
     | a2::s2' -> if ascii_eq a1 a2 then string_eq s1' s2' else false)

(** val sel0 : vals -> char list -> w **)

let sel0 vs nm =
  vs nm

(** val upd0 : vals -> char list -> w -> vals **)

let upd0 vs nm v nm' =
  if string_eq nm' nm then v else vs nm'

(** val bedrock_type_string : type0 **)

let bedrock_type_string =
  Obj.magic string_eq

(** val bedrock_type_listString : type0 **)

let bedrock_type_listString x y =
  false

(** val bedrock_type_vals : type0 **)

let bedrock_type_vals x y =
  false

(** val types_r0 : type0 repr **)

let types_r0 =
  { footprint = ((Some bedrock_type_W)::((Some
    bedrock_type_setting_X_state)::(None::(None::((Some
    bedrock_type_nat)::(None::((Some bedrock_type_string)::((Some
    bedrock_type_listString)::((Some bedrock_type_vals)::[])))))))));
    default = emptySet_type }

(** val badLocalVariable : nat **)

let badLocalVariable =
  O

(** val variablePosition : char list list -> char list -> nat **)

let rec variablePosition ns nm =
  match ns with
  | [] -> badLocalVariable
  | nm'::ns' ->
    if string_dec nm' nm
    then O
    else plus (S (S (S (S O)))) (variablePosition ns' nm)

(** val types0 : type0 list -> type0 list **)

let types0 types' =
  repr0 types_r0 types'

type deref_res =
| Nothing
| Constant of expr * nat
| Symbolic of expr * expr * expr

(** val deref0 : type0 list -> expr -> deref_res **)

let deref0 types' = function
| Func (f0, l) ->
  (match f0 with
   | O ->
     (match l with
      | [] -> Nothing
      | base::l0 ->
        (match l0 with
         | [] -> Nothing
         | offset::l1 ->
           (match l1 with
            | [] ->
              (match offset with
               | Func (f1, l2) ->
                 (match f1 with
                  | O -> Nothing
                  | S n0 ->
                    (match n0 with
                     | O -> Nothing
                     | S n1 ->
                       (match n1 with
                        | O -> Nothing
                        | S n2 ->
                          (match n2 with
                           | O -> Nothing
                           | S n3 ->
                             (match n3 with
                              | O -> Nothing
                              | S n4 ->
                                (match n4 with
                                 | O ->
                                   (match l2 with
                                    | [] -> Nothing
                                    | e0::l3 ->
                                      (match e0 with
                                       | Const (t0, k) ->
                                         (match l3 with
                                          | [] ->
                                            (match t0 with
                                             | TvProp ->
                                               Obj.magic (fun _ -> Nothing) k
                                             | TvType n5 ->
                                               (match n5 with
                                                | O -> Nothing
                                                | S n6 ->
                                                  (match n6 with
                                                   | O -> Nothing
                                                   | S n7 ->
                                                     (match n7 with
                                                      | O -> Nothing
                                                      | S n8 ->
                                                        (match n8 with
                                                         | O -> Nothing
                                                         | S n9 ->
                                                           (match n9 with
                                                            | O ->
                                                              (match 
                                                               div4
                                                                 (Obj.magic
                                                                   k) with
                                                               | Some k' ->
                                                                 Constant
                                                                   (base, k')
                                                               | None ->
                                                                 Nothing)
                                                            | S n10 ->
                                                              Nothing))))))
                                          | e1::l4 -> Nothing)
                                       | Func (f2, l4) ->
                                         (match f2 with
                                          | O -> Nothing
                                          | S n5 ->
                                            (match n5 with
                                             | O -> Nothing
                                             | S n6 ->
                                               (match n6 with
                                                | O -> Nothing
                                                | S n7 ->
                                                  (match n7 with
                                                   | O -> Nothing
                                                   | S n8 ->
                                                     (match n8 with
                                                      | O -> Nothing
                                                      | S n9 ->
                                                        (match n9 with
                                                         | O -> Nothing
                                                         | S n10 ->
                                                           (match n10 with
                                                            | O -> Nothing
                                                            | S n11 ->
                                                              (match n11 with
                                                               | O -> Nothing
                                                               | S n12 ->
                                                                 (match n12 with
                                                                  | O ->
                                                                    Nothing
                                                                  | S n13 ->
                                                                    (match n13 with
                                                                    | O ->
                                                                    Nothing
                                                                    | S n14 ->
                                                                    (match n14 with
                                                                    | O ->
                                                                    Nothing
                                                                    | S n15 ->
                                                                    (match n15 with
                                                                    | O ->
                                                                    Nothing
                                                                    | S n16 ->
                                                                    (match n16 with
                                                                    | O ->
                                                                    Nothing
                                                                    | S n17 ->
                                                                    (match n17 with
                                                                    | O ->
                                                                    Nothing
                                                                    | S n18 ->
                                                                    (match n18 with
                                                                    | O ->
                                                                    (match l4 with
                                                                    | [] ->
                                                                    Nothing
                                                                    | xs::l5 ->
                                                                    (match l5 with
                                                                    | [] ->
                                                                    Nothing
                                                                    | x::l6 ->
                                                                    (match l6 with
                                                                    | [] ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    Symbolic
                                                                    (base,
                                                                    xs, x)
                                                                    | e1::l7 ->
                                                                    Nothing)
                                                                    | e1::l7 ->
                                                                    Nothing)))
                                                                    | S n19 ->
                                                                    Nothing)))))))))))))))
                                       | _ -> Nothing))
                                 | S n5 -> Nothing))))))
               | _ -> Nothing)
            | e0::l2 -> Nothing)))
   | S n0 -> Nothing)
| _ -> Nothing

(** val listIn : type0 list -> expr -> char list list option **)

let rec listIn types' = function
| Func (f0, l) ->
  (match f0 with
   | O -> None
   | S n0 ->
     (match n0 with
      | O -> None
      | S n1 ->
        (match n1 with
         | O -> None
         | S n2 ->
           (match n2 with
            | O -> None
            | S n3 ->
              (match n3 with
               | O -> None
               | S n4 ->
                 (match n4 with
                  | O -> None
                  | S n5 ->
                    (match n5 with
                     | O -> None
                     | S n6 ->
                       (match n6 with
                        | O -> None
                        | S n7 ->
                          (match n7 with
                           | O -> None
                           | S n8 ->
                             (match n8 with
                              | O ->
                                (match l with
                                 | [] -> Some []
                                 | e0::l0 -> None)
                              | S n9 ->
                                (match n9 with
                                 | O ->
                                   (match l with
                                    | [] -> None
                                    | e0::l0 ->
                                      (match e0 with
                                       | Const (tp, s) ->
                                         (match l0 with
                                          | [] -> None
                                          | t0::l1 ->
                                            (match l1 with
                                             | [] ->
                                               (match tp with
                                                | TvProp ->
                                                  Obj.magic (fun _ -> None) s
                                                | TvType n10 ->
                                                  (match n10 with
                                                   | O -> None
                                                   | S n11 ->
                                                     (match n11 with
                                                      | O -> None
                                                      | S n12 ->
                                                        (match n12 with
                                                         | O -> None
                                                         | S n13 ->
                                                           (match n13 with
                                                            | O -> None
                                                            | S n14 ->
                                                              (match n14 with
                                                               | O -> None
                                                               | S n15 ->
                                                                 (match n15 with
                                                                  | O -> None
                                                                  | S n16 ->
                                                                    (match n16 with
                                                                    | O ->
                                                                    (match 
                                                                    listIn
                                                                    types' t0 with
                                                                    | Some t1 ->
                                                                    Some
                                                                    ((Obj.magic
                                                                    s)::t1)
                                                                    | None ->
                                                                    None)
                                                                    | S n17 ->
                                                                    None))))))))
                                             | e1::l2 -> None))
                                       | _ -> None))
                                 | S n10 -> None)))))))))))
| _ -> None

(** val sym_sel : type0 list -> expr -> char list -> expr **)

let rec sym_sel types' vs nm =
  match vs with
  | Func (f0, l) ->
    (match f0 with
     | O ->
       Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))), (vs::((Const
         ((TvType (S (S (S (S (S (S O))))))), (Obj.magic nm)))::[])))
     | S n0 ->
       (match n0 with
        | O ->
          Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))), (vs::((Const
            ((TvType (S (S (S (S (S (S O))))))), (Obj.magic nm)))::[])))
        | S n1 ->
          (match n1 with
           | O ->
             Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))),
               (vs::((Const ((TvType (S (S (S (S (S (S O))))))),
               (Obj.magic nm)))::[])))
           | S n2 ->
             (match n2 with
              | O ->
                Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))),
                  (vs::((Const ((TvType (S (S (S (S (S (S O))))))),
                  (Obj.magic nm)))::[])))
              | S n3 ->
                (match n3 with
                 | O ->
                   Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))),
                     (vs::((Const ((TvType (S (S (S (S (S (S O))))))),
                     (Obj.magic nm)))::[])))
                 | S n4 ->
                   (match n4 with
                    | O ->
                      Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))),
                        (vs::((Const ((TvType (S (S (S (S (S (S O))))))),
                        (Obj.magic nm)))::[])))
                    | S n5 ->
                      (match n5 with
                       | O ->
                         Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))),
                           (vs::((Const ((TvType (S (S (S (S (S (S O))))))),
                           (Obj.magic nm)))::[])))
                       | S n6 ->
                         (match n6 with
                          | O ->
                            Func ((S (S (S (S (S (S (S (S (S (S (S
                              O))))))))))), (vs::((Const ((TvType (S (S (S (S
                              (S (S O))))))), (Obj.magic nm)))::[])))
                          | S n7 ->
                            (match n7 with
                             | O ->
                               Func ((S (S (S (S (S (S (S (S (S (S (S
                                 O))))))))))), (vs::((Const ((TvType (S (S (S
                                 (S (S (S O))))))), (Obj.magic nm)))::[])))
                             | S n8 ->
                               (match n8 with
                                | O ->
                                  Func ((S (S (S (S (S (S (S (S (S (S (S
                                    O))))))))))), (vs::((Const ((TvType (S (S
                                    (S (S (S (S O))))))),
                                    (Obj.magic nm)))::[])))
                                | S n9 ->
                                  (match n9 with
                                   | O ->
                                     Func ((S (S (S (S (S (S (S (S (S (S (S
                                       O))))))))))), (vs::((Const ((TvType (S
                                       (S (S (S (S (S O))))))),
                                       (Obj.magic nm)))::[])))
                                   | S n10 ->
                                     (match n10 with
                                      | O ->
                                        Func ((S (S (S (S (S (S (S (S (S (S
                                          (S O))))))))))), (vs::((Const
                                          ((TvType (S (S (S (S (S (S
                                          O))))))), (Obj.magic nm)))::[])))
                                      | S n11 ->
                                        (match n11 with
                                         | O ->
                                           (match l with
                                            | [] ->
                                              Func ((S (S (S (S (S (S (S (S
                                                (S (S (S O))))))))))),
                                                (vs::((Const ((TvType (S (S
                                                (S (S (S (S O))))))),
                                                (Obj.magic nm)))::[])))
                                            | vs'::l0 ->
                                              (match l0 with
                                               | [] ->
                                                 Func ((S (S (S (S (S (S (S
                                                   (S (S (S (S O))))))))))),
                                                   (vs::((Const ((TvType (S
                                                   (S (S (S (S (S O))))))),
                                                   (Obj.magic nm)))::[])))
                                               | e::l1 ->
                                                 (match e with
                                                  | Const (tp, nm') ->
                                                    (match l1 with
                                                     | [] ->
                                                       Func ((S (S (S (S (S
                                                         (S (S (S (S (S (S
                                                         O))))))))))),
                                                         (vs::((Const
                                                         ((TvType (S (S (S (S
                                                         (S (S O))))))),
                                                         (Obj.magic nm)))::[])))
                                                     | v::l2 ->
                                                       (match l2 with
                                                        | [] ->
                                                          (match tp with
                                                           | TvProp ->
                                                             Obj.magic
                                                               (fun _ -> Func
                                                               ((S (S (S (S
                                                               (S (S (S (S (S
                                                               (S (S
                                                               O))))))))))),
                                                               (vs::((Const
                                                               ((TvType (S (S
                                                               (S (S (S (S
                                                               O))))))),
                                                               (Obj.magic nm)))::[]))))
                                                               nm'
                                                           | TvType n12 ->
                                                             (match n12 with
                                                              | O ->
                                                                Func ((S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S
                                                                  O))))))))))),
                                                                  (vs::((Const
                                                                  ((TvType (S
                                                                  (S (S (S (S
                                                                  (S
                                                                  O))))))),
                                                                  (Obj.magic
                                                                    nm)))::[])))
                                                              | S n13 ->
                                                                (match n13 with
                                                                 | O ->
                                                                   Func ((S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))),
                                                                    (vs::((Const
                                                                    ((TvType
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))),
                                                                    (Obj.magic
                                                                    nm)))::[])))
                                                                 | S n14 ->
                                                                   (match n14 with
                                                                    | O ->
                                                                    Func ((S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))),
                                                                    (vs::((Const
                                                                    ((TvType
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))),
                                                                    (Obj.magic
                                                                    nm)))::[])))
                                                                    | S n15 ->
                                                                    (match n15 with
                                                                    | O ->
                                                                    Func ((S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))),
                                                                    (vs::((Const
                                                                    ((TvType
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))),
                                                                    (Obj.magic
                                                                    nm)))::[])))
                                                                    | S n16 ->
                                                                    (match n16 with
                                                                    | O ->
                                                                    Func ((S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))),
                                                                    (vs::((Const
                                                                    ((TvType
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))),
                                                                    (Obj.magic
                                                                    nm)))::[])))
                                                                    | S n17 ->
                                                                    (match n17 with
                                                                    | O ->
                                                                    Func ((S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))),
                                                                    (vs::((Const
                                                                    ((TvType
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))),
                                                                    (Obj.magic
                                                                    nm)))::[])))
                                                                    | S n18 ->
                                                                    (match n18 with
                                                                    | O ->
                                                                    if 
                                                                    string_eq
                                                                    (Obj.magic
                                                                    nm') nm
                                                                    then v
                                                                    else 
                                                                    sym_sel
                                                                    types'
                                                                    vs' nm
                                                                    | S n19 ->
                                                                    Func ((S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S
                                                                    O))))))))))),
                                                                    (vs::((Const
                                                                    ((TvType
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    O))))))),
                                                                    (Obj.magic
                                                                    nm)))::[])))))))))))
                                                        | e0::l3 ->
                                                          Func ((S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S O))))))))))),
                                                            (vs::((Const
                                                            ((TvType (S (S (S
                                                            (S (S (S
                                                            O))))))),
                                                            (Obj.magic nm)))::[])))))
                                                  | _ ->
                                                    Func ((S (S (S (S (S (S
                                                      (S (S (S (S (S
                                                      O))))))))))),
                                                      (vs::((Const ((TvType
                                                      (S (S (S (S (S (S
                                                      O))))))),
                                                      (Obj.magic nm)))::[]))))))
                                         | S n12 ->
                                           Func ((S (S (S (S (S (S (S (S (S
                                             (S (S O))))))))))), (vs::((Const
                                             ((TvType (S (S (S (S (S (S
                                             O))))))),
                                             (Obj.magic nm)))::[]))))))))))))))))
  | _ ->
    Func ((S (S (S (S (S (S (S (S (S (S (S O))))))))))), (vs::((Const
      ((TvType (S (S (S (S (S (S O))))))), (Obj.magic nm)))::[])))

(** val sym_read0 :
    type0 list -> proverT -> facts -> expr list -> expr -> expr option **)

let sym_read0 types' prover summ args p =
  match args with
  | [] -> None
  | ns::l ->
    (match l with
     | [] -> None
     | vs::l0 ->
       (match l0 with
        | [] -> None
        | e::l1 ->
          (match l1 with
           | [] -> None
           | p'::l2 ->
             (match l2 with
              | [] ->
                (match deref0 types' p with
                 | Nothing -> None
                 | Constant (base, offset) ->
                   (match listIn types' ns with
                    | Some ns' ->
                      if prover.prove summ (Equal ((TvType O), p', base))
                      then (match nth_error ns' offset with
                            | Some nm -> Some (sym_sel types' vs nm)
                            | None -> None)
                      else None
                    | None -> None)
                 | Symbolic (base, nms, nm) ->
                   if if if prover.prove summ (Equal ((TvType O), p', base))
                         then prover.prove summ (Equal ((TvType (S (S (S (S
                                (S (S (S O)))))))), nms, ns))
                         else false
                      then prover.prove summ (Func ((S (S (S (S (S (S (S (S
                             (S (S (S (S (S O))))))))))))), (nm::(nms::[]))))
                      else false
                   then Some
                          (match nm with
                           | Const (tp, nm') ->
                             (match tp with
                              | TvProp ->
                                Obj.magic (fun _ -> Func ((S (S (S (S (S (S
                                  (S (S (S (S (S O))))))))))),
                                  (vs::(nm::[])))) nm'
                              | TvType n0 ->
                                (match n0 with
                                 | O ->
                                   Func ((S (S (S (S (S (S (S (S (S (S (S
                                     O))))))))))), (vs::(nm::[])))
                                 | S n1 ->
                                   (match n1 with
                                    | O ->
                                      Func ((S (S (S (S (S (S (S (S (S (S (S
                                        O))))))))))), (vs::(nm::[])))
                                    | S n2 ->
                                      (match n2 with
                                       | O ->
                                         Func ((S (S (S (S (S (S (S (S (S (S
                                           (S O))))))))))), (vs::(nm::[])))
                                       | S n3 ->
                                         (match n3 with
                                          | O ->
                                            Func ((S (S (S (S (S (S (S (S (S
                                              (S (S O))))))))))),
                                              (vs::(nm::[])))
                                          | S n4 ->
                                            (match n4 with
                                             | O ->
                                               Func ((S (S (S (S (S (S (S (S
                                                 (S (S (S O))))))))))),
                                                 (vs::(nm::[])))
                                             | S n5 ->
                                               (match n5 with
                                                | O ->
                                                  Func ((S (S (S (S (S (S (S
                                                    (S (S (S (S O))))))))))),
                                                    (vs::(nm::[])))
                                                | S n6 ->
                                                  (match n6 with
                                                   | O ->
                                                     sym_sel types' vs
                                                       (Obj.magic nm')
                                                   | S n7 ->
                                                     Func ((S (S (S (S (S (S
                                                       (S (S (S (S (S
                                                       O))))))))))),
                                                       (vs::(nm::[])))))))))))
                           | _ ->
                             Func ((S (S (S (S (S (S (S (S (S (S (S
                               O))))))))))), (vs::(nm::[]))))
                   else None)
              | e0::l3 -> None))))

(** val sym_write0 :
    type0 list -> proverT -> facts -> expr list -> expr -> expr -> expr list
    option **)

let sym_write0 types' prover summ args p v =
  match args with
  | [] -> None
  | ns::l ->
    (match l with
     | [] -> None
     | vs::l0 ->
       (match l0 with
        | [] -> None
        | avail::l1 ->
          (match l1 with
           | [] -> None
           | p'::l2 ->
             (match l2 with
              | [] ->
                (match deref0 types' p with
                 | Nothing -> None
                 | Constant (base, offset) ->
                   (match listIn types' ns with
                    | Some ns' ->
                      if prover.prove summ (Equal ((TvType O), p', base))
                      then (match nth_error ns' offset with
                            | Some nm ->
                              Some (ns::((Func ((S (S (S (S (S (S (S (S (S (S
                                (S (S O)))))))))))), (vs::((Const ((TvType (S
                                (S (S (S (S (S O))))))),
                                (Obj.magic nm)))::(v::[])))))::(avail::(p'::[]))))
                            | None -> None)
                      else None
                    | None -> None)
                 | Symbolic (base, nms, nm) ->
                   if if if prover.prove summ (Equal ((TvType O), p', base))
                         then prover.prove summ (Equal ((TvType (S (S (S (S
                                (S (S (S O)))))))), nms, ns))
                         else false
                      then prover.prove summ (Func ((S (S (S (S (S (S (S (S
                             (S (S (S (S (S O))))))))))))), (nm::(nms::[]))))
                      else false
                   then Some (ns::((Func ((S (S (S (S (S (S (S (S (S (S (S (S
                          O)))))))))))),
                          (vs::(nm::(v::[])))))::(avail::(p'::[]))))
                   else None)
              | e::l3 -> None))))

(** val memEval0 : type0 list -> MEVAL.PredEval.coq_MemEvalPred **)

let memEval0 types' =
  { MEVAL.PredEval.pred_read_word = (sym_read0 types');
    MEVAL.PredEval.pred_write_word = (sym_write0 types');
    MEVAL.PredEval.pred_read_byte = (fun p facts0 args p0 -> None);
    MEVAL.PredEval.pred_write_byte = (fun p facts0 args p0 v -> None) }

(** val memEvaluator0 : type0 list -> MEVAL.coq_MemEvaluator **)

let memEvaluator0 types' =
  { MEVAL.sread_word = (fun p f0 p0 h ->
    match FM.find (S (S O)) h.SH.impures with
    | Some argss ->
      MEVAL.PredEval.fold_args (types0 types') (fun args ->
        (memEval0 types').MEVAL.PredEval.pred_read_word p f0 args p0) argss
    | None -> None); MEVAL.swrite_word = (fun p f0 p0 v h ->
    match FM.find (S (S O)) h.SH.impures with
    | Some argss ->
      (match MEVAL.PredEval.fold_args_update (types0 types') (fun args ->
               (memEval0 types').MEVAL.PredEval.pred_write_word p f0 args p0
                 v) argss with
       | Some argss0 ->
         Some { SH.impures = (FM.add (S (S O)) argss0 h.SH.impures);
           SH.pures = h.SH.pures; SH.other = h.SH.other }
       | None -> None)
    | None -> None); MEVAL.sread_byte = (fun p f0 p0 h ->
    match FM.find (S (S O)) h.SH.impures with
    | Some argss ->
      MEVAL.PredEval.fold_args (types0 types') (fun args ->
        (memEval0 types').MEVAL.PredEval.pred_read_byte p f0 args p0) argss
    | None -> None); MEVAL.swrite_byte = (fun p f0 p0 v h ->
    match FM.find (S (S O)) h.SH.impures with
    | Some argss ->
      (match MEVAL.PredEval.fold_args_update (types0 types') (fun args ->
               (memEval0 types').MEVAL.PredEval.pred_write_byte p f0 args p0
                 v) argss with
       | Some argss0 ->
         Some { SH.impures = (FM.add (S (S O)) argss0 h.SH.impures);
           SH.pures = h.SH.pures; SH.other = h.SH.other }
       | None -> None)
    | None -> None) }

(** val reserved : w -> nat -> hProp **)

let reserved p len =
  allocated p O len

(** val merge0 : vals -> vals -> char list list -> vals **)

let rec merge0 vs vs' = function
| [] -> vs'
| nm::ns' -> upd0 (merge0 vs vs' ns') nm (sel0 vs nm)

type chunk' =
| StraightLine of instr list
| Structured of instr list * (assert0 LabelMap.t -> char list -> __ -> cmd)

type chunk = char list list -> nat -> chunk'

(** val toCmd :
    chunk -> assert0 LabelMap.t -> char list -> char list list -> nat -> cmd **)

let toCmd ch im mn ns res =
  match ch ns res with
  | StraightLine is -> straightline_ im mn is
  | Structured (is, c) ->
    (match is with
     | [] -> c im mn __
     | i::l -> seq_ im mn (straightline_ im mn is) (c im mn __))

(** val seq : chunk -> chunk -> chunk **)

let seq ch1 ch2 ns res =
  match ch1 ns res with
  | StraightLine is1 ->
    (match ch2 ns res with
     | StraightLine is2 -> StraightLine (app is1 is2)
     | Structured (is2, c) -> Structured ((app is1 is2), c))
  | Structured (is1, c1) ->
    Structured (is1, (fun im mn _ ->
      seq_ im mn (c1 im mn __) (toCmd ch2 im mn ns res)))

(** val instr0 : (char list list -> instr) -> chunk **)

let instr0 i ns x =
  StraightLine ((i ns)::[])

(** val diverge : chunk **)

let diverge x x0 =
  Structured ([], (fun im mn _ -> diverge_ im mn))

type rvalue' = char list list -> rvalue

type condition = { cOperand1 : rvalue'; cTest : test; cOperand2 : rvalue' }

(** val cOperand1 : condition -> rvalue' **)

let cOperand1 x = x.cOperand1

(** val cTest : condition -> test **)

let cTest x = x.cTest

(** val cOperand2 : condition -> rvalue' **)

let cOperand2 x = x.cOperand2

(** val if_0 : condition -> chunk -> chunk -> chunk **)

let if_0 c then0 else0 ns res =
  Structured ([], (fun im mn _ ->
    if_ im mn (c.cOperand1 ns) c.cTest (c.cOperand2 ns)
      (toCmd then0 im mn ns res) (toCmd else0 im mn ns res)))

(** val while_0 :
    (char list list -> nat -> assert0) -> condition -> chunk -> chunk **)

let while_0 inv0 c body5 ns res =
  Structured ([], (fun im mn _ ->
    while_ im mn (inv0 ns res) (c.cOperand1 ns) c.cTest (c.cOperand2 ns)
      (toCmd body5 im mn ns res)))

(** val goto : rvalue' -> chunk **)

let goto rv ns x =
  Structured ([], (fun im mn _ ->
    match rv ns with
    | RvLabel f0 -> goto_ im mn f0
    | _ -> iGoto im mn (rv ns)))

(** val setArgs : nat -> rvalue' list -> char list list -> instr list **)

let rec setArgs slot args ns =
  match args with
  | [] -> []
  | arg::args' ->
    (Binop ((LvReg Rv), (RvLval (LvReg Sp)), Plus, (RvImm
      (natToW (plus (S (S (S (S O)))) (mult (S (S (S (S O)))) (length ns)))))))::((Assign
      ((LvMem (Indir (Rv, (natToW slot)))),
      (arg ns)))::(setArgs (plus (S (S (S (S O)))) slot) args' ns))

type lvalue' = char list list -> lvalue

(** val call_0 :
    lvalue' option -> label -> rvalue' list -> (char list list -> nat ->
    assert0) -> chunk **)

let call_0 retOpt f0 args afterCall ns res =
  Structured
    ((app (setArgs (S (S (S (S O)))) args ns) ((Binop ((LvReg Sp), (RvLval
       (LvReg Sp)), Plus, (RvImm
       (natToW (plus (S (S (S (S O)))) (mult (S (S (S (S O)))) (length ns)))))))::[])),
    (fun im mn _ ->
    seq_ im mn (call_ im mn f0 (afterCall ns res))
      (straightline_ im mn ((Binop ((LvReg Sp), (RvLval (LvReg Sp)), Minus,
        (RvImm
        (natToW
          (plus (S (S (S (S O)))) (mult (S (S (S (S O)))) (length ns)))))))::(
        match retOpt with
        | Some lv -> (Assign ((lv ns), (RvLval (LvReg Rv))))::[]
        | None -> [])))))

type function1 = { fName : char list; fVars : char list list;
                   fReserved : nat; fPrecondition : assert0; fBody : 
                   chunk }

(** val bmodule_0 : import list -> char list -> function1 list -> module0 **)

let bmodule_0 im mn fs0 =
  bmodule_ im mn
    (map (fun p ->
      let { fName = f0; fVars = ns; fReserved = res; fPrecondition = pre;
        fBody = ch } = p
      in
      Pair ((Pair (f0, pre)), (fun im' _ -> toCmd ch im' mn ns res))) fs0)

(** val regInL : reg -> lvalue' **)

let regInL r x =
  LvReg r

(** val labl : char list -> char list -> label **)

let labl modl func1 =
  Pair (modl, (Global func1))

(** val lvalIn : lvalue' -> rvalue' **)

let lvalIn lv ns =
  RvLval (lv ns)

(** val immInR : w -> rvalue' **)

let immInR w0 x =
  RvImm w0

type rhs =
| Rvalue of rvalue'
| Bop of rvalue' * binop * rvalue'

(** val assign' : lvalue' -> rhs -> chunk **)

let assign' lv rh =
  instr0 (fun ns ->
    match rh with
    | Rvalue rv -> Assign ((lv ns), (rv ns))
    | Bop (rv1, bo, rv2) -> Binop ((lv ns), (rv1 ns), bo, (rv2 ns)))

(** val variableSlot : char list -> lvalue' **)

let variableSlot nm ns =
  LvMem (Indir (Sp,
    (natToW (plus (S (S (S (S O)))) (variablePosition ns nm)))))

type qspec =
| Body of hProp
| Quant of (__ -> qspec)

(** val qspecOut :
    qspec -> __ list -> (hProp -> ('a1, 'a2) propX) -> ('a1, 'a2) propX **)

let rec qspecOut qs b0 k =
  match qs with
  | Body p -> k p
  | Quant f0 -> Exists (b0, (fun x -> qspecOut (f0 x) b0 k))

(** val localsInvariant :
    (vals -> w -> qspec) -> (vals -> w -> w -> qspec) -> bool -> (w -> w) ->
    char list list -> nat -> assert0 **)

let localsInvariant pre post2 rpStashed adjustSp ns res st0 =
  let sp = adjustSp ((snd st0).regs Sp) in
  ExistsX ([], (Exists ((__::[]), (fun vs ->
  qspecOut (pre (sel0 (Obj.magic vs)) ((snd st0).regs Rv)) (__::[])
    (fun pRE -> And ((__::[]),
    (SepFormula.sepFormula (__::[])
      (starB (__::[])
        (lift (__::[])
          (starB [] (locals (('r'::('p'::[]))::ns) (Obj.magic vs) res sp)
            pRE)) (hvarB (__::[]) (fun x -> Var0 ([], (Obj.magic x))))) st0),
    (ExistsX ((__::[]), (And ((__::(__::[])), (Cptr ((__::(__::[])),
    (fst (Pair
      ((if rpStashed
        then sel0 (Obj.magic vs) ('r'::('p'::[]))
        else (snd st0).regs Rp), (fst st0)))), (fun x -> Var0 ((__::[]),
    (Obj.magic x))))), (Forall ((__::(__::[])), (fun st1 -> Imply
    ((__::(__::[])),
    (let st' = Pair
       ((snd (Pair
          ((if rpStashed
            then sel0 (Obj.magic vs) ('r'::('p'::[]))
            else (snd st0).regs Rp), (fst st0)))), st1)
     in
     And ((__::(__::[])), (Inj (__::(__::[]))), (Exists ((__::(__::[])),
     (fun vs' ->
     qspecOut
       (post2 (sel0 (Obj.magic vs)) ((snd st0).regs Rv)
         ((snd (Obj.magic st')).regs Rv)) (__::(__::[])) (fun pOST ->
       SepFormula.sepFormula (__::(__::[]))
         (starB (__::(__::[]))
           (lift (__::(__::[]))
             (starB [] (locals (('r'::('p'::[]))::ns) (Obj.magic vs') res sp)
               pOST))
           (hvarB (__::(__::[])) (fun x -> Lift ((__::[]), (Var0 ([],
             (Obj.magic x))))))) (Obj.magic st'))))))),
    (let x = Pair
       ((snd (Pair
          ((if rpStashed
            then sel0 (Obj.magic vs) ('r'::('p'::[]))
            else (snd st0).regs Rp), (fst st0)))), st1)
     in
     Var0 ((__::[]), (Obj.magic x)))))))))))))))))

type spec0 = { reserved0 : nat; formals : char list list;
               precondition : (char list list option -> assert0) }

(** val reserved0 : spec0 -> nat **)

let reserved0 x = x.reserved0

(** val formals : spec0 -> char list list **)

let formals x = x.formals

(** val precondition : spec0 -> char list list option -> assert0 **)

let precondition x = x.precondition

(** val default_type : type0 **)

let default_type x y =
  false

module ReifySepExpr = 
 functor (SEP__1:SepExpr) ->
 struct 
  
 end

module type SynUnifier = 
 sig 
  type coq_Subst 
  
  val coq_Subst_empty : type0 list -> coq_Subst
  
  val coq_Subst_lookup : type0 list -> uvar -> coq_Subst -> expr option
  
  val coq_Subst_size : type0 list -> coq_Subst -> nat
  
  val coq_Subst_domain : type0 list -> coq_Subst -> uvar list
  
  val exprUnify :
    type0 list -> nat -> expr -> expr -> coq_Subst -> coq_Subst option
  
  val exprInstantiate : type0 list -> coq_Subst -> expr -> expr
 end

module Unifier = 
 functor (E:Coq_OrderedType with type t = uvar) ->
 struct 
  module FM = Coq0_Make(E)
  
  module FACTS = Facts(FM)
  
  module MFACTS = MoreFMapFacts(FM)
  
  module PROPS = Properties(FM)
  
  (** val normalized : type0 list -> expr FM.t -> expr -> bool **)
  
  let rec normalized types4 ctx = function
  | Func (f0, l) ->
    fold_right (fun x acc -> if acc then normalized types4 ctx x else false)
      true l
  | Equal (t0, e1, e2) ->
    if normalized types4 ctx e1 then normalized types4 ctx e2 else false
  | Not e0 -> normalized types4 ctx e0
  | UVar x ->
    (match FM.find x ctx with
     | Some e0 -> false
     | None -> true)
  | _ -> true
  
  type coq_Subst = (expr FM.t, __) sigT
  
  (** val subst_empty : type0 list -> expr FM.t **)
  
  let subst_empty types4 =
    FM.empty
  
  (** val coq_Subst_empty : type0 list -> coq_Subst **)
  
  let coq_Subst_empty types4 =
    ExistT ((subst_empty types4), __)
  
  (** val subst_lookup : type0 list -> nat -> expr FM.t -> expr option **)
  
  let subst_lookup types4 k s =
    FM.find k s
  
  (** val coq_Subst_lookup :
      type0 list -> nat -> coq_Subst -> expr option **)
  
  let coq_Subst_lookup types4 k s =
    subst_lookup types4 k (projT1 s)
  
  (** val coq_Subst_size : type0 list -> coq_Subst -> nat **)
  
  let coq_Subst_size types4 s =
    FM.cardinal (projT1 s)
  
  (** val coq_Subst_domain : type0 list -> coq_Subst -> uvar list **)
  
  let coq_Subst_domain types4 s =
    map fst (FM.elements (projT1 s))
  
  (** val subst_exprInstantiate : type0 list -> expr FM.t -> expr -> expr **)
  
  let rec subst_exprInstantiate types4 sub0 e = match e with
  | Func (f0, args) ->
    Func (f0, (map (subst_exprInstantiate types4 sub0) args))
  | Equal (t0, l, r) ->
    Equal (t0, (subst_exprInstantiate types4 sub0 l),
      (subst_exprInstantiate types4 sub0 r))
  | Not e0 -> Not (subst_exprInstantiate types4 sub0 e0)
  | UVar n0 ->
    (match subst_lookup types4 n0 sub0 with
     | Some v -> v
     | None -> e)
  | _ -> e
  
  (** val exprInstantiate : type0 list -> coq_Subst -> expr -> expr **)
  
  let exprInstantiate types4 sub0 =
    subst_exprInstantiate types4 (projT1 sub0)
  
  (** val subst_set :
      type0 list -> nat -> expr -> expr FM.t -> expr FM.t option **)
  
  let subst_set types4 k v s =
    let v' = subst_exprInstantiate types4 s v in
    if mentionsU types4 k v'
    then None
    else let s0 = FM.add k v' s in
         let s1 = FM.map (subst_exprInstantiate types4 s0) s0 in Some s1
  
  (** val internal_eq_rew_fwd_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)
  
  let internal_eq_rew_fwd_r_dep x y hC =
    hC
  
  (** val coq_Subst_set :
      type0 list -> nat -> expr -> coq_Subst -> coq_Subst option **)
  
  let coq_Subst_set types4 k v s =
    match subst_set types4 k v (projT1 s) with
    | Some s' -> Some (ExistT (s', __))
    | None -> None
  
  (** val dep_in :
      type0 list -> expr list -> (expr -> expr -> coq_Subst -> __ ->
      coq_Subst option) -> expr list -> expr list -> coq_Subst -> coq_Subst
      option **)
  
  let rec dep_in types4 lS f0 ls rs sub0 =
    match ls with
    | [] ->
      (match rs with
       | [] -> Some sub0
       | e::l -> None)
    | l::ls0 ->
      (match rs with
       | [] -> None
       | r::rs0 ->
         (match f0 l r sub0 __ with
          | Some sub1 -> dep_in types4 lS f0 ls0 rs0 sub1
          | None -> None))
  
  (** val exprUnify_recursor :
      type0 list -> (nat, expr) prod -> ((nat, expr) prod -> __ -> expr ->
      coq_Subst -> coq_Subst option) -> expr -> coq_Subst -> coq_Subst option **)
  
  let exprUnify_recursor types4 bound_l recur r sub0 =
    let Pair (bound, l) = bound_l in
    (match l with
     | Const (t0, v) ->
       let l0 = Const (t0, v) in
       (match r with
        | Const (t', v') ->
          if equiv_dec eqDec_tvar t0 t'
          then if get_Eq types4 t0 v v' then Some sub0 else None
          else None
        | UVar u ->
          (match coq_Subst_lookup types4 u sub0 with
           | Some r' ->
             (match bound with
              | O -> None
              | S bound0 -> recur (Pair (bound0, l0)) __ r' sub0)
           | None -> coq_Subst_set types4 u l0 sub0)
        | _ -> None)
     | Var v ->
       let l0 = Var v in
       (match r with
        | Var v' -> if eq_nat_dec v v' then Some sub0 else None
        | UVar u ->
          (match coq_Subst_lookup types4 u sub0 with
           | Some r' ->
             (match bound with
              | O -> None
              | S bound0 -> recur (Pair (bound0, l0)) __ r' sub0)
           | None -> coq_Subst_set types4 u l0 sub0)
        | _ -> None)
     | Func (f1, args1) ->
       let l0 = Func (f1, args1) in
       (match r with
        | Func (f2, args2) ->
          if beq_nat f1 f2
          then dep_in types4 args1 (fun l1 r0 s _ ->
                 recur (Pair (bound, l1)) __ r0 s) args1 args2 sub0
          else None
        | UVar u ->
          (match coq_Subst_lookup types4 u sub0 with
           | Some r' ->
             (match bound with
              | O -> None
              | S bound0 -> recur (Pair (bound0, l0)) __ r' sub0)
           | None -> coq_Subst_set types4 u l0 sub0)
        | _ -> None)
     | Equal (t1, e1, f1) ->
       let l0 = Equal (t1, e1, f1) in
       (match r with
        | Equal (t2, e2, f2) ->
          if equiv_dec eqDec_tvar t1 t2
          then (match recur (Pair (bound, e1)) __ e2 sub0 with
                | Some sub1 -> recur (Pair (bound, f1)) __ f2 sub1
                | None -> None)
          else None
        | UVar u ->
          (match coq_Subst_lookup types4 u sub0 with
           | Some r' ->
             (match bound with
              | O -> None
              | S bound0 -> recur (Pair (bound0, l0)) __ r' sub0)
           | None -> coq_Subst_set types4 u l0 sub0)
        | _ -> None)
     | Not e1 ->
       let l0 = Not e1 in
       (match r with
        | Not e2 -> recur (Pair (bound, e1)) __ e2 sub0
        | UVar u ->
          (match coq_Subst_lookup types4 u sub0 with
           | Some r' ->
             (match bound with
              | O -> None
              | S bound0 -> recur (Pair (bound0, l0)) __ r' sub0)
           | None -> coq_Subst_set types4 u l0 sub0)
        | _ -> None)
     | UVar u ->
       (match r with
        | UVar u0 ->
          if beq_nat u u0
          then Some sub0
          else (match coq_Subst_lookup types4 u sub0 with
                | Some l' ->
                  (match coq_Subst_lookup types4 u0 sub0 with
                   | Some r' ->
                     (match bound with
                      | O -> None
                      | S bound0 -> recur (Pair (bound0, l')) __ r' sub0)
                   | None -> coq_Subst_set types4 u0 l' sub0)
                | None -> coq_Subst_set types4 u (UVar u0) sub0)
        | _ ->
          (match coq_Subst_lookup types4 u sub0 with
           | Some l' ->
             (match bound with
              | O -> None
              | S bound0 -> recur (Pair (bound0, l')) __ r sub0)
           | None -> coq_Subst_set types4 u r sub0)))
  
  (** val exprUnify :
      type0 list -> nat -> expr -> expr -> coq_Subst -> coq_Subst option **)
  
  let exprUnify types4 bound l =
    let rec fix_F x =
      exprUnify_recursor types4 x (fun y _ -> fix_F y)
    in fix_F (Pair (bound, l))
 end

module UNIFIER = Unifier(Ordered_nat)

module type SepLemma = 
 sig 
  module SE : 
   SepExpr
  
  type lemma = { coq_Foralls : variables; coq_Hyps : expr list;
                 coq_Lhs : SE.sexpr; coq_Rhs : SE.sexpr }
  
  val lemma_rect :
    type0 list -> tvar -> tvar -> (variables -> expr list -> SE.sexpr ->
    SE.sexpr -> 'a1) -> lemma -> 'a1
  
  val lemma_rec :
    type0 list -> tvar -> tvar -> (variables -> expr list -> SE.sexpr ->
    SE.sexpr -> 'a1) -> lemma -> 'a1
  
  val coq_Foralls : type0 list -> tvar -> tvar -> lemma -> variables
  
  val coq_Hyps : type0 list -> tvar -> tvar -> lemma -> expr list
  
  val coq_Lhs : type0 list -> tvar -> tvar -> lemma -> SE.sexpr
  
  val coq_Rhs : type0 list -> tvar -> tvar -> lemma -> SE.sexpr
  
  val coq_WellTyped_lemma :
    type0 list -> tvar -> tvar -> tfunctions -> SE.tpredicates -> lemma ->
    bool
 end

module Coq5_Make = 
 functor (SE__1:SepExpr) ->
 struct 
  module SE = SE__1
  
  type lemma = { coq_Foralls : variables; coq_Hyps : expr list;
                 coq_Lhs : SE__1.sexpr; coq_Rhs : SE__1.sexpr }
  
  (** val lemma_rect :
      type0 list -> tvar -> tvar -> (variables -> expr list -> SE__1.sexpr ->
      SE__1.sexpr -> 'a1) -> lemma -> 'a1 **)
  
  let lemma_rect types4 pcType stateType f0 l =
    let { coq_Foralls = x; coq_Hyps = x0; coq_Lhs = x1; coq_Rhs = x2 } = l in
    f0 x x0 x1 x2
  
  (** val lemma_rec :
      type0 list -> tvar -> tvar -> (variables -> expr list -> SE__1.sexpr ->
      SE__1.sexpr -> 'a1) -> lemma -> 'a1 **)
  
  let lemma_rec types4 pcType stateType f0 l =
    let { coq_Foralls = x; coq_Hyps = x0; coq_Lhs = x1; coq_Rhs = x2 } = l in
    f0 x x0 x1 x2
  
  (** val coq_Foralls : type0 list -> tvar -> tvar -> lemma -> variables **)
  
  let coq_Foralls types4 pcType stateType l =
    l.coq_Foralls
  
  (** val coq_Hyps : type0 list -> tvar -> tvar -> lemma -> expr list **)
  
  let coq_Hyps types4 pcType stateType l =
    l.coq_Hyps
  
  (** val coq_Lhs : type0 list -> tvar -> tvar -> lemma -> SE__1.sexpr **)
  
  let coq_Lhs types4 pcType stateType l =
    l.coq_Lhs
  
  (** val coq_Rhs : type0 list -> tvar -> tvar -> lemma -> SE__1.sexpr **)
  
  let coq_Rhs types4 pcType stateType l =
    l.coq_Rhs
  
  (** val coq_WellTyped_lemma :
      type0 list -> tvar -> tvar -> tfunctions -> SE__1.tpredicates -> lemma
      -> bool **)
  
  let coq_WellTyped_lemma types4 pcType stateType tfuncs tpreds l =
    if if allb (fun x ->
            is_well_typed types4 tfuncs []
              (coq_Foralls types4 pcType stateType l) x TvProp)
            (coq_Hyps types4 pcType stateType l)
       then SE__1.coq_WellTyped_sexpr types4 pcType stateType tfuncs tpreds
              [] (coq_Foralls types4 pcType stateType l)
              (coq_Lhs types4 pcType stateType l)
       else false
    then SE__1.coq_WellTyped_sexpr types4 pcType stateType tfuncs tpreds []
           (coq_Foralls types4 pcType stateType l)
           (coq_Rhs types4 pcType stateType l)
    else false
 end

module Coq6_Make = 
 functor (SL:SepLemma) ->
 struct 
  module SE = SL.SE
  
  module SEP_REIFY = ReifySepExpr(SE)
 end

module Coq_FM = IntMap

module Coq7_Make = 
 functor (SH__1:SepHeap) ->
 functor (U:SynUnifier) ->
 struct 
  module SE = SH__1.SE
  
  module HEAP_FACTS = SepHeapFacts(SH__1)
  
  module ST_EXT = SepTheoryX_Ext(SH__1.SE.ST)
  
  module LEM = Coq5_Make(SH__1.SE)
  
  module B = LEM.SE.ST.H
  
  (** val coq_ERROR : type0 list -> expr **)
  
  let coq_ERROR =
    failwith "AXIOM TO BE REALIZED"
  
  (** val openForUnification : type0 list -> nat -> expr -> expr **)
  
  let rec openForUnification types4 u e = match e with
  | Var v -> UVar (plus u v)
  | Func (f0, es) -> Func (f0, (map (openForUnification types4 u) es))
  | Equal (t0, l, r) ->
    Equal (t0, (openForUnification types4 u l),
      (openForUnification types4 u r))
  | Not e0 -> Not (openForUnification types4 u e0)
  | _ -> e
  
  (** val liftInstantiate :
      type0 list -> bool -> nat -> nat -> nat -> U.coq_Subst -> expr -> expr **)
  
  let rec liftInstantiate types4 u_or_G u g g' sub0 e = match e with
  | Const (t0, t1) -> e
  | Var v ->
    if ltb0 v g'
    then if u_or_G then UVar (plus v u) else Var (plus v g)
    else let idx = minus (plus u v) g' in
         (match U.coq_Subst_lookup types4 idx sub0 with
          | Some e0 -> e0
          | None -> UVar idx)
  | Func (f0, es) ->
    Func (f0, (map (liftInstantiate types4 u_or_G u g g' sub0) es))
  | Equal (t0, l, r) ->
    Equal (t0, (liftInstantiate types4 u_or_G u g g' sub0 l),
      (liftInstantiate types4 u_or_G u g g' sub0 r))
  | Not e0 -> Not (liftInstantiate types4 u_or_G u g g' sub0 e0)
  | UVar v ->
    (match U.coq_Subst_lookup types4 v sub0 with
     | Some e0 -> e0
     | None -> UVar v)
  
  type hintSide = LEM.lemma list
  
  type hintsPayload = { coq_Forward : hintSide; coq_Backward : hintSide }
  
  (** val hintsPayload_rect :
      type0 list -> tvar -> tvar -> (hintSide -> hintSide -> 'a1) ->
      hintsPayload -> 'a1 **)
  
  let hintsPayload_rect types4 pcType stateType f0 h =
    let { coq_Forward = x; coq_Backward = x0 } = h in f0 x x0
  
  (** val hintsPayload_rec :
      type0 list -> tvar -> tvar -> (hintSide -> hintSide -> 'a1) ->
      hintsPayload -> 'a1 **)
  
  let hintsPayload_rec types4 pcType stateType f0 h =
    let { coq_Forward = x; coq_Backward = x0 } = h in f0 x x0
  
  (** val coq_Forward :
      type0 list -> tvar -> tvar -> hintsPayload -> hintSide **)
  
  let coq_Forward types4 pcType stateType h =
    h.coq_Forward
  
  (** val coq_Backward :
      type0 list -> tvar -> tvar -> hintsPayload -> hintSide **)
  
  let coq_Backward types4 pcType stateType h =
    h.coq_Backward
  
  (** val default_hintsPayload :
      type0 list -> tvar -> tvar -> hintsPayload **)
  
  let default_hintsPayload types4 pcType stateType =
    { coq_Forward = []; coq_Backward = [] }
  
  (** val composite_hintsPayload :
      type0 list -> tvar -> tvar -> hintsPayload -> hintsPayload ->
      hintsPayload **)
  
  let composite_hintsPayload types4 pcType stateType l r =
    { coq_Forward =
      (app (coq_Forward types4 pcType stateType l)
        (coq_Forward types4 pcType stateType r)); coq_Backward =
      (app (coq_Backward types4 pcType stateType l)
        (coq_Backward types4 pcType stateType r)) }
  
  (** val hintsSoundness_rect :
      type0 list -> functions -> tvar -> tvar -> SE.predicates ->
      hintsPayload -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let hintsSoundness_rect types4 funcs pcType stateType preds payload f0 =
    f0 __ __
  
  (** val hintsSoundness_rec :
      type0 list -> functions -> tvar -> tvar -> SE.predicates ->
      hintsPayload -> (__ -> __ -> 'a1) -> 'a1 **)
  
  let hintsSoundness_rec types4 funcs pcType stateType preds payload f0 =
    f0 __ __
  
  (** val find : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 option **)
  
  let rec find f0 = function
  | [] -> None
  | x::ls' ->
    (match f0 x with
     | Some b0 -> Some b0
     | None -> find f0 ls')
  
  (** val findWithRest' :
      ('a1 -> 'a1 list -> 'a2 option) -> 'a1 list -> 'a1 list -> 'a2 option **)
  
  let rec findWithRest' f0 ls acc =
    match ls with
    | [] -> None
    | x::ls' ->
      (match f0 x (rev_append acc ls') with
       | Some b0 -> Some b0
       | None -> findWithRest' f0 ls' (x::acc))
  
  (** val findWithRest :
      ('a1 -> 'a1 list -> 'a2 option) -> 'a1 list -> 'a2 option **)
  
  let findWithRest f0 ls =
    findWithRest' f0 ls []
  
  type unfoldingState = { coq_Vars : variables; coq_UVars : variables;
                          coq_Heap : SH__1.coq_SHeap }
  
  (** val unfoldingState_rect :
      type0 list -> tvar -> tvar -> (variables -> variables ->
      SH__1.coq_SHeap -> 'a1) -> unfoldingState -> 'a1 **)
  
  let unfoldingState_rect types4 pcType stateType f0 u =
    let { coq_Vars = x; coq_UVars = x0; coq_Heap = x1 } = u in f0 x x0 x1
  
  (** val unfoldingState_rec :
      type0 list -> tvar -> tvar -> (variables -> variables ->
      SH__1.coq_SHeap -> 'a1) -> unfoldingState -> 'a1 **)
  
  let unfoldingState_rec types4 pcType stateType f0 u =
    let { coq_Vars = x; coq_UVars = x0; coq_Heap = x1 } = u in f0 x x0 x1
  
  (** val coq_Vars :
      type0 list -> tvar -> tvar -> unfoldingState -> variables **)
  
  let coq_Vars types4 pcType stateType u =
    u.coq_Vars
  
  (** val coq_UVars :
      type0 list -> tvar -> tvar -> unfoldingState -> variables **)
  
  let coq_UVars types4 pcType stateType u =
    u.coq_UVars
  
  (** val coq_Heap :
      type0 list -> tvar -> tvar -> unfoldingState -> SH__1.coq_SHeap **)
  
  let coq_Heap types4 pcType stateType u =
    u.coq_Heap
  
  (** val coq_Subst_to_env :
      type0 list -> functions -> env -> env -> U.coq_Subst -> variables ->
      uvar -> env option **)
  
  let rec coq_Subst_to_env types4 funcs u g s ts cur =
    match ts with
    | [] -> Some []
    | t0::ts0 ->
      (match U.coq_Subst_lookup types4 cur s with
       | Some e ->
         (match coq_Subst_to_env types4 funcs u g s ts0 (S cur) with
          | Some env0 ->
            (match exprD types4 funcs u g e t0 with
             | Some v -> Some ((ExistT (t0, v))::env0)
             | None -> None)
          | None -> None)
       | None -> None)
  
  (** val checkAllInstantiated :
      type0 list -> nat -> variables -> U.coq_Subst -> bool **)
  
  let rec checkAllInstantiated types4 from ts sub0 =
    match ts with
    | [] -> true
    | t0::ts0 ->
      (match U.coq_Subst_lookup types4 from sub0 with
       | Some x -> checkAllInstantiated types4 (S from) ts0 sub0
       | None -> false)
  
  (** val applicable :
      type0 list -> tvar -> tvar -> nat -> proverT -> facts -> bool -> nat ->
      nat -> LEM.lemma -> exprs -> exprs -> U.coq_Subst option **)
  
  let applicable types4 pcType stateType unify_bound0 prover facts0 u_or_G firstUvar firstVar lem args key0 =
    let numForalls = length (LEM.coq_Foralls types4 pcType stateType lem) in
    (match fold_left_2_opt (U.exprUnify types4 unify_bound0)
             (map (openForUnification types4 firstUvar) key0) args
             (U.coq_Subst_empty types4) with
     | Some subst ->
       if if beq_nat (U.coq_Subst_size types4 subst) numForalls
          then checkAllInstantiated types4 firstUvar
                 (LEM.coq_Foralls types4 pcType stateType lem) subst
          else false
       then if allb (prover.prove facts0)
                 (map
                   (liftInstantiate types4 u_or_G firstUvar firstVar O subst)
                   (LEM.coq_Hyps types4 pcType stateType lem))
            then Some subst
            else None
       else None
     | None -> None)
  
  (** val unfoldForward :
      type0 list -> tvar -> tvar -> nat -> proverT -> facts -> hintSide ->
      unfoldingState -> unfoldingState option **)
  
  let unfoldForward types4 pcType stateType unify_bound0 prover facts0 hs s =
    let imps =
      SH__1.impures types4 pcType stateType
        (coq_Heap types4 pcType stateType s)
    in
    let firstUvar = length (coq_UVars types4 pcType stateType s) in
    let firstVar = length (coq_Vars types4 pcType stateType s) in
    find (fun h ->
      match LEM.coq_Lhs types4 pcType stateType h with
      | LEM.SE.Func (f0, args') ->
        (match Coq_FM.find f0 (Obj.magic imps) with
         | Some argss ->
           findWithRest (fun args argss0 ->
             match applicable types4 pcType stateType unify_bound0 prover
                     facts0 false firstUvar firstVar h args args' with
             | Some subs ->
               let impures' =
                 Coq_FM.add f0 argss0
                   (Obj.magic
                     (SH__1.impures types4 pcType stateType
                       (coq_Heap types4 pcType stateType s)))
               in
               let sh = { SH__1.impures = (Obj.magic impures'); SH__1.pures =
                 (SH__1.pures types4 pcType stateType
                   (coq_Heap types4 pcType stateType s)); SH__1.other =
                 (SH__1.other types4 pcType stateType
                   (coq_Heap types4 pcType stateType s)) }
               in
               let Pair (exs, sh') =
                 SH__1.hash types4 pcType stateType
                   (Obj.magic (LEM.coq_Rhs types4 pcType stateType h))
               in
               let sh'0 =
                 SH__1.applySHeap types4 pcType stateType
                   (liftInstantiate types4 false firstUvar firstVar
                     (length exs) subs) sh'
               in
               Some { coq_Vars =
               (app (coq_Vars types4 pcType stateType s) (rev exs));
               coq_UVars = (coq_UVars types4 pcType stateType s); coq_Heap =
               (SH__1.star_SHeap types4 pcType stateType sh sh'0) }
             | None -> None) argss
         | None -> None)
      | _ -> None) hs
  
  (** val unfoldBackward :
      type0 list -> tvar -> tvar -> nat -> proverT -> facts -> hintSide ->
      unfoldingState -> unfoldingState option **)
  
  let unfoldBackward types4 pcType stateType unify_bound0 prover facts0 hs s =
    let imps =
      SH__1.impures types4 pcType stateType
        (coq_Heap types4 pcType stateType s)
    in
    let firstUvar = length (coq_UVars types4 pcType stateType s) in
    let firstVar = length (coq_Vars types4 pcType stateType s) in
    find (fun h ->
      match LEM.coq_Rhs types4 pcType stateType h with
      | LEM.SE.Func (f0, args') ->
        (match Coq_FM.find f0 (Obj.magic imps) with
         | Some argss ->
           findWithRest (fun args argss0 ->
             match applicable types4 pcType stateType unify_bound0 prover
                     facts0 true firstUvar firstVar h args args' with
             | Some subs ->
               let impures' =
                 Coq_FM.add f0 argss0
                   (Obj.magic
                     (SH__1.impures types4 pcType stateType
                       (coq_Heap types4 pcType stateType s)))
               in
               let sh = { SH__1.impures = (Obj.magic impures'); SH__1.pures =
                 (SH__1.pures types4 pcType stateType
                   (coq_Heap types4 pcType stateType s)); SH__1.other =
                 (SH__1.other types4 pcType stateType
                   (coq_Heap types4 pcType stateType s)) }
               in
               let Pair (exs, sh') =
                 SH__1.hash types4 pcType stateType
                   (Obj.magic (LEM.coq_Lhs types4 pcType stateType h))
               in
               let sh'0 =
                 SH__1.applySHeap types4 pcType stateType
                   (liftInstantiate types4 true firstUvar firstVar
                     (length exs) subs) sh'
               in
               Some { coq_Vars = (coq_Vars types4 pcType stateType s);
               coq_UVars =
               (app (coq_UVars types4 pcType stateType s) (rev exs));
               coq_Heap =
               (SH__1.star_SHeap types4 pcType stateType sh sh'0) }
             | None -> None) argss
         | None -> None)
      | _ -> None) hs
  
  (** val unify_bound : nat **)
  
  let unify_bound =
    S (S (S (S (S O))))
  
  (** val forward :
      type0 list -> tvar -> tvar -> hintsPayload -> proverT -> nat -> facts
      -> unfoldingState -> (unfoldingState, nat) prod **)
  
  let rec forward types4 pcType stateType hs prover bound facts0 s =
    match bound with
    | O -> Pair (s, bound)
    | S bound' ->
      (match unfoldForward types4 pcType stateType unify_bound prover facts0
               (coq_Forward types4 pcType stateType hs) s with
       | Some s' ->
         forward types4 pcType stateType hs prover bound' facts0 s'
       | None -> Pair (s, bound))
  
  (** val backward :
      type0 list -> tvar -> tvar -> hintsPayload -> proverT -> nat -> facts
      -> unfoldingState -> (unfoldingState, nat) prod **)
  
  let rec backward types4 pcType stateType hs prover bound facts0 s =
    match bound with
    | O -> Pair (s, bound)
    | S bound' ->
      (match unfoldBackward types4 pcType stateType unify_bound prover facts0
               (coq_Backward types4 pcType stateType hs) s with
       | Some s' ->
         backward types4 pcType stateType hs prover bound' facts0 s'
       | None -> Pair (s, bound))
  
  (** val quant : bool -> 'a1 list -> 'a1 list -> 'a1 list **)
  
  let quant b0 b1 e =
    if b0 then app b1 e else b1
  
  (** val fromTo : nat -> nat -> nat list **)
  
  let rec fromTo start = function
  | O -> []
  | S count0 -> start::(fromTo (S start) count0)
 end

(** val reflexivityProve : type0 list -> unit0 -> expr -> bool **)

let reflexivityProve types4 x = function
| Equal (t0, x0, y) -> expr_seq_dec types4 x0 y
| _ -> false

(** val reflexivityProver : type0 list -> proverT **)

let reflexivityProver types4 =
  { summarize = (fun x -> Obj.magic Tt); learn = (fun x x0 -> x); prove =
    (Obj.magic (reflexivityProve types4)) }

(** val reflexivityProver_correct :
    type0 list -> functions -> proverT_correct **)

let reflexivityProver_correct =
  failwith "AXIOM TO BE REALIZED"

module UNF = Coq7_Make(SH)(UNIFIER)

module ILAlgoTypes = 
 struct 
  module PACK = Coq4_Make(SEP)(BedrockCoreEnv)
  
  module SEP_REIFY = ReifySepExpr(SEP)
  
  module HINTS_REIFY = Coq6_Make(UNF.LEM)
  
  type coq_AllAlgos = { coq_Prover : proverT option;
                        coq_Hints : UNF.hintsPayload option;
                        coq_MemEval : MEVAL.coq_MemEvaluator option }
  
  (** val coq_AllAlgos_rect :
      type0 list -> (proverT option -> UNF.hintsPayload option ->
      MEVAL.coq_MemEvaluator option -> 'a1) -> coq_AllAlgos -> 'a1 **)
  
  let coq_AllAlgos_rect ts f0 a =
    let { coq_Prover = x; coq_Hints = x0; coq_MemEval = x1 } = a in
    f0 x x0 x1
  
  (** val coq_AllAlgos_rec :
      type0 list -> (proverT option -> UNF.hintsPayload option ->
      MEVAL.coq_MemEvaluator option -> 'a1) -> coq_AllAlgos -> 'a1 **)
  
  let coq_AllAlgos_rec ts f0 a =
    let { coq_Prover = x; coq_Hints = x0; coq_MemEval = x1 } = a in
    f0 x x0 x1
  
  (** val coq_Prover : type0 list -> coq_AllAlgos -> proverT option **)
  
  let coq_Prover _ x = x.coq_Prover
  
  (** val coq_Hints :
      type0 list -> coq_AllAlgos -> UNF.hintsPayload option **)
  
  let coq_Hints _ x = x.coq_Hints
  
  (** val coq_MemEval :
      type0 list -> coq_AllAlgos -> MEVAL.coq_MemEvaluator option **)
  
  let coq_MemEval _ x = x.coq_MemEval
  
  (** val oplus :
      ('a1 -> 'a1 -> 'a1) -> 'a1 option -> 'a1 option -> 'a1 option **)
  
  let oplus f0 l r =
    match l with
    | Some l0 ->
      (match r with
       | Some r0 -> Some (f0 l0 r0)
       | None -> l)
    | None -> r
  
  (** val coq_AllAlgos_composite :
      type0 list -> coq_AllAlgos -> coq_AllAlgos -> coq_AllAlgos **)
  
  let coq_AllAlgos_composite types4 l r =
    let { coq_Prover = pl; coq_Hints = hl; coq_MemEval = ml } = l in
    let { coq_Prover = pr; coq_Hints = hr; coq_MemEval = mr } = r in
    { coq_Prover =
    (oplus (composite_ProverT (repr0 BedrockCoreEnv.core types4)) pl pr);
    coq_Hints =
    (oplus (fun l0 r0 -> { UNF.coq_Forward =
      (app l0.UNF.coq_Forward r0.UNF.coq_Forward); UNF.coq_Backward =
      (app l0.UNF.coq_Backward r0.UNF.coq_Backward) }) hl hr); coq_MemEval =
    (oplus
      (MEVAL.Composite.coq_MemEvaluator_composite
        (repr0 BedrockCoreEnv.core types4) BedrockCoreEnv.pc
        BedrockCoreEnv.st) ml mr) }
  
  type coq_AllAlgos_correct =
    __
    (* singleton inductive, whose constructor was Build_AllAlgos_correct *)
  
  (** val coq_AllAlgos_correct_rect :
      type0 list -> functions -> SEP.predicates -> coq_AllAlgos -> (__ -> __
      -> __ -> 'a1) -> coq_AllAlgos_correct -> 'a1 **)
  
  let coq_AllAlgos_correct_rect types4 funcs preds algos f0 a =
    f0 a __ __
  
  (** val coq_AllAlgos_correct_rec :
      type0 list -> functions -> SEP.predicates -> coq_AllAlgos -> (__ -> __
      -> __ -> 'a1) -> coq_AllAlgos_correct -> 'a1 **)
  
  let coq_AllAlgos_correct_rec types4 funcs preds algos f0 a =
    f0 a __ __
  
  (** val coq_Acorrect_Prover :
      type0 list -> functions -> SEP.predicates -> coq_AllAlgos ->
      coq_AllAlgos_correct -> __ **)
  
  let coq_Acorrect_Prover types4 funcs preds algos a =
    a
  
  (** val coq_AllAlgos_correct_composite :
      type0 list -> coq_AllAlgos -> coq_AllAlgos -> functions ->
      SEP.predicates -> coq_AllAlgos_correct -> coq_AllAlgos_correct ->
      coq_AllAlgos_correct **)
  
  let coq_AllAlgos_correct_composite =
    failwith "AXIOM TO BE REALIZED"
  
  type coq_TypedPackage = { coq_Env : PACK.coq_TypeEnv;
                            coq_Algos : (type0 list -> coq_AllAlgos);
                            coq_Algos_correct : (type0 list -> functions ->
                                                PACK.SEP.predicates ->
                                                coq_AllAlgos_correct) }
  
  (** val coq_TypedPackage_rect :
      (PACK.coq_TypeEnv -> (type0 list -> coq_AllAlgos) -> (type0 list ->
      functions -> PACK.SEP.predicates -> coq_AllAlgos_correct) -> 'a1) ->
      coq_TypedPackage -> 'a1 **)
  
  let coq_TypedPackage_rect f0 t0 =
    let { coq_Env = x; coq_Algos = x0; coq_Algos_correct = x1 } = t0 in
    f0 x x0 x1
  
  (** val coq_TypedPackage_rec :
      (PACK.coq_TypeEnv -> (type0 list -> coq_AllAlgos) -> (type0 list ->
      functions -> PACK.SEP.predicates -> coq_AllAlgos_correct) -> 'a1) ->
      coq_TypedPackage -> 'a1 **)
  
  let coq_TypedPackage_rec f0 t0 =
    let { coq_Env = x; coq_Algos = x0; coq_Algos_correct = x1 } = t0 in
    f0 x x0 x1
  
  (** val coq_Env : coq_TypedPackage -> PACK.coq_TypeEnv **)
  
  let coq_Env x = x.coq_Env
  
  (** val coq_Algos : coq_TypedPackage -> type0 list -> coq_AllAlgos **)
  
  let coq_Algos x = x.coq_Algos
  
  (** val coq_Algos_correct :
      coq_TypedPackage -> type0 list -> functions -> PACK.SEP.predicates ->
      coq_AllAlgos_correct **)
  
  let coq_Algos_correct x = x.coq_Algos_correct
  
  (** val coq_EnvOf : coq_TypedPackage -> PACK.coq_TypeEnv **)
  
  let coq_EnvOf =
    coq_Env
  
  module EmptyPackage = 
   struct 
    (** val empty_package_subproof :
        type0 list -> functions -> PACK.SEP.predicates ->
        coq_AllAlgos_correct **)
    
    let empty_package_subproof =
      failwith "AXIOM TO BE REALIZED"
    
    (** val empty_package : coq_TypedPackage **)
    
    let empty_package =
      { coq_Env = { PACK.coq_Types = (nil_Repr emptySet_type);
        PACK.coq_Funcs = (fun ts ->
        nil_Repr
          (default_signature
            (repr0 PACK.CE.core (repr0 (nil_Repr emptySet_type) ts))));
        PACK.coq_Preds = (fun ts ->
        nil_Repr
          (Obj.magic
            (SEP.coq_Default_predicate
              (repr0 PACK.CE.core (repr0 (nil_Repr emptySet_type) ts))
              PACK.CE.pc PACK.CE.st))) }; coq_Algos = (fun ts ->
        { coq_Prover = None; coq_Hints = None; coq_MemEval = None });
        coq_Algos_correct = empty_package_subproof }
   end
  
  module BedrockPackage = 
   struct 
    (** val bedrock_package_subproof :
        type0 list -> functions -> PACK.SEP.predicates ->
        coq_AllAlgos_correct **)
    
    let bedrock_package_subproof =
      failwith "AXIOM TO BE REALIZED"
    
    (** val bedrock_package : coq_TypedPackage **)
    
    let bedrock_package =
      { coq_Env = { PACK.coq_Types = (nil_Repr emptySet_type);
        PACK.coq_Funcs = bedrock_funcs_r; PACK.coq_Preds = (fun ts ->
        nil_Repr
          (Obj.magic
            (SEP.coq_Default_predicate
              (repr0 PACK.CE.core (repr0 (nil_Repr emptySet_type) ts))
              PACK.CE.pc PACK.CE.st))) }; coq_Algos = (fun ts ->
        { coq_Prover = None; coq_Hints = None; coq_MemEval = None });
        coq_Algos_correct = bedrock_package_subproof }
   end
  
  module Tactics = 
   struct 
    module ProverPackTest = 
     struct 
      (** val coq_Unnamed_thm : coq_TypedPackage **)
      
      let coq_Unnamed_thm =
        { coq_Env = { PACK.coq_Types = (nil_Repr emptySet_type);
          PACK.coq_Funcs = (fun ts ->
          nil_Repr
            (default_signature
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
              (tl (tl (tl (tl (tl ts)))))))))))); PACK.coq_Preds = (fun ts ->
          nil_Repr
            (Obj.magic
              (SEP.coq_Default_predicate
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
                (tl (tl (tl (tl (tl ts)))))))))) (TvType O) (TvType (S O))))) };
          coq_Algos = (fun ts -> { coq_Prover = (Some
          (reflexivityProver
            (PACK.applyTypes { PACK.coq_Types = (nil_Repr emptySet_type);
              PACK.coq_Funcs = (fun ts0 ->
              nil_Repr
                (default_signature
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
                  (tl (tl (tl (tl (tl ts0)))))))))))); PACK.coq_Preds =
              (fun ts0 ->
              nil_Repr
                (Obj.magic
                  (SEP.coq_Default_predicate
                    (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
                    (tl (tl (tl (tl (tl ts0)))))))))) (TvType O) (TvType (S
                    O))))) } ts))); coq_Hints = None; coq_MemEval = None });
          coq_Algos_correct = (fun ts fs0 ps ->
          Obj.magic
            (reflexivityProver_correct
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
              (tl (tl (tl (tl (tl ts)))))))))) fs0)) }
     end
    
    (** val min_types_r : type0 repr **)
    
    let min_types_r =
      { footprint = (firstn (S (S O)) bedrock_types_r.footprint); default =
        bedrock_types_r.default }
    
    module MemPackTest = 
     struct 
      (** val coq_Unnamed_thm : coq_TypedPackage **)
      
      let coq_Unnamed_thm =
        { coq_Env = { PACK.coq_Types = { footprint = ((Some
          bedrock_type_W)::((Some bedrock_type_setting_X_state)::[]));
          default = emptySet_type }; PACK.coq_Funcs = (fun ts ->
          nil_Repr
            (default_signature
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
              (tl (tl (tl (tl (tl ts)))))))))))); PACK.coq_Preds = (fun ts ->
          nil_Repr
            (Obj.magic
              (SEP.coq_Default_predicate
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
                (tl (tl (tl (tl (tl ts)))))))))) (TvType O) (TvType (S O))))) };
          coq_Algos = (fun ts -> { coq_Prover = None; coq_Hints = None;
          coq_MemEval = (Some
          (MEVAL.Default.coq_MemEvaluator_default
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::
            (tl (tl (tl (tl (tl ts)))))))))) (TvType O) (TvType (S O)))) });
          coq_Algos_correct = (fun ts fs0 ps -> Obj.magic __) }
     end
    
    type hints = { coq_Types : type0 repr;
                   coq_Functions : (type0 list -> signature repr);
                   coq_PcType : tvar; coq_StateType : tvar;
                   coq_Predicates : (type0 list -> SEP.predicate repr);
                   coq_Hints : (type0 list -> UNF.hintsPayload) }
    
    (** val hints_rect :
        (type0 repr -> (type0 list -> signature repr) -> tvar -> tvar ->
        (type0 list -> SEP.predicate repr) -> (type0 list ->
        UNF.hintsPayload) -> __ -> 'a1) -> hints -> 'a1 **)
    
    let hints_rect f0 h =
      let { coq_Types = x; coq_Functions = x0; coq_PcType = x1;
        coq_StateType = x2; coq_Predicates = x3; coq_Hints = x4 } = h
      in
      f0 x x0 x1 x2 x3 x4 __
    
    (** val hints_rec :
        (type0 repr -> (type0 list -> signature repr) -> tvar -> tvar ->
        (type0 list -> SEP.predicate repr) -> (type0 list ->
        UNF.hintsPayload) -> __ -> 'a1) -> hints -> 'a1 **)
    
    let hints_rec f0 h =
      let { coq_Types = x; coq_Functions = x0; coq_PcType = x1;
        coq_StateType = x2; coq_Predicates = x3; coq_Hints = x4 } = h
      in
      f0 x x0 x1 x2 x3 x4 __
    
    (** val coq_Types : hints -> type0 repr **)
    
    let coq_Types x = x.coq_Types
    
    (** val coq_Functions : hints -> type0 list -> signature repr **)
    
    let coq_Functions x = x.coq_Functions
    
    (** val coq_PcType : hints -> tvar **)
    
    let coq_PcType x = x.coq_PcType
    
    (** val coq_StateType : hints -> tvar **)
    
    let coq_StateType x = x.coq_StateType
    
    (** val coq_Predicates : hints -> type0 list -> SEP.predicate repr **)
    
    let coq_Predicates x = x.coq_Predicates
    
    (** val coq_Hints : hints -> type0 list -> UNF.hintsPayload **)
    
    let coq_Hints x = x.coq_Hints
    
    (** val bedrock_env : PACK.coq_TypeEnv **)
    
    let bedrock_env =
      { PACK.coq_Types = (nil_Repr emptySet_type); PACK.coq_Funcs =
        (fun ts ->
        nil_Repr
          (default_signature
            (repr0 PACK.CE.core (repr0 (nil_Repr emptySet_type) ts))));
        PACK.coq_Preds = (fun ts ->
        nil_Repr
          (Obj.magic
            (SEP.coq_Default_predicate
              (repr0 PACK.CE.core (repr0 (nil_Repr emptySet_type) ts))
              PACK.CE.pc PACK.CE.st))) }
    
    module HintsPackTest = 
     struct 
      
     end
    
    (** val coq_Unnamed_thm_subproof :
        type0 list -> functions -> PACK.SEP.predicates ->
        coq_AllAlgos_correct **)
    
    module Extension = 
     struct 
      (** val extend_opt_hints :
          type0 list -> tvar -> tvar -> UNF.hintsPayload option ->
          UNF.LEM.lemma list -> UNF.LEM.lemma list -> UNF.hintsPayload option **)
      
      let extend_opt_hints types4 pc0 st0 o fwd bwd =
        match fwd with
        | [] ->
          (match bwd with
           | [] -> o
           | l::l0 ->
             (match o with
              | Some e ->
                Some { UNF.coq_Forward = (app e.UNF.coq_Forward fwd);
                  UNF.coq_Backward = (app e.UNF.coq_Backward bwd) }
              | None ->
                Some { UNF.coq_Forward = fwd; UNF.coq_Backward = bwd }))
        | l::l0 ->
          (match o with
           | Some e ->
             Some { UNF.coq_Forward = (app e.UNF.coq_Forward fwd);
               UNF.coq_Backward = (app e.UNF.coq_Backward bwd) }
           | None -> Some { UNF.coq_Forward = fwd; UNF.coq_Backward = bwd })
     end
   end
  
  type coq_AlgoImpl = coq_AllAlgos
  
  type coq_AlgoProof = coq_AllAlgos_correct
 end

(** val wordS : nat -> word -> char list **)

let rec wordS sz = function
| WO -> []
| WS (b0, n0, w') ->
  if b0
  then append (wordS n0 w') ('1'::[])
  else append (wordS n0 w') ('0'::[])

(** val binS : nat -> word -> char list **)

let binS sz w0 =
  append ('0'::('b'::[])) (wordS sz w0)

(** val regS : reg -> char list **)

let regS = function
| Sp -> '%'::('e'::('b'::('x'::[])))
| Rp -> '%'::('e'::('s'::('i'::[])))
| Rv -> '%'::('e'::('d'::('i'::[])))

(** val tab : char list **)

let tab =
  (ascii_of_nat (S (S (S (S (S (S (S (S (S O))))))))))::[]

(** val nl : char list **)

let nl =
  (ascii_of_nat (S (S (S (S (S (S (S (S (S (S O)))))))))))::[]

(** val locS : loc -> char list **)

let locS = function
| Reg r ->
  append
    ('b'::('e'::('d'::('r'::('o'::('c'::('k'::('_'::('h'::('e'::('a'::('p'::('('::[])))))))))))))
    (append (regS r) (')'::[]))
| Imm w0 ->
  append
    (binS (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) w0)
    ('+'::('b'::('e'::('d'::('r'::('o'::('c'::('k'::('_'::('h'::('e'::('a'::('p'::[])))))))))))))
| Indir (r, w0) ->
  append
    (binS (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) w0)
    (append
      ('+'::('b'::('e'::('d'::('r'::('o'::('c'::('k'::('_'::('h'::('e'::('a'::('p'::('('::[]))))))))))))))
      (append (regS r) (')'::[])))

type registerPair = { name8 : char list; name32 : char list }

(** val name8 : registerPair -> char list **)

let name8 x = x.name8

(** val name32 : registerPair -> char list **)

let name32 x = x.name32

(** val ecx : registerPair **)

let ecx =
  { name8 = ('c'::('l'::[])); name32 = ('e'::('c'::('x'::[]))) }

(** val edx : registerPair **)

let edx =
  { name8 = ('d'::('l'::[])); name32 = ('e'::('d'::('x'::[]))) }

(** val lvalueS : lvalue -> registerPair -> (char list, char list) prod **)

let lvalueS lv tmp =
  match lv with
  | LvReg r -> Pair ((regS r), [])
  | LvMem l -> Pair ((locS l), [])
  | LvMem8 l ->
    Pair ((append ('%'::[]) tmp.name32),
      (append tab
        (append ('m'::('o'::('v'::(' '::('%'::[])))))
          (append tmp.name8 (append (','::[]) (append (locS l) nl))))))

(** val label'S : label' -> char list **)

let label'S = function
| Global s -> s
| Local n0 ->
  wordS (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
    (nToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) n0)

(** val labelS : label -> char list **)

let labelS = function
| Pair (mod0, blk) -> append mod0 (append ('_'::[]) (label'S blk))

(** val rvalueS : rvalue -> registerPair -> (char list, char list) prod **)

let rvalueS rv tmp =
  match rv with
  | RvLval l0 ->
    (match l0 with
     | LvReg r -> Pair ([], (regS r))
     | LvMem l -> Pair ([], (locS l))
     | LvMem8 l ->
       Pair
         ((append tab
            (append ('x'::('o'::('r'::('l'::(' '::('%'::[]))))))
              (append tmp.name32
                (append (','::('%'::[]))
                  (append tmp.name32
                    (append nl
                      (append tab
                        (append ('m'::('o'::('v'::(' '::[]))))
                          (append (locS l)
                            (append (','::('%'::[])) (append tmp.name8 nl))))))))))),
         (append ('%'::[]) tmp.name32)))
  | RvImm w0 ->
    Pair ([],
      (append ('$'::[])
        (binS (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
          w0)))
  | RvLabel lab -> Pair ([], (append ('$'::[]) (labelS lab)))

(** val rvalueSnomem :
    rvalue -> registerPair -> (char list, char list) prod **)

let rvalueSnomem rv tmp =
  match rv with
  | RvLval l0 ->
    (match l0 with
     | LvReg r -> Pair ([], (regS r))
     | LvMem l ->
       Pair
         ((append tab
            (append ('m'::('o'::('v'::('l'::(' '::[])))))
              (append (locS l)
                (append (','::('%'::[])) (append tmp.name32 nl))))),
         (append ('%'::[]) tmp.name32))
     | LvMem8 l ->
       Pair
         ((append tab
            (append ('x'::('o'::('r'::('l'::(' '::('%'::[]))))))
              (append tmp.name32
                (append (','::('%'::[]))
                  (append tmp.name32
                    (append nl
                      (append tab
                        (append ('m'::('o'::('v'::(' '::[]))))
                          (append (locS l)
                            (append (','::('%'::[])) (append tmp.name8 nl))))))))))),
         (append ('%'::[]) tmp.name32)))
  | RvImm w0 ->
    Pair ([],
      (append ('$'::[])
        (binS (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
          w0)))
  | RvLabel lab -> Pair ([], (append ('$'::[]) (labelS lab)))

(** val rvalueSnoimm :
    rvalue -> registerPair -> (char list, char list) prod **)

let rvalueSnoimm rv tmp =
  match rv with
  | RvLval l0 ->
    (match l0 with
     | LvReg r -> Pair ([], (regS r))
     | LvMem l ->
       Pair
         ((append tab
            (append ('m'::('o'::('v'::('l'::(' '::[])))))
              (append (locS l)
                (append (','::('%'::[])) (append tmp.name32 nl))))),
         (append ('%'::[]) tmp.name32))
     | LvMem8 l ->
       Pair
         ((append tab
            (append ('x'::('o'::('r'::('l'::(' '::('%'::[]))))))
              (append tmp.name32
                (append (','::('%'::[]))
                  (append tmp.name32
                    (append nl
                      (append tab
                        (append ('m'::('o'::('v'::(' '::[]))))
                          (append (locS l)
                            (append (','::('%'::[])) (append tmp.name8 nl))))))))))),
         (append ('%'::[]) tmp.name32)))
  | RvImm w0 ->
    Pair
      ((append tab
         (append ('m'::('o'::('v'::('l'::(' '::('$'::[]))))))
           (append
             (binS (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S (S
               O)))))))))))))))))))))))))))))))) w0)
             (append (','::('%'::[])) (append tmp.name32 nl))))),
      (append ('%'::[]) tmp.name32))
  | RvLabel lab ->
    Pair
      ((append tab
         (append ('m'::('o'::('v'::('l'::(' '::('$'::[]))))))
           (append (labelS lab)
             (append (','::('%'::[])) (append tmp.name32 nl))))),
      (append ('%'::[]) tmp.name32))

(** val rvalueSinto : rvalue -> registerPair -> char list **)

let rvalueSinto rv tmp =
  match rv with
  | RvLval l0 ->
    (match l0 with
     | LvReg r ->
       append tab
         (append ('m'::('o'::('v'::('l'::(' '::[])))))
           (append (regS r) (append (','::('%'::[])) (append tmp.name32 nl))))
     | LvMem l ->
       append tab
         (append ('m'::('o'::('v'::('l'::(' '::[])))))
           (append (locS l) (append (','::('%'::[])) (append tmp.name32 nl))))
     | LvMem8 l ->
       append tab
         (append ('x'::('o'::('r'::('l'::(' '::('%'::[]))))))
           (append tmp.name32
             (append (','::('%'::[]))
               (append tmp.name32
                 (append nl
                   (append tab
                     (append ('m'::('o'::('v'::(' '::[]))))
                       (append (locS l)
                         (append (','::('%'::[])) (append tmp.name8 nl)))))))))))
  | RvImm w0 ->
    append tab
      (append ('m'::('o'::('v'::('l'::(' '::('$'::[]))))))
        (append
          (binS (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) w0)
          (append (','::('%'::[])) (append tmp.name32 nl))))
  | RvLabel lab ->
    append tab
      (append ('m'::('o'::('v'::('l'::(' '::('$'::[]))))))
        (append (labelS lab)
          (append (','::('%'::[])) (append tmp.name32 nl))))

(** val binopS : binop -> char list **)

let binopS = function
| Plus -> 'a'::('d'::('d'::('l'::[])))
| Minus -> 's'::('u'::('b'::('l'::[])))
| Times -> 'i'::('m'::('u'::('l'::('l'::[]))))

(** val lvalueIsMem : lvalue -> bool **)

let lvalueIsMem = function
| LvReg r -> false
| _ -> true

(** val rvalueIsMem : rvalue -> bool **)

let rvalueIsMem = function
| RvLval lv -> lvalueIsMem lv
| _ -> false

(** val rvalueIsImm : rvalue -> bool **)

let rvalueIsImm = function
| RvLval l -> false
| _ -> true

(** val instrS : instr -> char list **)

let instrS = function
| Assign (lv, rv) ->
  let Pair (lvS, lvI) = lvalueS lv ecx in
  let Pair (rvI, rvS) =
    if rvalueIsMem rv then rvalueSnomem rv edx else rvalueS rv edx
  in
  append rvI
    (append tab
      (append ('m'::('o'::('v'::('l'::(' '::[])))))
        (append rvS (append (','::[]) (append lvS (append nl lvI))))))
| Binop (lv, rv1, o, rv2) ->
  let Pair (lvS, lvI) = lvalueS lv ecx in
  let rv1I = rvalueSinto rv1 edx in
  let Pair (rv2I, rv2S) = rvalueS rv2 ecx in
  append rv1I
    (append rv2I
      (append tab
        (append (binopS o)
          (append (' '::[])
            (append rv2S
              (append (','::('%'::('e'::('d'::('x'::[])))))
                (append nl
                  (append tab
                    (append
                      ('m'::('o'::('v'::('l'::(' '::('%'::('e'::('d'::('x'::(','::[]))))))))))
                      (append lvS (append nl lvI)))))))))))

(** val testS : test -> char list **)

let testS = function
| Eq0 -> 'z'::[]
| Ne -> 'n'::('z'::[])
| Lt0 -> 'b'::[]
| Le -> 'n'::('a'::[])

(** val jmpS : jmp -> char list **)

let jmpS = function
| Uncond rv ->
  (match rv with
   | RvLabel lab ->
     append tab
       (append ('j'::('m'::('p'::(' '::[])))) (append (labelS lab) nl))
   | _ ->
     append (rvalueSinto rv edx)
       (append tab
         (append
           ('j'::('m'::('p'::(' '::('*'::('%'::('r'::('d'::('x'::[])))))))))
           nl)))
| Cond (rv1, t0, rv2, lab1, lab2) ->
  if rvalueIsMem rv2
  then (match t0 with
        | Lt0 ->
          let p = Pair ((Pair ((Pair (rv2, Le)), rv1)), lab2) in
          let Pair (p0, lab3) = p in
          let Pair (p1, rv3) = p0 in
          let Pair (rv4, t1) = p1 in
          (match rv4 with
           | RvImm w1 ->
             (match rv3 with
              | RvImm w2 ->
                if evalTest t1 w1 w2
                then append tab
                       (append ('j'::('m'::('p'::(' '::[]))))
                         (append (labelS lab3) nl))
                else append tab
                       (append ('j'::('m'::('p'::(' '::[]))))
                         (append (labelS lab1) nl))
              | _ ->
                let Pair (rv1I, rv1S) =
                  if rvalueIsImm rv4
                  then rvalueSnoimm rv4 ecx
                  else rvalueS rv4 ecx
                in
                let Pair (rv2I, rv2S) =
                  if rvalueIsMem rv4
                  then rvalueSnomem rv3 edx
                  else rvalueS rv3 edx
                in
                append rv1I
                  (append rv2I
                    (append tab
                      (append ('c'::('m'::('p'::('l'::(' '::[])))))
                        (append rv2S
                          (append (','::[])
                            (append rv1S
                              (append nl
                                (append tab
                                  (append ('j'::[])
                                    (append (testS t1)
                                      (append (' '::[])
                                        (append (labelS lab3)
                                          (append nl
                                            (append tab
                                              (append
                                                ('j'::('m'::('p'::(' '::[]))))
                                                (append (labelS lab1) nl)))))))))))))))))
           | _ ->
             let Pair (rv1I, rv1S) =
               if rvalueIsImm rv4
               then rvalueSnoimm rv4 ecx
               else rvalueS rv4 ecx
             in
             let Pair (rv2I, rv2S) =
               if rvalueIsMem rv4
               then rvalueSnomem rv3 edx
               else rvalueS rv3 edx
             in
             append rv1I
               (append rv2I
                 (append tab
                   (append ('c'::('m'::('p'::('l'::(' '::[])))))
                     (append rv2S
                       (append (','::[])
                         (append rv1S
                           (append nl
                             (append tab
                               (append ('j'::[])
                                 (append (testS t1)
                                   (append (' '::[])
                                     (append (labelS lab3)
                                       (append nl
                                         (append tab
                                           (append
                                             ('j'::('m'::('p'::(' '::[]))))
                                             (append (labelS lab1) nl)))))))))))))))))
        | Le ->
          let p = Pair ((Pair ((Pair (rv2, Lt0)), rv1)), lab2) in
          let Pair (p0, lab3) = p in
          let Pair (p1, rv3) = p0 in
          let Pair (rv4, t1) = p1 in
          (match rv4 with
           | RvImm w1 ->
             (match rv3 with
              | RvImm w2 ->
                if evalTest t1 w1 w2
                then append tab
                       (append ('j'::('m'::('p'::(' '::[]))))
                         (append (labelS lab3) nl))
                else append tab
                       (append ('j'::('m'::('p'::(' '::[]))))
                         (append (labelS lab1) nl))
              | _ ->
                let Pair (rv1I, rv1S) =
                  if rvalueIsImm rv4
                  then rvalueSnoimm rv4 ecx
                  else rvalueS rv4 ecx
                in
                let Pair (rv2I, rv2S) =
                  if rvalueIsMem rv4
                  then rvalueSnomem rv3 edx
                  else rvalueS rv3 edx
                in
                append rv1I
                  (append rv2I
                    (append tab
                      (append ('c'::('m'::('p'::('l'::(' '::[])))))
                        (append rv2S
                          (append (','::[])
                            (append rv1S
                              (append nl
                                (append tab
                                  (append ('j'::[])
                                    (append (testS t1)
                                      (append (' '::[])
                                        (append (labelS lab3)
                                          (append nl
                                            (append tab
                                              (append
                                                ('j'::('m'::('p'::(' '::[]))))
                                                (append (labelS lab1) nl)))))))))))))))))
           | _ ->
             let Pair (rv1I, rv1S) =
               if rvalueIsImm rv4
               then rvalueSnoimm rv4 ecx
               else rvalueS rv4 ecx
             in
             let Pair (rv2I, rv2S) =
               if rvalueIsMem rv4
               then rvalueSnomem rv3 edx
               else rvalueS rv3 edx
             in
             append rv1I
               (append rv2I
                 (append tab
                   (append ('c'::('m'::('p'::('l'::(' '::[])))))
                     (append rv2S
                       (append (','::[])
                         (append rv1S
                           (append nl
                             (append tab
                               (append ('j'::[])
                                 (append (testS t1)
                                   (append (' '::[])
                                     (append (labelS lab3)
                                       (append nl
                                         (append tab
                                           (append
                                             ('j'::('m'::('p'::(' '::[]))))
                                             (append (labelS lab1) nl)))))))))))))))))
        | x ->
          let p = Pair ((Pair ((Pair (rv2, x)), rv1)), lab1) in
          let Pair (p0, lab3) = p in
          let Pair (p1, rv3) = p0 in
          let Pair (rv4, t1) = p1 in
          (match rv4 with
           | RvImm w1 ->
             (match rv3 with
              | RvImm w2 ->
                if evalTest t1 w1 w2
                then append tab
                       (append ('j'::('m'::('p'::(' '::[]))))
                         (append (labelS lab3) nl))
                else append tab
                       (append ('j'::('m'::('p'::(' '::[]))))
                         (append (labelS lab2) nl))
              | _ ->
                let Pair (rv1I, rv1S) =
                  if rvalueIsImm rv4
                  then rvalueSnoimm rv4 ecx
                  else rvalueS rv4 ecx
                in
                let Pair (rv2I, rv2S) =
                  if rvalueIsMem rv4
                  then rvalueSnomem rv3 edx
                  else rvalueS rv3 edx
                in
                append rv1I
                  (append rv2I
                    (append tab
                      (append ('c'::('m'::('p'::('l'::(' '::[])))))
                        (append rv2S
                          (append (','::[])
                            (append rv1S
                              (append nl
                                (append tab
                                  (append ('j'::[])
                                    (append (testS t1)
                                      (append (' '::[])
                                        (append (labelS lab3)
                                          (append nl
                                            (append tab
                                              (append
                                                ('j'::('m'::('p'::(' '::[]))))
                                                (append (labelS lab2) nl)))))))))))))))))
           | _ ->
             let Pair (rv1I, rv1S) =
               if rvalueIsImm rv4
               then rvalueSnoimm rv4 ecx
               else rvalueS rv4 ecx
             in
             let Pair (rv2I, rv2S) =
               if rvalueIsMem rv4
               then rvalueSnomem rv3 edx
               else rvalueS rv3 edx
             in
             append rv1I
               (append rv2I
                 (append tab
                   (append ('c'::('m'::('p'::('l'::(' '::[])))))
                     (append rv2S
                       (append (','::[])
                         (append rv1S
                           (append nl
                             (append tab
                               (append ('j'::[])
                                 (append (testS t1)
                                   (append (' '::[])
                                     (append (labelS lab3)
                                       (append nl
                                         (append tab
                                           (append
                                             ('j'::('m'::('p'::(' '::[]))))
                                             (append (labelS lab2) nl))))))))))))))))))
  else let p = Pair ((Pair ((Pair (rv1, t0)), rv2)), lab1) in
       let Pair (p0, lab3) = p in
       let Pair (p1, rv3) = p0 in
       let Pair (rv4, t1) = p1 in
       (match rv4 with
        | RvImm w1 ->
          (match rv3 with
           | RvImm w2 ->
             if evalTest t1 w1 w2
             then append tab
                    (append ('j'::('m'::('p'::(' '::[]))))
                      (append (labelS lab3) nl))
             else append tab
                    (append ('j'::('m'::('p'::(' '::[]))))
                      (append (labelS lab2) nl))
           | _ ->
             let Pair (rv1I, rv1S) =
               if rvalueIsImm rv4
               then rvalueSnoimm rv4 ecx
               else rvalueS rv4 ecx
             in
             let Pair (rv2I, rv2S) =
               if rvalueIsMem rv4
               then rvalueSnomem rv3 edx
               else rvalueS rv3 edx
             in
             append rv1I
               (append rv2I
                 (append tab
                   (append ('c'::('m'::('p'::('l'::(' '::[])))))
                     (append rv2S
                       (append (','::[])
                         (append rv1S
                           (append nl
                             (append tab
                               (append ('j'::[])
                                 (append (testS t1)
                                   (append (' '::[])
                                     (append (labelS lab3)
                                       (append nl
                                         (append tab
                                           (append
                                             ('j'::('m'::('p'::(' '::[]))))
                                             (append (labelS lab2) nl)))))))))))))))))
        | _ ->
          let Pair (rv1I, rv1S) =
            if rvalueIsImm rv4 then rvalueSnoimm rv4 ecx else rvalueS rv4 ecx
          in
          let Pair (rv2I, rv2S) =
            if rvalueIsMem rv4 then rvalueSnomem rv3 edx else rvalueS rv3 edx
          in
          append rv1I
            (append rv2I
              (append tab
                (append ('c'::('m'::('p'::('l'::(' '::[])))))
                  (append rv2S
                    (append (','::[])
                      (append rv1S
                        (append nl
                          (append tab
                            (append ('j'::[])
                              (append (testS t1)
                                (append (' '::[])
                                  (append (labelS lab3)
                                    (append nl
                                      (append tab
                                        (append
                                          ('j'::('m'::('p'::(' '::[]))))
                                          (append (labelS lab2) nl)))))))))))))))))

(** val blockS : block -> char list **)

let blockS = function
| Pair (is, j) -> fold_right (fun i s -> append (instrS i) s) (jmpS j) is

(** val moduleS : module0 -> char list LabelMap.t **)

let moduleS m6 =
  LabelMap.mapi (fun lab bl ->
    let Pair (x, b0) = bl in
    append (labelS lab) (append (':'::[]) (append nl (blockS b0)))) m6.blocks

type 'x comp =
| Return of 'x
| Bind of __ comp * (__ -> 'x comp)
| Pick

type constructorIndex = __

type methodIndex = __

type constructorDom = __

type ('rep, 'dom) cConstructorType = 'dom -> 'rep

type ('rep, 'dom, 'cod) cMethodType = 'rep -> 'dom -> ('rep, 'cod) prod

type cADT = { cConstructors : (constructorIndex -> (__, constructorDom)
                              cConstructorType);
              cMethods : (methodIndex -> (__, __, __) cMethodType) }

type refineADT =
| RefinesADT

type ('a, 'b) ilist =
| Icons of 'a * 'a list * 'b * ('a, 'b) ilist
| Inil

(** val ilist_hd : 'a1 list -> ('a1, 'a2) ilist -> __ **)

let ilist_hd as0 = function
| Icons (a, as1, b0, as') -> Obj.magic b0
| Inil -> Obj.magic Tt

(** val ilist_tl : 'a1 list -> ('a1, 'a2) ilist -> __ **)

let ilist_tl as0 = function
| Icons (a, as1, b0, as') -> Obj.magic as'
| Inil -> Obj.magic Tt

type ('a, 'b) dep_Option =
| Dep_Some of 'a * 'b
| Dep_None

type ('a, 'b) dep_Option_elimT = __

(** val dep_Option_elim :
    'a1 option -> ('a1, 'a2) dep_Option -> ('a1, 'a2) dep_Option_elimT **)

let dep_Option_elim a_opt = function
| Dep_Some (a, b0) -> Obj.magic b0
| Dep_None -> Obj.magic Tt

(** val ith_error :
    'a1 list -> ('a1, 'a2) ilist -> nat -> ('a1, 'a2) dep_Option **)

let rec ith_error as0 il = function
| O ->
  (match as0 with
   | [] -> Dep_None
   | a::as' -> Dep_Some (a, (Obj.magic (ilist_hd (a::as') il))))
| S n1 ->
  (match as0 with
   | [] -> Dep_None
   | a::as' -> Obj.magic ith_error as' (ilist_tl (a::as') il) n1)

type 'a indexBound =
  nat
  (* singleton inductive, whose constructor was Build_IndexBound *)

(** val ibound : 'a1 -> 'a1 list -> 'a1 indexBound -> nat **)

let ibound a bound indexBound0 =
  indexBound0

type 'a boundedIndex = { bindex : 'a; indexb : 'a indexBound }

(** val bindex : 'a1 list -> 'a1 boundedIndex -> 'a1 **)

let bindex _ x = x.bindex

(** val indexb : 'a1 list -> 'a1 boundedIndex -> 'a1 indexBound **)

let indexb _ x = x.indexb

type boundedString = char list boundedIndex

(** val none_neq_Some : 'a1 -> 'a2 **)

let none_neq_Some =
  failwith "AXIOM TO BE REALIZED"

(** val nth_Bounded' :
    ('a1 -> 'a2) -> 'a1 list -> 'a2 -> 'a1 option -> 'a1 **)

let nth_Bounded' projAC bound c = function
| Some a -> a
| None -> none_neq_Some c

(** val nth_Bounded : ('a1 -> 'a2) -> 'a1 list -> 'a2 boundedIndex -> 'a1 **)

let nth_Bounded projAC bound idx =
  nth_Bounded' projAC bound idx.bindex
    (nth_error bound (ibound idx.bindex (map projAC bound) idx.indexb))

(** val ith_Bounded' :
    ('a1 -> 'a2) -> 'a1 list -> 'a2 -> 'a1 option -> ('a1, 'a3) dep_Option ->
    'a3 **)

let ith_Bounded' projAC as0 d a_opt x =
  match a_opt with
  | Some a -> Obj.magic (dep_Option_elim (Some a) x)
  | None -> none_neq_Some d

(** val ith_Bounded :
    ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a3) ilist -> 'a2 boundedIndex -> 'a3 **)

let ith_Bounded projAC bound il idx =
  ith_Bounded' projAC bound idx.bindex
    (nth_error bound (ibound idx.bindex (map projAC bound) idx.indexb))
    (ith_error bound il (ibound idx.bindex (map projAC bound) idx.indexb))

type consSig =
  char list
  (* singleton inductive, whose constructor was Build_consSig *)

(** val consID : consSig -> char list **)

let consID c =
  c

type consDom = __

type methSig =
  char list
  (* singleton inductive, whose constructor was Build_methSig *)

(** val methID : methSig -> char list **)

let methID m6 =
  m6

type methDom = __

type methCod = __

type 'rep cMethDef =
  ('rep, methDom, methCod) cMethodType
  (* singleton inductive, whose constructor was Build_cMethDef *)

(** val cMethBody :
    methSig -> 'a1 cMethDef -> ('a1, methDom, methCod) cMethodType **)

let cMethBody sig1 c =
  c

type 'rep cConsDef =
  ('rep, consDom) cConstructorType
  (* singleton inductive, whose constructor was Build_cConsDef *)

(** val cConsBody :
    consSig -> 'a1 cConsDef -> ('a1, consDom) cConstructorType **)

let cConsBody sig1 c =
  c

(** val getcConsDef :
    consSig list -> (consSig, 'a1 cConsDef) ilist -> boundedString -> ('a1,
    consDom) cConstructorType **)

let getcConsDef consSigs consDefs idx =
  cConsBody (nth_Bounded consID consSigs idx)
    (ith_Bounded consID consSigs consDefs idx)

(** val getcMethDef :
    methSig list -> (methSig, 'a1 cMethDef) ilist -> boundedString -> ('a1,
    methDom, methCod) cMethodType **)

let getcMethDef methSigs methDefs idx =
  cMethBody (nth_Bounded methID methSigs idx)
    (ith_Bounded methID methSigs methDefs idx)

(** val buildcADT :
    consSig list -> methSig list -> (consSig, 'a1 cConsDef) ilist ->
    (methSig, 'a1 cMethDef) ilist -> cADT **)

let buildcADT consSigs methSigs consDefs methDefs =
  { cConstructors = (fun idx ->
    getcConsDef consSigs (Obj.magic consDefs) (Obj.magic idx)); cMethods =
    (fun idx -> getcMethDef methSigs (Obj.magic methDefs) (Obj.magic idx)) }

module BedrockWordW = 
 struct 
  type coq_W = w
  
  (** val wzero : word **)
  
  let wzero =
    natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) O
  
  (** val wplus : word -> word -> word **)
  
  let wplus =
    wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
  
  (** val wminus : word -> word -> word **)
  
  let wminus =
    wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
  
  (** val weq : word -> word -> bool **)
  
  let weq =
    weqb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
  
  (** val wlt : w -> w -> bool **)
  
  let wlt =
    wltb
  
  (** val from_nat : nat -> word **)
  
  let from_nat =
    natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
 end

(** val sEmpty : char list **)

let sEmpty =
  'E'::('m'::('p'::('t'::('y'::[]))))

(** val sAdd : char list **)

let sAdd =
  'A'::('d'::('d'::[]))

(** val sRemove : char list **)

let sRemove =
  'R'::('e'::('m'::('o'::('v'::('e'::[])))))

(** val sIn : char list **)

let sIn =
  'I'::('n'::[])

(** val sSize : char list **)

let sSize =
  'S'::('i'::('z'::('e'::[])))

type color =
| Red
| Black

module Color = 
 struct 
  type t = color
 end

module Coq8_Make = 
 functor (X:OrderedType) ->
 struct 
  module Raw = 
   struct 
    type elt = X.t
    
    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree
    
    (** val empty : tree **)
    
    let empty =
      Leaf
    
    (** val is_empty : tree -> bool **)
    
    let is_empty = function
    | Leaf -> true
    | Node (t1, t2, t3, t4) -> false
    
    (** val mem : X.t -> tree -> bool **)
    
    let rec mem x = function
    | Leaf -> false
    | Node (t1, l, k, r) ->
      (match X.compare x k with
       | Eq -> true
       | Lt -> mem x l
       | Gt -> mem x r)
    
    (** val min_elt : tree -> elt option **)
    
    let rec min_elt = function
    | Leaf -> None
    | Node (t1, l, x, r) ->
      (match l with
       | Leaf -> Some x
       | Node (t2, t3, t4, t5) -> min_elt l)
    
    (** val max_elt : tree -> elt option **)
    
    let rec max_elt = function
    | Leaf -> None
    | Node (t1, l, x, r) ->
      (match r with
       | Leaf -> Some x
       | Node (t2, t3, t4, t5) -> max_elt r)
    
    (** val choose : tree -> elt option **)
    
    let choose =
      min_elt
    
    (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)
    
    let rec fold f0 t0 base =
      match t0 with
      | Leaf -> base
      | Node (t1, l, x, r) -> fold f0 r (f0 x (fold f0 l base))
    
    (** val elements_aux : X.t list -> tree -> X.t list **)
    
    let rec elements_aux acc = function
    | Leaf -> acc
    | Node (t0, l, x, r) -> elements_aux (x::(elements_aux acc r)) l
    
    (** val elements : tree -> X.t list **)
    
    let elements =
      elements_aux []
    
    (** val rev_elements_aux : X.t list -> tree -> X.t list **)
    
    let rec rev_elements_aux acc = function
    | Leaf -> acc
    | Node (t0, l, x, r) -> rev_elements_aux (x::(rev_elements_aux acc l)) r
    
    (** val rev_elements : tree -> X.t list **)
    
    let rev_elements =
      rev_elements_aux []
    
    (** val cardinal : tree -> nat **)
    
    let rec cardinal = function
    | Leaf -> O
    | Node (t0, l, t1, r) -> S (plus (cardinal l) (cardinal r))
    
    (** val maxdepth : tree -> nat **)
    
    let rec maxdepth = function
    | Leaf -> O
    | Node (t0, l, t1, r) -> S (max (maxdepth l) (maxdepth r))
    
    (** val mindepth : tree -> nat **)
    
    let rec mindepth = function
    | Leaf -> O
    | Node (t0, l, t1, r) -> S (min (mindepth l) (mindepth r))
    
    (** val for_all : (elt -> bool) -> tree -> bool **)
    
    let rec for_all f0 = function
    | Leaf -> true
    | Node (t0, l, x, r) ->
      if if f0 x then for_all f0 l else false then for_all f0 r else false
    
    (** val exists_ : (elt -> bool) -> tree -> bool **)
    
    let rec exists_ f0 = function
    | Leaf -> false
    | Node (t0, l, x, r) ->
      if if f0 x then true else exists_ f0 l then true else exists_ f0 r
    
    type enumeration =
    | End
    | More of elt * tree * enumeration
    
    (** val cons : tree -> enumeration -> enumeration **)
    
    let rec cons s e =
      match s with
      | Leaf -> e
      | Node (t0, l, x, r) -> cons l (More (x, r, e))
    
    (** val compare_more :
        X.t -> (enumeration -> comparison) -> enumeration -> comparison **)
    
    let compare_more x1 cont = function
    | End -> Gt
    | More (x2, r2, e3) ->
      (match X.compare x1 x2 with
       | Eq -> cont (cons r2 e3)
       | x -> x)
    
    (** val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison **)
    
    let rec compare_cont s1 cont e2 =
      match s1 with
      | Leaf -> cont e2
      | Node (t0, l1, x1, r1) ->
        compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2
    
    (** val compare_end : enumeration -> comparison **)
    
    let compare_end = function
    | End -> Eq
    | More (e, t0, e0) -> Lt
    
    (** val compare : tree -> tree -> comparison **)
    
    let compare s1 s2 =
      compare_cont s1 compare_end (cons s2 End)
    
    (** val equal : tree -> tree -> bool **)
    
    let equal s1 s2 =
      match compare s1 s2 with
      | Eq -> true
      | _ -> false
    
    (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)
    
    let rec subsetl subset_l1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (t0, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_l1 l2
       | Lt -> subsetl subset_l1 x1 l2
       | Gt -> if mem x1 r2 then subset_l1 s2 else false)
    
    (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)
    
    let rec subsetr subset_r1 x1 s2 = match s2 with
    | Leaf -> false
    | Node (t0, l2, x2, r2) ->
      (match X.compare x1 x2 with
       | Eq -> subset_r1 r2
       | Lt -> if mem x1 l2 then subset_r1 s2 else false
       | Gt -> subsetr subset_r1 x1 r2)
    
    (** val subset : tree -> tree -> bool **)
    
    let rec subset s1 s2 =
      match s1 with
      | Leaf -> true
      | Node (t0, l1, x1, r1) ->
        (match s2 with
         | Leaf -> false
         | Node (t1, l2, x2, r2) ->
           (match X.compare x1 x2 with
            | Eq -> if subset l1 l2 then subset r1 r2 else false
            | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
            | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))
    
    type t = tree
    
    (** val singleton : elt -> tree **)
    
    let singleton k =
      Node (Black, Leaf, k, Leaf)
    
    (** val makeBlack : tree -> tree **)
    
    let makeBlack = function
    | Leaf -> Leaf
    | Node (t1, a, x, b0) -> Node (Black, a, x, b0)
    
    (** val makeRed : tree -> tree **)
    
    let makeRed = function
    | Leaf -> Leaf
    | Node (t1, a, x, b0) -> Node (Red, a, x, b0)
    
    (** val lbal : tree -> X.t -> tree -> tree **)
    
    let lbal l k r =
      match l with
      | Leaf -> Node (Black, l, k, r)
      | Node (t0, a, x, c) ->
        (match t0 with
         | Red ->
           (match a with
            | Leaf ->
              (match c with
               | Leaf -> Node (Black, l, k, r)
               | Node (t1, b0, y, c0) ->
                 (match t1 with
                  | Red ->
                    Node (Red, (Node (Black, a, x, b0)), y, (Node (Black, c0,
                      k, r)))
                  | Black -> Node (Black, l, k, r)))
            | Node (t1, a0, x0, b0) ->
              (match t1 with
               | Red ->
                 Node (Red, (Node (Black, a0, x0, b0)), x, (Node (Black, c,
                   k, r)))
               | Black ->
                 (match c with
                  | Leaf -> Node (Black, l, k, r)
                  | Node (t2, b1, y, c0) ->
                    (match t2 with
                     | Red ->
                       Node (Red, (Node (Black, a, x, b1)), y, (Node (Black,
                         c0, k, r)))
                     | Black -> Node (Black, l, k, r)))))
         | Black -> Node (Black, l, k, r))
    
    (** val rbal : tree -> X.t -> tree -> tree **)
    
    let rbal l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b0, y, d) ->
      (match t0 with
       | Red ->
         (match b0 with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z0, d0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, l, k, b0)), y, (Node (Black, c,
                    z0, d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b1, y0, c) ->
            (match t1 with
             | Red ->
               Node (Red, (Node (Black, l, k, b1)), y0, (Node (Black, c, y,
                 d)))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z0, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b0)), y, (Node (Black,
                       c0, z0, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))
    
    (** val rbal' : tree -> X.t -> tree -> tree **)
    
    let rbal' l k r = match r with
    | Leaf -> Node (Black, l, k, r)
    | Node (t0, b0, z0, d) ->
      (match t0 with
       | Red ->
         (match b0 with
          | Leaf ->
            (match d with
             | Leaf -> Node (Black, l, k, r)
             | Node (t1, c, z1, d0) ->
               (match t1 with
                | Red ->
                  Node (Red, (Node (Black, l, k, b0)), z0, (Node (Black, c,
                    z1, d0)))
                | Black -> Node (Black, l, k, r)))
          | Node (t1, b1, y, c) ->
            (match t1 with
             | Red ->
               (match d with
                | Leaf ->
                  Node (Red, (Node (Black, l, k, b1)), y, (Node (Black, c,
                    z0, d)))
                | Node (t2, c0, z1, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b0)), z0, (Node (Black,
                       c0, z1, d0)))
                   | Black ->
                     Node (Red, (Node (Black, l, k, b1)), y, (Node (Black, c,
                       z0, d)))))
             | Black ->
               (match d with
                | Leaf -> Node (Black, l, k, r)
                | Node (t2, c0, z1, d0) ->
                  (match t2 with
                   | Red ->
                     Node (Red, (Node (Black, l, k, b0)), z0, (Node (Black,
                       c0, z1, d0)))
                   | Black -> Node (Black, l, k, r)))))
       | Black -> Node (Black, l, k, r))
    
    (** val lbalS : tree -> X.t -> tree -> tree **)
    
    let lbalS l k r =
      match l with
      | Leaf ->
        (match r with
         | Leaf -> Node (Red, l, k, r)
         | Node (t0, a, z0, c) ->
           (match t0 with
            | Red ->
              (match a with
               | Leaf -> Node (Red, l, k, r)
               | Node (t1, a0, y, b0) ->
                 (match t1 with
                  | Red -> Node (Red, l, k, r)
                  | Black ->
                    Node (Red, (Node (Black, l, k, a0)), y,
                      (rbal' b0 z0 (makeRed c)))))
            | Black -> rbal' l k (Node (Red, a, z0, c))))
      | Node (t0, a, x, b0) ->
        (match t0 with
         | Red -> Node (Red, (Node (Black, a, x, b0)), k, r)
         | Black ->
           (match r with
            | Leaf -> Node (Red, l, k, r)
            | Node (t1, a0, z0, c) ->
              (match t1 with
               | Red ->
                 (match a0 with
                  | Leaf -> Node (Red, l, k, r)
                  | Node (t2, a1, y, b1) ->
                    (match t2 with
                     | Red -> Node (Red, l, k, r)
                     | Black ->
                       Node (Red, (Node (Black, l, k, a1)), y,
                         (rbal' b1 z0 (makeRed c)))))
               | Black -> rbal' l k (Node (Red, a0, z0, c)))))
    
    (** val rbalS : tree -> X.t -> tree -> tree **)
    
    let rbalS l k r = match r with
    | Leaf ->
      (match l with
       | Leaf -> Node (Red, l, k, r)
       | Node (t0, a, x, b0) ->
         (match t0 with
          | Red ->
            (match b0 with
             | Leaf -> Node (Red, l, k, r)
             | Node (t1, b1, y, c) ->
               (match t1 with
                | Red -> Node (Red, l, k, r)
                | Black ->
                  Node (Red, (lbal (makeRed a) x b1), y, (Node (Black, c, k,
                    r)))))
          | Black -> lbal (Node (Red, a, x, b0)) k r))
    | Node (t0, b0, y, c) ->
      (match t0 with
       | Red -> Node (Red, l, k, (Node (Black, b0, y, c)))
       | Black ->
         (match l with
          | Leaf -> Node (Red, l, k, r)
          | Node (t1, a, x, b1) ->
            (match t1 with
             | Red ->
               (match b1 with
                | Leaf -> Node (Red, l, k, r)
                | Node (t2, b2, y0, c0) ->
                  (match t2 with
                   | Red -> Node (Red, l, k, r)
                   | Black ->
                     Node (Red, (lbal (makeRed a) x b2), y0, (Node (Black,
                       c0, k, r)))))
             | Black -> lbal (Node (Red, a, x, b1)) k r)))
    
    (** val ins : X.t -> tree -> tree **)
    
    let rec ins x s = match s with
    | Leaf -> Node (Red, Leaf, x, Leaf)
    | Node (c, l, y, r) ->
      (match X.compare x y with
       | Eq -> s
       | Lt ->
         (match c with
          | Red -> Node (Red, (ins x l), y, r)
          | Black -> lbal (ins x l) y r)
       | Gt ->
         (match c with
          | Red -> Node (Red, l, y, (ins x r))
          | Black -> rbal l y (ins x r)))
    
    (** val add : X.t -> tree -> tree **)
    
    let add x s =
      makeBlack (ins x s)
    
    (** val append : tree -> tree -> tree **)
    
    let rec append l = match l with
    | Leaf -> (fun r -> r)
    | Node (lc, ll, lx, lr) ->
      let rec append_l r = match r with
      | Leaf -> l
      | Node (rc, rl, rx, rr) ->
        (match lc with
         | Red ->
           (match rc with
            | Red ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))
               | Node (t0, lr', x, rl') ->
                 (match t0 with
                  | Red ->
                    Node (Red, (Node (Red, ll, lx, lr')), x, (Node (Red, rl',
                      rx, rr)))
                  | Black -> Node (Red, ll, lx, (Node (Red, lrl, rx, rr)))))
            | Black -> Node (Red, ll, lx, (append lr r)))
         | Black ->
           (match rc with
            | Red -> Node (Red, (append_l rl), rx, rr)
            | Black ->
              let lrl = append lr rl in
              (match lrl with
               | Leaf -> lbalS ll lx (Node (Black, lrl, rx, rr))
               | Node (t0, lr', x, rl') ->
                 (match t0 with
                  | Red ->
                    Node (Red, (Node (Black, ll, lx, lr')), x, (Node (Black,
                      rl', rx, rr)))
                  | Black -> lbalS ll lx (Node (Black, lrl, rx, rr))))))
      in append_l
    
    (** val del : X.t -> tree -> tree **)
    
    let rec del x = function
    | Leaf -> Leaf
    | Node (t1, a, y, b0) ->
      (match X.compare x y with
       | Eq -> append a b0
       | Lt ->
         (match a with
          | Leaf -> Node (Red, (del x a), y, b0)
          | Node (t2, t3, t4, t5) ->
            (match t2 with
             | Red -> Node (Red, (del x a), y, b0)
             | Black -> lbalS (del x a) y b0))
       | Gt ->
         (match b0 with
          | Leaf -> Node (Red, a, y, (del x b0))
          | Node (t2, t3, t4, t5) ->
            (match t2 with
             | Red -> Node (Red, a, y, (del x b0))
             | Black -> rbalS a y (del x b0))))
    
    (** val remove : X.t -> tree -> tree **)
    
    let remove x t0 =
      makeBlack (del x t0)
    
    (** val delmin : tree -> elt -> tree -> (elt, tree) prod **)
    
    let rec delmin l x r =
      match l with
      | Leaf -> Pair (x, r)
      | Node (lc, ll, lx, lr) ->
        let Pair (k, l') = delmin ll lx lr in
        (match lc with
         | Red -> Pair (k, (Node (Red, l', x, r)))
         | Black -> Pair (k, (lbalS l' x r)))
    
    (** val remove_min : tree -> (elt, tree) prod option **)
    
    let remove_min = function
    | Leaf -> None
    | Node (t1, l, x, r) ->
      let Pair (k, t2) = delmin l x r in Some (Pair (k, (makeBlack t2)))
    
    (** val bogus : (tree, elt list) prod **)
    
    let bogus =
      Pair (Leaf, [])
    
    (** val treeify_zero : elt list -> (tree, elt list) prod **)
    
    let treeify_zero acc =
      Pair (Leaf, acc)
    
    (** val treeify_one : elt list -> (tree, elt list) prod **)
    
    let treeify_one = function
    | [] -> bogus
    | x::acc0 -> Pair ((Node (Red, Leaf, x, Leaf)), acc0)
    
    (** val treeify_cont :
        (elt list -> (tree, elt list) prod) -> (elt list -> (tree, elt list)
        prod) -> elt list -> (tree, elt list) prod **)
    
    let treeify_cont f0 g acc =
      let Pair (l, l0) = f0 acc in
      (match l0 with
       | [] -> bogus
       | x::acc0 ->
         let Pair (r, acc1) = g acc0 in Pair ((Node (Black, l, x, r)), acc1))
    
    (** val treeify_aux :
        bool -> positive -> elt list -> (tree, elt list) prod **)
    
    let rec treeify_aux pred0 = function
    | XI n1 -> treeify_cont (treeify_aux false n1) (treeify_aux pred0 n1)
    | XO n1 -> treeify_cont (treeify_aux pred0 n1) (treeify_aux true n1)
    | XH -> if pred0 then treeify_zero else treeify_one
    
    (** val plength_aux : elt list -> positive -> positive **)
    
    let rec plength_aux l p =
      match l with
      | [] -> p
      | e::l0 -> plength_aux l0 (Coq_Pos.succ p)
    
    (** val plength : elt list -> positive **)
    
    let plength l =
      plength_aux l XH
    
    (** val treeify : elt list -> tree **)
    
    let treeify l =
      fst (treeify_aux true (plength l) l)
    
    (** val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list **)
    
    let rec filter_aux f0 s acc =
      match s with
      | Leaf -> acc
      | Node (t0, l, k, r) ->
        let acc0 = filter_aux f0 r acc in
        if f0 k then filter_aux f0 l (k::acc0) else filter_aux f0 l acc0
    
    (** val filter : (elt -> bool) -> t -> t **)
    
    let filter f0 s =
      treeify (filter_aux f0 s [])
    
    (** val partition_aux :
        (elt -> bool) -> tree -> X.t list -> X.t list -> (X.t list, X.t list)
        prod **)
    
    let rec partition_aux f0 s acc1 acc2 =
      match s with
      | Leaf -> Pair (acc1, acc2)
      | Node (t0, sl, k, sr) ->
        let Pair (acc3, acc4) = partition_aux f0 sr acc1 acc2 in
        if f0 k
        then partition_aux f0 sl (k::acc3) acc4
        else partition_aux f0 sl acc3 (k::acc4)
    
    (** val partition : (elt -> bool) -> t -> (t, t) prod **)
    
    let partition f0 s =
      let Pair (ok, ko) = partition_aux f0 s [] [] in
      Pair ((treeify ok), (treeify ko))
    
    (** val union_list : X.t list -> elt list -> elt list -> elt list **)
    
    let rec union_list l1 = match l1 with
    | [] -> rev_append
    | x::l1' ->
      let rec union_l1 l2 acc =
        match l2 with
        | [] -> rev_append l1 acc
        | y::l2' ->
          (match X.compare x y with
           | Eq -> union_list l1' l2' (x::acc)
           | Lt -> union_l1 l2' (y::acc)
           | Gt -> union_list l1' l2 (x::acc))
      in union_l1
    
    (** val linear_union : tree -> tree -> tree **)
    
    let linear_union s1 s2 =
      treeify (union_list (rev_elements s1) (rev_elements s2) [])
    
    (** val inter_list : X.t list -> elt list -> elt list -> elt list **)
    
    let rec inter_list = function
    | [] -> (fun x acc -> acc)
    | x::l1' ->
      let rec inter_l1 l2 acc =
        match l2 with
        | [] -> acc
        | y::l2' ->
          (match X.compare x y with
           | Eq -> inter_list l1' l2' (x::acc)
           | Lt -> inter_l1 l2' acc
           | Gt -> inter_list l1' l2 acc)
      in inter_l1
    
    (** val linear_inter : tree -> tree -> tree **)
    
    let linear_inter s1 s2 =
      treeify (inter_list (rev_elements s1) (rev_elements s2) [])
    
    (** val diff_list : X.t list -> elt list -> elt list -> elt list **)
    
    let rec diff_list l1 = match l1 with
    | [] -> (fun x acc -> acc)
    | x::l1' ->
      let rec diff_l1 l2 acc =
        match l2 with
        | [] -> rev_append l1 acc
        | y::l2' ->
          (match X.compare x y with
           | Eq -> diff_list l1' l2' acc
           | Lt -> diff_l1 l2' acc
           | Gt -> diff_list l1' l2 (x::acc))
      in diff_l1
    
    (** val linear_diff : tree -> tree -> tree **)
    
    let linear_diff s1 s2 =
      treeify (diff_list (rev_elements s1) (rev_elements s2) [])
    
    (** val skip_red : tree -> tree **)
    
    let skip_red t0 = match t0 with
    | Leaf -> t0
    | Node (t1, t', t2, t3) ->
      (match t1 with
       | Red -> t'
       | Black -> t0)
    
    (** val skip_black : tree -> tree **)
    
    let skip_black t0 =
      match skip_red t0 with
      | Leaf -> Leaf
      | Node (t1, t', t2, t3) ->
        (match t1 with
         | Red -> Node (Red, t', t2, t3)
         | Black -> t')
    
    (** val compare_height : tree -> tree -> tree -> tree -> comparison **)
    
    let rec compare_height s1x s1 s2 s2x =
      match skip_red s1x with
      | Leaf ->
        (match skip_red s1 with
         | Leaf ->
           (match skip_red s2x with
            | Leaf -> Eq
            | Node (t0, t1, t2, t3) -> Lt)
         | Node (t0, s1', t1, t2) ->
           (match skip_red s2 with
            | Leaf -> Eq
            | Node (t3, s2', t4, t5) ->
              (match skip_red s2x with
               | Leaf -> Eq
               | Node (t6, s2x', t7, t8) ->
                 compare_height Leaf s1' s2' (skip_black s2x'))))
      | Node (t0, s1x', t1, t2) ->
        (match skip_red s1 with
         | Leaf ->
           (match skip_red s2 with
            | Leaf ->
              (match skip_red s2x with
               | Leaf -> Gt
               | Node (t3, t4, t5, t6) -> Lt)
            | Node (t3, t4, t5, t6) ->
              (match skip_red s2x with
               | Leaf -> Eq
               | Node (t7, t8, t9, t10) -> Lt))
         | Node (t3, s1', t4, t5) ->
           (match skip_red s2 with
            | Leaf -> Gt
            | Node (t6, s2', t7, t8) ->
              (match skip_red s2x with
               | Leaf -> compare_height (skip_black s1x') s1' s2' Leaf
               | Node (t9, s2x', t10, t11) ->
                 compare_height (skip_black s2x') s1' s2' (skip_black s2x'))))
    
    (** val union : t -> t -> t **)
    
    let union t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_union t1 t2
      | Lt -> fold add t1 t2
      | Gt -> fold add t2 t1
    
    (** val diff : t -> t -> t **)
    
    let diff t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_diff t1 t2
      | Lt -> filter (fun k -> negb (mem k t2)) t1
      | Gt -> fold remove t2 t1
    
    (** val inter : t -> t -> t **)
    
    let inter t1 t2 =
      match compare_height t1 t1 t2 t2 with
      | Eq -> linear_inter t1 t2
      | Lt -> filter (fun k -> mem k t2) t1
      | Gt -> filter (fun k -> mem k t1) t2
    
    (** val ltb_tree : X.t -> tree -> bool **)
    
    let rec ltb_tree x = function
    | Leaf -> true
    | Node (t0, l, y, r) ->
      (match X.compare x y with
       | Gt -> if ltb_tree x l then ltb_tree x r else false
       | _ -> false)
    
    (** val gtb_tree : X.t -> tree -> bool **)
    
    let rec gtb_tree x = function
    | Leaf -> true
    | Node (t0, l, y, r) ->
      (match X.compare x y with
       | Lt -> if gtb_tree x l then gtb_tree x r else false
       | _ -> false)
    
    (** val isok : tree -> bool **)
    
    let rec isok = function
    | Leaf -> true
    | Node (t0, l, x, r) ->
      if if if isok l then isok r else false then ltb_tree x l else false
      then gtb_tree x r
      else false
    
    module MX = OrderedTypeFacts(X)
    
    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * X.t * tree
    | R_min_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_min_elt
    
    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * X.t * tree
    | R_max_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_max_elt
    
    module L = MakeListOrdering(X)
    
    (** val flatten_e : enumeration -> elt list **)
    
    let rec flatten_e = function
    | End -> []
    | More (x, t0, r) -> x::(app (elements t0) (flatten_e r))
    
    (** val rcase :
        (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1 **)
    
    let rcase f0 g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x, b0) ->
      (match t1 with
       | Red -> f0 a x b0
       | Black -> g t0)
    
    (** val rrcase :
        (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree
        -> 'a1 **)
    
    let rrcase f0 g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, x, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b0, y, c0) ->
               (match t2 with
                | Red -> f0 a x b0 y c0
                | Black -> g t0))
          | Node (t2, a0, x0, b0) ->
            (match t2 with
             | Red -> f0 a0 x0 b0 x c
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b1, y, c0) ->
                  (match t3 with
                   | Red -> f0 a x b1 y c0
                   | Black -> g t0))))
       | Black -> g t0)
    
    (** val rrcase' :
        (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree
        -> 'a1 **)
    
    let rrcase' f0 g t0 = match t0 with
    | Leaf -> g t0
    | Node (t1, a, y, c) ->
      (match t1 with
       | Red ->
         (match a with
          | Leaf ->
            (match c with
             | Leaf -> g t0
             | Node (t2, b0, y0, c0) ->
               (match t2 with
                | Red -> f0 a y b0 y0 c0
                | Black -> g t0))
          | Node (t2, a0, x, b0) ->
            (match t2 with
             | Red ->
               (match c with
                | Leaf -> f0 a0 x b0 y c
                | Node (t3, b1, y0, c0) ->
                  (match t3 with
                   | Red -> f0 a y b1 y0 c0
                   | Black -> f0 a0 x b0 y c))
             | Black ->
               (match c with
                | Leaf -> g t0
                | Node (t3, b1, y0, c0) ->
                  (match t3 with
                   | Red -> f0 a y b1 y0 c0
                   | Black -> g t0))))
       | Black -> g t0)
   end
  
  module E = 
   struct 
    type t = X.t
    
    (** val compare : t -> t -> comparison **)
    
    let compare =
      X.compare
    
    (** val eq_dec : t -> t -> bool **)
    
    let eq_dec =
      X.eq_dec
   end
  
  type elt = X.t
  
  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  (** val this : t_ -> Raw.t **)
  
  let this t0 =
    t0
  
  type t = t_
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    Raw.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    Raw.add x (this s)
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    Raw.remove x (this s)
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    Raw.singleton x
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    Raw.union (this s) (this s')
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    Raw.inter (this s) (this s')
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    Raw.diff (this s) (this s')
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    Raw.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    Raw.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    Raw.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    Raw.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    Raw.elements (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    Raw.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f0 s =
    Raw.fold f0 (this s)
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    Raw.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f0 s =
    Raw.filter f0 (this s)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f0 s =
    Raw.for_all f0 (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f0 s =
    Raw.exists_ f0 (this s)
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition f0 s =
    let p = Raw.partition f0 (this s) in Pair ((fst p), (snd p))
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec s s' =
    let b0 = Raw.equal s s' in if b0 then true else false
  
  (** val compare : t -> t -> comparison **)
  
  let compare s s' =
    Raw.compare (this s) (this s')
  
  (** val min_elt : t -> elt option **)
  
  let min_elt s =
    Raw.min_elt (this s)
  
  (** val max_elt : t -> elt option **)
  
  let max_elt s =
    Raw.max_elt (this s)
  
  (** val mk_opt_t : (elt, Raw.t) prod option -> (elt, t) prod option **)
  
  let mk_opt_t = function
  | Some p -> let Pair (k, s') = p in Some (Pair (k, s'))
  | None -> None
  
  (** val remove_min : t_ -> (elt, t) prod option **)
  
  let remove_min s =
    mk_opt_t (Raw.remove_min (this s))
 end

module BedrockWordAsOrderedType = 
 struct 
  type t = BedrockWordW.coq_W
  
  (** val compare : t -> t -> comparison **)
  
  let compare x y =
    if BedrockWordW.wlt x y
    then Lt
    else if BedrockWordW.wlt y x then Gt else Eq
  
  (** val eq_dec : t -> t -> bool **)
  
  let eq_dec x y =
    if BedrockWordW.weq x y then true else false
 end

module FiniteSetADTMSet = 
 functor (FSMSet:sig 
  type elt = BedrockWordW.coq_W
  
  type t 
  
  val empty : t
  
  val is_empty : t -> bool
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val singleton : elt -> t
  
  val remove : elt -> t -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val filter : (elt -> bool) -> t -> t
  
  val partition : (elt -> bool) -> t -> (t, t) prod
  
  val cardinal : t -> nat
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val eq_dec : t -> t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end) ->
 struct 
  (** val coq_FiniteSetCImpl : cADT **)
  
  let coq_FiniteSetCImpl =
    buildcADT (sEmpty::[]) (sAdd::(sRemove::(sIn::(sSize::[])))) (Icons
      (sEmpty, [], (fun x -> FSMSet.empty), Inil)) (Icons (sAdd,
      (sRemove::(sIn::(sSize::[]))), (fun fs0 w0 -> Pair
      ((FSMSet.add (Obj.magic w0) fs0), (Obj.magic Tt))), (Icons (sRemove,
      (sIn::(sSize::[])), (fun fs0 w0 -> Pair
      ((FSMSet.remove (Obj.magic w0) fs0), (Obj.magic Tt))), (Icons (sIn,
      (sSize::[]), (fun fs0 w0 -> Pair (fs0,
      (Obj.magic (FSMSet.mem (Obj.magic w0) fs0)))), (Icons (sSize, [],
      (fun fs0 x -> Pair (fs0,
      (Obj.magic (BedrockWordW.from_nat (FSMSet.cardinal fs0))))),
      Inil))))))))
  
  (** val coq_FiniteSetImpl : (cADT, refineADT) sigT **)
  
  let coq_FiniteSetImpl =
    ExistT (coq_FiniteSetCImpl, RefinesADT)
 end

module MSetRBT_BedrockWord = Coq8_Make(BedrockWordAsOrderedType)

module FiniteSetADTMSetRBT = FiniteSetADTMSet(MSetRBT_BedrockWord)

(** val to_list0 : 'a1 list comp **)

let to_list0 =
  Pick

(** val fold_right0 : ('a1 -> 'a2 -> 'a2 comp) -> 'a2 comp -> 'a2 comp **)

let fold_right0 f0 b0 =
  Bind ((Obj.magic to_list0), (fun ls ->
    fold_right (fun a b' -> Bind ((Obj.magic b'), (Obj.magic f0 a))) b0
      (Obj.magic ls)))

(** val ensemble_fold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a2 comp **)

let ensemble_fold_right f0 b0 =
  fold_right0 (fun a b1 -> Return (f0 a b1)) (Return b0)

module String_as_OT = StringKey

module StringMap = Coq0_Make(String_as_OT)

(** val app_all : 'a1 list list -> 'a1 list **)

let rec app_all = function
| [] -> []
| x::xs -> app x (app_all xs)

type 'aDTValue value0 =
| SCA of w
| ADT of 'aDTValue

type 'aDTValue axiomaticSpec =
| Build_AxiomaticSpec

(** val is_adt : 'a1 value0 -> bool **)

let is_adt = function
| SCA w0 -> false
| ADT a -> true

type expr0 =
| Var1 of char list
| Const0 of w
| Binop0 of binop * expr0 * expr0
| TestE of test * expr0 * expr0

type glabel = (char list, char list) prod

(** val default0 : 'a1 -> 'a1 option -> 'a1 **)

let default0 def = function
| Some v -> v
| None -> def

(** val option_dec : 'a1 option -> 'a1 sumor **)

let option_dec =
  failwith "AXIOM TO BE REALIZED"

(** val sumbool_to_bool : bool -> bool **)

let sumbool_to_bool = function
| true -> true
| false -> false

(** val fold_right_2 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 list -> 'a1 **)

let rec fold_right_2 f0 def = function
| [] -> def
| x::xs ->
  (match xs with
   | [] -> x
   | y::l -> f0 x (fold_right_2 f0 def xs))

(** val noDup_bool : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec noDup_bool eqb1 = function
| [] -> true
| x::xs ->
  if forallb (fun e -> negb (eqb1 e x)) xs then noDup_bool eqb1 xs else false

(** val sumbool_to_bool0 : bool -> bool **)

let sumbool_to_bool0 = function
| true -> true
| false -> false

(** val string_bool : char list -> char list -> bool **)

let string_bool a b0 =
  sumbool_to_bool0 (string_dec a b0)

(** val is_no_dup : char list list -> bool **)

let is_no_dup =
  noDup_bool string_bool

module M = StringMap

(** val uncurry0 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3 **)

let uncurry0 f0 p =
  f0 (fst p) (snd p)

(** val filter0 : (M.key -> 'a1 -> bool) -> 'a1 M.t -> 'a1 M.t **)

let filter0 f0 m6 =
  M.fold (fun k e m7 -> if f0 k e then M.add k e m7 else m7) m6 M.empty

module Coq_M = StringSet

(** val in_dec0 : Coq_M.elt -> Coq_M.t -> bool **)

let in_dec0 =
  failwith "AXIOM TO BE REALIZED"

(** val of_list0 : Coq_M.elt list -> Coq_M.t **)

let of_list0 l =
  fold_right Coq_M.add Coq_M.empty l

type stmt =
| Skip
| Seq of stmt * stmt
| If of expr0 * stmt * stmt
| While of expr0 * stmt
| Call of char list * expr0 * char list list
| Label of char list * glabel
| Assign0 of char list * expr0

type operationalSpec = { argVars : char list list; retVar : char list;
                         body : stmt }

(** val argVars : operationalSpec -> char list list **)

let argVars x = x.argVars

(** val retVar : operationalSpec -> char list **)

let retVar x = x.retVar

(** val body : operationalSpec -> stmt **)

let body x = x.body

(** val free_vars : expr0 -> StringSet.t **)

let rec free_vars = function
| Var1 s -> StringSet.singleton s
| Const0 w0 -> StringSet.empty
| Binop0 (op, a, b0) -> StringSet.union (free_vars a) (free_vars b0)
| TestE (te, a, b0) -> StringSet.union (free_vars a) (free_vars b0)

(** val tmp_prefix : char list **)

let tmp_prefix =
  '!'::[]

module GLabel_as_MOT = 
 struct 
  type t = glabel
  
  (** val to_bl : t -> label **)
  
  let to_bl lbl =
    Pair ((fst lbl), (Global (snd lbl)))
  
  (** val compare : t -> t -> t compare0 **)
  
  let compare x y =
    let c = LabelKey.compare (to_bl x) (to_bl y) in
    (match c with
     | LT -> LT
     | EQ -> EQ
     | GT -> GT)
 end

module GLabel_as_OT = MOT_to_OT(GLabel_as_MOT)

module GLabel_as_UDT = Make_UDT(GLabel_as_OT)

module GLabelMap = Coq0_Make(GLabel_as_OT)

type stmt0 =
| Skip0
| Seq0 of stmt0 * stmt0
| If0 of expr0 * stmt0 * stmt0
| While0 of expr0 * stmt0
| Call0 of char list * glabel * char list list
| Assign1 of char list * expr0

type operationalSpec0 = { argVars0 : char list list; retVar0 : char list;
                          body0 : stmt0 }

(** val argVars0 : operationalSpec0 -> char list list **)

let argVars0 x = x.argVars0

(** val retVar0 : operationalSpec0 -> char list **)

let retVar0 x = x.retVar0

(** val body0 : operationalSpec0 -> stmt0 **)

let body0 x = x.body0

(** val fun_ptr_varname : char list **)

let fun_ptr_varname =
  append tmp_prefix ('f'::('p'::('t'::('r'::[]))))

(** val compile : stmt0 -> stmt **)

let rec compile = function
| Skip0 -> Skip
| Seq0 (a, b0) -> Seq ((compile a), (compile b0))
| If0 (e, t0, f0) -> If (e, (compile t0), (compile f0))
| While0 (e, c) -> While (e, (compile c))
| Call0 (x, f0, args) ->
  Seq ((Label (fun_ptr_varname, f0)), (Call (x, (Var1 fun_ptr_varname),
    args)))
| Assign1 (x, e) -> Assign0 (x, e)

(** val compile_op : operationalSpec0 -> operationalSpec **)

let compile_op spec1 =
  { argVars = spec1.argVars0; retVar = spec1.retVar0; body =
    (compile spec1.body0) }

type stmt1 =
| Skip1
| Seq1 of stmt1 * stmt1
| If1 of expr0 * stmt1 * stmt1
| While1 of expr0 * stmt1
| Call1 of char list option * expr0 * expr0 list
| Label0 of char list * glabel
| Assign2 of char list * expr0

type funcCore = { argVars1 : char list list; retVar1 : char list;
                  body1 : stmt1 }

(** val argVars1 : funcCore -> char list list **)

let argVars1 x = x.argVars1

(** val retVar1 : funcCore -> char list **)

let retVar1 x = x.retVar1

(** val body1 : funcCore -> stmt1 **)

let body1 x = x.body1

module W_as_MOT = 
 struct 
  type t = w
  
  (** val compare : t -> t -> t compare0 **)
  
  let compare x y =
    let s =
      lt_eq_lt_dec
        (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))) x)
        (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))) y)
    in
    (match s with
     | Inleft s0 -> if s0 then LT else EQ
     | Inright -> GT)
 end

module W_as_OT = MOT_to_OT(W_as_MOT)

module WordMap = Coq0_Make(W_as_OT)

module type ADT = 
 sig 
  type coq_ADTValue 
 end

type internalFuncSpec =
  funcCore
  (* singleton inductive, whose constructor was Build_InternalFuncSpec *)

(** val fun0 : internalFuncSpec -> funcCore **)

let fun0 i =
  i

type 'aDTValue heap = 'aDTValue WordMap.t

type 'aDTValue state0 = (vals, 'aDTValue heap) prod

type 'aDTValue callee =
| Foreign of 'aDTValue axiomaticSpec
| Internal of internalFuncSpec

type 'aDTValue argTriple = { word0 : w; aDTIn : 'aDTValue value0;
                             aDTOut : 'aDTValue option }

(** val word0 : 'a1 argTriple -> w **)

let word0 x = x.word0

(** val aDTIn : 'a1 argTriple -> 'a1 value0 **)

let aDTIn x = x.aDTIn

(** val aDTOut : 'a1 argTriple -> 'a1 option **)

let aDTOut x = x.aDTOut

(** val store_out : 'a1 heap -> 'a1 argTriple -> 'a1 heap **)

let store_out heap0 t0 =
  match t0.aDTIn with
  | SCA w0 -> heap0
  | ADT a0 ->
    (match t0.aDTOut with
     | Some a -> WordMap.add t0.word0 a heap0
     | None -> WordMap.remove t0.word0 heap0)

(** val decide_ret : w -> 'a1 value0 -> (w, 'a1 option) prod **)

let decide_ret addr0 = function
| SCA w0 -> Pair (w0, None)
| ADT a -> Pair (addr0, (Some a))

(** val heap_upd_option :
    'a1 WordMap.t -> WordMap.key -> 'a1 option -> 'a1 WordMap.t **)

let heap_upd_option m6 k = function
| Some x -> WordMap.add k x m6
| None -> m6

module Coq9_Make = 
 functor (E:ADT) ->
 struct 
  type coq_Heap = E.coq_ADTValue heap
  
  type coq_State = E.coq_ADTValue state0
  
  type coq_ArgIn = E.coq_ADTValue value0
  
  type coq_ArgOut = E.coq_ADTValue option
  
  type coq_Ret = E.coq_ADTValue value0
  
  type coq_ForeignFuncSpec = E.coq_ADTValue axiomaticSpec
  
  type coq_Callee = E.coq_ADTValue callee
  
  type coq_ArgTriple = E.coq_ADTValue argTriple
  
  (** val is_adt : E.coq_ADTValue value0 -> bool **)
  
  let is_adt =
    is_adt
  
  (** val store_out :
      E.coq_ADTValue heap -> E.coq_ADTValue argTriple -> E.coq_ADTValue heap **)
  
  let store_out =
    store_out
  
  (** val decide_ret :
      w -> E.coq_ADTValue value0 -> (w, E.coq_ADTValue option) prod **)
  
  let decide_ret =
    decide_ret
  
  (** val heap_upd_option :
      E.coq_ADTValue WordMap.t -> WordMap.key -> E.coq_ADTValue option ->
      E.coq_ADTValue WordMap.t **)
  
  let heap_upd_option =
    heap_upd_option
  
  (** val coq_Foreign :
      E.coq_ADTValue axiomaticSpec -> E.coq_ADTValue callee **)
  
  let coq_Foreign x =
    Foreign x
  
  (** val coq_Internal : internalFuncSpec -> E.coq_ADTValue callee **)
  
  let coq_Internal x =
    Internal x
  
  module P = Properties(WordMap)
  
  type elt = E.coq_ADTValue
  
  (** val heap_sel : coq_Heap -> WordMap.key -> E.coq_ADTValue option **)
  
  let heap_sel h p =
    WordMap.find p h
  
  (** val heap_upd : coq_Heap -> WordMap.key -> elt -> elt WordMap.t **)
  
  let heap_upd h p v =
    WordMap.add p v h
  
  (** val heap_remove :
      coq_Heap -> WordMap.key -> E.coq_ADTValue WordMap.t **)
  
  let heap_remove h p =
    WordMap.remove p h
  
  (** val heap_empty : elt WordMap.t **)
  
  let heap_empty =
    WordMap.empty
  
  (** val heap_merge : elt WordMap.t -> elt WordMap.t -> elt WordMap.t **)
  
  let heap_merge =
    P.update
  
  (** val heap_elements : elt WordMap.t -> (WordMap.key, elt) prod list **)
  
  let heap_elements =
    WordMap.elements
  
  (** val heap_diff : elt WordMap.t -> elt WordMap.t -> elt WordMap.t **)
  
  let heap_diff =
    P.diff
 end

(** val compile0 : stmt -> stmt1 **)

let rec compile0 = function
| Skip -> Skip1
| Seq (a, b0) -> Seq1 ((compile0 a), (compile0 b0))
| If (e, t0, f0) -> If1 (e, (compile0 t0), (compile0 f0))
| While (e, c) -> While1 (e, (compile0 c))
| Call (x, f0, args) -> Call1 ((Some x), f0, (map (fun x0 -> Var1 x0) args))
| Label (x, lbl) -> Label0 (x, lbl)
| Assign0 (x, e) -> Assign2 (x, e)

(** val compile_op0 : operationalSpec -> internalFuncSpec **)

let compile_op0 spec1 =
  { argVars1 = spec1.argVars; retVar1 = spec1.retVar; body1 =
    (compile0 spec1.body) }

type func0 = { name : char list; core0 : funcCore }

(** val name : func0 -> char list **)

let name x = x.name

(** val core0 : func0 -> funcCore **)

let core0 x = x.core0

(** val union_list0 : StringSet.t list -> StringSet.t **)

let union_list0 ls =
  fold_right StringSet.union StringSet.empty ls

(** val free_vars0 : stmt1 -> StringSet.t **)

let rec free_vars0 = function
| Skip1 -> StringSet.empty
| Seq1 (a, b0) -> StringSet.union (free_vars0 a) (free_vars0 b0)
| If1 (cond, t0, f0) ->
  StringSet.union (StringSet.union (free_vars cond) (free_vars0 t0))
    (free_vars0 f0)
| While1 (cond, body5) -> StringSet.union (free_vars cond) (free_vars0 body5)
| Call1 (var0, f0, args) ->
  StringSet.union
    (StringSet.union
      (default0 StringSet.empty (option_map StringSet.singleton var0))
      (free_vars f0)) (union_list0 (map free_vars args))
| Label0 (x, lbl) -> StringSet.singleton x
| Assign2 (x, e) -> StringSet.union (StringSet.singleton x) (free_vars e)

(** val get_local_vars :
    stmt1 -> Coq_M.elt list -> StringSet.elt -> StringSet.elt list **)

let get_local_vars stmt2 arg_vars ret_var =
  StringSet.elements
    (StringSet.diff (StringSet.add ret_var (free_vars0 stmt2))
      (Obj.magic (of_list0 arg_vars)))

(** val depth : expr0 -> nat **)

let rec depth = function
| Binop0 (b0, a, b1) -> max (depth a) (S (depth b1))
| TestE (t0, a, b0) -> max (depth a) (S (depth b0))
| _ -> O

(** val max_list : nat -> nat list -> nat **)

let max_list =
  fold_right max

(** val depth0 : stmt1 -> nat **)

let rec depth0 = function
| Seq1 (a, b0) -> max (depth0 a) (depth0 b0)
| If1 (cond, t0, f0) -> max (depth cond) (max (depth0 t0) (depth0 f0))
| While1 (cond, body5) -> max (depth cond) (depth0 body5)
| Call1 (o, f0, args) -> max (depth f0) (max_list O (map depth args))
| Assign2 (s, e) -> depth e
| _ -> O

(** val cito_module_impl_prefix : char list **)

let cito_module_impl_prefix =
  '_'::('_'::('c'::('m'::('o'::('d'::('_'::('i'::('m'::('p'::('l'::('_'::[])))))))))))

(** val impl_module_name : char list -> char list **)

let impl_module_name s =
  append cito_module_impl_prefix s

(** val is_good_module_name : char list -> bool **)

let is_good_module_name s =
  negb (prefix cito_module_impl_prefix s)

type fFunction =
  operationalSpec
  (* singleton inductive, whose constructor was Build_FFunction *)

(** val core1 : fFunction -> operationalSpec **)

let core1 f0 =
  f0

type 'aDTValue fModule = { imports0 : 'aDTValue axiomaticSpec GLabelMap.t;
                           functions0 : fFunction StringMap.t }

(** val functions0 : 'a1 fModule -> fFunction StringMap.t **)

let functions0 x = x.functions0

type 'aDTValue compileUnit = { prog : stmt0;
                               imports1 : 'aDTValue axiomaticSpec GLabelMap.t }

(** val prog : 'a1 compileUnit -> stmt0 **)

let prog x = x.prog

(** val imports1 : 'a1 compileUnit -> 'a1 axiomaticSpec GLabelMap.t **)

let imports1 x = x.imports1

(** val string_as_var : char list -> expr0 **)

let string_as_var str =
  Var1 str

(** val nat_as_constant : nat -> expr0 **)

let nat_as_constant n0 =
  Const0
    (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) n0)

(** val fold0 :
    StringMap.key -> StringMap.key -> StringMap.key -> glabel -> glabel ->
    stmt0 -> stmt0 **)

let fold0 head is_empty0 seq5 _pop_ _empty_ loop_body =
  Seq0 ((Call0 (is_empty0, _empty_, (seq5::[]))), (While0 ((TestE (Eq0,
    (string_as_var is_empty0), (nat_as_constant O))), (Seq0 ((Call0 (head,
    _pop_, (seq5::[]))), (Seq0 (loop_body, (Call0 (is_empty0, _empty_,
    (seq5::[]))))))))))

type aDTValue =
| List of w list
| Junk
| FEnsemble

module Adt = 
 struct 
  type coq_ADTValue = aDTValue
 end

(** val list_new : aDTValue axiomaticSpec **)

let list_new =
  Build_AxiomaticSpec

(** val list_delete : aDTValue axiomaticSpec **)

let list_delete =
  Build_AxiomaticSpec

(** val list_pop : aDTValue axiomaticSpec **)

let list_pop =
  Build_AxiomaticSpec

(** val list_empty : aDTValue axiomaticSpec **)

let list_empty =
  Build_AxiomaticSpec

(** val list_push : aDTValue axiomaticSpec **)

let list_push =
  Build_AxiomaticSpec

(** val list_copy : aDTValue axiomaticSpec **)

let list_copy =
  Build_AxiomaticSpec

(** val list_rev : aDTValue axiomaticSpec **)

let list_rev =
  Build_AxiomaticSpec

(** val list_length : aDTValue axiomaticSpec **)

let list_length =
  Build_AxiomaticSpec

(** val fEnsemble_sEmpty : aDTValue axiomaticSpec **)

let fEnsemble_sEmpty =
  Build_AxiomaticSpec

(** val fEnsemble_sDelete : aDTValue axiomaticSpec **)

let fEnsemble_sDelete =
  Build_AxiomaticSpec

(** val fEnsemble_sAdd : aDTValue axiomaticSpec **)

let fEnsemble_sAdd =
  Build_AxiomaticSpec

(** val fEnsemble_sRemove : aDTValue axiomaticSpec **)

let fEnsemble_sRemove =
  Build_AxiomaticSpec

(** val fEnsemble_sIn : aDTValue axiomaticSpec **)

let fEnsemble_sIn =
  Build_AxiomaticSpec

(** val fEnsemble_sSize : aDTValue axiomaticSpec **)

let fEnsemble_sSize =
  Build_AxiomaticSpec

module K = GLabel_as_UDT

module Coq0_M = GLabelMap

(** val uncurry1 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3 **)

let uncurry1 f0 p =
  f0 (fst p) (snd p)

(** val of_list1 : (Coq0_M.key, 'a1) prod list -> 'a1 Coq0_M.t **)

let of_list1 l =
  fold_right (uncurry1 Coq0_M.add) Coq0_M.empty l

(** val update0 : 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)

let update0 m6 m7 =
  Coq0_M.fold Coq0_M.add m7 m6

module P = 
 struct 
  module F = 
   struct 
    (** val eqb : glabel -> glabel -> bool **)
    
    let eqb x y =
      if K.eq_dec x y then true else false
    
    (** val coq_In_dec : 'a1 Coq0_M.t -> Coq0_M.key -> bool **)
    
    let coq_In_dec =
      failwith "AXIOM TO BE REALIZED"
    
    (** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)
    
    let option_map f0 = function
    | Some a -> Some (f0 a)
    | None -> None
   end
  
  (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3 **)
  
  let uncurry f0 p =
    f0 (fst p) (snd p)
  
  (** val of_list : (Coq0_M.key, 'a1) prod list -> 'a1 Coq0_M.t **)
  
  let of_list l =
    fold_right (uncurry Coq0_M.add) Coq0_M.empty l
  
  (** val to_list : 'a1 Coq0_M.t -> (Coq0_M.key, 'a1) prod list **)
  
  let to_list x =
    Coq0_M.elements x
  
  (** val fold_rec :
      (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Coq0_M.t -> ('a1
      Coq0_M.t -> __ -> 'a3) -> (Coq0_M.key -> 'a1 -> 'a2 -> 'a1 Coq0_M.t ->
      'a1 Coq0_M.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3 **)
  
  let fold_rec =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rec_bis :
      (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Coq0_M.t -> ('a1
      Coq0_M.t -> 'a1 Coq0_M.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
      (Coq0_M.key -> 'a1 -> 'a2 -> 'a1 Coq0_M.t -> __ -> __ -> 'a3 -> 'a3) ->
      'a3 **)
  
  let fold_rec_bis =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rec_nodep :
      (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Coq0_M.t -> 'a3 ->
      (Coq0_M.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)
  
  let fold_rec_nodep =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rec_weak :
      (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 Coq0_M.t -> 'a1
      Coq0_M.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (Coq0_M.key -> 'a1 ->
      'a2 -> 'a1 Coq0_M.t -> __ -> 'a3 -> 'a3) -> 'a1 Coq0_M.t -> 'a3 **)
  
  let fold_rec_weak =
    failwith "AXIOM TO BE REALIZED"
  
  (** val fold_rel :
      (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> (Coq0_M.key -> 'a1 -> 'a3 -> 'a3)
      -> 'a2 -> 'a3 -> 'a1 Coq0_M.t -> 'a4 -> (Coq0_M.key -> 'a1 -> 'a2 ->
      'a3 -> __ -> 'a4 -> 'a4) -> 'a4 **)
  
  let fold_rel =
    failwith "AXIOM TO BE REALIZED"
  
  (** val map_induction :
      ('a1 Coq0_M.t -> __ -> 'a2) -> ('a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a2 ->
      Coq0_M.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 Coq0_M.t -> 'a2 **)
  
  let map_induction =
    failwith "AXIOM TO BE REALIZED"
  
  (** val map_induction_bis :
      ('a1 Coq0_M.t -> 'a1 Coq0_M.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
      (Coq0_M.key -> 'a1 -> 'a1 Coq0_M.t -> __ -> 'a2 -> 'a2) -> 'a1 Coq0_M.t
      -> 'a2 **)
  
  let map_induction_bis =
    failwith "AXIOM TO BE REALIZED"
  
  (** val cardinal_inv_2 : 'a1 Coq0_M.t -> nat -> (Coq0_M.key, 'a1) prod **)
  
  let cardinal_inv_2 =
    failwith "AXIOM TO BE REALIZED"
  
  (** val cardinal_inv_2b : 'a1 Coq0_M.t -> (Coq0_M.key, 'a1) prod **)
  
  let cardinal_inv_2b =
    failwith "AXIOM TO BE REALIZED"
  
  (** val filter :
      (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
  
  let filter f0 m6 =
    Coq0_M.fold (fun k e m7 -> if f0 k e then Coq0_M.add k e m7 else m7) m6
      Coq0_M.empty
  
  (** val for_all : (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
  
  let for_all f0 m6 =
    Coq0_M.fold (fun k e b0 -> if f0 k e then b0 else false) m6 true
  
  (** val exists_ : (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
  
  let exists_ f0 m6 =
    Coq0_M.fold (fun k e b0 -> if f0 k e then true else b0) m6 false
  
  (** val partition :
      (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> ('a1 Coq0_M.t, 'a1
      Coq0_M.t) prod **)
  
  let partition f0 m6 =
    Pair ((filter f0 m6), (filter (fun k e -> negb (f0 k e)) m6))
  
  (** val update : 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
  
  let update m6 m7 =
    Coq0_M.fold Coq0_M.add m7 m6
  
  (** val restrict : 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
  
  let restrict m6 m7 =
    filter (fun k x -> Coq0_M.mem k m7) m6
  
  (** val diff : 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
  
  let diff m6 m7 =
    filter (fun k x -> negb (Coq0_M.mem k m7)) m6
  
  (** val coq_Partition_In :
      'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> Coq0_M.key -> bool **)
  
  let coq_Partition_In m6 m7 m8 k =
    F.coq_In_dec m7 k
  
  (** val update_dec :
      'a1 Coq0_M.t -> 'a1 Coq0_M.t -> Coq0_M.key -> 'a1 -> bool **)
  
  let update_dec m6 m' k e =
    F.coq_In_dec m' k
  
  (** val filter_dom :
      (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
  
  let filter_dom f0 =
    filter (fun k x -> f0 k)
  
  (** val filter_range : ('a1 -> bool) -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
  
  let filter_range f0 =
    filter (fun x -> f0)
  
  (** val for_all_dom : (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> bool **)
  
  let for_all_dom f0 =
    for_all (fun k x -> f0 k)
  
  (** val for_all_range : ('a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
  
  let for_all_range f0 =
    for_all (fun x -> f0)
  
  (** val exists_dom : (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> bool **)
  
  let exists_dom f0 =
    exists_ (fun k x -> f0 k)
  
  (** val exists_range : ('a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
  
  let exists_range f0 =
    exists_ (fun x -> f0)
  
  (** val partition_dom :
      (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> ('a1 Coq0_M.t, 'a1 Coq0_M.t)
      prod **)
  
  let partition_dom f0 =
    partition (fun k x -> f0 k)
  
  (** val partition_range :
      ('a1 -> bool) -> 'a1 Coq0_M.t -> ('a1 Coq0_M.t, 'a1 Coq0_M.t) prod **)
  
  let partition_range f0 =
    partition (fun x -> f0)
 end

(** val to_map : (Coq0_M.key, 'a1) prod list -> 'a1 Coq0_M.t **)

let to_map l =
  P.of_list l

(** val keys : 'a1 Coq0_M.t -> Coq0_M.key list **)

let keys m6 =
  map fst (Coq0_M.elements m6)

(** val inKey_dec : Coq0_M.key -> (Coq0_M.key, 'a1) prod list -> bool **)

let inKey_dec k ls =
  in_dec K.eq_dec k (map fst ls)

(** val diff_map :
    (Coq0_M.key, 'a1) prod list -> (Coq0_M.key, 'a1) prod list ->
    (Coq0_M.key, 'a1) prod list **)

let diff_map ls1 ls2 =
  let f0 = fun p -> negb (sumbool_to_bool (inKey_dec (fst p) ls2)) in
  filter f0 ls1

module UWFacts = 
 struct 
  module WFacts = 
   struct 
    module P = 
     struct 
      module F = 
       struct 
        (** val eqb : glabel -> glabel -> bool **)
        
        let eqb x y =
          if K.eq_dec x y then true else false
        
        (** val coq_In_dec : 'a1 Coq0_M.t -> Coq0_M.key -> bool **)
        
        let coq_In_dec =
          failwith "AXIOM TO BE REALIZED"
        
        (** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)
        
        let option_map f0 = function
        | Some a -> Some (f0 a)
        | None -> None
       end
      
      (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3 **)
      
      let uncurry f0 p =
        f0 (fst p) (snd p)
      
      (** val of_list : (Coq0_M.key, 'a1) prod list -> 'a1 Coq0_M.t **)
      
      let of_list l =
        fold_right (uncurry Coq0_M.add) Coq0_M.empty l
      
      (** val to_list : 'a1 Coq0_M.t -> (Coq0_M.key, 'a1) prod list **)
      
      let to_list x =
        Coq0_M.elements x
      
      (** val fold_rec :
          (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Coq0_M.t -> ('a1
          Coq0_M.t -> __ -> 'a3) -> (Coq0_M.key -> 'a1 -> 'a2 -> 'a1 Coq0_M.t
          -> 'a1 Coq0_M.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3 **)
      
      let fold_rec =
        failwith "AXIOM TO BE REALIZED"
      
      (** val fold_rec_bis :
          (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Coq0_M.t -> ('a1
          Coq0_M.t -> 'a1 Coq0_M.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
          (Coq0_M.key -> 'a1 -> 'a2 -> 'a1 Coq0_M.t -> __ -> __ -> 'a3 ->
          'a3) -> 'a3 **)
      
      let fold_rec_bis =
        failwith "AXIOM TO BE REALIZED"
      
      (** val fold_rec_nodep :
          (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 Coq0_M.t -> 'a3 ->
          (Coq0_M.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)
      
      let fold_rec_nodep =
        failwith "AXIOM TO BE REALIZED"
      
      (** val fold_rec_weak :
          (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 Coq0_M.t -> 'a1
          Coq0_M.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (Coq0_M.key -> 'a1
          -> 'a2 -> 'a1 Coq0_M.t -> __ -> 'a3 -> 'a3) -> 'a1 Coq0_M.t -> 'a3 **)
      
      let fold_rec_weak =
        failwith "AXIOM TO BE REALIZED"
      
      (** val fold_rel :
          (Coq0_M.key -> 'a1 -> 'a2 -> 'a2) -> (Coq0_M.key -> 'a1 -> 'a3 ->
          'a3) -> 'a2 -> 'a3 -> 'a1 Coq0_M.t -> 'a4 -> (Coq0_M.key -> 'a1 ->
          'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4 **)
      
      let fold_rel =
        failwith "AXIOM TO BE REALIZED"
      
      (** val map_induction :
          ('a1 Coq0_M.t -> __ -> 'a2) -> ('a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a2
          -> Coq0_M.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 Coq0_M.t -> 'a2 **)
      
      let map_induction =
        failwith "AXIOM TO BE REALIZED"
      
      (** val map_induction_bis :
          ('a1 Coq0_M.t -> 'a1 Coq0_M.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Coq0_M.key -> 'a1 -> 'a1 Coq0_M.t -> __ -> 'a2 -> 'a2) -> 'a1
          Coq0_M.t -> 'a2 **)
      
      let map_induction_bis =
        failwith "AXIOM TO BE REALIZED"
      
      (** val cardinal_inv_2 :
          'a1 Coq0_M.t -> nat -> (Coq0_M.key, 'a1) prod **)
      
      let cardinal_inv_2 =
        failwith "AXIOM TO BE REALIZED"
      
      (** val cardinal_inv_2b : 'a1 Coq0_M.t -> (Coq0_M.key, 'a1) prod **)
      
      let cardinal_inv_2b =
        failwith "AXIOM TO BE REALIZED"
      
      (** val filter :
          (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
      
      let filter f0 m6 =
        Coq0_M.fold (fun k e m7 -> if f0 k e then Coq0_M.add k e m7 else m7)
          m6 Coq0_M.empty
      
      (** val for_all :
          (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
      
      let for_all f0 m6 =
        Coq0_M.fold (fun k e b0 -> if f0 k e then b0 else false) m6 true
      
      (** val exists_ :
          (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
      
      let exists_ f0 m6 =
        Coq0_M.fold (fun k e b0 -> if f0 k e then true else b0) m6 false
      
      (** val partition :
          (Coq0_M.key -> 'a1 -> bool) -> 'a1 Coq0_M.t -> ('a1 Coq0_M.t, 'a1
          Coq0_M.t) prod **)
      
      let partition f0 m6 =
        Pair ((filter f0 m6), (filter (fun k e -> negb (f0 k e)) m6))
      
      (** val update : 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
      
      let update m6 m7 =
        Coq0_M.fold Coq0_M.add m7 m6
      
      (** val restrict : 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
      
      let restrict m6 m7 =
        filter (fun k x -> Coq0_M.mem k m7) m6
      
      (** val diff : 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
      
      let diff m6 m7 =
        filter (fun k x -> negb (Coq0_M.mem k m7)) m6
      
      (** val coq_Partition_In :
          'a1 Coq0_M.t -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t -> Coq0_M.key -> bool **)
      
      let coq_Partition_In m6 m7 m8 k =
        F.coq_In_dec m7 k
      
      (** val update_dec :
          'a1 Coq0_M.t -> 'a1 Coq0_M.t -> Coq0_M.key -> 'a1 -> bool **)
      
      let update_dec m6 m' k e =
        F.coq_In_dec m' k
      
      (** val filter_dom :
          (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
      
      let filter_dom f0 =
        filter (fun k x -> f0 k)
      
      (** val filter_range :
          ('a1 -> bool) -> 'a1 Coq0_M.t -> 'a1 Coq0_M.t **)
      
      let filter_range f0 =
        filter (fun x -> f0)
      
      (** val for_all_dom : (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> bool **)
      
      let for_all_dom f0 =
        for_all (fun k x -> f0 k)
      
      (** val for_all_range : ('a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
      
      let for_all_range f0 =
        for_all (fun x -> f0)
      
      (** val exists_dom : (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> bool **)
      
      let exists_dom f0 =
        exists_ (fun k x -> f0 k)
      
      (** val exists_range : ('a1 -> bool) -> 'a1 Coq0_M.t -> bool **)
      
      let exists_range f0 =
        exists_ (fun x -> f0)
      
      (** val partition_dom :
          (Coq0_M.key -> bool) -> 'a1 Coq0_M.t -> ('a1 Coq0_M.t, 'a1
          Coq0_M.t) prod **)
      
      let partition_dom f0 =
        partition (fun k x -> f0 k)
      
      (** val partition_range :
          ('a1 -> bool) -> 'a1 Coq0_M.t -> ('a1 Coq0_M.t, 'a1 Coq0_M.t) prod **)
      
      let partition_range f0 =
        partition (fun x -> f0)
     end
    
    (** val to_map : (Coq0_M.key, 'a1) prod list -> 'a1 Coq0_M.t **)
    
    let to_map l =
      P.of_list l
    
    (** val keys : 'a1 Coq0_M.t -> Coq0_M.key list **)
    
    let keys m6 =
      map fst (Coq0_M.elements m6)
    
    (** val find_list :
        Coq0_M.key -> (glabel, 'a1) prod list -> 'a1 option **)
    
    let find_list k =
      findA (P.F.eqb k)
   end
  
  (** val coq_InKey_dec :
      Coq0_M.key -> (Coq0_M.key, 'a1) prod list -> bool **)
  
  let coq_InKey_dec k ls =
    in_dec K.eq_dec k (map fst ls)
  
  (** val diff_map :
      (Coq0_M.key, 'a1) prod list -> (Coq0_M.key, 'a1) prod list ->
      (Coq0_M.key, 'a1) prod list **)
  
  let diff_map ls1 ls2 =
    let f0 = fun p -> negb (sumbool_to_bool (coq_InKey_dec (fst p) ls2)) in
    filter f0 ls1
 end

(** val update_all : 'a1 Coq0_M.t list -> 'a1 Coq0_M.t **)

let update_all ms0 =
  fold_left (fun acc m6 -> UWFacts.WFacts.P.update acc m6) ms0 Coq0_M.empty

(** val makePair : glabel -> 'a1 -> (glabel, 'a1) prod **)

let makePair k v =
  Pair (k, v)

(** val addPair :
    (GLabelMap.key, 'a1) prod -> 'a1 GLabelMap.t -> 'a1 GLabelMap.t **)

let addPair pair m6 =
  GLabelMap.add (fst pair) (snd pair) m6

(** val basic_imports : aDTValue axiomaticSpec GLabelMap.t **)

let basic_imports =
  addPair
    (makePair (Pair (('A'::('D'::('T'::[]))),
      ('e'::('m'::('p'::('t'::('y'::[]))))))) list_empty)
    (addPair
      (makePair (Pair (('A'::('D'::('T'::[]))), ('p'::('o'::('p'::[])))))
        list_pop)
      (addPair
        (makePair (Pair (('A'::('D'::('T'::[]))), ('n'::('e'::('w'::[])))))
          list_new)
        (addPair
          (makePair (Pair (('A'::('D'::('T'::[]))),
            ('p'::('u'::('s'::('h'::[])))))) list_push)
          (addPair
            (makePair (Pair (('A'::('D'::('T'::[]))),
              ('c'::('o'::('p'::('y'::[])))))) list_copy)
            (addPair
              (makePair (Pair (('A'::('D'::('T'::[]))),
                ('d'::('e'::('l'::('e'::('t'::('e'::[])))))))) list_delete)
              (addPair
                (makePair (Pair (('A'::('D'::('T'::[]))),
                  ('r'::('e'::('v'::[]))))) list_rev)
                (addPair
                  (makePair (Pair (('A'::('D'::('T'::[]))),
                    ('s'::('E'::('m'::('p'::('t'::('y'::[]))))))))
                    fEnsemble_sEmpty)
                  (addPair
                    (makePair (Pair (('A'::('D'::('T'::[]))),
                      ('s'::('A'::('d'::('d'::[])))))) fEnsemble_sAdd)
                    (addPair
                      (makePair (Pair (('A'::('D'::('T'::[]))),
                        ('s'::('R'::('e'::('m'::('o'::('v'::('e'::[])))))))))
                        fEnsemble_sRemove)
                      (addPair
                        (makePair (Pair (('A'::('D'::('T'::[]))),
                          ('s'::('D'::('e'::('l'::('e'::('t'::('e'::[])))))))))
                          fEnsemble_sDelete)
                        (addPair
                          (makePair (Pair (('A'::('D'::('T'::[]))),
                            ('s'::('I'::('n'::[]))))) fEnsemble_sIn)
                          (addPair
                            (makePair (Pair (('A'::('D'::('T'::[]))),
                              ('s'::('S'::('i'::('z'::('e'::[])))))))
                              fEnsemble_sSize) GLabelMap.empty))))))))))))

(** val sumUniqueSpec :
    BedrockWordW.coq_W list -> BedrockWordW.coq_W comp **)

let sumUniqueSpec ls =
  ensemble_fold_right BedrockWordW.wplus BedrockWordW.wzero

(** val fullySharpenedFacadeProgramOnListReturningWordByRefinements :
    (w list -> w comp) -> (stmt0, (__, 'a1) prod) sigT -> (stmt0, (__, 'a1)
    prod) sigT **)

let fullySharpenedFacadeProgramOnListReturningWordByRefinements spec1 = function
| ExistT (prog0, p) ->
  let Pair (_, p0) = p in ExistT (prog0, (Pair (__, p0)))

type fullySharpenedFacadeProgramOnListReturningWord = aDTValue compileUnit

type is_disjoint_r =
  unit0
  (* singleton inductive, whose constructor was Build_is_disjoint_r *)

type is_syntax_ok_r =
  unit0
  (* singleton inductive, whose constructor was Build_is_syntax_ok_r *)

(** val compileUnit_construct :
    'a1 axiomaticSpec GLabelMap.t -> (stmt0, (__, (is_disjoint_r,
    (is_syntax_ok_r, __) sigT) sigT) prod) sigT -> 'a1 compileUnit **)

let compileUnit_construct imports3 = function
| ExistT (prog0, p) -> { prog = prog0; imports1 = imports3 }

(** val sumUniqueImpl :
    (cADT, refineADT) sigT -> fullySharpenedFacadeProgramOnListReturningWord **)

let sumUniqueImpl finiteSetImpl =
  compileUnit_construct basic_imports
    (fullySharpenedFacadeProgramOnListReturningWordByRefinements
      sumUniqueSpec (ExistT ((Seq0 ((Seq0 ((Seq0 ((Seq0 ((Call0
      (('$'::('d'::('i'::('s'::('c'::('a'::('r'::('d'::[])))))))), (Pair
      (('A'::('D'::('T'::[]))), ('r'::('e'::('v'::[]))))),
      (('a'::('r'::('g'::('1'::[]))))::[]))), (Seq0 ((Assign1
      (('r'::('e'::('t'::[]))), (Const0 BedrockWordW.wzero))), (Seq0 ((Call0
      (('$'::('a'::('d'::('t'::[])))), (Pair (('A'::('D'::('T'::[]))),
      ('s'::('E'::('m'::('p'::('t'::('y'::[])))))))), [])),
      (fold0 ('$'::('h'::('e'::('a'::('d'::[])))))
        ('$'::('i'::('s'::('_'::('e'::('m'::('p'::('t'::('y'::[])))))))))
        ('a'::('r'::('g'::('1'::[])))) (Pair (('A'::('D'::('T'::[]))),
        ('p'::('o'::('p'::[]))))) (Pair (('A'::('D'::('T'::[]))),
        ('e'::('m'::('p'::('t'::('y'::[]))))))) (Seq0 ((Call0
        (('$'::('c'::('o'::('n'::('d'::[]))))), (Pair
        (('A'::('D'::('T'::[]))), ('s'::('I'::('n'::[]))))),
        (('$'::('a'::('d'::('t'::[]))))::(('$'::('h'::('e'::('a'::('d'::[])))))::[])))),
        (If0 ((TestE (Eq0,
        (string_as_var ('$'::('c'::('o'::('n'::('d'::[])))))),
        (nat_as_constant O))), (Seq0 ((Seq0 ((Seq0 ((Seq0 ((Assign1
        (('$'::('t'::('1'::[]))),
        (string_as_var ('$'::('h'::('e'::('a'::('d'::[])))))))), (Seq0
        ((Assign1 (('$'::('t'::('2'::[]))),
        (string_as_var ('r'::('e'::('t'::[])))))), (Assign1
        (('r'::('e'::('t'::[]))), (Binop0 (Plus,
        (string_as_var ('$'::('t'::('1'::[])))),
        (string_as_var ('$'::('t'::('2'::[])))))))))))), Skip0)), (Call0
        (('$'::('d'::('u'::('m'::('m'::('y'::('_'::('r'::('e'::('t'::[])))))))))),
        (Pair (('A'::('D'::('T'::[]))), ('s'::('A'::('d'::('d'::[])))))),
        (('$'::('a'::('d'::('t'::[]))))::(('$'::('h'::('e'::('a'::('d'::[])))))::[])))))),
        (Seq0 (Skip0, Skip0)))), Skip0))))))))))), (Call0
      (('$'::('d'::('i'::('s'::('c'::('a'::('r'::('d'::[])))))))), (Pair
      (('A'::('D'::('T'::[]))),
      ('s'::('D'::('e'::('l'::('e'::('t'::('e'::[]))))))))),
      (('$'::('a'::('d'::('t'::[]))))::[]))))), (Call0
      (('$'::('d'::('u'::('m'::('m'::('y'::('_'::('r'::('e'::('t'::[])))))))))),
      (Pair (('A'::('D'::('T'::[]))),
      ('d'::('e'::('l'::('e'::('t'::('e'::[])))))))),
      (('a'::('r'::('g'::('1'::[]))))::[]))))), (Seq0 (Skip0, Skip0)))),
      (Pair (__,
      (let h = Tt in ExistT (h, (let h0 = Tt in ExistT (h0, __)))))))))

module BedrockPtsToEvaluator = 
 struct 
  (** val ptsto32_types_r : type0 repr **)
  
  let ptsto32_types_r =
    { footprint =
      (map (fun x -> Some x)
        (bedrock_type_W::(bedrock_type_setting_X_state::[]))); default =
      emptySet_type }
  
  type psummary = facts
  
  (** val expr_equal :
      type0 list -> proverT -> psummary -> tvar -> expr -> expr -> bool **)
  
  let expr_equal types4 prover sum tv a b0 =
    if expr_seq_dec types4 a b0
    then true
    else prover.prove sum (Equal (tv, a, b0))
  
  (** val sym_read_word_ptsto32 :
      type0 list -> proverT -> psummary -> expr list -> expr -> expr option **)
  
  let sym_read_word_ptsto32 types4 prover summ args p =
    match args with
    | [] -> None
    | p'::l ->
      (match l with
       | [] -> None
       | v'::l0 ->
         (match l0 with
          | [] ->
            if expr_equal types4 prover summ (TvType O) p p'
            then Some v'
            else None
          | e::l1 -> None))
  
  (** val sym_write_word_ptsto32 :
      type0 list -> proverT -> psummary -> expr list -> expr -> expr -> expr
      list option **)
  
  let sym_write_word_ptsto32 types4 prover summ args p v =
    match args with
    | [] -> None
    | p'::l ->
      (match l with
       | [] -> None
       | v'::l0 ->
         (match l0 with
          | [] ->
            if expr_equal types4 prover summ (TvType O) p p'
            then Some (p::(v::[]))
            else None
          | e::l1 -> None))
  
  (** val coq_MemEval_ptsto32 :
      type0 list -> MEVAL.PredEval.coq_MemEvalPred **)
  
  let coq_MemEval_ptsto32 types4 =
    { MEVAL.PredEval.pred_read_word = (sym_read_word_ptsto32 types4);
      MEVAL.PredEval.pred_write_word = (sym_write_word_ptsto32 types4);
      MEVAL.PredEval.pred_read_byte = (fun p facts0 args p0 -> None);
      MEVAL.PredEval.pred_write_byte = (fun p facts0 args p0 v -> None) }
  
  (** val types : type0 list -> type0 list **)
  
  let types types' =
    repr0 ptsto32_types_r types'
  
  (** val ptsto32_ssig : type0 list -> SEP.predicate **)
  
  let ptsto32_ssig types' =
    { SEP.coq_SDomain = ((TvType O)::((TvType O)::[])); SEP.coq_SDenotation =
      (Obj.magic (ptsto32 [])) }
  
  (** val ptsto32_ssig_r : type0 list -> SEP.predicate repr **)
  
  let ptsto32_ssig_r types' =
    { footprint = (map (fun x -> Some x) ((ptsto32_ssig types')::[]));
      default =
      (SEP.coq_Default_predicate (types types') (TvType O) (TvType (S O))) }
  
  (** val coq_MemEvaluator_ptsto32 : type0 list -> MEVAL.coq_MemEvaluator **)
  
  let coq_MemEvaluator_ptsto32 types' =
    { MEVAL.sread_word = (fun p f0 p0 h ->
      match FM.find O h.SH.impures with
      | Some argss ->
        MEVAL.PredEval.fold_args types' (fun args ->
          (coq_MemEval_ptsto32 types').MEVAL.PredEval.pred_read_word p f0
            args p0) argss
      | None -> None); MEVAL.swrite_word = (fun p f0 p0 v h ->
      match FM.find O h.SH.impures with
      | Some argss ->
        (match MEVAL.PredEval.fold_args_update types' (fun args ->
                 (coq_MemEval_ptsto32 types').MEVAL.PredEval.pred_write_word
                   p f0 args p0 v) argss with
         | Some argss0 ->
           Some { SH.impures = (FM.add O argss0 h.SH.impures); SH.pures =
             h.SH.pures; SH.other = h.SH.other }
         | None -> None)
      | None -> None); MEVAL.sread_byte = (fun p f0 p0 h ->
      match FM.find O h.SH.impures with
      | Some argss ->
        MEVAL.PredEval.fold_args types' (fun args ->
          (coq_MemEval_ptsto32 types').MEVAL.PredEval.pred_read_byte p f0
            args p0) argss
      | None -> None); MEVAL.swrite_byte = (fun p f0 p0 v h ->
      match FM.find O h.SH.impures with
      | Some argss ->
        (match MEVAL.PredEval.fold_args_update types' (fun args ->
                 (coq_MemEval_ptsto32 types').MEVAL.PredEval.pred_write_byte
                   p f0 args p0 v) argss with
         | Some argss0 ->
           Some { SH.impures = (FM.add O argss0 h.SH.impures); SH.pures =
             h.SH.pures; SH.other = h.SH.other }
         | None -> None)
      | None -> None) }
  
  (** val ptsto32_pack : MEVAL.coq_MemEvaluatorPackage **)
  
  let ptsto32_pack =
    { MEVAL.coq_MemEvalTypes = (nil_Repr emptySet_type);
      MEVAL.coq_MemEvalFuncs = (fun ts ->
      nil_Repr (default_signature (repr0 ptsto32_types_r ts)));
      MEVAL.coq_MemEvalPreds = (fun ts ->
      listToRepr ((Obj.magic (ptsto32_ssig ts))::[])
        (Obj.magic
          (SEP.coq_Default_predicate (repr0 ptsto32_types_r ts) (TvType O)
            (TvType (S O))))); MEVAL.coq_MemEval = (fun ts ->
      coq_MemEvaluator_ptsto32
        (repr0 ptsto32_types_r (repr0 (nil_Repr emptySet_type) ts))) }
 end

(** val array8 : b list -> w -> hProp **)

let rec array8 bs p =
  match bs with
  | [] -> empB []
  | b0::bs' ->
    starB [] (ptsto8 [] p b0)
      (array8 bs'
        (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
          p
          (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) (S O))))

(** val selN0 : b list -> nat -> b **)

let rec selN0 bs n0 =
  match bs with
  | [] -> wzero (S (S (S (S (S (S (S (S O))))))))
  | b0::bs' ->
    (match n0 with
     | O -> b0
     | S n' -> selN0 bs' n')

(** val sel1 : b list -> w -> b **)

let sel1 bs a =
  selN0 bs
    (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) a)

(** val updN0 : b list -> nat -> b -> b list **)

let rec updN0 bs n0 v =
  match bs with
  | [] -> []
  | b0::bs' ->
    (match n0 with
     | O -> v::bs'
     | S n' -> b0::(updN0 bs' n' v))

(** val upd1 : b list -> w -> b -> b list **)

let upd1 bs a v =
  updN0 bs
    (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) a) v

(** val bedrock_type_B : type0 **)

let bedrock_type_B x y =
  false

(** val bedrock_type_listB : type0 **)

let bedrock_type_listB x y =
  false

(** val types_r1 : type0 repr **)

let types_r1 =
  { footprint = ((Some bedrock_type_W)::((Some
    bedrock_type_setting_X_state)::(None::(None::((Some
    bedrock_type_nat)::(None::(None::(None::(None::((Some
    bedrock_type_B)::((Some bedrock_type_listB)::[]))))))))))); default =
    emptySet_type }

(** val types1 : type0 list -> type0 list **)

let types1 types' =
  repr0 types_r1 types'

(** val deref1 : type0 list -> expr -> (expr, expr) prod option **)

let deref1 types' = function
| Func (f0, l) ->
  (match f0 with
   | O ->
     (match l with
      | [] -> None
      | base::l0 ->
        (match l0 with
         | [] -> None
         | offset::l1 ->
           (match l1 with
            | [] -> Some (Pair (base, offset))
            | e0::l2 -> None)))
   | S n0 -> None)
| _ -> None

(** val sym_read1 :
    type0 list -> proverT -> facts -> expr list -> expr -> expr option **)

let sym_read1 types' prover summ args p =
  match args with
  | [] -> None
  | bs::l ->
    (match l with
     | [] -> None
     | p'::l0 ->
       (match l0 with
        | [] ->
          (match deref1 types' p with
           | Some p0 ->
             let Pair (base, offset) = p0 in
             if if prover.prove summ (Equal ((TvType O), p', base))
                then prover.prove summ (Func ((S (S (S (S O)))),
                       (offset::((Func ((S (S (S (S (S O))))), ((Func ((S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O))))))))))))))), (bs::[])))::[])))::[]))))
                else false
             then Some (Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S O)))))))))))))))))), ((Func ((S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S O)))))))))))))))),
                    (bs::(offset::[]))))::[])))
             else None
           | None -> None)
        | e::l1 -> None))

(** val sym_write1 :
    type0 list -> proverT -> facts -> expr list -> expr -> expr -> expr list
    option **)

let sym_write1 types' prover summ args p v =
  match args with
  | [] -> None
  | bs::l ->
    (match l with
     | [] -> None
     | p'::l0 ->
       (match l0 with
        | [] ->
          (match deref1 types' p with
           | Some p0 ->
             let Pair (base, offset) = p0 in
             if if prover.prove summ (Equal ((TvType O), p', base))
                then prover.prove summ (Func ((S (S (S (S O)))),
                       (offset::((Func ((S (S (S (S (S O))))), ((Func ((S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O))))))))))))))), (bs::[])))::[])))::[]))))
                else false
             then Some ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S O))))))))))))))))), (bs::(offset::((Func ((S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O))))))))))))))))))), (v::[])))::[])))))::(p'::[]))
             else None
           | None -> None)
        | e::l1 -> None))

(** val memEval1 : type0 list -> MEVAL.PredEval.coq_MemEvalPred **)

let memEval1 types' =
  { MEVAL.PredEval.pred_read_word = (fun p facts0 args p0 -> None);
    MEVAL.PredEval.pred_write_word = (fun p facts0 args p0 v -> None);
    MEVAL.PredEval.pred_read_byte = (sym_read1 types');
    MEVAL.PredEval.pred_write_byte = (sym_write1 types') }

(** val memEvaluator1 : type0 list -> MEVAL.coq_MemEvaluator **)

let memEvaluator1 types' =
  { MEVAL.sread_word = (fun p f0 p0 h ->
    match FM.find (S (S (S O))) h.SH.impures with
    | Some argss ->
      MEVAL.PredEval.fold_args (types1 types') (fun args ->
        (memEval1 types').MEVAL.PredEval.pred_read_word p f0 args p0) argss
    | None -> None); MEVAL.swrite_word = (fun p f0 p0 v h ->
    match FM.find (S (S (S O))) h.SH.impures with
    | Some argss ->
      (match MEVAL.PredEval.fold_args_update (types1 types') (fun args ->
               (memEval1 types').MEVAL.PredEval.pred_write_word p f0 args p0
                 v) argss with
       | Some argss0 ->
         Some { SH.impures = (FM.add (S (S (S O))) argss0 h.SH.impures);
           SH.pures = h.SH.pures; SH.other = h.SH.other }
       | None -> None)
    | None -> None); MEVAL.sread_byte = (fun p f0 p0 h ->
    match FM.find (S (S (S O))) h.SH.impures with
    | Some argss ->
      MEVAL.PredEval.fold_args (types1 types') (fun args ->
        (memEval1 types').MEVAL.PredEval.pred_read_byte p f0 args p0) argss
    | None -> None); MEVAL.swrite_byte = (fun p f0 p0 v h ->
    match FM.find (S (S (S O))) h.SH.impures with
    | Some argss ->
      (match MEVAL.PredEval.fold_args_update (types1 types') (fun args ->
               (memEval1 types').MEVAL.PredEval.pred_write_byte p f0 args p0
                 v) argss with
       | Some argss0 ->
         Some { SH.impures = (FM.add (S (S (S O))) argss0 h.SH.impures);
           SH.pures = h.SH.pures; SH.other = h.SH.other }
       | None -> None)
    | None -> None) }

type assumption_summary = expr list

(** val assumptionSummarize :
    type0 list -> expr list -> assumption_summary **)

let assumptionSummarize types4 hyps =
  hyps

(** val assumptionProve :
    type0 list -> assumption_summary -> expr -> bool **)

let rec assumptionProve types4 hyps goal =
  match hyps with
  | [] -> false
  | exp::b0 ->
    if expr_seq_dec types4 exp goal
    then true
    else assumptionProve types4 b0 goal

(** val assumptionLearn :
    type0 list -> assumption_summary -> expr list -> assumption_summary **)

let assumptionLearn types4 sum hyps =
  app sum hyps

(** val types2 : type0 list -> type0 list **)

let types2 types' =
  repr0 bedrock_types_r types'

type equality = { source : expr; destination : expr; difference : w }

(** val source : type0 list -> equality -> expr **)

let source _ x = x.source

(** val destination : type0 list -> equality -> expr **)

let destination _ x = x.destination

(** val difference : type0 list -> equality -> w **)

let difference _ x = x.difference

type word_summary = { equalities : equality list;
                      lessThans : (expr, expr) prod list;
                      notEquals : (expr, expr) prod list }

(** val equalities : type0 list -> word_summary -> equality list **)

let equalities _ x = x.equalities

(** val lessThans : type0 list -> word_summary -> (expr, expr) prod list **)

let lessThans _ x = x.lessThans

(** val notEquals : type0 list -> word_summary -> (expr, expr) prod list **)

let notEquals _ x = x.notEquals

(** val natToWord' : nat -> nat -> word **)

let rec natToWord' sz n0 =
  match sz with
  | O -> WO
  | S sz' -> WS ((mod2 n0), sz', (natToWord' sz' (div0 n0)))

(** val zero1 : word **)

let zero1 =
  WS (false, (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))), (WS
    (false, (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))), (WS (false, (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S O))))))))))))))))))))))))))))), (WS (false, (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))), (WS (false, (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))), (WS (false, (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))), (WS (false, (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))), (WS
    (false, (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S O)))))))))))))))))))))))), (WS (false, (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))), (WS
    (false, (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))), (WS (false, (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O))))))))))))))))))))), (WS (false, (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))),
    (WS (false, (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))), (WS (false, (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S O)))))))))))))))))), (WS (false, (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O))))))))))))))))), (WS (false, (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))), (WS (false, (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))), (WS (false, (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))), (WS (false, (S (S (S
    (S (S (S (S (S (S (S (S (S (S O))))))))))))), (WS (false, (S (S (S (S (S
    (S (S (S (S (S (S (S O)))))))))))), (WS (false, (S (S (S (S (S (S (S (S
    (S (S (S O))))))))))), (WS (false, (S (S (S (S (S (S (S (S (S (S
    O)))))))))), (WS (false, (S (S (S (S (S (S (S (S (S O))))))))), (WS
    (false, (S (S (S (S (S (S (S (S O)))))))), (WS (false, (S (S (S (S (S (S
    (S O))))))), (WS (false, (S (S (S (S (S (S O)))))), (WS (false, (S (S (S
    (S (S O))))), (WS (false, (S (S (S (S O)))), (WS (false, (S (S (S O))),
    (WS (false, (S (S O)), (WS (false, (S O), (WS (false, O,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val pow32 : n **)

let pow32 =
  Npos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    XH))))))))))))))))))))))))))))))))

(** val wplus' : word -> word -> word **)

let wplus' =
  wordBin N.add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))

(** val wneg' : w -> word **)

let wneg' w0 =
  nToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
    (N.sub pow32
      (wordToN (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
        w0))

(** val wminus' : w -> w -> w **)

let wminus' x y =
  wplus' x (wneg' y)

(** val decompose : type0 list -> expr -> (expr, w) prod **)

let rec decompose types' e = match e with
| Func (f0, l) ->
  (match f0 with
   | O ->
     (match l with
      | [] -> Pair (e, zero1)
      | e1::l0 ->
        (match l0 with
         | [] -> Pair (e, zero1)
         | e0::l1 ->
           (match e0 with
            | Func (f1, l2) ->
              (match f1 with
               | O -> Pair (e, zero1)
               | S n0 ->
                 (match n0 with
                  | O -> Pair (e, zero1)
                  | S n1 ->
                    (match n1 with
                     | O -> Pair (e, zero1)
                     | S n2 ->
                       (match n2 with
                        | O -> Pair (e, zero1)
                        | S n3 ->
                          (match n3 with
                           | O -> Pair (e, zero1)
                           | S n4 ->
                             (match n4 with
                              | O ->
                                (match l2 with
                                 | [] -> Pair (e, zero1)
                                 | e2::l3 ->
                                   (match e2 with
                                    | Const (t0, k) ->
                                      (match t0 with
                                       | TvProp ->
                                         Obj.magic (fun _ -> Pair (e, zero1))
                                           k
                                       | TvType n5 ->
                                         (match n5 with
                                          | O -> Pair (e, zero1)
                                          | S n6 ->
                                            (match n6 with
                                             | O -> Pair (e, zero1)
                                             | S n7 ->
                                               (match n7 with
                                                | O -> Pair (e, zero1)
                                                | S n8 ->
                                                  (match n8 with
                                                   | O -> Pair (e, zero1)
                                                   | S n9 ->
                                                     (match n9 with
                                                      | O ->
                                                        (match l3 with
                                                         | [] ->
                                                           (match l1 with
                                                            | [] ->
                                                              let Pair (
                                                                e1', d) =
                                                                decompose
                                                                  types' e1
                                                              in
                                                              Pair (e1',
                                                              (wplus' d
                                                                (natToWord'
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  O))))))))))))))))))))))))))))))))
                                                                  (Obj.magic
                                                                    k))))
                                                            | e3::l4 ->
                                                              Pair (e, zero1))
                                                         | e3::l4 ->
                                                           Pair (e, zero1))
                                                      | S n10 ->
                                                        Pair (e, zero1)))))))
                                    | _ -> Pair (e, zero1)))
                              | S n5 -> Pair (e, zero1)))))))
            | _ -> Pair (e, zero1))))
   | S n0 ->
     (match n0 with
      | O ->
        (match l with
         | [] -> Pair (e, zero1)
         | e1::l0 ->
           (match l0 with
            | [] -> Pair (e, zero1)
            | e0::l1 ->
              (match e0 with
               | Func (f1, l2) ->
                 (match f1 with
                  | O -> Pair (e, zero1)
                  | S n1 ->
                    (match n1 with
                     | O -> Pair (e, zero1)
                     | S n2 ->
                       (match n2 with
                        | O -> Pair (e, zero1)
                        | S n3 ->
                          (match n3 with
                           | O -> Pair (e, zero1)
                           | S n4 ->
                             (match n4 with
                              | O -> Pair (e, zero1)
                              | S n5 ->
                                (match n5 with
                                 | O ->
                                   (match l2 with
                                    | [] -> Pair (e, zero1)
                                    | e2::l3 ->
                                      (match e2 with
                                       | Const (t0, k) ->
                                         (match t0 with
                                          | TvProp ->
                                            Obj.magic (fun _ -> Pair (e,
                                              zero1)) k
                                          | TvType n6 ->
                                            (match n6 with
                                             | O -> Pair (e, zero1)
                                             | S n7 ->
                                               (match n7 with
                                                | O -> Pair (e, zero1)
                                                | S n8 ->
                                                  (match n8 with
                                                   | O -> Pair (e, zero1)
                                                   | S n9 ->
                                                     (match n9 with
                                                      | O -> Pair (e, zero1)
                                                      | S n10 ->
                                                        (match n10 with
                                                         | O ->
                                                           (match l3 with
                                                            | [] ->
                                                              (match l1 with
                                                               | [] ->
                                                                 let Pair (
                                                                   e1', d) =
                                                                   decompose
                                                                    types' e1
                                                                 in
                                                                 Pair (e1',
                                                                 (wminus' d
                                                                   (natToWord'
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S (S
                                                                    (S (S
                                                                    O))))))))))))))))))))))))))))))))
                                                                    (Obj.magic
                                                                    k))))
                                                               | e3::l4 ->
                                                                 Pair (e,
                                                                   zero1))
                                                            | e3::l4 ->
                                                              Pair (e, zero1))
                                                         | S n11 ->
                                                           Pair (e, zero1)))))))
                                       | _ -> Pair (e, zero1)))
                                 | S n6 -> Pair (e, zero1)))))))
               | _ -> Pair (e, zero1))))
      | S n1 -> Pair (e, zero1)))
| _ -> Pair (e, zero1)

(** val combine0 : type0 list -> equality -> equality -> equality list **)

let combine0 types' f1 f2 =
  if expr_seq_dec (types2 types') f1.destination f2.source
  then { source = f1.source; destination = f2.destination; difference =
         (wplus' f1.difference f2.difference) }::[]
  else []

(** val combineAll :
    type0 list -> equality -> equality list -> equality list **)

let rec combineAll types' f0 fs0 = match fs0 with
| [] -> fs0
| f'::fs1 ->
  app (combine0 types' f0 f')
    (app (combine0 types' f' f0) (combineAll types' f0 fs1))

(** val alreadyCovered' : type0 list -> equality -> equality list -> bool **)

let rec alreadyCovered' types' f0 = function
| [] -> false
| f'::fs' ->
  if if expr_seq_dec (types2 types') f0.source f'.source
     then expr_seq_dec (types2 types') f0.destination f'.destination
     else false
  then true
  else alreadyCovered' types' f0 fs'

(** val alreadyCovered : type0 list -> equality -> equality list -> bool **)

let alreadyCovered types' f0 fs0 =
  if expr_seq_dec (types2 types') f0.source f0.destination
  then true
  else alreadyCovered' types' f0 fs0

(** val merge1 :
    type0 list -> equality list -> equality list -> equality list **)

let rec merge1 types' fs1 fs2 =
  match fs1 with
  | [] -> fs2
  | f0::fs1' ->
    merge1 types' fs1'
      (if alreadyCovered types' f0 fs2 then fs2 else f0::fs2)

(** val wordLearn1 : type0 list -> word_summary -> expr -> word_summary **)

let wordLearn1 types' sum = function
| Func (f0, l) ->
  (match f0 with
   | O -> sum
   | S n0 ->
     (match n0 with
      | O -> sum
      | S n1 ->
        (match n1 with
         | O -> sum
         | S n2 ->
           (match n2 with
            | O -> sum
            | S n3 ->
              (match n3 with
               | O ->
                 (match l with
                  | [] -> sum
                  | e1::l0 ->
                    (match l0 with
                     | [] -> sum
                     | e2::l1 ->
                       (match l1 with
                        | [] ->
                          { equalities = sum.equalities; lessThans = ((Pair
                            (e1, e2))::sum.lessThans); notEquals =
                            sum.notEquals }
                        | e0::l2 -> sum)))
               | S n4 -> sum)))))
| Equal (t0, e1, e2) ->
  (match t0 with
   | TvProp -> sum
   | TvType n0 ->
     (match n0 with
      | O ->
        let Pair (b1, n1) = decompose types' e1 in
        let Pair (b2, n2) = decompose types' e2 in
        let f1 = { source = b1; destination = b2; difference =
          (wminus' n1 n2) }
        in
        let f2 = { source = b2; destination = b1; difference =
          (wminus' n2 n1) }
        in
        let equalities0 =
          merge1 types' (f1::(combineAll types' f1 sum.equalities))
            sum.equalities
        in
        let equalities1 =
          merge1 types' (f2::(combineAll types' f2 equalities0)) equalities0
        in
        { equalities = equalities1; lessThans = sum.lessThans; notEquals =
        sum.notEquals }
      | S n1 -> sum))
| Not e0 ->
  (match e0 with
   | Equal (t0, e1, e2) ->
     (match t0 with
      | TvProp -> sum
      | TvType n0 ->
        (match n0 with
         | O ->
           { equalities = sum.equalities; lessThans = sum.lessThans;
             notEquals = ((Pair (e1, e2))::sum.notEquals) }
         | S n1 -> sum))
   | _ -> sum)
| _ -> sum

(** val wordLearn :
    type0 list -> word_summary -> expr list -> word_summary **)

let rec wordLearn types' sum = function
| [] -> sum
| h::hyps' -> wordLearn types' (wordLearn1 types' sum h) hyps'

(** val equalitysEq : type0 list -> equality -> equality -> bool **)

let equalitysEq types' f1 f2 =
  if if expr_seq_dec (types2 types') f1.source f2.source
     then expr_seq_dec (types2 types') f1.destination f2.destination
     else false
  then w_seq f1.difference f2.difference
  else false

(** val equalityMatches : type0 list -> equality -> equality list -> bool **)

let rec equalityMatches types' f0 = function
| [] -> false
| f'::fs' ->
  if equalitysEq types' f0 f' then true else equalityMatches types' f0 fs'

(** val lessThanMatches :
    type0 list -> expr -> expr -> (expr, expr) prod list -> equality list ->
    bool **)

let rec lessThanMatches types' e1 e2 lts eqs =
  match lts with
  | [] -> false
  | p::lts' ->
    let Pair (e1', e2') = p in
    if if if expr_seq_dec (types2 types') e1 e1'
          then true
          else equalityMatches types' { source = e1; destination = e1';
                 difference = zero1 } eqs
       then if expr_seq_dec (types2 types') e2 e2'
            then true
            else equalityMatches types' { source = e2; destination = e2';
                   difference = zero1 } eqs
       else false
    then true
    else lessThanMatches types' e1 e2 lts' eqs

(** val wordProve : type0 list -> word_summary -> expr -> bool **)

let wordProve types' sum = function
| Func (f0, l) ->
  (match f0 with
   | O -> false
   | S n0 ->
     (match n0 with
      | O -> false
      | S n1 ->
        (match n1 with
         | O -> false
         | S n2 ->
           (match n2 with
            | O -> false
            | S n3 ->
              (match n3 with
               | O ->
                 (match l with
                  | [] -> false
                  | e1::l0 ->
                    (match l0 with
                     | [] -> false
                     | e2::l1 ->
                       (match l1 with
                        | [] ->
                          lessThanMatches types' e1 e2 sum.lessThans
                            sum.equalities
                        | e0::l2 -> false)))
               | S n4 -> false)))))
| Equal (t0, e1, e2) ->
  (match t0 with
   | TvProp -> false
   | TvType n0 ->
     (match n0 with
      | O ->
        let Pair (b1, n1) = decompose types' e1 in
        let Pair (b2, n2) = decompose types' e2 in
        if expr_seq_dec (types2 types') b1 b2
        then w_seq n1 n2
        else equalityMatches types' { source = b1; destination = b2;
               difference = (wminus' n1 n2) } sum.equalities
      | S n1 -> false))
| Not e0 ->
  (match e0 with
   | Equal (t0, e1, e2) ->
     (match t0 with
      | TvProp -> false
      | TvType n0 ->
        (match n0 with
         | O -> lessThanMatches types' e1 e2 sum.notEquals sum.equalities
         | S n1 -> false))
   | _ -> false)
| _ -> false

(** val wordSummarize : type0 list -> expr list -> word_summary **)

let wordSummarize types' =
  wordLearn types' { equalities = []; lessThans = []; notEquals = [] }

(** val types3 : type0 list -> type0 list **)

let types3 types' =
  types types'

(** val deupd : type0 list -> expr -> expr **)

let rec deupd types' e = match e with
| Func (f0, l) ->
  (match f0 with
   | O -> e
   | S n0 ->
     (match n0 with
      | O -> e
      | S n1 ->
        (match n1 with
         | O -> e
         | S n2 ->
           (match n2 with
            | O -> e
            | S n3 ->
              (match n3 with
               | O -> e
               | S n4 ->
                 (match n4 with
                  | O -> e
                  | S n5 ->
                    (match n5 with
                     | O -> e
                     | S n6 ->
                       (match n6 with
                        | O -> e
                        | S n7 ->
                          (match n7 with
                           | O ->
                             (match l with
                              | [] -> e
                              | e'::l0 ->
                                (match l0 with
                                 | [] -> e
                                 | e0::l1 ->
                                   (match l1 with
                                    | [] -> e
                                    | e1::l2 ->
                                      (match l2 with
                                       | [] -> deupd types' e'
                                       | e2::l3 -> e))))
                           | S n8 -> e)))))))))
| _ -> e

(** val factIn : type0 list -> expr -> (expr, expr) prod option **)

let factIn types' = function
| Func (f0, l) ->
  (match f0 with
   | O -> None
   | S n0 ->
     (match n0 with
      | O -> None
      | S n1 ->
        (match n1 with
         | O -> None
         | S n2 ->
           (match n2 with
            | O -> None
            | S n3 ->
              (match n3 with
               | O ->
                 (match l with
                  | [] -> None
                  | i::l0 ->
                    (match l0 with
                     | [] -> None
                     | e0::l1 ->
                       (match e0 with
                        | Func (f1, l2) ->
                          (match f1 with
                           | O -> None
                           | S n4 ->
                             (match n4 with
                              | O -> None
                              | S n5 ->
                                (match n5 with
                                 | O -> None
                                 | S n6 ->
                                   (match n6 with
                                    | O -> None
                                    | S n7 ->
                                      (match n7 with
                                       | O -> None
                                       | S n8 ->
                                         (match n8 with
                                          | O ->
                                            (match l2 with
                                             | [] -> None
                                             | e1::l3 ->
                                               (match e1 with
                                                | Func (f2, l4) ->
                                                  (match f2 with
                                                   | O -> None
                                                   | S n9 ->
                                                     (match n9 with
                                                      | O -> None
                                                      | S n10 ->
                                                        (match n10 with
                                                         | O -> None
                                                         | S n11 ->
                                                           (match n11 with
                                                            | O -> None
                                                            | S n12 ->
                                                              (match n12 with
                                                               | O -> None
                                                               | S n13 ->
                                                                 (match n13 with
                                                                  | O -> None
                                                                  | S n14 ->
                                                                    (match n14 with
                                                                    | O ->
                                                                    (match l4 with
                                                                    | [] ->
                                                                    None
                                                                    | a::l5 ->
                                                                    (match l5 with
                                                                    | [] ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    Some
                                                                    (Pair (i,
                                                                    (deupd
                                                                    types' a)))
                                                                    | e2::l6 ->
                                                                    None)
                                                                    | e2::l6 ->
                                                                    None)
                                                                    | e2::l6 ->
                                                                    None))
                                                                    | S n15 ->
                                                                    None)))))))
                                                | _ -> None))
                                          | S n9 -> None))))))
                        | _ -> None)))
               | S n4 -> None)))))
| _ -> None

type boundSummary = (expr, expr) prod list

(** val boundLearn1 : type0 list -> boundSummary -> expr -> boundSummary **)

let boundLearn1 types' summ e =
  match factIn types' e with
  | Some fact -> fact::summ
  | None -> summ

(** val boundLearn :
    type0 list -> boundSummary -> expr list -> boundSummary **)

let rec boundLearn types' summ = function
| [] -> summ
| e::es0 -> boundLearn1 types' (boundLearn types' summ es0) e

(** val boundSummarize : type0 list -> expr list -> boundSummary **)

let boundSummarize types' =
  boundLearn types' []

(** val hypMatches :
    type0 list -> (expr, expr) prod -> boundSummary -> bool **)

let rec hypMatches types' fact = function
| [] -> false
| p::summ' ->
  let Pair (i, a) = p in
  if if expr_seq_dec (types3 types') i (fst fact)
     then expr_seq_dec (types3 types') a (snd fact)
     else false
  then true
  else hypMatches types' fact summ'

(** val boundProve : type0 list -> boundSummary -> expr -> bool **)

let boundProve types' summ goal =
  match factIn types' goal with
  | Some fact -> hypMatches types' fact summ
  | None -> false

module Plugin_PtsTo = BedrockPtsToEvaluator

type tacPackage = ILAlgoTypes.coq_TypedPackage

(** val note_ : assert0 LabelMap.t -> char list -> cmd **)

let note_ imps mn pre =
  { postcondition = (fun st0 -> And ([], (pre st0), (Inj []))); verifCond =
    (__::[]); generate = (fun base exit -> { entry = N0; blocks0 = ((Pair
    (pre, (Pair ([], (Uncond (RvLabel (Pair (mn, (Local
    exit)))))))))::[]) }) }

(** val note__ : chunk **)

let note__ x x0 =
  Structured ([], (fun im mn _ -> note_ im mn))

(** val assertStar_ :
    assert0 LabelMap.t -> char list -> (char list, char list) prod list ->
    assert0 -> cmd **)

let assertStar_ imps mn ls post2 pre =
  { postcondition = post2; verifCond = (__::[]); generate = (fun base exit ->
    { entry = N0; blocks0 = ((Pair (pre, (Pair ([], (Uncond (RvLabel (Pair
    (mn, (Local exit)))))))))::[]) }) }

(** val localsInvariantCont :
    (vals -> w -> qspec) -> bool -> (w -> w) -> char list list -> nat ->
    assert0 **)

let localsInvariantCont pre rpStashed adjustSp ns res st0 =
  let sp = adjustSp ((snd st0).regs Sp) in
  ExistsX ([], (Exists ((__::[]), (fun vs ->
  qspecOut (pre (sel0 (Obj.magic vs)) ((snd st0).regs Rv)) (__::[])
    (fun pre0 ->
    SepFormula.sepFormula (__::[])
      (starB (__::[])
        (lift (__::[])
          (starB [] (locals (('r'::('p'::[]))::ns) (Obj.magic vs) res sp)
            pre0)) (hvarB (__::[]) (fun x -> Var0 ([], (Obj.magic x))))) st0)))))

(** val locals_return :
    char list list -> vals -> nat -> w -> char list list -> nat -> nat ->
    hProp **)

let locals_return ns vs avail p ns' avail' offset =
  locals ns vs avail p

(** val locals_call :
    char list list -> vals -> nat -> w -> char list list -> nat -> nat ->
    hProp **)

let locals_call ns vs avail p ns' avail' offset =
  locals ns vs avail p

(** val excessStack :
    w -> char list list -> nat -> char list list -> nat -> hProp **)

let excessStack p ns avail ns' avail' =
  reserved
    (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) p
      (natToW
        (mult (S (S (S (S O))))
          (plus (plus (length ns) (length ns')) avail'))))
    (minus (minus avail (length ns')) avail')

(** val locals_in :
    char list list -> vals -> nat -> w -> char list list -> char list list ->
    nat -> hProp **)

let locals_in ns vs avail p ns' ns'' avail' =
  locals ns vs avail p

(** val locals_out :
    char list list -> vals -> nat -> w -> char list list -> char list list ->
    nat -> hProp **)

let locals_out ns vs avail p ns' ns'' avail' =
  locals ns vs avail p

(** val abortS : spec0 **)

let abortS =
  let n' = O in
  { reserved0 = n'; formals = []; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    localsInvariantCont (fun x x0 -> Body (empB [])) true (fun w0 -> w0)
      extras0 (minus n' (length extras0))
  | None ->
    localsInvariantCont (fun x x0 -> Body (empB [])) false (fun w0 -> w0) []
      n') }

module Coq10_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
 end

module type FREE_LIST = 
 sig 
  val freeList : nat -> w -> hProp
  
  val mallocHeap : w -> hProp
 end

module FreeList = 
 struct 
  (** val freeList : nat -> w -> hProp **)
  
  let rec freeList n0 p =
    match n0 with
    | O -> injB []
    | S n' ->
      starB [] (injB [])
        (exB [] (fun sz ->
          exB [] (fun p' ->
            starB []
              (starB [] (starB [] (injB []) (ptsto32m [] p O (sz::(p'::[]))))
                (allocated
                  (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) p
                    (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S
                      (S O)))))))))) O
                  (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) sz))) (freeList n' p'))))
  
  (** val mallocHeap : w -> hProp **)
  
  let mallocHeap p =
    exB [] (fun n0 ->
      exB [] (fun p' -> starB [] (ptsto32 [] p p') (freeList n0 p')))
 end

(** val initS : spec0 **)

let initS =
  let vars0 =
    ('b'::('a'::('s'::('e'::[]))))::(('s'::('i'::('z'::('e'::[]))))::[])
  in
  let n' = O in
  { reserved0 = n'; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    localsInvariant (fun v x -> Body
      (starB [] (starB [] (injB []) (injB []))
        (allocated (v ('b'::('a'::('s'::('e'::[]))))) O
          (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
            (v ('s'::('i'::('z'::('e'::[]))))))))) (fun v x x0 -> Body
      (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))) true
      (fun w0 -> w0) extras0
      (minus n' (minus (length extras0) (length vars0)))
  | None ->
    localsInvariant (fun v x -> Body
      (starB [] (starB [] (injB []) (injB []))
        (allocated (v ('b'::('a'::('s'::('e'::[]))))) O
          (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
            (v ('s'::('i'::('z'::('e'::[]))))))))) (fun v x x0 -> Body
      (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))) false
      (fun w0 -> w0) vars0 n') }

(** val freeS : spec0 **)

let freeS =
  let vars0 = ('b'::('a'::('s'::('e'::[]))))::(('p'::[])::(('n'::[])::[])) in
  let n' = S (S O) in
  { reserved0 = n'; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    localsInvariant (fun v x -> Body
      (starB []
        (starB [] (starB [] (injB []) (injB []))
          (allocated (v ('p'::[])) O
            (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) (v ('n'::[])))))
        (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))))
      (fun v x x0 -> Body
      (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))) true
      (fun w0 -> w0) extras0
      (minus n' (minus (length extras0) (length vars0)))
  | None ->
    localsInvariant (fun v x -> Body
      (starB []
        (starB [] (starB [] (injB []) (injB []))
          (allocated (v ('p'::[])) O
            (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) (v ('n'::[])))))
        (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))))
      (fun v x x0 -> Body
      (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))) false
      (fun w0 -> w0) vars0 n') }

(** val mallocS : spec0 **)

let mallocS =
  let vars0 = ('b'::('a'::('s'::('e'::[]))))::(('n'::[])::[]) in
  let n' = S (S (S (S O))) in
  { reserved0 = n'; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    localsInvariant (fun v x -> Body
      (starB [] (injB [])
        (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))))
      (fun v x r -> Body
      (starB []
        (starB [] (starB [] (injB []) (injB []))
          (allocated r O
            (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) (v ('n'::[])))))
        (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[])))))))) true
      (fun w0 -> w0) extras0
      (minus n' (minus (length extras0) (length vars0)))
  | None ->
    localsInvariant (fun v x -> Body
      (starB [] (injB [])
        (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[]))))))))
      (fun v x r -> Body
      (starB []
        (starB [] (starB [] (injB []) (injB []))
          (allocated r O
            (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) (v ('n'::[])))))
        (FreeList.mallocHeap (v ('b'::('a'::('s'::('e'::[])))))))) false
      (fun w0 -> w0) vars0 n') }

(** val m : module0 **)

let m =
  bmodule_0 [] ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
    ((let vars0 =
        ('b'::('a'::('s'::('e'::[]))))::(('s'::('i'::('z'::('e'::[]))))::[])
      in
      let b' =
        seq
          (seq
            (assign' (regInL Rv) (Rvalue
              (lvalIn (variableSlot ('b'::('a'::('s'::('e'::[]))))))))
            (assign' (fun x -> LvMem (Reg Rv)) (Bop
              ((lvalIn (variableSlot ('b'::('a'::('s'::('e'::[])))))), Plus,
              (immInR (natToW (S (S (S (S O))))))))))
          (seq
            (seq
              (assign' (regInL Rv) (Bop
                ((lvalIn (variableSlot ('b'::('a'::('s'::('e'::[])))))),
                Plus, (immInR (natToW (S (S (S (S O)))))))))
              (assign' (fun x -> LvMem (Reg Rv)) (Bop
                ((lvalIn (variableSlot ('s'::('i'::('z'::('e'::[])))))),
                Minus, (immInR (natToW (S (S (S O)))))))))
            (seq
              (seq
                (assign' (regInL Rv) (Bop
                  ((lvalIn (variableSlot ('b'::('a'::('s'::('e'::[])))))),
                  Plus,
                  (immInR (natToW (S (S (S (S (S (S (S (S O)))))))))))))
                (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                  (immInR (natToW O)))))
              (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
                (seq
                  (assign' (regInL Rp) (Rvalue
                    (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                  (goto (lvalIn (regInL Rp)))))))
      in
      { fName = ('i'::('n'::('i'::('t'::[])))); fVars = vars0; fReserved =
      initS.reserved0; fPrecondition = (initS.precondition None); fBody =
      (seq
        (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
          (lvalIn (regInL Rp))))
        (seq (fun x x0 -> Structured ([], (fun im mn _ ->
          assert_ im mn (initS.precondition (Some vars0))))) (fun ns res ->
          b' ns (minus res (minus (length vars0) (length initS.formals)))))) })::(
    (let vars0 =
       ('b'::('a'::('s'::('e'::[]))))::(('p'::[])::(('n'::[])::(('c'::('u'::('r'::[])))::(('t'::('m'::('p'::[])))::[]))))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('b'::('a'::('s'::('e'::[]))))))))
           (assign' (variableSlot ('c'::('u'::('r'::[])))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (while_0
             (let a = true in
              let b0 = fun w0 -> w0 in
              (fun c d e -> Exists ([], (fun len ->
              localsInvariant (fun v x -> Body
                (starB []
                  (starB []
                    (starB [] (starB [] (injB []) (injB []))
                      (allocated (v ('p'::[])) O
                        (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S O)))))))))))))))))))))))))))))))) (v ('n'::[])))))
                    (ptsto32 [] (v ('b'::('a'::('s'::('e'::[])))))
                      (v ('c'::('u'::('r'::[]))))))
                  (FreeList.freeList (Obj.magic len)
                    (v ('c'::('u'::('r'::[]))))))) (fun v x r -> Quant
                (fun p -> Quant (fun len' -> Body
                (starB []
                  (ptsto32 [] (v ('b'::('a'::('s'::('e'::[])))))
                    (Obj.magic p))
                  (FreeList.freeList (Obj.magic len') (Obj.magic p)))))) a b0
                c d e)))) { cOperand1 =
             (lvalIn (variableSlot ('c'::('u'::('r'::[]))))); cTest = Ne;
             cOperand2 = (immInR (natToW O)) }
             (seq
               (assign' (variableSlot ('t'::('m'::('p'::[])))) (Bop
                 ((immInR (natToW (S (S (S (S O)))))), Times,
                 (lvalIn (variableSlot ('n'::[]))))))
               (seq
                 (assign' (variableSlot ('t'::('m'::('p'::[])))) (Bop
                   ((lvalIn (variableSlot ('p'::[]))), Plus,
                   (lvalIn (variableSlot ('t'::('m'::('p'::[]))))))))
                 (if_0 { cOperand1 =
                   (lvalIn (variableSlot ('t'::('m'::('p'::[]))))); cTest =
                   Eq0; cOperand2 =
                   (lvalIn (variableSlot ('c'::('u'::('r'::[]))))) }
                   (seq note__
                     (seq
                       (seq
                         (assign' (regInL Rv) (Rvalue
                           (lvalIn (variableSlot ('c'::('u'::('r'::[])))))))
                         (assign' (variableSlot ('t'::('m'::('p'::[]))))
                           (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                       (seq
                         (assign' (variableSlot ('t'::('m'::('p'::[])))) (Bop
                           ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))),
                           Plus, (lvalIn (variableSlot ('n'::[]))))))
                         (seq
                           (seq
                             (assign' (regInL Rv) (Rvalue
                               (lvalIn (variableSlot ('p'::[])))))
                             (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                               (lvalIn
                                 (variableSlot ('t'::('m'::('p'::[]))))))))
                           (seq
                             (seq
                               (assign' (regInL Rv) (Bop
                                 ((lvalIn
                                    (variableSlot ('c'::('u'::('r'::[]))))),
                                 Plus, (immInR (natToW (S (S (S (S O)))))))))
                               (assign'
                                 (variableSlot ('t'::('m'::('p'::[]))))
                                 (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                             (seq
                               (seq
                                 (assign' (regInL Rv) (Bop
                                   ((lvalIn (variableSlot ('p'::[]))), Plus,
                                   (immInR (natToW (S (S (S (S O)))))))))
                                 (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                                   (lvalIn
                                     (variableSlot ('t'::('m'::('p'::[]))))))))
                               (seq
                                 (seq
                                   (assign' (regInL Rv) (Rvalue
                                     (lvalIn
                                       (variableSlot
                                         ('b'::('a'::('s'::('e'::[]))))))))
                                   (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                                     (lvalIn (variableSlot ('p'::[]))))))
                                 (seq
                                   (assign' (regInL Rv) (Rvalue
                                     (immInR (natToW O))))
                                   (seq
                                     (assign' (regInL Rp) (Rvalue
                                       (lvalIn (fun x -> LvMem (Indir (Sp,
                                         (natToW O)))))))
                                     (goto (lvalIn (regInL Rp))))))))))))
                   (seq
                     (seq
                       (assign' (regInL Rv) (Rvalue
                         (lvalIn (variableSlot ('c'::('u'::('r'::[])))))))
                       (assign' (variableSlot ('t'::('m'::('p'::[]))))
                         (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                     (seq
                       (assign' (variableSlot ('t'::('m'::('p'::[])))) (Bop
                         ((immInR (natToW (S (S (S (S O)))))), Times,
                         (lvalIn (variableSlot ('t'::('m'::('p'::[]))))))))
                       (seq
                         (assign' (variableSlot ('t'::('m'::('p'::[])))) (Bop
                           ((lvalIn (variableSlot ('c'::('u'::('r'::[]))))),
                           Plus,
                           (lvalIn (variableSlot ('t'::('m'::('p'::[]))))))))
                         (seq
                           (assign' (variableSlot ('t'::('m'::('p'::[]))))
                             (Bop
                             ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))),
                             Plus,
                             (immInR
                               (natToW (S (S (S (S (S (S (S (S O)))))))))))))
                           (if_0 { cOperand1 =
                             (lvalIn (variableSlot ('t'::('m'::('p'::[])))));
                             cTest = Eq0; cOperand2 =
                             (lvalIn (variableSlot ('p'::[]))) }
                             (seq
                               (seq
                                 (assign' (regInL Rv) (Bop
                                   ((lvalIn
                                      (variableSlot ('c'::('u'::('r'::[]))))),
                                   Plus,
                                   (immInR (natToW (S (S (S (S O)))))))))
                                 (assign'
                                   (variableSlot ('t'::('m'::('p'::[]))))
                                   (Rvalue
                                   (lvalIn (fun x -> LvMem (Reg Rv))))))
                               (if_0 { cOperand1 =
                                 (lvalIn
                                   (variableSlot ('t'::('m'::('p'::[])))));
                                 cTest = Eq0; cOperand2 =
                                 (immInR (natToW O)) }
                                 (seq
                                   (seq
                                     (assign' (regInL Rv) (Rvalue
                                       (lvalIn
                                         (variableSlot
                                           ('c'::('u'::('r'::[])))))))
                                     (assign'
                                       (variableSlot
                                         ('b'::('a'::('s'::('e'::[])))))
                                       (Rvalue
                                       (lvalIn (fun x -> LvMem (Reg Rv))))))
                                   (seq
                                     (assign'
                                       (variableSlot
                                         ('b'::('a'::('s'::('e'::[]))))) (Bop
                                       ((lvalIn
                                          (variableSlot
                                            ('b'::('a'::('s'::('e'::[])))))),
                                       Plus,
                                       (lvalIn (variableSlot ('n'::[]))))))
                                     (seq
                                       (seq
                                         (assign' (regInL Rv) (Rvalue
                                           (lvalIn
                                             (variableSlot
                                               ('c'::('u'::('r'::[])))))))
                                         (assign' (fun x -> LvMem (Reg Rv))
                                           (Rvalue
                                           (lvalIn
                                             (variableSlot
                                               ('b'::('a'::('s'::('e'::[])))))))))
                                       (seq
                                         (assign' (regInL Rv) (Rvalue
                                           (immInR (natToW O))))
                                         (seq
                                           (assign' (regInL Rp) (Rvalue
                                             (lvalIn (fun x -> LvMem (Indir
                                               (Sp, (natToW O)))))))
                                           (goto (lvalIn (regInL Rp))))))))
                                 (seq
                                   (assign'
                                     (variableSlot
                                       ('b'::('a'::('s'::('e'::[]))))) (Bop
                                     ((immInR (natToW (S (S (S (S O)))))),
                                     Times,
                                     (lvalIn (variableSlot ('n'::[]))))))
                                   (seq
                                     (assign'
                                       (variableSlot
                                         ('b'::('a'::('s'::('e'::[]))))) (Bop
                                       ((lvalIn (variableSlot ('p'::[]))),
                                       Plus,
                                       (lvalIn
                                         (variableSlot
                                           ('b'::('a'::('s'::('e'::[])))))))))
                                     (if_0 { cOperand1 =
                                       (lvalIn
                                         (variableSlot
                                           ('t'::('m'::('p'::[]))))); cTest =
                                       Eq0; cOperand2 =
                                       (lvalIn
                                         (variableSlot
                                           ('b'::('a'::('s'::('e'::[])))))) }
                                       (seq
                                         (seq
                                           (assign' (regInL Rv) (Rvalue
                                             (lvalIn
                                               (variableSlot
                                                 ('b'::('a'::('s'::('e'::[]))))))))
                                           (assign'
                                             (variableSlot
                                               ('b'::('a'::('s'::('e'::[])))))
                                             (Rvalue
                                             (lvalIn (fun x -> LvMem (Reg
                                               Rv))))))
                                         (seq
                                           (assign'
                                             (variableSlot
                                               ('b'::('a'::('s'::('e'::[])))))
                                             (Bop
                                             ((lvalIn
                                                (variableSlot
                                                  ('b'::('a'::('s'::('e'::[])))))),
                                             Plus,
                                             (lvalIn
                                               (variableSlot ('n'::[]))))))
                                           (seq
                                             (assign'
                                               (variableSlot
                                                 ('b'::('a'::('s'::('e'::[])))))
                                               (Bop
                                               ((lvalIn
                                                  (variableSlot
                                                    ('b'::('a'::('s'::('e'::[])))))),
                                               Plus,
                                               (immInR (natToW (S (S O)))))))
                                             (seq
                                               (seq
                                                 (assign' (regInL Rv) (Rvalue
                                                   (lvalIn
                                                     (variableSlot
                                                       ('c'::('u'::('r'::[])))))))
                                                 (assign'
                                                   (variableSlot ('n'::[]))
                                                   (Rvalue
                                                   (lvalIn (fun x -> LvMem
                                                     (Reg Rv))))))
                                               (seq
                                                 (assign'
                                                   (variableSlot
                                                     ('b'::('a'::('s'::('e'::[])))))
                                                   (Bop
                                                   ((lvalIn
                                                      (variableSlot
                                                        ('b'::('a'::('s'::('e'::[])))))),
                                                   Plus,
                                                   (lvalIn
                                                     (variableSlot ('n'::[]))))))
                                                 (seq
                                                   (seq
                                                     (assign' (regInL Rv)
                                                       (Rvalue
                                                       (lvalIn
                                                         (variableSlot
                                                           ('c'::('u'::('r'::[])))))))
                                                     (assign' (fun x -> LvMem
                                                       (Reg Rv)) (Rvalue
                                                       (lvalIn
                                                         (variableSlot
                                                           ('b'::('a'::('s'::('e'::[])))))))))
                                                   (seq
                                                     (seq
                                                       (assign' (regInL Rv)
                                                         (Bop
                                                         ((lvalIn
                                                            (variableSlot
                                                              ('t'::('m'::('p'::[]))))),
                                                         Plus,
                                                         (immInR
                                                           (natToW (S (S (S
                                                             (S O)))))))))
                                                       (assign'
                                                         (variableSlot
                                                           ('t'::('m'::('p'::[]))))
                                                         (Rvalue
                                                         (lvalIn (fun x ->
                                                           LvMem (Reg Rv))))))
                                                     (seq
                                                       (seq
                                                         (assign' (regInL Rv)
                                                           (Bop
                                                           ((lvalIn
                                                              (variableSlot
                                                                ('c'::('u'::('r'::[]))))),
                                                           Plus,
                                                           (immInR
                                                             (natToW (S (S (S
                                                               (S O)))))))))
                                                         (assign' (fun x ->
                                                           LvMem (Reg Rv))
                                                           (Rvalue
                                                           (lvalIn
                                                             (variableSlot
                                                               ('t'::('m'::('p'::[]))))))))
                                                       (seq
                                                         (assign' (regInL Rv)
                                                           (Rvalue
                                                           (immInR
                                                             (natToW O))))
                                                         (seq
                                                           (assign'
                                                             (regInL Rp)
                                                             (Rvalue
                                                             (lvalIn
                                                               (fun x ->
                                                               LvMem (Indir
                                                               (Sp,
                                                               (natToW O)))))))
                                                           (goto
                                                             (lvalIn
                                                               (regInL Rp)))))))))))))
                                       (seq
                                         (seq
                                           (assign' (regInL Rv) (Rvalue
                                             (lvalIn
                                               (variableSlot
                                                 ('c'::('u'::('r'::[])))))))
                                           (assign'
                                             (variableSlot
                                               ('b'::('a'::('s'::('e'::[])))))
                                             (Rvalue
                                             (lvalIn (fun x -> LvMem (Reg
                                               Rv))))))
                                         (seq
                                           (assign'
                                             (variableSlot
                                               ('b'::('a'::('s'::('e'::[])))))
                                             (Bop
                                             ((lvalIn
                                                (variableSlot
                                                  ('b'::('a'::('s'::('e'::[])))))),
                                             Plus,
                                             (lvalIn
                                               (variableSlot ('n'::[]))))))
                                           (seq
                                             (seq
                                               (assign' (regInL Rv) (Rvalue
                                                 (lvalIn
                                                   (variableSlot
                                                     ('c'::('u'::('r'::[])))))))
                                               (assign' (fun x -> LvMem (Reg
                                                 Rv)) (Rvalue
                                                 (lvalIn
                                                   (variableSlot
                                                     ('b'::('a'::('s'::('e'::[])))))))))
                                             (seq
                                               (assign' (regInL Rv) (Rvalue
                                                 (immInR (natToW O))))
                                               (seq
                                                 (assign' (regInL Rp) (Rvalue
                                                   (lvalIn (fun x -> LvMem
                                                     (Indir (Sp,
                                                     (natToW O)))))))
                                                 (goto (lvalIn (regInL Rp)))))))))))))
                             (if_0 { cOperand1 =
                               (lvalIn (variableSlot ('p'::[]))); cTest =
                               Lt0; cOperand2 =
                               (lvalIn
                                 (variableSlot ('c'::('u'::('r'::[]))))) }
                               (seq note__
                                 (seq
                                   (seq
                                     (assign' (regInL Rv) (Rvalue
                                       (lvalIn (variableSlot ('p'::[])))))
                                     (assign' (fun x -> LvMem (Reg Rv)) (Bop
                                       ((lvalIn (variableSlot ('n'::[]))),
                                       Minus, (immInR (natToW (S (S O))))))))
                                   (seq
                                     (seq
                                       (assign' (regInL Rv) (Rvalue
                                         (lvalIn
                                           (variableSlot
                                             ('b'::('a'::('s'::('e'::[]))))))))
                                       (assign'
                                         (variableSlot
                                           ('t'::('m'::('p'::[])))) (Rvalue
                                         (lvalIn (fun x -> LvMem (Reg Rv))))))
                                     (seq
                                       (seq
                                         (assign' (regInL Rv) (Rvalue
                                           (lvalIn
                                             (variableSlot
                                               ('b'::('a'::('s'::('e'::[]))))))))
                                         (assign' (fun x -> LvMem (Reg Rv))
                                           (Rvalue
                                           (lvalIn (variableSlot ('p'::[]))))))
                                       (seq
                                         (seq
                                           (assign' (regInL Rv) (Bop
                                             ((lvalIn
                                                (variableSlot ('p'::[]))),
                                             Plus,
                                             (immInR
                                               (natToW (S (S (S (S O)))))))))
                                           (assign' (fun x -> LvMem (Reg Rv))
                                             (Rvalue
                                             (lvalIn
                                               (variableSlot
                                                 ('t'::('m'::('p'::[]))))))))
                                         (seq
                                           (assign' (regInL Rv) (Rvalue
                                             (immInR (natToW O))))
                                           (seq
                                             (assign' (regInL Rp) (Rvalue
                                               (lvalIn (fun x -> LvMem (Indir
                                                 (Sp, (natToW O)))))))
                                             (goto (lvalIn (regInL Rp))))))))))
                               (seq
                                 (assign'
                                   (variableSlot
                                     ('b'::('a'::('s'::('e'::[]))))) (Bop
                                   ((lvalIn
                                      (variableSlot ('c'::('u'::('r'::[]))))),
                                   Plus,
                                   (immInR (natToW (S (S (S (S O)))))))))
                                 (seq
                                   (assign' (regInL Rv) (Rvalue
                                     (lvalIn
                                       (variableSlot
                                         ('b'::('a'::('s'::('e'::[]))))))))
                                   (assign'
                                     (variableSlot ('c'::('u'::('r'::[]))))
                                     (Rvalue
                                     (lvalIn (fun x -> LvMem (Reg Rv)))))))))))))))))
           (seq note__
             (seq
               (seq
                 (assign' (regInL Rv) (Rvalue
                   (lvalIn (variableSlot ('p'::[])))))
                 (assign' (fun x -> LvMem (Reg Rv)) (Bop
                   ((lvalIn (variableSlot ('n'::[]))), Minus,
                   (immInR (natToW (S (S O))))))))
               (seq
                 (seq
                   (assign' (regInL Rv) (Rvalue
                     (lvalIn (variableSlot ('b'::('a'::('s'::('e'::[]))))))))
                   (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
                     (lvalIn (fun x -> LvMem (Reg Rv))))))
                 (seq
                   (seq
                     (assign' (regInL Rv) (Rvalue
                       (lvalIn (variableSlot ('b'::('a'::('s'::('e'::[]))))))))
                     (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                       (lvalIn (variableSlot ('p'::[]))))))
                   (seq
                     (seq
                       (assign' (regInL Rv) (Bop
                         ((lvalIn (variableSlot ('p'::[]))), Plus,
                         (immInR (natToW (S (S (S (S O)))))))))
                       (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                         (lvalIn (variableSlot ('t'::('m'::('p'::[]))))))))
                     (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
                       (seq
                         (assign' (regInL Rp) (Rvalue
                           (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                         (goto (lvalIn (regInL Rp)))))))))))
     in
     { fName = ('f'::('r'::('e'::('e'::[])))); fVars = vars0; fReserved =
     freeS.reserved0; fPrecondition = (freeS.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (freeS.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length freeS.formals)))))) })::(
    (let vars0 =
       ('b'::('a'::('s'::('e'::[]))))::(('n'::[])::(('c'::('u'::('r'::[])))::(('p'::('r'::('e'::('v'::[]))))::(('t'::('m'::('p'::[])))::(('t'::('m'::('p'::('2'::[]))))::[])))))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('b'::('a'::('s'::('e'::[]))))))))
           (assign' (variableSlot ('c'::('u'::('r'::[])))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (assign' (variableSlot ('p'::('r'::('e'::('v'::[]))))) (Rvalue
             (lvalIn (variableSlot ('b'::('a'::('s'::('e'::[]))))))))
           (seq
             (while_0
               (let a = true in
                let b0 = fun w0 -> w0 in
                (fun c d e -> Exists ([], (fun len ->
                localsInvariant (fun v x -> Body
                  (starB []
                    (starB [] (injB [])
                      (ptsto32 [] (v ('p'::('r'::('e'::('v'::[])))))
                        (v ('c'::('u'::('r'::[]))))))
                    (FreeList.freeList (Obj.magic len)
                      (v ('c'::('u'::('r'::[]))))))) (fun v x r -> Quant
                  (fun p -> Quant (fun len' -> Body
                  (starB []
                    (starB []
                      (starB [] (starB [] (injB []) (injB []))
                        (allocated r O
                          (wordToNat (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S O))))))))))))))))))))))))))))))))
                            (v ('n'::[])))))
                      (ptsto32 [] (v ('p'::('r'::('e'::('v'::[])))))
                        (Obj.magic p)))
                    (FreeList.freeList (Obj.magic len') (Obj.magic p)))))) a
                  b0 c d e)))) { cOperand1 =
               (lvalIn (variableSlot ('c'::('u'::('r'::[]))))); cTest = Ne;
               cOperand2 = (immInR (natToW O)) }
               (seq
                 (seq
                   (assign' (regInL Rv) (Rvalue
                     (lvalIn (variableSlot ('c'::('u'::('r'::[])))))))
                   (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
                     (lvalIn (fun x -> LvMem (Reg Rv))))))
                 (seq
                   (assign' (variableSlot ('t'::('m'::('p'::[])))) (Bop
                     ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))), Plus,
                     (immInR (natToW (S (S O)))))))
                   (if_0 { cOperand1 =
                     (lvalIn (variableSlot ('t'::('m'::('p'::[]))))); cTest =
                     Eq0; cOperand2 = (lvalIn (variableSlot ('n'::[]))) }
                     (seq note__
                       (seq
                         (seq
                           (assign' (regInL Rv) (Bop
                             ((lvalIn (variableSlot ('c'::('u'::('r'::[]))))),
                             Plus, (immInR (natToW (S (S (S (S O)))))))))
                           (assign' (variableSlot ('t'::('m'::('p'::[]))))
                             (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                         (seq
                           (seq
                             (assign' (regInL Rv) (Rvalue
                               (lvalIn
                                 (variableSlot
                                   ('p'::('r'::('e'::('v'::[]))))))))
                             (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                               (lvalIn
                                 (variableSlot ('t'::('m'::('p'::[]))))))))
                           (seq
                             (assign' (regInL Rv) (Rvalue
                               (lvalIn
                                 (variableSlot ('c'::('u'::('r'::[])))))))
                             (seq
                               (assign' (regInL Rp) (Rvalue
                                 (lvalIn (fun x -> LvMem (Indir (Sp,
                                   (natToW O)))))))
                               (goto (lvalIn (regInL Rp))))))))
                     (seq
                       (seq
                         (assign' (regInL Rv) (Rvalue
                           (lvalIn (variableSlot ('c'::('u'::('r'::[])))))))
                         (assign'
                           (variableSlot ('t'::('m'::('p'::('2'::[])))))
                           (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                       (if_0 { cOperand1 = (lvalIn (variableSlot ('n'::[])));
                         cTest = Lt0; cOperand2 =
                         (lvalIn
                           (variableSlot ('t'::('m'::('p'::('2'::[])))))) }
                         (seq
                           (assign' (variableSlot ('t'::('m'::('p'::[]))))
                             (Bop
                             ((lvalIn
                                (variableSlot ('t'::('m'::('p'::('2'::[])))))),
                             Minus, (lvalIn (variableSlot ('n'::[]))))))
                           (seq
                             (assign' (variableSlot ('t'::('m'::('p'::[]))))
                               (Bop
                               ((lvalIn
                                  (variableSlot ('t'::('m'::('p'::[]))))),
                               Plus, (immInR (natToW (S (S O)))))))
                             (seq
                               (assign'
                                 (variableSlot ('t'::('m'::('p'::[])))) (Bop
                                 ((immInR (natToW (S (S (S (S O)))))), Times,
                                 (lvalIn
                                   (variableSlot ('t'::('m'::('p'::[]))))))))
                               (seq
                                 (assign'
                                   (variableSlot ('t'::('m'::('p'::[]))))
                                   (Bop
                                   ((lvalIn
                                      (variableSlot ('c'::('u'::('r'::[]))))),
                                   Plus,
                                   (lvalIn
                                     (variableSlot ('t'::('m'::('p'::[]))))))))
                                 (seq
                                   (assign'
                                     (variableSlot
                                       ('t'::('m'::('p'::('2'::[]))))) (Bop
                                     ((lvalIn
                                        (variableSlot
                                          ('t'::('m'::('p'::('2'::[])))))),
                                     Minus,
                                     (lvalIn (variableSlot ('n'::[]))))))
                                   (seq
                                     (seq
                                       (assign' (regInL Rv) (Rvalue
                                         (lvalIn
                                           (variableSlot
                                             ('c'::('u'::('r'::[])))))))
                                       (assign' (fun x -> LvMem (Reg Rv))
                                         (Rvalue
                                         (lvalIn
                                           (variableSlot
                                             ('t'::('m'::('p'::('2'::[])))))))))
                                     (seq
                                       (assign' (regInL Rv) (Rvalue
                                         (lvalIn
                                           (variableSlot
                                             ('t'::('m'::('p'::[])))))))
                                       (seq
                                         (assign' (regInL Rp) (Rvalue
                                           (lvalIn (fun x -> LvMem (Indir
                                             (Sp, (natToW O)))))))
                                         (goto (lvalIn (regInL Rp)))))))))))
                         (seq
                           (assign'
                             (variableSlot ('p'::('r'::('e'::('v'::[])))))
                             (Bop
                             ((lvalIn (variableSlot ('c'::('u'::('r'::[]))))),
                             Plus, (immInR (natToW (S (S (S (S O)))))))))
                           (seq
                             (assign' (regInL Rv) (Rvalue
                               (lvalIn
                                 (variableSlot
                                   ('p'::('r'::('e'::('v'::[]))))))))
                             (assign' (variableSlot ('c'::('u'::('r'::[]))))
                               (Rvalue (lvalIn (fun x -> LvMem (Reg Rv)))))))))))))
             diverge))
     in
     { fName = ('m'::('a'::('l'::('l'::('o'::('c'::[])))))); fVars = vars0;
     fReserved = mallocS.reserved0; fPrecondition =
     (mallocS.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (mallocS.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length mallocS.formals)))))) })::[])))

(** val starL : __ list -> ('a1 -> hpropB) -> 'a1 list -> hpropB **)

let rec starL g p = function
| [] -> empB g
| x::ls0 -> starB g (p x) (starL g p ls0)

(** val to_bedrock_label : glabel -> label **)

let to_bedrock_label l =
  Pair ((fst l), (Global (snd l)))

(** val empty_vs : vals **)

let empty_vs x =
  natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) O

(** val has_extra_stack : word -> nat -> nat -> nat -> hpropB **)

let has_extra_stack sp offset e_stack e_stack_real =
  starB []
    (ptsto32 []
      (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) sp
        (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))) (S (S (S (S O))))))
      (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
        e_stack))
    (allocated
      (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
        (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
          sp
          (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S
            O))))))))))
        (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))) (mult (S (S (S (S O)))) offset)))
      O e_stack_real)

(** val cptr_AlX :
    __ list -> w -> settings0 -> ((settings0, state) prod -> (w, (settings0,
    state) prod) propX) -> (w, (settings0, state) prod) propX **)

let cptr_AlX g p stn a =
  ExistsX (g, (And ((__::g), (Cptr ((__::g), p, (fun x -> Var0 (g,
    (Obj.magic x))))), (Forall ((__::g), (fun st0 -> ForallX ((__::g), (Imply
    ((__::(__::g)), (Obj.magic a (Pair (stn, st0))),
    (let x = Pair (stn, st0) in Lift ((__::g), (Var0 (g, (Obj.magic x))))))))))))))

module Coq11_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
  
  (** val make_triples :
      (w, E.coq_ADTValue value0) prod list -> SemanticsMake.coq_ArgOut list
      -> E.coq_ADTValue argTriple list **)
  
  let rec make_triples pairs outs =
    match pairs with
    | [] -> []
    | p::ps ->
      (match outs with
       | [] -> []
       | o::os ->
         { word0 = (fst p); aDTIn = (snd p); aDTOut =
           o }::(make_triples ps os))
  
  (** val store_pair :
      SemanticsMake.coq_Heap -> (w, SemanticsMake.coq_ArgIn) prod ->
      SemanticsMake.coq_Heap **)
  
  let store_pair heap0 p =
    match snd p with
    | SCA w0 -> heap0
    | ADT a -> SemanticsMake.heap_upd heap0 (fst p) a
  
  (** val make_heap :
      (w, SemanticsMake.coq_ArgIn) prod list -> SemanticsMake.coq_Heap **)
  
  let make_heap pairs =
    fold_left store_pair pairs SemanticsMake.heap_empty
  
  module Make = 
   functor (R:sig 
    type coq_RepInv = w -> E.coq_ADTValue -> hProp
    
    val rep_inv : coq_RepInv
   end) ->
   struct 
    (** val is_heap : SemanticsMake.coq_Heap -> hProp **)
    
    let is_heap h =
      starL [] (fun p -> R.rep_inv (fst p) (snd p))
        (SemanticsMake.heap_elements h)
    
    (** val is_state :
        word -> w -> nat -> nat -> char list list -> SemanticsMake.coq_State
        -> w list -> hProp **)
    
    let is_state sp rp e_stack e_stack_real vars0 v temps =
      starB []
        (starB []
          (starB []
            (starB []
              (locals vars0 (fst v) O
                (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))) sp
                  (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S
                    O)))))))))))
              (array temps
                (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O))))))))))))))))))))))))))))))))
                  (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) sp
                    (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S
                      (S O))))))))))
                  (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O))))))))))))))))))))))))))))))))
                    (mult (S (S (S (S O)))) (length vars0))))))
            (is_heap (snd v))) (ptsto32 [] sp rp))
        (has_extra_stack sp (plus (length vars0) (length temps)) e_stack
          e_stack_real)
    
    (** val layout_option : w -> E.coq_ADTValue option -> hProp **)
    
    let layout_option addr0 = function
    | Some a -> R.rep_inv addr0 a
    | None -> injB []
    
    (** val internal_spec :
        __ list -> (ST.settings -> w -> E.coq_ADTValue callee option) ->
        funcCore -> (ST.settings, state) prod -> (w, (ST.settings, state)
        prod) propX **)
    
    let internal_spec g fs0 spec1 st0 =
      Exists ((__::g), (fun v -> Exists ((__::g), (fun rp -> Exists ((__::g),
        (fun e_stack -> And ((__::g),
        (SepFormula.sepFormula (__::g)
          (starB (__::g)
            (lift (__::g)
              (starB []
                (is_state ((snd st0).regs Sp) (Obj.magic rp)
                  (Obj.magic e_stack) (Obj.magic e_stack) spec1.argVars1
                  (Obj.magic v) []) (FreeList.mallocHeap (natToW O))))
            (hvarB (__::g) (fun x -> Var0 (g, (Obj.magic x))))) st0),
        (let stn = fst st0 in
         And ((__::g), (Inj (__::g)), (ExistsX ((__::g), (And ((__::(__::g)),
         (Cptr ((__::(__::g)), (fst (Pair (((snd st0).regs Rp), stn))),
         (fun x -> Var0 ((__::g), (Obj.magic x))))), (Forall ((__::(__::g)),
         (fun st1 -> Imply ((__::(__::g)),
         (let st' = Pair ((snd (Pair (((snd st0).regs Rp), stn))), st1) in
          Exists ((__::(__::g)), (fun v' -> Exists ((__::(__::g)),
          (fun rp' -> Exists ((__::(__::g)), (fun e_stack' -> And
          ((__::(__::g)),
          (SepFormula.sepFormula (__::(__::g))
            (starB (__::(__::g))
              (lift (__::(__::g))
                (starB []
                  (is_state ((snd (Obj.magic st')).regs Sp) (Obj.magic rp')
                    (Obj.magic e_stack') (Obj.magic e_stack) spec1.argVars1
                    (Obj.magic v') []) (FreeList.mallocHeap (natToW O))))
              (hvarB (__::(__::g)) (fun x -> Lift ((__::g), (Var0 (g,
                (Obj.magic x))))))) (Obj.magic st')), (Inj
          (__::(__::g))))))))))),
         (let x = Pair ((snd (Pair (((snd st0).regs Rp), stn))), st1) in
          Var0 ((__::g), (Obj.magic x))))))))))))))))))))
    
    (** val foreign_spec :
        __ list -> E.coq_ADTValue axiomaticSpec -> (ST.settings, state) prod
        -> (w, (ST.settings, state) prod) propX **)
    
    let foreign_spec g spec1 st0 =
      Exists ((__::g), (fun pairs -> Exists ((__::g), (fun rp -> Exists
        ((__::g), (fun e_stack ->
        let heap0 = make_heap (Obj.magic pairs) in
        And ((__::g),
        (SepFormula.sepFormula (__::g)
          (starB (__::g)
            (lift (__::g)
              (starB []
                (is_state ((snd st0).regs Sp) (Obj.magic rp)
                  (Obj.magic e_stack) (Obj.magic e_stack) [] (Pair (empty_vs,
                  heap0)) (map fst (Obj.magic pairs)))
                (FreeList.mallocHeap (natToW O))))
            (hvarB (__::g) (fun x -> Var0 (g, (Obj.magic x))))) st0),
        (let stn = fst st0 in
         And ((__::g), (Inj (__::g)), (ExistsX ((__::g), (And ((__::(__::g)),
         (Cptr ((__::(__::g)), (fst (Pair (((snd st0).regs Rp), stn))),
         (fun x -> Var0 ((__::g), (Obj.magic x))))), (Forall ((__::(__::g)),
         (fun st1 -> Imply ((__::(__::g)),
         (let st' = Pair ((snd (Pair (((snd st0).regs Rp), stn))), st1) in
          Exists ((__::(__::g)), (fun args' -> Exists ((__::(__::g)),
          (fun addr0 -> Exists ((__::(__::g)), (fun ret -> Exists
          ((__::(__::g)), (fun rp' -> Exists ((__::(__::g)), (fun outs ->
          let t0 = SemanticsMake.decide_ret (Obj.magic addr0) (Obj.magic ret)
          in
          let ret_w = fst t0 in
          let ret_a = snd t0 in
          let triples = make_triples (Obj.magic pairs) (Obj.magic outs) in
          let heap1 = fold_left SemanticsMake.store_out triples heap0 in
          Exists ((__::(__::g)), (fun vs -> Exists ((__::(__::g)),
          (fun e_stack' -> And ((__::(__::g)),
          (SepFormula.sepFormula (__::(__::g))
            (starB (__::(__::g))
              (lift (__::(__::g))
                (starB []
                  (starB []
                    (is_state ((snd st0).regs Sp) (Obj.magic rp')
                      (Obj.magic e_stack') (Obj.magic e_stack) [] (Pair
                      ((Obj.magic vs), heap1)) (Obj.magic args'))
                    (layout_option ret_w ret_a))
                  (FreeList.mallocHeap (natToW O))))
              (hvarB (__::(__::g)) (fun x -> Lift ((__::g), (Var0 (g,
                (Obj.magic x))))))) (Obj.magic st')), (Inj
          (__::(__::g))))))))))))))))))),
         (let x = Pair ((snd (Pair (((snd st0).regs Rp), stn))), st1) in
          Var0 ((__::g), (Obj.magic x))))))))))))))))))))
    
    (** val funcs_ok :
        settings0 -> (settings0 -> w -> SemanticsMake.coq_Callee option) ->
        (w, (settings0, state) prod) propX0 **)
    
    let funcs_ok stn fs0 =
      And ([], (Forall ([], (fun i -> Forall ([], (fun spec1 -> Imply ([],
        (Inj []),
        (cptr_AlX [] (Obj.magic i) stn
          (internal_spec (__::[]) fs0 (fun0 (Obj.magic spec1)))))))))),
        (Forall ([], (fun i -> Forall ([], (fun spec1 -> Imply ([], (Inj []),
        (cptr_AlX [] (Obj.magic i) stn
          (foreign_spec (__::[]) (Obj.magic spec1))))))))))
    
    (** val inv_template : char list list -> nat -> stmt1 -> assert0 **)
    
    let inv_template vars0 temp_size0 s st0 =
      Exists ([], (fun fs0 ->
        let stn = fst st0 in
        And ([], (funcs_ok stn (Obj.magic fs0)), (ExistsX ([], (Exists
        ((__::[]), (fun v -> Exists ((__::[]), (fun temps -> Exists
        ((__::[]), (fun rp -> Exists ((__::[]), (fun e_stack -> And
        ((__::[]),
        (SepFormula.sepFormula (__::[])
          (starB (__::[])
            (lift (__::[])
              (starB []
                (is_state ((snd st0).regs Sp) (Obj.magic rp)
                  (Obj.magic e_stack) (Obj.magic e_stack) vars0 (Obj.magic v)
                  (Obj.magic temps)) (FreeList.mallocHeap (natToW O))))
            (hvarB (__::[]) (fun x -> Var0 ([], (Obj.magic x))))) st0), (And
        ((__::[]), (Inj (__::[])), (ExistsX ((__::[]), (And ((__::(__::[])),
        (Cptr ((__::(__::[])), (fst (Pair ((Obj.magic rp), stn))), (fun x ->
        Var0 ((__::[]), (Obj.magic x))))), (Forall ((__::(__::[])),
        (fun st1 -> Imply ((__::(__::[])),
        (let st' = Pair ((snd (Pair (rp, stn))), st1) in
         Exists ((__::(__::[])), (fun v' -> Exists ((__::(__::[])),
         (fun temps' -> And ((__::(__::[])),
         (SepFormula.sepFormula (__::(__::[]))
           (starB (__::(__::[]))
             (lift (__::(__::[]))
               (starB []
                 (is_state ((snd (Obj.magic st')).regs Sp) (Obj.magic rp)
                   (Obj.magic e_stack) (Obj.magic e_stack) vars0
                   (Obj.magic v') (Obj.magic temps'))
                 (FreeList.mallocHeap (natToW O))))
             (hvarB (__::(__::[])) (fun x -> Lift ((__::[]), (Var0 ([],
               (Obj.magic x))))))) (Obj.magic st')), (Inj
         (__::(__::[]))))))))),
        (let x = Pair ((snd (Pair (rp, stn))), st1) in
         Var0 ((__::[]), (Obj.magic x))))))))))))))))))))))))))))
    
    (** val inv : char list list -> nat -> stmt1 -> assert0 **)
    
    let inv vars0 temp_size0 s x =
      inv_template vars0 temp_size0 s x
   end
 end

module Coq12_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
  
  (** val precond : char list list -> nat -> stmt1 -> stmt1 -> assert0 **)
  
  let precond vars0 temp_size0 s k =
    InvMake2.inv vars0 temp_size0 (Seq1 (s, k))
  
  (** val postcond : char list list -> nat -> stmt1 -> assert0 **)
  
  let postcond vars0 temp_size0 k =
    InvMake2.inv vars0 temp_size0 k
  
  (** val verifCond :
      char list list -> nat -> stmt1 -> stmt1 -> assert0 -> __ list **)
  
  let verifCond vars0 temp_size0 s k pre =
    __::(__::[])
 end

module Coq13_Make = 
 functor (E:ADT) ->
 struct 
  module WfMake = Coq10_Make(E)
 end

type goodFunction =
  func0
  (* singleton inductive, whose constructor was Build_GoodFunction *)

(** val fun1 : goodFunction -> func0 **)

let fun1 g =
  g

(** val to_good_function : func0 -> goodFunction **)

let to_good_function f0 =
  f0

(** val to_internal_func_spec : goodFunction -> internalFuncSpec **)

let to_internal_func_spec f0 =
  (fun1 f0).core0

type goodModule = { name0 : char list; functions1 : goodFunction list }

(** val name0 : goodModule -> char list **)

let name0 x = x.name0

(** val functions1 : goodModule -> goodFunction list **)

let functions1 x = x.functions1

(** val is_label_map_to_word :
    (glabel -> w option) -> glabel -> word -> bool **)

let is_label_map_to_word l2w lbl p =
  match l2w lbl with
  | Some p' ->
    if weq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) p p'
    then true
    else false
  | None -> false

(** val is_label_map_to_word' :
    (glabel -> w option) -> word -> (glabel, 'a1) prod -> bool **)

let is_label_map_to_word' l2w p x =
  is_label_map_to_word l2w (fst x) p

(** val find_by_word :
    (glabel -> w option) -> (glabel, 'a1) prod list -> w -> 'a1 option **)

let find_by_word l2w m6 p =
  match find (is_label_map_to_word' l2w p) m6 with
  | Some p0 -> let Pair (g, a) = p0 in Some a
  | None -> None

module Coq14_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
  
  (** val spec_without_funcs_ok :
      funcCore -> (ST.settings -> w -> E.coq_ADTValue callee option) ->
      assert0 **)
  
  let spec_without_funcs_ok func1 fs0 st0 =
    ExistsX ([], (InvMake2.internal_spec [] fs0 func1 st0))
  
  (** val spec : funcCore -> assert0 **)
  
  let spec func1 st0 =
    Exists ([], (fun fs0 ->
      let stn = fst st0 in
      And ([], (InvMake2.funcs_ok stn (Obj.magic fs0)),
      (spec_without_funcs_ok func1 (Obj.magic fs0) st0))))
  
  (** val verifCond : funcCore -> assert0 -> __ list **)
  
  let verifCond func1 pre =
    __::[]
 end

(** val name_marker : glabel -> (w, (settings0, state) prod) propX0 **)

let name_marker id =
  Exists ([], (fun s -> Inj []))

module Coq15_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
  
  (** val glabel2w : settings0 -> glabel -> w option **)
  
  let glabel2w stn lbl =
    stn.labels (to_bedrock_label lbl)
  
  (** val func_export_IFS :
      goodModule -> goodFunction -> ((char list, char list) prod,
      internalFuncSpec) prod **)
  
  let func_export_IFS m6 f0 =
    Pair ((Pair (m6.name0, (fun1 f0).name)), (to_internal_func_spec f0))
  
  (** val module_exports_IFS :
      goodModule -> ((char list, char list) prod, internalFuncSpec) prod list **)
  
  let module_exports_IFS m6 =
    map (func_export_IFS m6) m6.functions1
  
  (** val exports_IFS : goodModule list -> internalFuncSpec Coq0_M.t **)
  
  let exports_IFS modules0 =
    to_map (app_all (map module_exports_IFS modules0))
  
  (** val is_export :
      goodModule list -> settings0 -> w -> internalFuncSpec option **)
  
  let is_export modules0 stn =
    find_by_word (glabel2w stn)
      (GLabelMap.elements (Obj.magic (exports_IFS modules0)))
  
  (** val is_import :
      SemanticsMake.coq_ForeignFuncSpec GLabelMap.t -> settings0 -> w ->
      SemanticsMake.coq_ForeignFuncSpec option **)
  
  let is_import imports3 stn =
    find_by_word (glabel2w stn) (GLabelMap.elements imports3)
  
  (** val fs :
      goodModule list -> SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
      settings0 -> w -> SemanticsMake.coq_Callee option **)
  
  let fs modules0 imports3 stn p =
    match is_export modules0 stn p with
    | Some spec1 -> Some (SemanticsMake.coq_Internal spec1)
    | None ->
      (match is_import imports3 stn p with
       | Some spec1 -> Some (SemanticsMake.coq_Foreign spec1)
       | None -> None)
  
  module Make = 
   functor (M__2:sig 
    type coq_RepInv = w -> E.coq_ADTValue -> hProp
    
    val rep_inv : coq_RepInv
   end) ->
   struct 
    module CompileFuncSpecMake = Coq14_Make(E)(M__2)
    
    (** val func_spec :
        goodModule list -> SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
        glabel -> funcCore -> assert0 **)
    
    let func_spec modules0 imps id f0 st0 =
      Imply ([], (And ([], (name_marker id), (Inj []))),
        (CompileFuncSpecMake.spec_without_funcs_ok f0 (fs modules0 imps) st0))
    
    (** val foreign_func_spec :
        glabel -> E.coq_ADTValue axiomaticSpec -> assert0 **)
    
    let foreign_func_spec id spec1 st0 =
      And ([], (name_marker id), (ExistsX ([],
        (CompileFuncSpecMake.InvMake2.foreign_spec [] spec1 st0))))
    
    (** val imports :
        SemanticsMake.coq_ForeignFuncSpec GLabelMap.t -> assert0 GLabelMap.t **)
    
    let imports imps =
      GLabelMap.mapi foreign_func_spec imps
    
    (** val func_export :
        goodModule list -> SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
        goodModule -> goodFunction -> ((char list, char list) prod, assert0)
        prod **)
    
    let func_export modules0 imps module1 f0 =
      let lbl = Pair (module1.name0, (fun1 f0).name) in
      Pair (lbl, (func_spec modules0 imps lbl (fun1 f0).core0))
    
    (** val module_exports :
        goodModule list -> SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
        goodModule -> assert0 Coq0_M.t **)
    
    let module_exports modules0 imps m6 =
      of_list1 (map (func_export modules0 imps m6) m6.functions1)
    
    (** val exports :
        goodModule list -> SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
        assert0 Coq0_M.t **)
    
    let exports modules0 imps =
      update_all (map (module_exports modules0 imps) modules0)
    
    (** val impl_label : char list -> char list -> glabel **)
    
    let impl_label mod_name0 f_name =
      Pair ((impl_module_name mod_name0), f_name)
    
    (** val func_impl_export :
        goodModule -> goodFunction -> (glabel, assert0) prod **)
    
    let func_impl_export m6 f0 =
      Pair ((impl_label m6.name0 (fun1 f0).name),
        (CompileFuncSpecMake.spec (fun1 f0).core0))
    
    (** val module_impl_exports : goodModule -> assert0 Coq0_M.t **)
    
    let module_impl_exports m6 =
      of_list1 (map (func_impl_export m6) m6.functions1)
    
    (** val impl_exports : goodModule list -> assert0 Coq0_M.t **)
    
    let impl_exports modules0 =
      update_all (map module_impl_exports modules0)
    
    (** val all_exports :
        goodModule list -> SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
        assert0 Coq0_M.t **)
    
    let all_exports modules0 imps =
      update0 (exports modules0 imps) (impl_exports modules0)
   end
 end

(** val wrap :
    assert0 LabelMap.t -> char list -> cmd -> (assert0 -> assert0) ->
    (assert0 -> __ list) -> cmd **)

let wrap imports3 modName body5 postcondition0 verifCond3 pre =
  let cout = body5 pre in
  { postcondition = (postcondition0 pre); verifCond = (verifCond3 pre);
  generate = (fun base exit ->
  let cg = cout.generate (N.succ base) base in
  { entry = (N.succ cg.entry); blocks0 = ((Pair (cout.postcondition, (Pair
  ([], (Uncond (RvLabel (Pair (modName, (Local exit)))))))))::cg.blocks0) }) }

module Coq16_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
 end

(** val func_to_import : char list -> function0 -> import **)

let func_to_import mn f0 =
  Pair ((Pair (mn, (fst (fst f0)))), (snd (fst f0)))

(** val post :
    char list list -> char list option -> assert0 -> (ST.settings, state)
    prod -> (w, (settings0, state) prod) propX **)

let post vars0 var0 pre st0 =
  Exists ([], (fun st_pre -> And ([],
    (Obj.magic pre (Pair ((fst st0), st_pre))), (Inj []))))

(** val verifCond0 :
    char list list -> char list option -> assert0 -> __ list **)

let verifCond0 vars0 var0 pre =
  __::(__::[])

(** val strline : assert0 LabelMap.t -> char list -> instr list -> cmd **)

let strline imports3 modName =
  straightline_ imports3 modName

(** val saveRv : assert0 LabelMap.t -> char list -> lvalue -> cmd **)

let saveRv imports3 modName lv =
  strline imports3 modName ((Assign (lv, (RvLval (LvReg Rv))))::[])

(** val vars_start : nat **)

let vars_start =
  mult (S (S (S (S O)))) (S (S O))

(** val var_slot : char list list -> char list -> lvalue **)

let var_slot vars0 x =
  LvMem (Indir (Sp, (natToW (plus vars_start (variablePosition vars0 x)))))

(** val skip : assert0 LabelMap.t -> char list -> cmd **)

let skip imports3 modName =
  straightline_ imports3 modName []

(** val body2 :
    char list list -> char list option -> assert0 LabelMap.t -> char list ->
    cmd **)

let body2 vars0 var0 imports3 modName =
  match var0 with
  | Some x -> saveRv imports3 modName (var_slot vars0 x)
  | None -> skip imports3 modName

(** val compile1 :
    char list list -> char list option -> assert0 LabelMap.t -> char list ->
    cmd **)

let compile1 vars0 var0 imports3 modName =
  wrap imports3 modName (body2 vars0 var0 imports3 modName) (post vars0 var0)
    (verifCond0 vars0 var0)

(** val vars_start0 : nat **)

let vars_start0 =
  mult (S (S (S (S O)))) (S (S O))

(** val var_slot0 : char list list -> char list -> lvalue **)

let var_slot0 vars0 x =
  LvMem (Indir (Sp, (natToW (plus vars_start0 (variablePosition vars0 x)))))

(** val temp_start : char list list -> nat **)

let temp_start vars0 =
  plus vars_start0 (mult (S (S (S (S O)))) (length vars0))

(** val temp_slot : char list list -> nat -> lvalue **)

let temp_slot vars0 n0 =
  LvMem (Indir (Sp,
    (natToW (plus (temp_start vars0) (mult (S (S (S (S O)))) n0)))))

(** val post0 :
    char list list -> nat -> expr0 -> nat -> assert0 -> (ST.settings, state)
    prod -> (w, (settings0, state) prod) propX **)

let post0 vars0 temp_size0 expr1 base pre st0 =
  Exists ([], (fun st_pre -> And ([],
    (Obj.magic pre (Pair ((fst st0), st_pre))), (Inj []))))

(** val verifCond1 :
    char list list -> nat -> expr0 -> nat -> assert0 -> __ list **)

let verifCond1 vars0 temp_size0 expr1 base pre =
  __::(__::[])

(** val seq2 : assert0 LabelMap.t -> char list -> cmd -> cmd -> cmd **)

let seq2 imports3 modName =
  seq_ imports3 modName

(** val skip0 : assert0 LabelMap.t -> char list -> cmd **)

let skip0 imports3 modName =
  straightline_ imports3 modName []

(** val seq0 : assert0 LabelMap.t -> char list -> cmd list -> cmd **)

let rec seq0 imports3 modName = function
| [] -> skip0 imports3 modName
| a::ls' -> seq2 imports3 modName a (seq0 imports3 modName ls')

(** val strline0 : assert0 LabelMap.t -> char list -> instr list -> cmd **)

let strline0 imports3 modName =
  straightline_ imports3 modName

(** val do_compile :
    char list list -> assert0 LabelMap.t -> char list -> expr0 -> nat -> cmd **)

let rec do_compile vars0 imports3 modName expr1 base =
  match expr1 with
  | Var1 str ->
    strline0 imports3 modName ((Assign ((LvReg Rv), (RvLval
      (var_slot0 vars0 str))))::[])
  | Const0 w0 ->
    strline0 imports3 modName ((Assign ((LvReg Rv), (RvImm w0)))::[])
  | Binop0 (op, a, b0) ->
    seq0 imports3 modName
      ((do_compile vars0 imports3 modName a base)::((strline0 imports3
                                                      modName ((Assign
                                                      ((temp_slot vars0 base),
                                                      (RvLval (LvReg
                                                      Rv))))::[]))::(
      (do_compile vars0 imports3 modName b0 (S base))::((strline0 imports3
                                                          modName ((Binop
                                                          ((LvReg Rv),
                                                          (RvLval
                                                          (temp_slot vars0
                                                            base)), op,
                                                          (RvLval (LvReg
                                                          Rv))))::[]))::[]))))
  | TestE (te, a, b0) ->
    seq0 imports3 modName
      ((do_compile vars0 imports3 modName a base)::((strline0 imports3
                                                      modName ((Assign
                                                      ((temp_slot vars0 base),
                                                      (RvLval (LvReg
                                                      Rv))))::[]))::(
      (do_compile vars0 imports3 modName b0 (S base))::((if_ imports3 modName
                                                          (RvLval
                                                          (temp_slot vars0
                                                            base)) te (RvLval
                                                          (LvReg Rv))
                                                          (strline0 imports3
                                                            modName ((Assign
                                                            ((LvReg Rv),
                                                            (RvImm
                                                            (natToWord (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              O))))))))))))))))))))))))))))))))
                                                              (S O)))))::[]))
                                                          (strline0 imports3
                                                            modName ((Assign
                                                            ((LvReg Rv),
                                                            (RvImm
                                                            (natToWord (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              O))))))))))))))))))))))))))))))))
                                                              O))))::[])))::[]))))

(** val body3 :
    char list list -> assert0 LabelMap.t -> char list -> expr0 -> nat -> cmd **)

let body3 vars0 imports3 modName =
  do_compile vars0 imports3 modName

(** val compile2 :
    char list list -> nat -> assert0 LabelMap.t -> char list -> expr0 -> nat
    -> cmd **)

let compile2 vars0 temp_size0 imports3 modName expr1 base =
  wrap imports3 modName (body3 vars0 imports3 modName expr1 base)
    (post0 vars0 temp_size0 expr1 base)
    (verifCond1 vars0 temp_size0 expr1 base)

(** val post1 :
    char list list -> nat -> expr0 list -> nat -> nat -> assert0 ->
    (ST.settings, state) prod -> (w, (settings0, state) prod) propX **)

let post1 vars0 temp_size0 exprs0 base dst pre st0 =
  Exists ([], (fun st_pre -> And ([],
    (Obj.magic pre (Pair ((fst st0), st_pre))), (Inj []))))

(** val verifCond2 :
    char list list -> nat -> expr0 list -> nat -> nat -> assert0 -> __ list **)

let verifCond2 vars0 temp_size0 exprs0 dst base pre =
  __::(__::[])

(** val seq1 : assert0 LabelMap.t -> char list -> cmd -> cmd -> cmd **)

let seq1 imports3 modName =
  seq_ imports3 modName

(** val skip1 : assert0 LabelMap.t -> char list -> cmd **)

let skip1 imports3 modName =
  straightline_ imports3 modName []

(** val seq3 : assert0 LabelMap.t -> char list -> cmd list -> cmd **)

let rec seq3 imports3 modName = function
| [] -> skip1 imports3 modName
| a::ls' -> seq1 imports3 modName a (seq3 imports3 modName ls')

(** val strline1 : assert0 LabelMap.t -> char list -> instr list -> cmd **)

let strline1 imports3 modName =
  straightline_ imports3 modName

(** val saveRv0 : assert0 LabelMap.t -> char list -> lvalue -> cmd **)

let saveRv0 imports3 modName lv =
  strline1 imports3 modName ((Assign (lv, (RvLval (LvReg Rv))))::[])

(** val stack_slot : nat -> lvalue **)

let stack_slot n0 =
  LvMem (Indir (Sp, (natToW n0)))

(** val compile_expr :
    char list list -> nat -> assert0 LabelMap.t -> char list -> expr0 -> nat
    -> cmd **)

let compile_expr vars0 temp_size0 imports3 modName e n0 =
  compile2 vars0 temp_size0 imports3 modName e n0

(** val do_compile0 :
    char list list -> nat -> assert0 LabelMap.t -> char list -> expr0 list ->
    nat -> nat -> cmd list **)

let rec do_compile0 vars0 temp_size0 imports3 modName exprs0 base dst =
  match exprs0 with
  | [] -> []
  | x::xs ->
    (compile_expr vars0 temp_size0 imports3 modName x base)::((saveRv0
                                                                imports3
                                                                modName
                                                                (stack_slot
                                                                  dst))::
      (do_compile0 vars0 temp_size0 imports3 modName xs base
        (plus (S (S (S (S O)))) dst)))

(** val body4 :
    char list list -> nat -> expr0 list -> nat -> nat -> assert0 LabelMap.t
    -> char list -> cmd **)

let body4 vars0 temp_size0 exprs0 base dst imports3 modName =
  seq3 imports3 modName
    (do_compile0 vars0 temp_size0 imports3 modName exprs0 base dst)

(** val compile3 :
    char list list -> nat -> expr0 list -> nat -> nat -> assert0 LabelMap.t
    -> char list -> cmd **)

let compile3 vars0 temp_size0 exprs0 base dst imports3 modName =
  wrap imports3 modName
    (body4 vars0 temp_size0 exprs0 base dst imports3 modName)
    (post1 vars0 temp_size0 exprs0 base dst)
    (verifCond2 vars0 temp_size0 exprs0 dst base)

(** val stack_slot0 : nat -> lvalue **)

let stack_slot0 n0 =
  LvMem (Indir (Sp, (natToW (mult (S (S (S (S O)))) n0))))

(** val vars_start1 : nat **)

let vars_start1 =
  mult (S (S (S (S O)))) (S (S O))

(** val var_slot1 : char list list -> char list -> lvalue **)

let var_slot1 vars0 x =
  LvMem (Indir (Sp, (natToW (plus vars_start1 (variablePosition vars0 x)))))

(** val temp_start0 : char list list -> nat **)

let temp_start0 vars0 =
  plus vars_start1 (mult (S (S (S (S O)))) (length vars0))

(** val frame_len : char list list -> nat -> nat **)

let frame_len vars0 temp_size0 =
  plus (temp_start0 vars0) (mult (S (S (S (S O)))) temp_size0)

(** val frame_len_w : char list list -> nat -> w **)

let frame_len_w vars0 temp_size0 =
  natToW (frame_len vars0 temp_size0)

(** val callee_stack_start : char list list -> nat -> nat **)

let callee_stack_start vars0 temp_size0 =
  frame_len vars0 temp_size0

(** val callee_stack_slot : char list list -> nat -> nat -> lvalue **)

let callee_stack_slot vars0 temp_size0 n0 =
  LvMem (Indir (Sp,
    (natToW
      (plus (callee_stack_start vars0 temp_size0)
        (mult (S (S (S (S O)))) n0)))))

(** val seq4 : assert0 LabelMap.t -> char list -> cmd -> cmd -> cmd **)

let seq4 imports3 modName =
  seq_ imports3 modName

(** val strline2 : assert0 LabelMap.t -> char list -> instr list -> cmd **)

let strline2 imports3 modName =
  straightline_ imports3 modName

(** val skip__ : assert0 LabelMap.t -> char list -> cmd **)

let skip__ imports3 modName =
  skip_ imports3 modName

(** val if__ :
    assert0 LabelMap.t -> char list -> rvalue -> test -> rvalue -> cmd -> cmd
    -> cmd **)

let if__ imports3 =
  if_ imports3

(** val while__ :
    assert0 LabelMap.t -> char list -> assert0 -> rvalue -> test -> rvalue ->
    cmd -> cmd **)

let while__ imports3 =
  while_ imports3

(** val seq__ : assert0 LabelMap.t -> char list -> cmd list -> cmd **)

let rec seq__ imports3 modName = function
| [] -> skip__ imports3 modName
| a::ls' -> seq4 imports3 modName a (seq__ imports3 modName ls')

(** val saveRv1 : assert0 LabelMap.t -> char list -> lvalue -> cmd **)

let saveRv1 imports3 modName lv =
  strline2 imports3 modName ((Assign (lv, (RvLval (LvReg Rv))))::[])

(** val checkExtraStack :
    assert0 LabelMap.t -> char list -> nat -> cmd -> cmd **)

let checkExtraStack imports3 modName n0 cmd0 =
  seq4 imports3 modName
    (strline2 imports3 modName ((Assign ((LvReg Rv), (RvLval
      (stack_slot0 (S O)))))::[]))
    (if_ imports3 modName (RvImm (natToW n0)) Le (RvLval (LvReg Rv)) cmd0
      (diverge_ imports3 modName))

(** val cmp :
    char list list -> nat -> assert0 LabelMap.t -> char list -> (expr0 ->
    stmt1 -> stmt1 -> assert0) -> (char list option -> stmt1 -> assert0) ->
    (expr0 -> nat -> cmd) -> (expr0 list -> nat -> nat -> cmd) -> stmt1 ->
    stmt1 -> cmd **)

let rec cmp vars0 temp_size0 imports3 modName loop_inv0 after_call0 compile_expr0 compile_exprs0 s k =
  match s with
  | Skip1 -> skip__ imports3 modName
  | Seq1 (a, b0) ->
    seq4 imports3 modName
      (cmp vars0 temp_size0 imports3 modName loop_inv0 after_call0
        compile_expr0 compile_exprs0 a (Seq1 (b0, k)))
      (cmp vars0 temp_size0 imports3 modName loop_inv0 after_call0
        compile_expr0 compile_exprs0 b0 k)
  | If1 (cond, t0, f0) ->
    seq4 imports3 modName (compile_expr0 cond O)
      (if__ imports3 modName (RvLval (LvReg Rv)) Ne (RvImm (natToW O))
        (cmp vars0 temp_size0 imports3 modName loop_inv0 after_call0
          compile_expr0 compile_exprs0 t0 k)
        (cmp vars0 temp_size0 imports3 modName loop_inv0 after_call0
          compile_expr0 compile_exprs0 f0 k))
  | While1 (cond, body5) ->
    seq4 imports3 modName (compile_expr0 cond O)
      (while__ imports3 modName (loop_inv0 cond body5 k) (RvLval (LvReg Rv))
        Ne (RvImm (natToW O))
        (seq4 imports3 modName
          (cmp vars0 temp_size0 imports3 modName loop_inv0 after_call0
            compile_expr0 compile_exprs0 body5 (Seq1 ((While1 (cond, body5)),
            k))) (compile_expr0 cond O)))
  | Call1 (var0, f0, args) ->
    let callee_frame_len = plus (S (S O)) (length args) in
    checkExtraStack imports3 modName callee_frame_len
      (seq__ imports3 modName
        ((compile_exprs0 args O
           (plus (callee_stack_start vars0 temp_size0) (S (S (S (S (S (S (S
             (S O))))))))))::((compile_expr0 f0 O)::((strline2 imports3
                                                       modName ((Binop
                                                       ((callee_stack_slot
                                                          vars0 temp_size0 (S
                                                          O)), (RvLval
                                                       (stack_slot0 (S O))),
                                                       Minus, (RvImm
                                                       (natToW
                                                         callee_frame_len))))::((Binop
                                                       ((LvReg Sp), (RvLval
                                                       (LvReg Sp)), Plus,
                                                       (RvImm
                                                       (frame_len_w vars0
                                                         temp_size0))))::[])))::(
        (iCall_ imports3 modName (RvLval (LvReg Rv)) (after_call0 var0 k))::(
        (strline2 imports3 modName ((Binop ((LvReg Sp), (RvLval (LvReg Sp)),
          Minus, (RvImm (frame_len_w vars0 temp_size0))))::[]))::((compile1
                                                                    vars0
                                                                    var0
                                                                    imports3
                                                                    modName)::[])))))))
  | Label0 (x, lbl) ->
    strline2 imports3 modName ((Assign ((var_slot1 vars0 x), (RvLabel
      (to_bedrock_label lbl))))::[])
  | Assign2 (x, e) ->
    seq4 imports3 modName (compile_expr0 e O)
      (saveRv1 imports3 modName (var_slot1 vars0 x))

module Coq17_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
  
  (** val loop_inv :
      char list list -> nat -> expr0 -> stmt1 -> stmt1 -> assert0 **)
  
  let loop_inv vars0 temp_size0 cond body5 k =
    let s = Seq1 ((While1 (cond, body5)), k) in
    InvMake2.inv_template vars0 temp_size0 s
  
  (** val after_call :
      char list list -> nat -> char list option -> stmt1 -> assert0 **)
  
  let after_call vars0 temp_size0 ret k st0 =
    Exists ([], (fun fs0 ->
      let stn = fst st0 in
      And ([], (InvMake2.funcs_ok stn (Obj.magic fs0)), (ExistsX ([], (Exists
      ((__::[]), (fun vs -> Exists ((__::[]), (fun heap1 -> Exists ((__::[]),
      (fun heap2 -> Exists ((__::[]), (fun temps -> Exists ((__::[]),
      (fun rp -> Exists ((__::[]), (fun e_stack -> Exists ((__::[]),
      (fun ret_w -> Exists ((__::[]), (fun ret_a ->
      let old_sp =
        wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
          ((snd st0).regs Sp) (frame_len_w vars0 temp_size0)
      in
      And ((__::[]),
      (SepFormula.sepFormula (__::[])
        (starB (__::[])
          (lift (__::[])
            (starB []
              (starB []
                (starB []
                  (InvMake2.is_state old_sp (Obj.magic rp)
                    (Obj.magic e_stack) (Obj.magic e_stack) vars0 (Pair
                    ((Obj.magic vs), (Obj.magic heap1))) (Obj.magic temps))
                  (InvMake2.is_heap (Obj.magic heap2)))
                (InvMake2.layout_option (Obj.magic ret_w) (Obj.magic ret_a)))
              (FreeList.mallocHeap (natToW O))))
          (hvarB (__::[]) (fun x -> Var0 ([], (Obj.magic x))))) st0), (And
      ((__::[]), (Inj (__::[])), (ExistsX ((__::[]), (And ((__::(__::[])),
      (Cptr ((__::(__::[])), (fst (Pair ((Obj.magic rp), stn))), (fun x ->
      Var0 ((__::[]), (Obj.magic x))))), (Forall ((__::(__::[])), (fun st1 ->
      Imply ((__::(__::[])),
      (let st' = Pair ((snd (Pair (rp, stn))), st1) in
       Exists ((__::(__::[])), (fun v' -> Exists ((__::(__::[])),
       (fun temps' -> And ((__::(__::[])),
       (SepFormula.sepFormula (__::(__::[]))
         (starB (__::(__::[]))
           (lift (__::(__::[]))
             (starB []
               (InvMake2.is_state ((snd (Obj.magic st')).regs Sp)
                 (Obj.magic rp) (Obj.magic e_stack) (Obj.magic e_stack) vars0
                 (Obj.magic v') (Obj.magic temps'))
               (FreeList.mallocHeap (natToW O))))
           (hvarB (__::(__::[])) (fun x -> Lift ((__::[]), (Var0 ([],
             (Obj.magic x))))))) (Obj.magic st')), (Inj (__::(__::[]))))))))),
      (let x = Pair ((snd (Pair (rp, stn))), st1) in
       Var0 ((__::[]), (Obj.magic x))))))))))))))))))))))))))))))))))))
  
  (** val compile_expr :
      char list list -> nat -> assert0 LabelMap.t -> char list -> expr0 ->
      nat -> cmd **)
  
  let compile_expr vars0 temp_size0 imports3 modName e n0 =
    compile2 vars0 temp_size0 imports3 modName e n0
  
  (** val compile_exprs :
      char list list -> nat -> assert0 LabelMap.t -> char list -> expr0 list
      -> nat -> nat -> cmd **)
  
  let compile_exprs vars0 temp_size0 imports3 modName es n0 dst =
    compile3 vars0 temp_size0 es n0 dst imports3 modName
  
  (** val compile :
      char list list -> nat -> assert0 LabelMap.t -> char list -> stmt1 ->
      stmt1 -> cmd **)
  
  let compile vars0 temp_size0 imports3 modName =
    cmp vars0 temp_size0 imports3 modName (loop_inv vars0 temp_size0)
      (after_call vars0 temp_size0)
      (compile_expr vars0 temp_size0 imports3 modName)
      (compile_exprs vars0 temp_size0 imports3 modName)
 end

module Coq18_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
  
  module Sem = Coq9_Make(E)
  
  module Properties = Properties(WordMap)
 end

module Coq19_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module U = Coq18_Make(E)(M__2)
  
  (** val is_heap_upd_option :
      E.coq_ADTValue WordMap.t -> WordMap.key -> E.coq_ADTValue option ->
      hProp **)
  
  let is_heap_upd_option h addr0 a =
    U.InvMake2.is_heap (U.Sem.heap_upd_option h addr0 a)
  
  (** val is_heap_merge :
      U.Sem.elt WordMap.t -> U.Sem.elt WordMap.t -> hProp **)
  
  let is_heap_merge h1 h2 =
    U.InvMake2.is_heap (U.Sem.heap_merge h1 h2)
  
  (** val hints_heap_upd_option_subproof :
      type0 list -> functions -> ILAlgoTypes.PACK.SEP.predicates ->
      ILAlgoTypes.coq_AllAlgos_correct **)
  
  let hints_heap_upd_option_subproof =
    failwith "AXIOM TO BE REALIZED"
  
  (** val hints_heap_upd_option : tacPackage **)
  
  let hints_heap_upd_option =
    let types_rV = { footprint = ((Some bedrock_type_W)::((Some
      bedrock_type_setting_X_state)::((Some bedrock_type_state)::((Some
      bedrock_type_reg)::((Some bedrock_type_nat)::((Some
      bedrock_type_listW)::((Some bedrock_type_string)::((Some
      bedrock_type_listString)::((Some bedrock_type_vals)::((Some
      bedrock_type_B)::((Some bedrock_type_listB)::((Some
      default_type)::((Some default_type)::[]))))))))))))); default =
      emptySet_type }
    in
    let funcs_rV = fun ts -> { footprint = ((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType O)::((TvType O)::[])); range = (TvType O);
      denotation =
      (Obj.magic
        (wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))) })::((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wmult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType (S (S O)))::((TvType (S (S (S O))))::[])); range =
      (TvType O); denotation = (Obj.magic regs) })::((Some { domain =
      ((TvType O)::((TvType O)::[])); range = TvProp; denotation =
      (Obj.magic __) })::((Some { domain = ((TvType (S (S (S (S O)))))::[]);
      range = (TvType O); denotation = (Obj.magic natToW) })::((Some
      { domain = ((TvType (S (S (S (S (S O))))))::[]); range = (TvType (S (S
      (S (S O))))); denotation = (Obj.magic length) })::((Some { domain =
      ((TvType (S (S (S (S (S O))))))::((TvType O)::[])); range = (TvType O);
      denotation = (Obj.magic sel) })::((Some { domain = ((TvType (S (S (S (S
      (S O))))))::((TvType O)::((TvType O)::[]))); range = (TvType (S (S (S
      (S (S O)))))); denotation = (Obj.magic upd) })::((Some { domain = [];
      range = (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic []) })::((Some { domain = ((TvType (S (S (S (S (S (S
      O)))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])); range =
      (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic (fun x x0 -> x::x0)) })::((Some { domain = ((TvType (S (S (S
      (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S O)))))))::[]));
      range = (TvType O); denotation = (Obj.magic sel0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S
      O)))))))::((TvType O)::[]))); range = (TvType (S (S (S (S (S (S (S (S
      O))))))))); denotation = (Obj.magic upd0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S O)))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[])); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S O)))))))::[])); range = (TvType (S (S (S (S O)))));
      denotation = (Obj.magic variablePosition) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::[]); range =
      (TvType (S (S (S (S O))))); denotation = (Obj.magic length) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S (S (S (S
      O)))))))))))::((TvType O)::[])); range = (TvType (S (S (S (S (S (S (S
      (S (S O)))))))))); denotation = (Obj.magic sel1) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::((TvType
      O)::((TvType (S (S (S (S (S (S (S (S (S O))))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S (S (S O))))))))))); denotation =
      (Obj.magic upd1) })::((Some { domain = ((TvType (S (S (S (S (S (S (S (S
      (S O))))))))))::[]); range = (TvType O); denotation =
      (Obj.magic btoW) })::((Some { domain = ((TvType O)::[]); range =
      (TvType (S (S (S (S (S (S (S (S (S O)))))))))); denotation =
      (Obj.magic wtoB) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::((Some { domain = ((TvType (S
      (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S (S (S
      O)))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S O))))))))); denotation =
      (Obj.magic merge0) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::[])))))))))))))))))))))))));
      default = (default_signature (repr0 types_rV ts)) }
    in
    let preds_rV = fun ts -> { footprint = ((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType O)::[])); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic (ptsto32 [])) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S O))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::[]))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S O)))))))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array8) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_call) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::[]))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic excessStack) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals_in) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_return) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_out) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S (S (S O)))))))))))))::[]);
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic U.InvMake2.is_heap) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType (S (S (S (S (S (S (S (S (S (S (S O))))))))))))::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic U.InvMake2.layout_option) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S (S (S O)))))))))))))::((TvType O)::((TvType (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))::[])));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic is_heap_upd_option) }))::[])))))))))))); default =
      (SEP.coq_Default_predicate (repr0 types_rV ts) BedrockCoreEnv.pc
        BedrockCoreEnv.st) }
    in
    let env0 = { ILAlgoTypes.PACK.coq_Types = types_rV;
      ILAlgoTypes.PACK.coq_Funcs = funcs_rV; ILAlgoTypes.PACK.coq_Preds =
      (Obj.magic preds_rV) }
    in
    let algos_V = fun ts -> { ILAlgoTypes.coq_Prover = (Some { summarize =
      (fun hyps ->
      Obj.magic (Pair ((Pair
        ((assumptionSummarize
           (types2
             (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
             (tl
               (tl
                 (tl
                   (tl
                     (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
           hyps), Tt)), (Pair
        ((wordSummarize
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           hyps),
        (boundSummarize
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          hyps)))))); learn = (fun facts0 hyps ->
      let Pair (fl, fr) = Obj.magic facts0 in
      Obj.magic (Pair
        ((let Pair (fl0, fr0) = fl in
          Pair
          ((assumptionLearn
             (types2
               (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
               (tl
                 (tl
                   (tl
                     (tl
                       (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
             fl0 hyps), fr0)),
        (let Pair (fl0, fr0) = fr in
         Pair
         ((wordLearn
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            fl0 hyps),
         (boundLearn
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           fr0 hyps)))))); prove = (fun facts0 goal ->
      let Pair (fl, fr) = Obj.magic facts0 in
      if let Pair (fl0, fr0) = fl in
         if assumptionProve
              (types2
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
              fl0 goal
         then true
         else reflexivityProve
                (types2
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
                fr0 goal
      then true
      else let Pair (fl0, fr0) = fr in
           if wordProve
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                fl0 goal
           then true
           else boundProve
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                  fr0 goal) }); ILAlgoTypes.coq_Hints = (Some
      { UNF.coq_Forward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))), ((Var (S
      (S (S (S (S (S O)))))))::((Var (S (S (S (S (S O))))))::((Var (S (S (S
      O))))::((Var (S (S O)))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S O)))), ((Var
        (S (S (S (S (S (S O)))))))::((Var (S (S (S (S O)))))::((Var (S (S (S
        O))))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S
        O)))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S O))))))))))))))))))))), ((Var (S (S (S (S (S (S
      O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S O))))))::((Var (S (S
      (S (S O)))))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S O)))))),
        ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S O))))::((Var (S (S
        O)))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S (S (S
        O)))))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S
        (S (S (S O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)),
        ((Var (S (S (S (S (S O))))))::((Func ((S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))), ((Var (S
        (S (S (S O)))))::((Var O)::((Var (S (S (S (S (S (S (S
        O))))))))::[])))))::((Var (S O))::((Var (S (S O)))::[]))))))))) }::[]));
      UNF.coq_Backward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S
      (S (S (S O))))))::((Var (S (S (S O))))::((Var (S (S O)))::((Var
      O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S
        O))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S (S
        O)))))::((Var (S (S (S O))))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S O)))::((Var O)::[])))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))), ((Var (S (S (S (S
      (S (S O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S O))))))::((Var
      (S (S (S (S O)))))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S
        (S O)))))::((Var (S (S (S O))))::((Var O)::((Var (S O))::[])))))));
      UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S
        O)))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S
        O))))::((Var (S (S O)))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S (S (S O)))))::((Var O)::[])))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S (S (S (S (S (S (S (S O))))))))))))::((TvType
      O)::((TvType (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))::[])));
      UNF.LEM.coq_Hyps = []; UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S (S
        O))))))))), ((Var (S (S O)))::[]))), (ILAlgoTypes.HINTS_REIFY.SE.Func
        ((S (S (S (S (S (S (S (S (S (S O)))))))))), ((Var (S O))::((Var
        O)::[]))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S (S
        (S (S O))))))))))), ((Var (S (S O)))::((Var (S O))::((Var
        O)::[])))))) }::[]))) }); ILAlgoTypes.coq_MemEval = (Some
      (MEVAL.Composite.coq_MemEvaluator_composite
        (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
        (tl
          (tl
            (tl (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
        BedrockCoreEnv.pc BedrockCoreEnv.st
        (MEVAL.Composite.coq_MemEvaluator_composite
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          BedrockCoreEnv.pc BedrockCoreEnv.st
          (MEVAL.Composite.coq_MemEvaluator_composite
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            BedrockCoreEnv.pc BedrockCoreEnv.st
            (Plugin_PtsTo.coq_MemEvaluator_ptsto32
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
            (memEvaluator
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))
          (memEvaluator0
            (types0
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))))
        (memEvaluator1
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))) }
    in
    { ILAlgoTypes.coq_Env = env0; ILAlgoTypes.coq_Algos = algos_V;
    ILAlgoTypes.coq_Algos_correct = hints_heap_upd_option_subproof }
  
  (** val hints_heap_merge_subproof :
      type0 list -> functions -> ILAlgoTypes.PACK.SEP.predicates ->
      ILAlgoTypes.coq_AllAlgos_correct **)
  
  let hints_heap_merge_subproof =
    failwith "AXIOM TO BE REALIZED"
  
  (** val hints_heap_merge : tacPackage **)
  
  let hints_heap_merge =
    let types_rV = { footprint = ((Some bedrock_type_W)::((Some
      bedrock_type_setting_X_state)::((Some bedrock_type_state)::((Some
      bedrock_type_reg)::((Some bedrock_type_nat)::((Some
      bedrock_type_listW)::((Some bedrock_type_string)::((Some
      bedrock_type_listString)::((Some bedrock_type_vals)::((Some
      bedrock_type_B)::((Some bedrock_type_listB)::((Some
      default_type)::[])))))))))))); default = emptySet_type }
    in
    let funcs_rV = fun ts -> { footprint = ((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType O)::((TvType O)::[])); range = (TvType O);
      denotation =
      (Obj.magic
        (wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))) })::((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wmult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType (S (S O)))::((TvType (S (S (S O))))::[])); range =
      (TvType O); denotation = (Obj.magic regs) })::((Some { domain =
      ((TvType O)::((TvType O)::[])); range = TvProp; denotation =
      (Obj.magic __) })::((Some { domain = ((TvType (S (S (S (S O)))))::[]);
      range = (TvType O); denotation = (Obj.magic natToW) })::((Some
      { domain = ((TvType (S (S (S (S (S O))))))::[]); range = (TvType (S (S
      (S (S O))))); denotation = (Obj.magic length) })::((Some { domain =
      ((TvType (S (S (S (S (S O))))))::((TvType O)::[])); range = (TvType O);
      denotation = (Obj.magic sel) })::((Some { domain = ((TvType (S (S (S (S
      (S O))))))::((TvType O)::((TvType O)::[]))); range = (TvType (S (S (S
      (S (S O)))))); denotation = (Obj.magic upd) })::((Some { domain = [];
      range = (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic []) })::((Some { domain = ((TvType (S (S (S (S (S (S
      O)))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])); range =
      (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic (fun x x0 -> x::x0)) })::((Some { domain = ((TvType (S (S (S
      (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S O)))))))::[]));
      range = (TvType O); denotation = (Obj.magic sel0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S
      O)))))))::((TvType O)::[]))); range = (TvType (S (S (S (S (S (S (S (S
      O))))))))); denotation = (Obj.magic upd0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S O)))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[])); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S O)))))))::[])); range = (TvType (S (S (S (S O)))));
      denotation = (Obj.magic variablePosition) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::[]); range =
      (TvType (S (S (S (S O))))); denotation = (Obj.magic length) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S (S (S (S
      O)))))))))))::((TvType O)::[])); range = (TvType (S (S (S (S (S (S (S
      (S (S O)))))))))); denotation = (Obj.magic sel1) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::((TvType
      O)::((TvType (S (S (S (S (S (S (S (S (S O))))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S (S (S O))))))))))); denotation =
      (Obj.magic upd1) })::((Some { domain = ((TvType (S (S (S (S (S (S (S (S
      (S O))))))))))::[]); range = (TvType O); denotation =
      (Obj.magic btoW) })::((Some { domain = ((TvType O)::[]); range =
      (TvType (S (S (S (S (S (S (S (S (S O)))))))))); denotation =
      (Obj.magic wtoB) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::((Some { domain = ((TvType (S
      (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S (S (S
      O)))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S O))))))))); denotation =
      (Obj.magic merge0) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::[])))))))))))))))))))))))));
      default = (default_signature (repr0 types_rV ts)) }
    in
    let preds_rV = fun ts -> { footprint = ((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType O)::[])); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic (ptsto32 [])) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S O))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::[]))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S O)))))))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array8) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_call) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::[]))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic excessStack) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals_in) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_return) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_out) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S (S O))))))))))))::[]);
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic U.InvMake2.is_heap) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S (S O))))))))))))::((TvType (S (S (S (S (S (S (S
        (S (S (S (S O))))))))))))::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic is_heap_merge) }))::[]))))))))))); default =
      (SEP.coq_Default_predicate (repr0 types_rV ts) BedrockCoreEnv.pc
        BedrockCoreEnv.st) }
    in
    let env0 = { ILAlgoTypes.PACK.coq_Types = types_rV;
      ILAlgoTypes.PACK.coq_Funcs = funcs_rV; ILAlgoTypes.PACK.coq_Preds =
      (Obj.magic preds_rV) }
    in
    let algos_V = fun ts -> { ILAlgoTypes.coq_Prover = (Some { summarize =
      (fun hyps ->
      Obj.magic (Pair ((Pair
        ((assumptionSummarize
           (types2
             (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
             (tl
               (tl
                 (tl
                   (tl
                     (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
           hyps), Tt)), (Pair
        ((wordSummarize
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           hyps),
        (boundSummarize
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          hyps)))))); learn = (fun facts0 hyps ->
      let Pair (fl, fr) = Obj.magic facts0 in
      Obj.magic (Pair
        ((let Pair (fl0, fr0) = fl in
          Pair
          ((assumptionLearn
             (types2
               (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
               (tl
                 (tl
                   (tl
                     (tl
                       (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
             fl0 hyps), fr0)),
        (let Pair (fl0, fr0) = fr in
         Pair
         ((wordLearn
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            fl0 hyps),
         (boundLearn
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           fr0 hyps)))))); prove = (fun facts0 goal ->
      let Pair (fl, fr) = Obj.magic facts0 in
      if let Pair (fl0, fr0) = fl in
         if assumptionProve
              (types2
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
              fl0 goal
         then true
         else reflexivityProve
                (types2
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
                fr0 goal
      then true
      else let Pair (fl0, fr0) = fr in
           if wordProve
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                fl0 goal
           then true
           else boundProve
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                  fr0 goal) }); ILAlgoTypes.coq_Hints = (Some
      { UNF.coq_Forward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))), ((Var (S
      (S (S (S (S (S O)))))))::((Var (S (S (S (S (S O))))))::((Var (S (S (S
      O))))::((Var (S (S O)))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S O)))), ((Var
        (S (S (S (S (S (S O)))))))::((Var (S (S (S (S O)))))::((Var (S (S (S
        O))))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S
        O)))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S O))))))))))))))))))))), ((Var (S (S (S (S (S (S
      O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S O))))))::((Var (S (S
      (S (S O)))))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S O)))))),
        ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S O))))::((Var (S (S
        O)))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S (S (S
        O)))))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S
        (S (S (S O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)),
        ((Var (S (S (S (S (S O))))))::((Func ((S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))), ((Var (S
        (S (S (S O)))))::((Var O)::((Var (S (S (S (S (S (S (S
        O))))))))::[])))))::((Var (S O))::((Var (S (S O)))::[]))))))))) }::[]));
      UNF.coq_Backward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S
      (S (S (S O))))))::((Var (S (S (S O))))::((Var (S (S O)))::((Var
      O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S
        O))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S (S
        O)))))::((Var (S (S (S O))))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S O)))::((Var O)::[])))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))), ((Var (S (S (S (S
      (S (S O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S O))))))::((Var
      (S (S (S (S O)))))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S
        (S O)))))::((Var (S (S (S O))))::((Var O)::((Var (S O))::[])))))));
      UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S
        O)))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S
        O))))::((Var (S (S O)))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S (S (S O)))))::((Var O)::[])))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S (S (S (S (S (S (S (S O))))))))))))::((TvType (S (S
      (S (S (S (S (S (S (S (S (S O))))))))))))::[])); UNF.LEM.coq_Hyps = [];
      UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S (S
        O))))))))), ((Var (S O))::[]))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S
        (S (S (S (S (S (S (S (S O))))))))), ((Var O)::[]))))));
      UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S (S
        (S O)))))))))), ((Var (S O))::((Var O)::[]))))) }::[]))) });
      ILAlgoTypes.coq_MemEval = (Some
      (MEVAL.Composite.coq_MemEvaluator_composite
        (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
        (tl
          (tl
            (tl (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
        BedrockCoreEnv.pc BedrockCoreEnv.st
        (MEVAL.Composite.coq_MemEvaluator_composite
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          BedrockCoreEnv.pc BedrockCoreEnv.st
          (MEVAL.Composite.coq_MemEvaluator_composite
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            BedrockCoreEnv.pc BedrockCoreEnv.st
            (Plugin_PtsTo.coq_MemEvaluator_ptsto32
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
            (memEvaluator
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))
          (memEvaluator0
            (types0
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))))
        (memEvaluator1
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))) }
    in
    { ILAlgoTypes.coq_Env = env0; ILAlgoTypes.coq_Algos = algos_V;
    ILAlgoTypes.coq_Algos_correct = hints_heap_merge_subproof }
 end

module Coq20_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
 end

module Coq21_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
 end

module Coq22_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileStmtSpecMake = Coq12_Make(E)(M__2)
  
  module CompileStmtImplMake = Coq17_Make(E)(M__2)
  
  module LayoutHints3Make = Coq19_Make(E)(M__2)
  
  module CompileStmtTacticsMake = Coq16_Make(E)(M__2)
  
  module SemanticsFactsMake = Coq20_Make(E)
  
  module SemanticsFacts3Make = Coq21_Make(E)
 end

module Coq23_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module PostOkMake = Coq22_Make(E)(M__2)
  
  module CompileStmtTacticsMake = Coq16_Make(E)(M__2)
  
  module SemanticsFactsMake = Coq20_Make(E)
 end

module Coq24_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileStmtSpecMake = Coq12_Make(E)(M__2)
  
  module CompileStmtImplMake = Coq17_Make(E)(M__2)
  
  module CompileStmtTacticsMake = Coq16_Make(E)(M__2)
  
  module SemanticsFactsMake = Coq20_Make(E)
 end

module Coq25_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
  
  module P = Properties(WordMap)
  
  (** val hints_heap_empty_bwd_subproof :
      type0 list -> functions -> ILAlgoTypes.PACK.SEP.predicates ->
      ILAlgoTypes.coq_AllAlgos_correct **)
  
  let hints_heap_empty_bwd_subproof =
    failwith "AXIOM TO BE REALIZED"
  
  (** val hints_heap_empty_bwd : tacPackage **)
  
  let hints_heap_empty_bwd =
    let types_rV = { footprint = ((Some bedrock_type_W)::((Some
      bedrock_type_setting_X_state)::((Some bedrock_type_state)::((Some
      bedrock_type_reg)::((Some bedrock_type_nat)::((Some
      bedrock_type_listW)::((Some bedrock_type_string)::((Some
      bedrock_type_listString)::((Some bedrock_type_vals)::((Some
      bedrock_type_B)::((Some bedrock_type_listB)::((Some
      default_type)::[])))))))))))); default = emptySet_type }
    in
    let funcs_rV = fun ts -> { footprint = ((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType O)::((TvType O)::[])); range = (TvType O);
      denotation =
      (Obj.magic
        (wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))) })::((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wmult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType (S (S O)))::((TvType (S (S (S O))))::[])); range =
      (TvType O); denotation = (Obj.magic regs) })::((Some { domain =
      ((TvType O)::((TvType O)::[])); range = TvProp; denotation =
      (Obj.magic __) })::((Some { domain = ((TvType (S (S (S (S O)))))::[]);
      range = (TvType O); denotation = (Obj.magic natToW) })::((Some
      { domain = ((TvType (S (S (S (S (S O))))))::[]); range = (TvType (S (S
      (S (S O))))); denotation = (Obj.magic length) })::((Some { domain =
      ((TvType (S (S (S (S (S O))))))::((TvType O)::[])); range = (TvType O);
      denotation = (Obj.magic sel) })::((Some { domain = ((TvType (S (S (S (S
      (S O))))))::((TvType O)::((TvType O)::[]))); range = (TvType (S (S (S
      (S (S O)))))); denotation = (Obj.magic upd) })::((Some { domain = [];
      range = (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic []) })::((Some { domain = ((TvType (S (S (S (S (S (S
      O)))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])); range =
      (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic (fun x x0 -> x::x0)) })::((Some { domain = ((TvType (S (S (S
      (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S O)))))))::[]));
      range = (TvType O); denotation = (Obj.magic sel0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S
      O)))))))::((TvType O)::[]))); range = (TvType (S (S (S (S (S (S (S (S
      O))))))))); denotation = (Obj.magic upd0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S O)))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[])); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S O)))))))::[])); range = (TvType (S (S (S (S O)))));
      denotation = (Obj.magic variablePosition) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::[]); range =
      (TvType (S (S (S (S O))))); denotation = (Obj.magic length) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S (S (S (S
      O)))))))))))::((TvType O)::[])); range = (TvType (S (S (S (S (S (S (S
      (S (S O)))))))))); denotation = (Obj.magic sel1) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::((TvType
      O)::((TvType (S (S (S (S (S (S (S (S (S O))))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S (S (S O))))))))))); denotation =
      (Obj.magic upd1) })::((Some { domain = ((TvType (S (S (S (S (S (S (S (S
      (S O))))))))))::[]); range = (TvType O); denotation =
      (Obj.magic btoW) })::((Some { domain = ((TvType O)::[]); range =
      (TvType (S (S (S (S (S (S (S (S (S O)))))))))); denotation =
      (Obj.magic wtoB) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::((Some { domain = ((TvType (S
      (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S (S (S
      O)))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S O))))))))); denotation =
      (Obj.magic merge0) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::((Some { domain = []; range =
      (TvType (S (S (S (S (S (S (S (S (S (S (S O)))))))))))); denotation =
      (Obj.magic InvMake.SemanticsMake.heap_empty) })::[]))))))))))))))))))))))))));
      default = (default_signature (repr0 types_rV ts)) }
    in
    let preds_rV = fun ts -> { footprint = ((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType O)::[])); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic (ptsto32 [])) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S O))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::[]))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S O)))))))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array8) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_call) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::[]))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic excessStack) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals_in) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_return) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_out) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S (S O))))))))))))::[]);
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic InvMake2.is_heap) }))::[])))))))))); default =
      (SEP.coq_Default_predicate (repr0 types_rV ts) BedrockCoreEnv.pc
        BedrockCoreEnv.st) }
    in
    let env0 = { ILAlgoTypes.PACK.coq_Types = types_rV;
      ILAlgoTypes.PACK.coq_Funcs = funcs_rV; ILAlgoTypes.PACK.coq_Preds =
      (Obj.magic preds_rV) }
    in
    let algos_V = fun ts -> { ILAlgoTypes.coq_Prover = (Some { summarize =
      (fun hyps ->
      Obj.magic (Pair ((Pair
        ((assumptionSummarize
           (types2
             (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
             (tl
               (tl
                 (tl
                   (tl
                     (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
           hyps), Tt)), (Pair
        ((wordSummarize
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           hyps),
        (boundSummarize
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          hyps)))))); learn = (fun facts0 hyps ->
      let Pair (fl, fr) = Obj.magic facts0 in
      Obj.magic (Pair
        ((let Pair (fl0, fr0) = fl in
          Pair
          ((assumptionLearn
             (types2
               (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
               (tl
                 (tl
                   (tl
                     (tl
                       (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
             fl0 hyps), fr0)),
        (let Pair (fl0, fr0) = fr in
         Pair
         ((wordLearn
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            fl0 hyps),
         (boundLearn
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           fr0 hyps)))))); prove = (fun facts0 goal ->
      let Pair (fl, fr) = Obj.magic facts0 in
      if let Pair (fl0, fr0) = fl in
         if assumptionProve
              (types2
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
              fl0 goal
         then true
         else reflexivityProve
                (types2
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
                fr0 goal
      then true
      else let Pair (fl0, fr0) = fr in
           if wordProve
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                fl0 goal
           then true
           else boundProve
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                  fr0 goal) }); ILAlgoTypes.coq_Hints = (Some
      { UNF.coq_Forward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))), ((Var (S
      (S (S (S (S (S O)))))))::((Var (S (S (S (S (S O))))))::((Var (S (S (S
      O))))::((Var (S (S O)))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S O)))), ((Var
        (S (S (S (S (S (S O)))))))::((Var (S (S (S (S O)))))::((Var (S (S (S
        O))))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S
        O)))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S O))))))))))))))))))))), ((Var (S (S (S (S (S (S
      O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S O))))))::((Var (S (S
      (S (S O)))))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S O)))))),
        ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S O))))::((Var (S (S
        O)))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S (S (S
        O)))))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S
        (S (S (S O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)),
        ((Var (S (S (S (S (S O))))))::((Func ((S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))), ((Var (S
        (S (S (S O)))))::((Var O)::((Var (S (S (S (S (S (S (S
        O))))))))::[])))))::((Var (S O))::((Var (S (S O)))::[]))))))))) }::[]));
      UNF.coq_Backward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S
      (S (S (S O))))))::((Var (S (S (S O))))::((Var (S (S O)))::((Var
      O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S
        O))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S (S
        O)))))::((Var (S (S (S O))))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S O)))::((Var O)::[])))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))), ((Var (S (S (S (S
      (S (S O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S O))))))::((Var
      (S (S (S (S O)))))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S
        (S O)))))::((Var (S (S (S O))))::((Var O)::((Var (S O))::[])))))));
      UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S
        O)))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S
        O))))::((Var (S (S O)))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S (S (S O)))))::((Var O)::[])))))))))) }::({ UNF.LEM.coq_Foralls =
      []; UNF.LEM.coq_Hyps = []; UNF.LEM.coq_Lhs =
      (Obj.magic ILAlgoTypes.HINTS_REIFY.SE.Emp); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S (S
        O))))))))), ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))), []))::[])))) }::[]))) });
      ILAlgoTypes.coq_MemEval = (Some
      (MEVAL.Composite.coq_MemEvaluator_composite
        (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
        (tl
          (tl
            (tl (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
        BedrockCoreEnv.pc BedrockCoreEnv.st
        (MEVAL.Composite.coq_MemEvaluator_composite
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          BedrockCoreEnv.pc BedrockCoreEnv.st
          (MEVAL.Composite.coq_MemEvaluator_composite
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            BedrockCoreEnv.pc BedrockCoreEnv.st
            (Plugin_PtsTo.coq_MemEvaluator_ptsto32
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
            (memEvaluator
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))
          (memEvaluator0
            (types0
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))))
        (memEvaluator1
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))) }
    in
    { ILAlgoTypes.coq_Env = env0; ILAlgoTypes.coq_Algos = algos_V;
    ILAlgoTypes.coq_Algos_correct = hints_heap_empty_bwd_subproof }
 end

module Coq26_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module U = Coq18_Make(E)(M__2)
  
  (** val heap_to_split :
      U.InvMake.SemanticsMake.coq_Heap -> (w, U.Sem.coq_ArgIn) prod list ->
      hProp **)
  
  let heap_to_split h x =
    U.InvMake2.is_heap h
  
  (** val hints_split_heap_subproof :
      type0 list -> functions -> ILAlgoTypes.PACK.SEP.predicates ->
      ILAlgoTypes.coq_AllAlgos_correct **)
  
  let hints_split_heap_subproof =
    failwith "AXIOM TO BE REALIZED"
  
  (** val hints_split_heap : tacPackage **)
  
  let hints_split_heap =
    let types_rV = { footprint = ((Some bedrock_type_W)::((Some
      bedrock_type_setting_X_state)::((Some bedrock_type_state)::((Some
      bedrock_type_reg)::((Some bedrock_type_nat)::((Some
      bedrock_type_listW)::((Some bedrock_type_string)::((Some
      bedrock_type_listString)::((Some bedrock_type_vals)::((Some
      bedrock_type_B)::((Some bedrock_type_listB)::((Some
      default_type)::((Some default_type)::[]))))))))))))); default =
      emptySet_type }
    in
    let funcs_rV = fun ts -> { footprint = ((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wplus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType O)::((TvType O)::[])); range = (TvType O);
      denotation =
      (Obj.magic
        (wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))) })::((Some { domain = ((TvType
      O)::((TvType O)::[])); range = (TvType O); denotation =
      (Obj.magic
        (wmult (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))) })::((Some
      { domain = ((TvType (S (S O)))::((TvType (S (S (S O))))::[])); range =
      (TvType O); denotation = (Obj.magic regs) })::((Some { domain =
      ((TvType O)::((TvType O)::[])); range = TvProp; denotation =
      (Obj.magic __) })::((Some { domain = ((TvType (S (S (S (S O)))))::[]);
      range = (TvType O); denotation = (Obj.magic natToW) })::((Some
      { domain = ((TvType (S (S (S (S (S O))))))::[]); range = (TvType (S (S
      (S (S O))))); denotation = (Obj.magic length) })::((Some { domain =
      ((TvType (S (S (S (S (S O))))))::((TvType O)::[])); range = (TvType O);
      denotation = (Obj.magic sel) })::((Some { domain = ((TvType (S (S (S (S
      (S O))))))::((TvType O)::((TvType O)::[]))); range = (TvType (S (S (S
      (S (S O)))))); denotation = (Obj.magic upd) })::((Some { domain = [];
      range = (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic []) })::((Some { domain = ((TvType (S (S (S (S (S (S
      O)))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])); range =
      (TvType (S (S (S (S (S (S (S O)))))))); denotation =
      (Obj.magic (fun x x0 -> x::x0)) })::((Some { domain = ((TvType (S (S (S
      (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S O)))))))::[]));
      range = (TvType O); denotation = (Obj.magic sel0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S
      O)))))))::((TvType O)::[]))); range = (TvType (S (S (S (S (S (S (S (S
      O))))))))); denotation = (Obj.magic upd0) })::((Some { domain =
      ((TvType (S (S (S (S (S (S O)))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[])); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S O)))))))::[])); range = (TvType (S (S (S (S O)))));
      denotation = (Obj.magic variablePosition) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::[]); range =
      (TvType (S (S (S (S O))))); denotation = (Obj.magic length) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S (S (S (S
      O)))))))))))::((TvType O)::[])); range = (TvType (S (S (S (S (S (S (S
      (S (S O)))))))))); denotation = (Obj.magic sel1) })::((Some { domain =
      ((TvType (S (S (S (S (S (S (S (S (S (S O)))))))))))::((TvType
      O)::((TvType (S (S (S (S (S (S (S (S (S O))))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S (S (S O))))))))))); denotation =
      (Obj.magic upd1) })::((Some { domain = ((TvType (S (S (S (S (S (S (S (S
      (S O))))))))))::[]); range = (TvType O); denotation =
      (Obj.magic btoW) })::((Some { domain = ((TvType O)::[]); range =
      (TvType (S (S (S (S (S (S (S (S (S O)))))))))); denotation =
      (Obj.magic wtoB) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::((Some { domain = ((TvType (S
      (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S (S (S (S (S (S
      O)))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[]))); range =
      (TvType (S (S (S (S (S (S (S (S O))))))))); denotation =
      (Obj.magic merge0) })::((Some { domain = ((TvType (S (S (S (S (S (S (S
      (S (S (S (S (S O)))))))))))))::((TvType (S (S (S (S (S (S (S (S (S (S
      (S O))))))))))))::[])); range = TvProp; denotation =
      (Obj.magic __) })::((Some { domain = ((TvType (S (S (S (S (S (S (S (S
      (S (S (S O))))))))))))::[]); range = (TvType (S (S (S (S (S (S (S (S (S
      (S (S (S O))))))))))))); denotation =
      (Obj.magic U.InvMake.make_heap) })::((Some { domain = ((TvType (S (S (S
      (S (S (S (S (S (S (S (S (S O)))))))))))))::((TvType (S (S (S (S (S (S
      (S (S (S (S (S (S O)))))))))))))::[])); range = (TvType (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))); denotation =
      (Obj.magic U.Sem.heap_diff) })::((Some { domain = ((TvType (S (S (S (S
      (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType
      (S (S (S (S O)))))::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::[]))))); range = TvProp; denotation = (Obj.magic __) })::((Some
      { domain = ((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::[]))))); range =
      TvProp; denotation = (Obj.magic __) })::[]))))))))))))))))))))))))))));
      default = (default_signature (repr0 types_rV ts)) }
    in
    let preds_rV = fun ts -> { footprint = ((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType O)::[])); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic (ptsto32 [])) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S O))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::[]))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S O)))))))))))::((TvType O)::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic array8) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_call) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType
        O)::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::((TvType (S (S (S (S (S (S (S O))))))))::((TvType (S (S (S (S
        O)))))::[]))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic excessStack) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation = (Obj.magic locals_in) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S (S (S O)))))))))))))::((TvType (S (S (S (S (S (S
        (S (S (S (S (S O))))))))))))::[]));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic heap_to_split) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S (S (S (S (S (S O)))))))))))))::[]);
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic U.InvMake2.is_heap) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S O)))))::((TvType (S (S
        (S (S O)))))::[]))))))); ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_return) }))::((Some
      (Obj.magic { ILAlgoTypes.HINTS_REIFY.SE.coq_SDomain = ((TvType (S (S (S
        (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S (S
        O)))))))))::((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S
        (S (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
        O))))))))::((TvType (S (S (S (S O)))))::[])))))));
        ILAlgoTypes.HINTS_REIFY.SE.coq_SDenotation =
        (Obj.magic locals_out) }))::[]))))))))))); default =
      (SEP.coq_Default_predicate (repr0 types_rV ts) BedrockCoreEnv.pc
        BedrockCoreEnv.st) }
    in
    let env0 = { ILAlgoTypes.PACK.coq_Types = types_rV;
      ILAlgoTypes.PACK.coq_Funcs = funcs_rV; ILAlgoTypes.PACK.coq_Preds =
      (Obj.magic preds_rV) }
    in
    let algos_V = fun ts -> { ILAlgoTypes.coq_Prover = (Some { summarize =
      (fun hyps ->
      Obj.magic (Pair ((Pair
        ((assumptionSummarize
           (types2
             (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
             (tl
               (tl
                 (tl
                   (tl
                     (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
           hyps), Tt)), (Pair
        ((wordSummarize
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           hyps),
        (boundSummarize
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          hyps)))))); learn = (fun facts0 hyps ->
      let Pair (fl, fr) = Obj.magic facts0 in
      Obj.magic (Pair
        ((let Pair (fl0, fr0) = fl in
          Pair
          ((assumptionLearn
             (types2
               (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
               (tl
                 (tl
                   (tl
                     (tl
                       (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
             fl0 hyps), fr0)),
        (let Pair (fl0, fr0) = fr in
         Pair
         ((wordLearn
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            fl0 hyps),
         (boundLearn
           (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
           (tl
             (tl
               (tl
                 (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
           fr0 hyps)))))); prove = (fun facts0 goal ->
      let Pair (fl, fr) = Obj.magic facts0 in
      if let Pair (fl0, fr0) = fl in
         if assumptionProve
              (types2
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
              fl0 goal
         then true
         else reflexivityProve
                (types2
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
                fr0 goal
      then true
      else let Pair (fl0, fr0) = fr in
           if wordProve
                (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                (tl
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                fl0 goal
           then true
           else boundProve
                  (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
                  (tl
                    (tl
                      (tl
                        (tl
                          (tl
                            (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
                  fr0 goal) }); ILAlgoTypes.coq_Hints = (Some
      { UNF.coq_Forward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))), ((Var (S
      (S (S (S (S (S O)))))))::((Var (S (S (S (S (S O))))))::((Var (S (S (S
      O))))::((Var (S (S O)))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S O)))), ((Var
        (S (S (S (S (S (S O)))))))::((Var (S (S (S (S O)))))::((Var (S (S (S
        O))))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S
        O)))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S O))))))))))))))))))))), ((Var (S (S (S (S (S (S
      O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S O))))))::((Var (S (S
      (S (S O)))))::((Var O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S O)))))),
        ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S O))))::((Var (S (S
        O)))::((Var (S O))::((Var (S (S (S (S (S O))))))::((Var (S (S (S (S
        O)))))::((Var O)::[])))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S
        (S (S (S O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)),
        ((Var (S (S (S (S (S O))))))::((Func ((S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))), ((Var (S
        (S (S (S O)))))::((Var O)::((Var (S (S (S (S (S (S (S
        O))))))))::[])))))::((Var (S O))::((Var (S (S O)))::[]))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S (S (S (S (S (S (S (S O))))))))))))::((TvType (S (S
      (S (S (S (S (S (S (S (S (S (S O)))))))))))))::[])); UNF.LEM.coq_Hyps =
      ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S O))))))))))))))))))))))), ((Var (S O))::((Var O)::[]))))::[]);
      UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S
        O))))))), ((Var (S O))::((Var O)::[]))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S O)))))))),
        ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S O)))))))))))))))))))))))), ((Var O)::[])))::[]))),
        (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S O)))))))),
        ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S O))))))))))))))))))))))))), ((Var (S O))::((Func ((S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))), ((Var O)::[])))::[]))))::[])))))) }::[])));
      UNF.coq_Backward = ({ UNF.LEM.coq_Foralls = ((TvType (S (S (S (S
      O)))))::((TvType O)::((TvType (S (S (S (S O)))))::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::[]))))))); UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S
      (S (S (S (S O))))))::((Var (S (S (S O))))::((Var (S (S O)))::((Var
      O)::[])))))))::[]); UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S (S O)))))::((Const ((TvType (S (S (S (S
        O))))), (Obj.magic O)))::((Var (S O))::[])))))),
        (ILAlgoTypes.HINTS_REIFY.SE.Exists ((TvType (S (S (S (S (S (S (S (S
        O))))))))), (ILAlgoTypes.HINTS_REIFY.SE.Star
        ((ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S (S (S (S
        O)))))))::((Var O)::((Var (S (S (S O))))::((Func (O, ((Var (S (S
        O)))::((Func ((S (S (S (S (S O))))), ((Var (S
        O))::[])))::[]))))::[])))))), (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S
        (S (S (S O))))), ((Var (S (S O)))::((Var (S (S (S (S (S (S (S
        O))))))))::((Var (S (S (S (S O)))))::((Var (S (S (S (S (S (S
        O)))))))::((Var (S (S (S O))))::[])))))))))))))); UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S (S
        O))))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S (S
        O)))))::((Var (S (S (S O))))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S O)))::((Var O)::[])))))))))) }::({ UNF.LEM.coq_Foralls =
      ((TvType (S (S (S (S O)))))::((TvType O)::((TvType (S (S (S (S
      O)))))::((TvType (S (S (S (S (S (S (S (S O)))))))))::((TvType (S (S (S
      (S (S (S (S O))))))))::((TvType (S (S (S (S (S (S (S
      O))))))))::((TvType (S (S (S (S (S (S (S O))))))))::[])))))));
      UNF.LEM.coq_Hyps = ((Func ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))), ((Var
      (S (S (S (S (S (S O)))))))::((Var (S (S O)))::((Var (S (S (S (S (S
      O))))))::((Var (S (S (S (S O)))))::((Var O)::[])))))))::[]);
      UNF.LEM.coq_Lhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S O)), ((Var (S (S (S
        (S O)))))::((Var (S (S (S O))))::((Var O)::((Var (S O))::[])))))));
      UNF.LEM.coq_Rhs =
      (Obj.magic (ILAlgoTypes.HINTS_REIFY.SE.Func ((S (S (S (S (S (S (S (S (S
        (S O)))))))))), ((Var (S (S (S (S (S (S O)))))))::((Var (S (S (S
        O))))::((Var (S (S O)))::((Var (S O))::((Var (S (S (S (S (S
        O))))))::((Var (S (S (S (S O)))))::((Var O)::[])))))))))) }::[])) });
      ILAlgoTypes.coq_MemEval = (Some
      (MEVAL.Composite.coq_MemEvaluator_composite
        (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
        (tl
          (tl
            (tl (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
        BedrockCoreEnv.pc BedrockCoreEnv.st
        (MEVAL.Composite.coq_MemEvaluator_composite
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
          BedrockCoreEnv.pc BedrockCoreEnv.st
          (MEVAL.Composite.coq_MemEvaluator_composite
            (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
            (tl
              (tl
                (tl
                  (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))
            BedrockCoreEnv.pc BedrockCoreEnv.st
            (Plugin_PtsTo.coq_MemEvaluator_ptsto32
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))
            (memEvaluator
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))
          (memEvaluator0
            (types0
              (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
              (tl
                (tl
                  (tl
                    (tl
                      (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts))))))))))))))))))))))))))
        (memEvaluator1
          (bedrock_type_W::(bedrock_type_setting_X_state::(bedrock_type_state::(bedrock_type_reg::(bedrock_type_nat::(bedrock_type_listW::(bedrock_type_string::(bedrock_type_listString::(bedrock_type_vals::(bedrock_type_B::(bedrock_type_listB::
          (tl
            (tl
              (tl
                (tl (tl (tl (tl (tl (tl (tl (tl (repr0 types_rV ts)))))))))))))))))))))))))) }
    in
    { ILAlgoTypes.coq_Env = env0; ILAlgoTypes.coq_Algos = algos_V;
    ILAlgoTypes.coq_Algos_correct = hints_split_heap_subproof }
 end

module Coq27_Make = 
 functor (E:ADT) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module Properties = Properties(WordMap)
  
  module Facts = Facts(WordMap)
  
  module Make = 
   functor (R:sig 
    type coq_RepInv = w -> E.coq_ADTValue -> hProp
    
    val rep_inv : coq_RepInv
   end) ->
   struct 
    module Inner = InvMake.Make(R)
   end
 end

module Coq28_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileStmtSpecMake = Coq12_Make(E)(M__2)
  
  module CompileStmtImplMake = Coq17_Make(E)(M__2)
  
  module LayoutHintsMake = Coq25_Make(E)(M__2)
  
  module LayoutHints2Make = Coq26_Make(E)(M__2)
  
  module CompileStmtTacticsMake = Coq16_Make(E)(M__2)
  
  module InvFactsMake = Coq27_Make(E)
  
  module Inner = InvFactsMake.Make(M__2)
 end

module Coq29_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module VerifCondOkNonCallMake = Coq23_Make(E)(M__2)
  
  module VerifCondOkNonCall2Make = Coq24_Make(E)(M__2)
  
  module VerifCondOkCallMake = Coq28_Make(E)(M__2)
 end

module Coq30_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module PostOkMake = Coq22_Make(E)(M__2)
  
  module VerifCondOkMake = Coq29_Make(E)(M__2)
  
  (** val compile :
      char list list -> nat -> assert0 LabelMap.t -> char list -> stmt1 ->
      stmt1 -> cmd **)
  
  let compile vars0 temp_size0 imports3 modName s k =
    wrap imports3 modName
      (PostOkMake.CompileStmtImplMake.compile vars0 temp_size0 imports3
        modName s k) (fun x ->
      PostOkMake.CompileStmtSpecMake.postcond vars0 temp_size0 k)
      (PostOkMake.CompileStmtSpecMake.verifCond vars0 temp_size0 s k)
 end

module Coq31_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
 end

type optimizer = stmt1 -> char list -> stmt1

(** val compose : optimizer -> optimizer -> optimizer **)

let compose f0 g s r =
  g (f0 s r) r

module Coq32_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
 end

module Coq33_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileStmtMake = Coq30_Make(E)(M__2)
  
  module CompileFuncSpecMake = Coq14_Make(E)(M__2)
  
  module CompileStmtTacticsMake = Coq16_Make(E)(M__2)
  
  module SemanticsFacts2Make = Coq31_Make(E)
  
  module GoodFuncMake = Coq13_Make(E)
  
  module GoodOptimizerMake = Coq32_Make(E)
  
  (** val body_stmt : func0 -> optimizer -> stmt1 **)
  
  let body_stmt func1 optimizer1 =
    optimizer1 func1.core0.body1 func1.core0.retVar1
  
  (** val local_vars : func0 -> optimizer -> StringSet.elt list **)
  
  let local_vars func1 optimizer1 =
    get_local_vars (body_stmt func1 optimizer1) func1.core0.argVars1
      func1.core0.retVar1
  
  (** val vars : func0 -> optimizer -> char list list **)
  
  let vars func1 optimizer1 =
    app func1.core0.argVars1 (local_vars func1 optimizer1)
  
  (** val temp_size : func0 -> optimizer -> nat **)
  
  let temp_size func1 optimizer1 =
    depth0 (body_stmt func1 optimizer1)
  
  (** val stack_slot : nat -> lvalue **)
  
  let stack_slot n0 =
    LvMem (Indir (Sp, (natToW (mult (S (S (S (S O)))) n0))))
  
  (** val vars_start : nat **)
  
  let vars_start =
    S (S (S (S (S (S (S (S O)))))))
  
  (** val var_slot : func0 -> optimizer -> char list -> lvalue **)
  
  let var_slot func1 optimizer1 x =
    LvMem (Indir (Sp,
      (natToW (plus vars_start (variablePosition (vars func1 optimizer1) x)))))
  
  (** val coq_Seq2 : char list -> assert0 LabelMap.t -> cmd -> cmd -> cmd **)
  
  let coq_Seq2 module_name imports3 =
    seq_ imports3 module_name
  
  (** val coq_Skip : char list -> assert0 LabelMap.t -> cmd **)
  
  let coq_Skip module_name imports3 =
    skip_ imports3 module_name
  
  (** val coq_Seq : char list -> assert0 LabelMap.t -> cmd list -> cmd **)
  
  let rec coq_Seq module_name imports3 = function
  | [] -> coq_Skip module_name imports3
  | a::ls' ->
    coq_Seq2 module_name imports3 a (coq_Seq module_name imports3 ls')
  
  (** val coq_Strline :
      char list -> assert0 LabelMap.t -> instr list -> cmd **)
  
  let coq_Strline module_name imports3 =
    straightline_ imports3 module_name
  
  (** val coq_CheckExtraStack :
      char list -> assert0 LabelMap.t -> nat -> cmd -> cmd **)
  
  let coq_CheckExtraStack module_name imports3 n0 cmd0 =
    coq_Seq2 module_name imports3
      (coq_Strline module_name imports3 ((Assign ((LvReg Rv), (RvLval
        (stack_slot (S O)))))::[]))
      (if_ imports3 module_name (RvImm (natToW n0)) Le (RvLval (LvReg Rv))
        cmd0 (diverge_ imports3 module_name))
  
  (** val compile_stmt :
      func0 -> char list -> optimizer -> assert0 LabelMap.t -> stmt1 -> cmd **)
  
  let compile_stmt func1 module_name optimizer1 imports3 s =
    CompileStmtMake.compile (vars func1 optimizer1)
      (temp_size func1 optimizer1) imports3 module_name s Skip1
  
  (** val len_local_vars : func0 -> optimizer -> nat **)
  
  let len_local_vars func1 optimizer1 =
    length (local_vars func1 optimizer1)
  
  (** val body' :
      func0 -> char list -> optimizer -> assert0 LabelMap.t -> cmd **)
  
  let body' func1 module_name optimizer1 imports3 =
    let stack_needed =
      plus (len_local_vars func1 optimizer1) (temp_size func1 optimizer1)
    in
    coq_CheckExtraStack module_name imports3 stack_needed
      (coq_Seq module_name imports3
        ((coq_Strline module_name imports3 ((Binop ((stack_slot (S O)),
           (RvLval (stack_slot (S O))), Minus, (RvImm
           (natToW stack_needed))))::((Assign ((stack_slot O), (RvLval (LvReg
           Rp))))::[])))::((compile_stmt func1 module_name optimizer1
                             imports3 (body_stmt func1 optimizer1))::(
        (coq_Strline module_name imports3 ((Assign ((LvReg Rv), (RvLval
          (var_slot func1 optimizer1 func1.core0.retVar1))))::((Assign
          ((LvReg Rp), (RvLval (stack_slot O))))::[])))::((iGoto imports3
                                                            module_name
                                                            (RvLval (LvReg
                                                            Rp)))::[])))))
  
  (** val body :
      func0 -> char list -> optimizer -> assert0 LabelMap.t -> cmd **)
  
  let body func1 module_name optimizer1 imports3 =
    wrap imports3 module_name (body' func1 module_name optimizer1 imports3)
      (fun pre ->
      (body' func1 module_name optimizer1 imports3 pre).postcondition)
      (CompileFuncSpecMake.verifCond func1.core0)
 end

module Coq34_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileFuncImplMake = Coq33_Make(E)(M__2)
  
  (** val body :
      char list -> func0 -> optimizer -> assert0 LabelMap.t -> cmd **)
  
  let body module_name func1 optimizer1 imports3 cin =
    CompileFuncImplMake.body func1 module_name optimizer1 imports3 cin
  
  (** val compile : char list -> func0 -> optimizer -> function0 **)
  
  let compile module_name func1 optimizer1 =
    Pair ((Pair (func1.name,
      (CompileFuncImplMake.CompileFuncSpecMake.spec func1.core0))),
      (fun x _ -> body module_name func1 optimizer1 x))
 end

module Coq35_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileFuncMake = Coq34_Make(E)(M__2)
  
  (** val imports : import list **)
  
  let imports =
    []
  
  (** val mod_name : goodModule -> char list **)
  
  let mod_name module1 =
    impl_module_name module1.name0
  
  (** val compile_func' : goodModule -> optimizer -> func0 -> function0 **)
  
  let compile_func' module1 optimizer1 f0 =
    CompileFuncMake.compile (mod_name module1) f0 optimizer1
  
  (** val compile_func :
      goodModule -> optimizer -> goodFunction -> function0 **)
  
  let compile_func module1 optimizer1 f0 =
    compile_func' module1 optimizer1 (fun1 f0)
  
  (** val compiled_funcs : goodModule -> optimizer -> function0 list **)
  
  let compiled_funcs module1 optimizer1 =
    map (compile_func module1 optimizer1) module1.functions1
  
  (** val compile : goodModule -> optimizer -> module0 **)
  
  let compile module1 optimizer1 =
    bmodule_ imports (mod_name module1) (compiled_funcs module1 optimizer1)
 end

module Coq36_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileModuleMake = Coq35_Make(E)(M__2)
  
  module LinkSpecMake = Coq15_Make(E)
  
  module LinkSpecMake2 = LinkSpecMake.Make(M__2)
  
  module SS = StringSet
  
  (** val coq_FName : func0 -> char list **)
  
  let coq_FName =
    name
  
  (** val coq_MName : goodModule -> char list **)
  
  let coq_MName =
    name0
  
  (** val dummy : module0 **)
  
  let dummy =
    bmodule_ [] [] []
  
  (** val link_all : module0 list -> module0 **)
  
  let link_all ls =
    fold_right_2 link dummy ls
  
  (** val compile : optimizer -> goodModule -> module0 **)
  
  let compile optimizer1 m6 =
    CompileModuleMake.compile m6 optimizer1
  
  (** val impl_MName : goodModule -> char list **)
  
  let impl_MName m6 =
    impl_module_name (coq_MName m6)
  
  (** val ms : goodModule list -> optimizer -> module0 list **)
  
  let ms modules0 optimizer1 =
    map (compile optimizer1) modules0
  
  (** val m : goodModule list -> optimizer -> module0 **)
  
  let m modules0 optimizer1 =
    link_all (ms modules0 optimizer1)
 end

module Coq37_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module CompileFuncSpecMake = Coq14_Make(E)(M__2)
  
  module LinkSpecMake = Coq15_Make(E)
  
  module LinkSpecMake2 = LinkSpecMake.Make(M__2)
  
  module SS = StringSet
  
  (** val accessible_labels :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> Coq0_M.key list **)
  
  let accessible_labels modules0 imports3 =
    app (keys (Obj.magic imports3))
      (keys (LinkSpecMake.exports_IFS modules0))
  
  (** val func_spec_IFS :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> glabel -> internalFuncSpec -> assert0 **)
  
  let func_spec_IFS modules0 imports3 id spec1 =
    LinkSpecMake2.func_spec modules0 imports3 id (fun0 spec1)
  
  (** val bimports_base :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> import list **)
  
  let bimports_base modules0 imports3 =
    app
      (GLabelMap.elements
        (GLabelMap.mapi LinkSpecMake2.foreign_func_spec imports3))
      (GLabelMap.elements
        (GLabelMap.mapi (func_spec_IFS modules0 imports3)
          (Obj.magic (LinkSpecMake.exports_IFS modules0))))
  
  (** val get_module_Imports :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> assert0 Coq0_M.t **)
  
  let get_module_Imports modules0 imports3 m6 =
    UWFacts.WFacts.P.diff
      (UWFacts.WFacts.P.update
        (UWFacts.WFacts.P.update (LinkSpecMake2.exports modules0 imports3)
          (Obj.magic (LinkSpecMake2.imports imports3)))
        (LinkSpecMake2.module_impl_exports m6))
      (LinkSpecMake2.module_exports modules0 imports3 m6)
  
  (** val mod_name : goodModule -> char list **)
  
  let mod_name m6 =
    m6.name0
  
  (** val tgt : goodModule -> goodFunction -> glabel **)
  
  let tgt m6 f0 =
    LinkSpecMake2.impl_label (mod_name m6) (fun1 f0).name
  
  (** val body :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> goodFunction -> assert0 LabelMap.t -> cmd **)
  
  let body modules0 imports3 m6 f0 im =
    seq_ im (mod_name m6)
      (assertStar_ im (mod_name m6) (accessible_labels modules0 imports3)
        (LinkSpecMake2.CompileFuncSpecMake.spec (fun1 f0).core0))
      (goto_ im (mod_name m6) (to_bedrock_label (tgt m6 f0)))
  
  (** val make_stub :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> goodFunction -> function0 **)
  
  let make_stub modules0 imports3 m6 f0 =
    Pair ((Pair ((fun1 f0).name,
      (LinkSpecMake2.func_spec modules0 imports3 (Pair (m6.name0,
        (fun1 f0).name)) (fun1 f0).core0))), (fun x _ ->
      body modules0 imports3 m6 f0 x))
  
  (** val bimports :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> import list **)
  
  let bimports modules0 imports3 m6 =
    app (bimports_base modules0 imports3)
      (map (LinkSpecMake2.func_impl_export m6) m6.functions1)
  
  (** val stubs :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> function0 list **)
  
  let stubs modules0 imports3 m6 =
    map (make_stub modules0 imports3 m6) m6.functions1
  
  (** val bexports :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> import list **)
  
  let bexports modules0 imports3 m6 =
    map (func_to_import m6.name0) (stubs modules0 imports3 m6)
  
  (** val bimports_diff_bexports :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> (Coq0_M.key, assert0) prod list **)
  
  let bimports_diff_bexports modules0 imports3 m6 =
    diff_map (bimports modules0 imports3 m6) (bexports modules0 imports3 m6)
  
  (** val make_module :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> module0 **)
  
  let make_module modules0 imports3 m6 =
    bmodule_ (bimports_diff_bexports modules0 imports3 m6) m6.name0
      (stubs modules0 imports3 m6)
  
  (** val full_imports :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> goodModule -> assert0 LabelMap.t **)
  
  let full_imports modules0 imports3 m6 =
    fullImports (bimports_diff_bexports modules0 imports3 m6) m6.name0
      (stubs modules0 imports3 m6)
  
  (** val get_module_exports_map :
      goodModule -> internalFuncSpec Coq0_M.t **)
  
  let get_module_exports_map m6 =
    of_list1 (LinkSpecMake.module_exports_IFS m6)
  
  (** val proj_imply1 : __ list -> ('a1, 'a2) propX -> ('a1, 'a2) propX **)
  
  let proj_imply1 g = function
  | Imply (g0, p1, p0) -> p1
  | x -> x
  
  (** val proj_and1 : __ list -> ('a1, 'a2) propX -> ('a1, 'a2) propX **)
  
  let proj_and1 g = function
  | And (g0, p1, p0) -> p1
  | x -> x
  
  (** val unexX :
      __ list -> ('a1, 'a2) propX -> (__, __ -> ('a1, 'a2) propX) sigT **)
  
  let unexX g = function
  | Inj g0 -> ExistT (__, (fun x -> Inj g0))
  | Cptr (g0, y, p0) -> ExistT (__, (fun x -> Inj g0))
  | And (g0, p0, p1) -> ExistT (__, (fun x -> Inj g0))
  | Or (g0, p0, p1) -> ExistT (__, (fun x -> Inj g0))
  | Imply (g0, p0, p1) -> ExistT (__, (fun x -> Inj g0))
  | Forall (g0, p0) -> ExistT (__, (fun x -> Inj g0))
  | Exists (g0, p1) -> ExistT (__, p1)
  | Var0 (g0, p0) -> ExistT (__, (fun x -> Inj (__::g0)))
  | Lift (g0, p0) -> ExistT (__, (fun x -> Inj (__::g0)))
  | ForallX (g0, p0) -> ExistT (__, (fun x -> Inj g0))
  | ExistsX (g0, p0) -> ExistT (__, (fun x -> Inj g0))
 end

module Coq38_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module StubMake = Coq37_Make(E)(M__2)
  
  module LinkSpecMake = Coq15_Make(E)
  
  module LinkSpecMake2 = LinkSpecMake.Make(M__2)
  
  module SS = StringSet
  
  (** val final_imports :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> assert0 Coq0_M.t **)
  
  let final_imports modules0 imports3 =
    UWFacts.WFacts.P.update (Obj.magic (LinkSpecMake2.imports imports3))
      (LinkSpecMake2.impl_exports modules0)
  
  (** val dummy : module0 **)
  
  let dummy =
    bmodule_ [] [] []
  
  (** val link_all : module0 list -> module0 **)
  
  let link_all ls =
    fold_right_2 link dummy ls
  
  (** val ms :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> module0 list **)
  
  let ms modules0 imports3 =
    map (StubMake.make_module modules0 imports3) modules0
  
  (** val m :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> module0 **)
  
  let m modules0 imports3 =
    link_all (ms modules0 imports3)
 end

module Coq39_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module LinkModuleImplsMake = Coq36_Make(E)(M__2)
  
  module StubsMake = Coq38_Make(E)(M__2)
  
  module GoodOptimizerMake = Coq32_Make(E)
  
  module LinkSpecMake = Coq15_Make(E)
  
  module LinkSpecMake2 = LinkSpecMake.Make(M__2)
  
  module SS = StringSet
  
  (** val impls : goodModule list -> optimizer -> module0 **)
  
  let impls modules0 optimizer1 =
    LinkModuleImplsMake.m modules0 optimizer1
  
  (** val stubs :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> module0 **)
  
  let stubs modules0 imports3 =
    StubsMake.m modules0 imports3
  
  (** val result :
      goodModule list -> LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec
      GLabelMap.t -> optimizer -> module0 **)
  
  let result modules0 imports3 optimizer1 =
    link (impls modules0 optimizer1) (stubs modules0 imports3)
 end

module Coq40_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
  
  module LinkMake = Coq39_Make(E)(M__2)
  
  (** val wrapper_module :
      char list -> import list -> (((char list,
      LinkMake.StubsMake.StubMake.LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec)
      prod, nat) prod, label) prod list -> module0 **)
  
  let wrapper_module mname impls0 fs0 =
    bmodule_ impls0 mname
      (map (fun p ->
        let Pair (p0, delegate) = p in
        let Pair (p1, n0) = p0 in
        let Pair (name1, ffs) = p1 in
        Pair ((Pair (name1,
        (LinkMake.StubsMake.StubMake.LinkSpecMake2.foreign_func_spec (Pair
          (mname, name1)) ffs))), (fun im _ ->
        if_ im mname (RvLval (LvMem (Indir (Sp,
          (natToW (S (S (S (S O))))))))) Lt0 (RvImm (natToW n0))
          (goto_ im mname
            (labl ('s'::('y'::('s'::[])))
              ('a'::('b'::('o'::('r'::('t'::[])))))))
          (goto_ im mname delegate)))) fs0)
  
  (** val zip_vals :
      char list list -> (w,
      LinkMake.StubsMake.StubMake.LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.coq_ArgIn)
      prod list -> vals **)
  
  let rec zip_vals args pairs =
    match args with
    | [] -> empty_vs
    | arg::args0 ->
      (match pairs with
       | [] -> empty_vs
       | p::pairs0 ->
         let Pair (w0, a) = p in upd0 (zip_vals args0 pairs0) arg w0)
  
  module Hints = Coq27_Make(E)
  
  module Inner = Hints.Make(M__2)
  
  module Properties = Properties(WordMap)
  
  module Facts = Facts(WordMap)
 end

module SS = StringSet

(** val const_dec : expr0 -> w sumor **)

let const_dec =
  failwith "AXIOM TO BE REALIZED"

(** val const_zero_dec : expr0 -> bool **)

let const_zero_dec =
  failwith "AXIOM TO BE REALIZED"

type sET = SS.t

type map0 = w StringMap.t

(** val empty_set : SS.t **)

let empty_set =
  SS.empty

(** val empty_map : w StringMap.t **)

let empty_map =
  StringMap.empty

(** val subtract : 'a1 M.t -> SS.t -> 'a1 M.t **)

let subtract m6 s =
  filter0 (fun k x -> negb (SS.mem k s)) m6

(** val const_folding_expr : expr0 -> map0 -> expr0 **)

let rec const_folding_expr e env0 = e
  (*match e with
  | Var1 var0 ->
    (match option_dec (StringMap.find var0 env0) with
     | Inleft s -> Const0 s
     | Inright -> e)
  | Const0 w0 -> e
  | Binop0 (op, a, b0) ->
    let a' = const_folding_expr a env0 in
    let b' = const_folding_expr b0 env0 in
    (match const_dec a' with
     | Inleft s ->
       (match const_dec b' with
        | Inleft s0 -> Const0 (evalBinop op s s0)
        | Inright -> Binop0 (op, a', b'))
     | Inright -> Binop0 (op, a', b'))
  | TestE (op, a, b0) ->
    let a' = const_folding_expr a env0 in
    let b' = const_folding_expr b0 env0 in
    (match const_dec a' with
     | Inleft s ->
       (match const_dec b' with
        | Inleft s0 ->
          Const0
            (if evalTest op s s0
             then natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) (S O)
             else natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) O)
        | Inright -> TestE (op, a', b'))
     | Inright -> TestE (op, a', b'))*)

(** val const_folding : stmt1 -> map0 -> ((stmt1, map0) prod, sET) prod **)

let rec const_folding s map1 = Pair (Pair (s, map1), empty_set)
  (*match s with
  | Skip1 -> Pair ((Pair (Skip1, map1)), empty_set)
  | Seq1 (a, b0) ->
    let result_a = const_folding a map1 in
    let map' = snd (fst result_a) in
    let result_b = const_folding b0 map' in
    let a' = fst (fst result_a) in
    let b' = fst (fst result_b) in
    let map'' = snd (fst result_b) in
    let written_a = snd result_a in
    let written_b = snd result_b in
    Pair ((Pair ((Seq1 (a', b')), map'')), (SS.union written_a written_b))
  | If1 (c, t0, f0) ->
    let c' = const_folding_expr c map1 in
    (match const_dec c' with
     | Inleft s0 ->
       if wneb s0
            (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) O)
       then const_folding t0 map1
       else const_folding f0 map1
     | Inright ->
       let result_t = const_folding t0 map1 in
       let result_f = const_folding f0 map1 in
       let t' = fst (fst result_t) in
       let f' = fst (fst result_f) in
       let written_t = snd result_t in
       let written_f = snd result_f in
       let map' = subtract (subtract (Obj.magic map1) written_t) written_f in
       Pair ((Pair ((If1 (c', t', f')), (Obj.magic map'))),
       (SS.union written_t written_f)))
  | While1 (c, b0) ->
    if const_zero_dec (const_folding_expr c map1)
    then Pair ((Pair (Skip1, map1)), empty_set)
    else let c' = const_folding_expr c StringMap.empty in
         let result_b = const_folding b0 StringMap.empty in
         let b' = fst (fst result_b) in
         let written_b = snd result_b in
         let map' = subtract (Obj.magic map1) written_b in
         Pair ((Pair ((While1 (c', b')), (Obj.magic map'))), written_b)
  | Call1 (x, f0, args) ->
    let f' = const_folding_expr f0 map1 in
    let args' = map (fun e -> const_folding_expr e map1) args in
    (match x with
     | Some s0 ->
       let map3 = StringMap.remove s0 map1 in
       Pair ((Pair ((Call1 (x, f', args')), map3)), (SS.singleton s0))
     | None -> Pair ((Pair ((Call1 (x, f', args')), map1)), empty_set))
  | Label0 (x, l) ->
    let map3 = StringMap.remove x map1 in
    Pair ((Pair (s, map3)), (SS.singleton x))
  | Assign2 (x, e) ->
    let e' = const_folding_expr e map1 in
    (match const_dec e' with
     | Inleft s0 ->
       let map' = StringMap.add x s0 map1 in
       Pair ((Pair ((Assign2 (x, (Const0 s0))), map')), (SS.singleton x))
     | Inright ->
       let map' = StringMap.remove x map1 in
       Pair ((Pair ((Assign2 (x, e')), map')), (SS.singleton x)))*)

(** val constant_folding : stmt1 -> stmt1 **)

let constant_folding s =
  fst (fst (const_folding s empty_map))

(** val optimizer0 : stmt1 -> stmt1 **)

let optimizer0 =
  constant_folding

(** val opt : optimizer **)

let opt s x =
  optimizer0 s

module Coq41_Make = 
 functor (E:ADT) ->
 struct 
  module GoodOptimizerMake = Coq32_Make(E)
 end

type sET0 = StringSet.t

(** val used_vars : expr0 -> StringSet.t **)

let rec used_vars = function
| Var1 x -> StringSet.singleton x
| Const0 w0 -> StringSet.empty
| Binop0 (b0, a, b1) -> StringSet.union (used_vars a) (used_vars b1)
| TestE (t0, a, b0) -> StringSet.union (used_vars a) (used_vars b0)

(** val used_vars_stmt : stmt1 -> StringSet.t **)

let rec used_vars_stmt = function
| Seq1 (a, b0) -> StringSet.union (used_vars_stmt a) (used_vars_stmt b0)
| If1 (e, t0, f0) ->
  StringSet.union (StringSet.union (used_vars e) (used_vars_stmt t0))
    (used_vars_stmt f0)
| While1 (e, body5) -> StringSet.union (used_vars e) (used_vars_stmt body5)
| Call1 (o, f0, args) ->
  StringSet.union (used_vars f0) (union_list0 (map used_vars args))
| Assign2 (s0, e) -> used_vars e
| _ -> StringSet.empty

(** val elim_dead : stmt1 -> sET0 -> (stmt1, sET0) prod **)

let rec elim_dead s used = Pair (s, used)
  (*match s with
  | Skip1 -> Pair (s, used)
  | Seq1 (a, b0) ->
    let result0 = elim_dead b0 used in
    let b1 = fst result0 in
    let used0 = snd result0 in
    let result1 = elim_dead a used0 in
    let a0 = fst result1 in
    let used1 = snd result1 in Pair ((Seq1 (a0, b1)), used1)
  | If1 (e, t0, f0) ->
    let result0 = elim_dead t0 used in
    let t1 = fst result0 in
    let used_t = snd result0 in
    let result1 = elim_dead f0 used in
    let f1 = fst result1 in
    let used_f = snd result1 in
    Pair ((If1 (e, t1, f1)),
    (StringSet.union (StringSet.union (used_vars e) used_t) used_f))
  | While1 (e, body5) ->
    let result0 =
      elim_dead body5
        (StringSet.union (StringSet.union used (used_vars e))
          (used_vars_stmt body5))
    in
    let body6 = fst result0 in
    let used' = snd result0 in
    Pair ((While1 (e, body6)),
    (StringSet.union (StringSet.union used used') (used_vars e)))
  | Call1 (x, f0, args) ->
    Pair (s,
      (StringSet.union
        (StringSet.union
          (StringSet.diff used
            (default0 StringSet.empty (option_map StringSet.singleton x)))
          (used_vars f0)) (union_list0 (map used_vars args))))
  | Label0 (x, g) -> Pair (s, (StringSet.diff used (StringSet.singleton x)))
  | Assign2 (x, e) ->
    if in_dec0 x (Obj.magic used)
    then Pair (s,
           (StringSet.union (StringSet.diff used (StringSet.singleton x))
             (used_vars e)))
    else Pair (Skip1, used)*)

(** val opt0 : stmt1 -> StringSet.elt -> stmt1 **)

let opt0 s retvar =
  fst (elim_dead s (StringSet.singleton retvar))

module Coq42_Make = 
 functor (E:ADT) ->
 struct 
  module GoodOptimizerMake = Coq32_Make(E)
 end

module Coq43_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
  
  (** val to_bool : bool -> bool **)
  
  let to_bool = function
  | true -> true
  | false -> false
  
  (** val coq_GoodToLink_bool :
      goodModule list -> SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
      bool **)
  
  let coq_GoodToLink_bool modules0 imports3 =
    let imported_module_names =
      map (fun x -> fst (fst x)) (GLabelMap.elements imports3)
    in
    let module_names = map name0 modules0 in
    if if if negb (sumbool_to_bool0 (zerop (length modules0)))
          then is_no_dup module_names
          else false
       then forallb (fun s ->
              negb (sumbool_to_bool0 (in_dec string_dec s module_names)))
              imported_module_names
       else false
    then forallb is_good_module_name imported_module_names
    else false
 end

(** val f : func0 **)

let f =
  { name =
    ('r'::('e'::('t'::('u'::('r'::('n'::('_'::('z'::('e'::('r'::('o'::[])))))))))));
    core0 = { argVars1 = []; retVar1 = ('r'::('e'::('t'::[]))); body1 =
    (Assign2 (('r'::('e'::('t'::[]))), (Const0 (natToW O)))) } }

module Coq44_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module LinkSpecMake = Coq15_Make(E)
  
  module LinkSpecMake2 = LinkSpecMake.Make(M__2)
  
  module Made = Coq40_Make(E)(M__2)
  
  (** val opt : optimizer **)
  
  let opt =
    compose opt opt0
  
  module GoodOptimizerMake = Coq32_Make(E)
  
  module ConstFoldingMake = Coq41_Make(E)
  
  module ElimDeadMake = Coq42_Make(E)
  
  module LinkMake = Coq39_Make(E)(M__2)
  
  (** val link_with_adts :
      goodModule list ->
      LinkMake.LinkSpecMake.SemanticsMake.coq_ForeignFuncSpec GLabelMap.t ->
      module0 **)
  
  let link_with_adts modules0 imports3 =
    LinkMake.result modules0 imports3 opt
  
  module LinkFactsMake = Coq43_Make(E)
 end

module Coq45_Make = 
 functor (E:ADT) ->
 struct 
  module SemanticsMake = Coq9_Make(E)
 end

module Coq46_Make = 
 functor (E:ADT) ->
 struct 
  module TransitMake = Coq45_Make(E)
  
  module SemanticsMake = Coq9_Make(E)
  
  type coq_Specs = SemanticsMake.coq_Callee GLabelMap.t
  
  (** val f_var : char list **)
  
  let f_var =
    '_'::('f'::[])
  
  type entailment = __
  
  type coq_StmtEx =
  | SkipEx
  | SeqEx of coq_StmtEx * coq_StmtEx
  | IfEx of expr0 * coq_StmtEx * coq_StmtEx
  | WhileEx of expr0 * coq_StmtEx
  | AssignEx of char list * expr0
  | AssertEx
  | DCallEx of char list option * glabel * expr0 list
  
  (** val coq_StmtEx_rect :
      'a1 -> (coq_StmtEx -> 'a1 -> coq_StmtEx -> 'a1 -> 'a1) -> (expr0 ->
      coq_StmtEx -> 'a1 -> coq_StmtEx -> 'a1 -> 'a1) -> (__ -> expr0 ->
      coq_StmtEx -> 'a1 -> 'a1) -> (char list -> expr0 -> 'a1) -> (__ -> 'a1)
      -> (char list option -> glabel -> expr0 list -> 'a1) -> coq_StmtEx ->
      'a1 **)
  
  let rec coq_StmtEx_rect f0 f1 f2 f3 f4 f5 f6 = function
  | SkipEx -> f0
  | SeqEx (s0, s1) ->
    f1 s0 (coq_StmtEx_rect f0 f1 f2 f3 f4 f5 f6 s0) s1
      (coq_StmtEx_rect f0 f1 f2 f3 f4 f5 f6 s1)
  | IfEx (e, s0, s1) ->
    f2 e s0 (coq_StmtEx_rect f0 f1 f2 f3 f4 f5 f6 s0) s1
      (coq_StmtEx_rect f0 f1 f2 f3 f4 f5 f6 s1)
  | WhileEx (e, s0) -> f3 __ e s0 (coq_StmtEx_rect f0 f1 f2 f3 f4 f5 f6 s0)
  | AssignEx (s0, e) -> f4 s0 e
  | AssertEx -> f5 __
  | DCallEx (o, g, l) -> f6 o g l
  
  (** val coq_StmtEx_rec :
      'a1 -> (coq_StmtEx -> 'a1 -> coq_StmtEx -> 'a1 -> 'a1) -> (expr0 ->
      coq_StmtEx -> 'a1 -> coq_StmtEx -> 'a1 -> 'a1) -> (__ -> expr0 ->
      coq_StmtEx -> 'a1 -> 'a1) -> (char list -> expr0 -> 'a1) -> (__ -> 'a1)
      -> (char list option -> glabel -> expr0 list -> 'a1) -> coq_StmtEx ->
      'a1 **)
  
  let rec coq_StmtEx_rec f0 f1 f2 f3 f4 f5 f6 = function
  | SkipEx -> f0
  | SeqEx (s0, s1) ->
    f1 s0 (coq_StmtEx_rec f0 f1 f2 f3 f4 f5 f6 s0) s1
      (coq_StmtEx_rec f0 f1 f2 f3 f4 f5 f6 s1)
  | IfEx (e, s0, s1) ->
    f2 e s0 (coq_StmtEx_rec f0 f1 f2 f3 f4 f5 f6 s0) s1
      (coq_StmtEx_rec f0 f1 f2 f3 f4 f5 f6 s1)
  | WhileEx (e, s0) -> f3 __ e s0 (coq_StmtEx_rec f0 f1 f2 f3 f4 f5 f6 s0)
  | AssignEx (s0, e) -> f4 s0 e
  | AssertEx -> f5 __
  | DCallEx (o, g, l) -> f6 o g l
  
  (** val to_stmt : coq_StmtEx -> stmt1 **)
  
  let rec to_stmt = function
  | SeqEx (a, b0) -> Seq1 ((to_stmt a), (to_stmt b0))
  | IfEx (e, t0, f0) -> If1 (e, (to_stmt t0), (to_stmt f0))
  | WhileEx (e, b0) -> While1 (e, (to_stmt b0))
  | AssignEx (x, e) -> Assign2 (x, e)
  | DCallEx (x, f0, args) ->
    Seq1 ((Label0 (f_var, f0)), (Call1 (x, (Var1 f_var), args)))
  | _ -> Skip1
  
  (** val vc : coq_StmtEx -> entailment list **)
  
  let rec vc = function
  | SeqEx (a, b0) -> app (vc a) (vc b0)
  | IfEx (e, t0, f0) -> app (vc t0) (vc f0)
  | WhileEx (e, body5) -> __::(__::(vc body5))
  | AssertEx -> __::[]
  | DCallEx (x, f0, args) -> __::[]
  | _ -> []
  
  type coq_Env =
    (glabel -> w option, w -> SemanticsMake.coq_Callee option) prod
 end

module Coq47_Make = 
 functor (E:ADT) ->
 struct 
  module LinkSpecMake = Coq15_Make(E)
  
  module ProgramLogicMake = Coq46_Make(E)
 end

module Coq48_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
  
  (** val compileS : spec0 **)
  
  let compileS =
    let vars0 =
      ('a'::('r'::('g'::('1'::[]))))::(('a'::('r'::('g'::('2'::[]))))::[])
    in
    let n' =
      plus (S (S (S (S (S (S O)))))) (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S O))))))))))))))))))))
    in
    { reserved0 = n'; formals = vars0; precondition = (fun extras ->
    match extras with
    | Some extras0 ->
      let a = true in
      let b0 = fun w0 -> w0 in
      let d = minus n' (minus (length extras0) (length vars0)) in
      (fun e -> Exists ([], (fun v1 -> Exists ([], (fun v2 -> Exists ([],
      (fun h ->
      localsInvariant (fun v x -> Body
        (starB [] (starB [] (InvMake2.is_heap (Obj.magic h)) (injB []))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Quant (fun h' ->
        Body
        (starB [] (starB [] (InvMake2.is_heap (Obj.magic h')) (injB []))
          (FreeList.mallocHeap (natToW O))))) a b0 extras0 d e)))))))
    | None ->
      let a = false in
      let b0 = fun w0 -> w0 in
      (fun e -> Exists ([], (fun v1 -> Exists ([], (fun v2 -> Exists ([],
      (fun h ->
      localsInvariant (fun v x -> Body
        (starB [] (starB [] (InvMake2.is_heap (Obj.magic h)) (injB []))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Quant (fun h' ->
        Body
        (starB [] (starB [] (InvMake2.is_heap (Obj.magic h')) (injB []))
          (FreeList.mallocHeap (natToW O))))) a b0 vars0 n' e)))))))) }
  
  type coq_CompileOut = { bedrock_module : module0;
                          bedrock_module_impl : module0 }
  
  (** val coq_CompileOut_rect :
      (module0 -> __ -> __ -> module0 -> __ -> 'a1) -> coq_CompileOut -> 'a1 **)
  
  let coq_CompileOut_rect f0 c =
    let { bedrock_module = x; bedrock_module_impl = x0 } = c in
    f0 x __ __ x0 __
  
  (** val coq_CompileOut_rec :
      (module0 -> __ -> __ -> module0 -> __ -> 'a1) -> coq_CompileOut -> 'a1 **)
  
  let coq_CompileOut_rec f0 c =
    let { bedrock_module = x; bedrock_module_impl = x0 } = c in
    f0 x __ __ x0 __
  
  (** val bedrock_module : coq_CompileOut -> module0 **)
  
  let bedrock_module c =
    c.bedrock_module
  
  (** val bedrock_module_impl : coq_CompileOut -> module0 **)
  
  let bedrock_module_impl c =
    c.bedrock_module_impl
 end

type dFFun =
  operationalSpec0
  (* singleton inductive, whose constructor was Build_DFFun *)

(** val core2 : dFFun -> operationalSpec0 **)

let core2 d =
  d

type 'aDTValue dFModule = { imports2 : 'aDTValue axiomaticSpec GLabelMap.t;
                            funs : dFFun StringMap.t }

(** val imports2 : 'a1 dFModule -> 'a1 axiomaticSpec GLabelMap.t **)

let imports2 x = x.imports2

(** val funs : 'a1 dFModule -> dFFun StringMap.t **)

let funs x = x.funs

type cFun =
  funcCore
  (* singleton inductive, whose constructor was Build_CFun *)

(** val core3 : cFun -> funcCore **)

let core3 c =
  c

type cModule =
  cFun StringMap.t
  (* singleton inductive, whose constructor was Build_CModule *)

(** val funs0 : cModule -> cFun StringMap.t **)

let funs0 c =
  c

(** val cfun_to_gfun : char list -> cFun -> goodFunction **)

let cfun_to_gfun name1 f0 =
  { name = name1; core0 = (core3 f0) }

(** val cfuns_to_gfuns : cFun StringMap.t -> goodFunction list **)

let cfuns_to_gfuns fs0 =
  map (uncurry0 cfun_to_gfun) (StringMap.elements fs0)

(** val cmodule_to_gmodule : char list -> cModule -> goodModule **)

let cmodule_to_gmodule name1 m6 =
  { name0 = name1; functions1 = (cfuns_to_gfuns (funs0 m6)) }

(** val compile_func0 : fFunction -> cFun **)

let compile_func0 f0 =
  fun0 (compile_op0 (core1 f0))

(** val compile_to_cmodule : 'a1 fModule -> cModule **)

let compile_to_cmodule module1 =
  StringMap.map compile_func0 module1.functions0

(** val compile_to_gmodule : 'a1 fModule -> char list -> goodModule **)

let compile_to_gmodule module1 name1 =
  cmodule_to_gmodule name1 (compile_to_cmodule module1)

(** val compile_func1 : dFFun -> fFunction **)

let compile_func1 f0 =
  compile_op (core2 f0)

(** val compile_to_fmodule : 'a1 dFModule -> 'a1 fModule **)

let compile_to_fmodule module1 =
  { imports0 = module1.imports2; functions0 =
    (StringMap.map compile_func1 module1.funs) }

(** val compile_to_gmodule0 : 'a1 dFModule -> char list -> goodModule **)

let compile_to_gmodule0 module1 name1 =
  compile_to_gmodule (compile_to_fmodule module1) name1

module Coq49_Make = 
 functor (E:ADT) ->
 functor (M__2:sig 
  type coq_RepInv = w -> E.coq_ADTValue -> hProp
  
  val rep_inv : coq_RepInv
 end) ->
 struct 
  module MakeWrapperMake = Coq44_Make(E)(M__2)
  
  module LinkSpecFactsMake = Coq47_Make(E)
  
  module InvMake = Coq11_Make(E)
  
  module InvMake2 = InvMake.Make(M__2)
  
  module LinkFactsMake = Coq43_Make(E)
  
  module CompileOutMake = Coq48_Make(E)(M__2)
  
  (** val core : E.coq_ADTValue compileUnit -> operationalSpec0 **)
  
  let core compile_unit =
    { argVars0 =
      (('a'::('r'::('g'::('1'::[]))))::(('a'::('r'::('g'::('2'::[]))))::[]));
      retVar0 = ('r'::('e'::('t'::[]))); body0 = compile_unit.prog }
  
  (** val coq_function : E.coq_ADTValue compileUnit -> dFFun **)
  
  let coq_function compile_unit =
    core compile_unit
  
  (** val coq_module :
      E.coq_ADTValue compileUnit -> E.coq_ADTValue dFModule **)
  
  let coq_module compile_unit =
    { imports2 = compile_unit.imports1; funs =
      (StringMap.add ('d'::('f'::('f'::('u'::('n'::[])))))
        (coq_function compile_unit) StringMap.empty) }
  
  (** val good_module : E.coq_ADTValue compileUnit -> goodModule **)
  
  let good_module compile_unit =
    compile_to_gmodule0 (coq_module compile_unit)
      ('d'::('f'::('m'::('o'::('d'::('u'::('l'::('e'::[]))))))))
  
  (** val modules : E.coq_ADTValue compileUnit -> goodModule list **)
  
  let modules compile_unit =
    (good_module compile_unit)::[]
  
  (** val dummy_gf : goodFunction **)
  
  let dummy_gf =
    to_good_function f
  
  (** val spec_op : E.coq_ADTValue compileUnit -> goodFunction **)
  
  let spec_op compile_unit =
    hd dummy_gf (good_module compile_unit).functions1
  
  (** val make_heap' :
      (w, InvMake.SemanticsMake.coq_ArgIn) prod list ->
      InvMake.SemanticsMake.coq_Heap **)
  
  let make_heap' = failwith "GOSH!"
    (*fold_right (fun x m6 -> InvMake.store_pair m6 x) WordMap.empty*)
  
  (** val output_module : E.coq_ADTValue compileUnit -> module0 **)
  
  let output_module compile_unit =
    bmodule_0 ((Pair ((Pair
      (('d'::('f'::('m'::('o'::('d'::('u'::('l'::('e'::[])))))))),
      ('d'::('f'::('f'::('u'::('n'::[]))))))),
      (MakeWrapperMake.LinkSpecMake2.func_spec (modules compile_unit)
        compile_unit.imports1 (Pair
        (('d'::('f'::('m'::('o'::('d'::('u'::('l'::('e'::[])))))))),
        ('d'::('f'::('f'::('u'::('n'::[])))))))
        (fun1 (spec_op compile_unit)).core0)))::[])
      ('e'::('x'::('p'::('o'::('r'::('t'::[]))))))
      ((let vars0 =
          ('a'::('r'::('g'::('1'::[]))))::(('a'::('r'::('g'::('2'::[]))))::(('R'::[])::[]))
        in
        let b' =
          seq
            (call_0 (Some (variableSlot ('R'::[])))
              (labl
                ('d'::('f'::('m'::('o'::('d'::('u'::('l'::('e'::[]))))))))
                ('d'::('f'::('f'::('u'::('n'::[]))))))
              ((immInR
                 (natToW (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S O))))))))))))))))))))))::((lvalIn
                                                        (variableSlot
                                                          ('a'::('r'::('g'::('1'::[]))))))::(
              (lvalIn (variableSlot ('a'::('r'::('g'::('2'::[]))))))::[])))
              (let inv0 =
                 localsInvariant (fun x r -> Body (empB [])) (fun x r r' ->
                   Body (injB []))
               in
               fun ns ->
               inv0 true (fun w0 ->
                 wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O)))))))))))))))))))))))))))))))) w0
                   (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                     O))))))))))))))))))))))))))))))))
                     (plus (S (S (S (S O))))
                       (mult (S (S (S (S O)))) (length ns))))) ns))
            (seq
              (assign' (regInL Rv) (Rvalue
                (lvalIn (variableSlot ('R'::[])))))
              (seq
                (assign' (regInL Rp) (Rvalue
                  (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                (goto (lvalIn (regInL Rp)))))
        in
        { fName = ('d'::('f'::('f'::('u'::('n'::[]))))); fVars = vars0;
        fReserved = CompileOutMake.compileS.reserved0; fPrecondition =
        (CompileOutMake.compileS.precondition None); fBody =
        (seq
          (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
            (lvalIn (regInL Rp))))
          (seq (fun x x0 -> Structured ([], (fun im mn _ ->
            assert_ im mn (CompileOutMake.compileS.precondition (Some vars0)))))
            (fun ns res ->
            b' ns
              (minus res
                (minus (length vars0)
                  (length CompileOutMake.compileS.formals)))))) })::[])
  
  (** val compile :
      E.coq_ADTValue compileUnit -> CompileOutMake.coq_CompileOut **)
  
  let compile compile_unit =
    { CompileOutMake.bedrock_module = (output_module compile_unit);
      CompileOutMake.bedrock_module_impl =
      (MakeWrapperMake.link_with_adts (modules compile_unit)
        compile_unit.imports1) }
  
  module LinkUnfoldHelp = 
   struct 
    
   end
 end

(** val newS : (__ -> w -> hProp) -> nat -> spec0 **)

let newS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::[]
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    localsInvariant (fun x x0 -> Body (FreeList.mallocHeap (natToW O)))
      (fun x x0 r -> Body
      (starB [] (p __ r) (FreeList.mallocHeap (natToW O)))) true (fun w0 ->
      w0) extras0 (minus res (minus (length extras0) (length vars0)))
  | None ->
    localsInvariant (fun x x0 -> Body (FreeList.mallocHeap (natToW O)))
      (fun x x0 r -> Body
      (starB [] (p __ r) (FreeList.mallocHeap (natToW O)))) false (fun w0 ->
      w0) vars0 res) }

(** val deleteS : (__ -> w -> hProp) -> nat -> spec0 **)

let deleteS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a b0 extras0 d
        e))))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a b0 vars0 res
        e))))) }

(** val memS : (__ -> w -> hProp) -> nat -> spec0 **)

let memS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::[]))
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e))))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e))))) }

(** val addS : (__ -> w -> hProp) -> nat -> spec0 **)

let addS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::[]))
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e))))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e))))) }

(** val removeS : (__ -> w -> hProp) -> nat -> spec0 **)

let removeS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::[]))
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e))))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e))))) }

(** val sizeS : (__ -> w -> hProp) -> nat -> spec0 **)

let sizeS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e))))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([],
    (Obj.magic (fun _ ->
      localsInvariant (fun v x -> Body
        (starB [] (p __ (v ('s'::('e'::('l'::('f'::[]))))))
          (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
        (starB []
          (starB [] (injB []) (p __ (v ('s'::('e'::('l'::('f'::[])))))))
          (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e))))) }

module type Coq_ADT = 
 sig 
  val lset : w -> hProp
  
  val lset' : nat -> w -> hProp
 end

module Coq_Adt = 
 struct 
  (** val lset' : nat -> w -> hProp **)
  
  let rec lset' n0 p =
    match n0 with
    | O -> starB [] (injB []) (injB [])
    | S n' ->
      starB [] (starB [] (injB []) (injB []))
        (exB [] (fun x ->
          starB [] (injB [])
            (exB [] (fun p' ->
              starB [] (ptsto32m [] p O (x::(p'::[]))) (lset' n' p')))))
  
  (** val lset : w -> hProp **)
  
  let lset c =
    starB [] (starB [] (injB []) (injB []))
      (exB [] (fun p ->
        exB [] (fun junk ->
          starB [] (ptsto32m [] c O (p::(junk::[])))
            (exB [] (fun n0 -> lset' n0 p)))))
 end

(** val newS0 : spec0 **)

let newS0 =
  newS (fun _ -> Coq_Adt.lset) (S (S (S (S (S (S (S (S O))))))))

(** val deleteS0 : spec0 **)

let deleteS0 =
  deleteS (fun _ -> Coq_Adt.lset) (S (S (S (S (S (S (S O)))))))

(** val memS0 : spec0 **)

let memS0 =
  memS (fun _ -> Coq_Adt.lset) (S O)

(** val addS0 : spec0 **)

let addS0 =
  addS (fun _ -> Coq_Adt.lset) (S (S (S (S (S (S (S (S (S O)))))))))

(** val removeS0 : spec0 **)

let removeS0 =
  removeS (fun _ -> Coq_Adt.lset) (S (S (S (S (S (S (S O)))))))

(** val sizeS0 : spec0 **)

let sizeS0 =
  sizeS (fun _ -> Coq_Adt.lset) (S O)

(** val m0 : module0 **)

let m0 =
  bmodule_0
    ((let x = 'm'::('a'::('l'::('l'::('o'::('c'::[]))))) in
      let y = 'm'::('a'::('l'::('l'::('o'::('c'::[]))))) in
      Pair ((Pair (x, y)), (mallocS.precondition None)))::((let x =
                                                              'm'::('a'::('l'::('l'::('o'::('c'::[])))))
                                                            in
                                                            let y =
                                                              'f'::('r'::('e'::('e'::[])))
                                                            in
                                                            Pair ((Pair (x,
                                                            y)),
                                                            (freeS.precondition
                                                              None)))::[]))
    ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
    ((let vars0 =
        ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('x'::[])::[])
      in
      let b' =
        seq
          (call_0 (Some (variableSlot ('x'::[])))
            (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
              ('m'::('a'::('l'::('l'::('o'::('c'::[])))))))
            ((immInR (natToW O))::((immInR (natToW (S (S O))))::[]))
            (let inv0 =
               localsInvariant (fun x r -> Body
                 (starB []
                   (starB [] (starB [] (allocated r O (S (S O))) (injB []))
                     (injB [])) (FreeList.mallocHeap (natToW O))))
                 (fun x r r' -> Body
                 (starB [] (Coq_Adt.lset r')
                   (FreeList.mallocHeap (natToW O))))
             in
             fun ns ->
             inv0 true (fun w0 ->
               wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))) w0
                 (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O))))))))))))))))))))))))))))))))
                   (plus (S (S (S (S O))))
                     (mult (S (S (S (S O)))) (length ns))))) ns))
          (seq
            (seq
              (assign' (regInL Rv) (Rvalue
                (lvalIn (variableSlot ('x'::[])))))
              (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                (immInR (natToW O)))))
            (seq
              (assign' (regInL Rv) (Rvalue
                (lvalIn (variableSlot ('x'::[])))))
              (seq
                (assign' (regInL Rp) (Rvalue
                  (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                (goto (lvalIn (regInL Rp))))))
      in
      { fName = ('n'::('e'::('w'::[]))); fVars = vars0; fReserved =
      newS0.reserved0; fPrecondition = (newS0.precondition None); fBody =
      (seq
        (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
          (lvalIn (regInL Rp))))
        (seq (fun x x0 -> Structured ([], (fun im mn _ ->
          assert_ im mn (newS0.precondition (Some vars0))))) (fun ns res ->
          b' ns (minus res (minus (length vars0) (length newS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('l'::('s'::[]))::[]))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('l'::('s'::[]))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (call_0 None
             (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
               ('f'::('r'::('e'::('e'::[])))))
             ((immInR (natToW O))::((lvalIn
                                      (variableSlot
                                        ('s'::('e'::('l'::('f'::[]))))))::(
             (immInR (natToW (S (S O))))::[])))
             (let inv0 = fun a b0 c d e -> Exists ([],
                (Obj.magic (fun _ -> Exists ([], (fun n0 ->
                  localsInvariant (fun v x -> Body
                    (starB []
                      (Coq_Adt.lset' (Obj.magic n0) (v ('l'::('s'::[]))))
                      (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
                    (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a
                    b0 c d e)))))
              in
              fun ns ->
              inv0 true (fun w0 ->
                wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))) w0
                  (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O))))))))))))))))))))))))))))))))
                    (plus (S (S (S (S O))))
                      (mult (S (S (S (S O)))) (length ns))))) ns))
           (seq
             (while_0
               (let a = true in
                let b0 = fun w0 -> w0 in
                (fun c d e -> Exists ([],
                (Obj.magic (fun _ -> Exists ([], (fun n0 ->
                  localsInvariant (fun v x -> Body
                    (starB []
                      (Coq_Adt.lset' (Obj.magic n0) (v ('l'::('s'::[]))))
                      (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
                    (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a
                    b0 c d e))))))) { cOperand1 =
               (lvalIn (variableSlot ('l'::('s'::[])))); cTest = Ne;
               cOperand2 = (immInR (natToW O)) }
               (seq
                 (seq
                   (assign' (regInL Rv) (Bop
                     ((lvalIn (variableSlot ('l'::('s'::[])))), Plus,
                     (immInR (natToW (S (S (S (S O)))))))))
                   (assign' (variableSlot ('s'::('e'::('l'::('f'::[])))))
                     (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                 (seq
                   (call_0 None
                     (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
                       ('f'::('r'::('e'::('e'::[])))))
                     ((immInR (natToW O))::((lvalIn
                                              (variableSlot ('l'::('s'::[]))))::(
                     (immInR (natToW (S (S O))))::[])))
                     (let inv0 = fun a b0 c d e -> Exists ([],
                        (Obj.magic (fun _ -> Exists ([], (fun n0 ->
                          localsInvariant (fun v x -> Body
                            (starB []
                              (Coq_Adt.lset' (Obj.magic n0)
                                (v ('s'::('e'::('l'::('f'::[]))))))
                              (FreeList.mallocHeap (natToW O))))
                            (fun v x r -> Body
                            (starB [] (injB [])
                              (FreeList.mallocHeap (natToW O)))) a b0 c d e)))))
                      in
                      fun ns ->
                      inv0 true (fun w0 ->
                        wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          O)))))))))))))))))))))))))))))))) w0
                          (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S O))))))))))))))))))))))))))))))))
                            (plus (S (S (S (S O))))
                              (mult (S (S (S (S O)))) (length ns))))) ns))
                   (assign' (variableSlot ('l'::('s'::[]))) (Rvalue
                     (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[])))))))))))
             (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
               (seq
                 (assign' (regInL Rp) (Rvalue
                   (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                 (goto (lvalIn (regInL Rp)))))))
     in
     { fName = ('d'::('e'::('l'::('e'::('t'::('e'::[])))))); fVars = vars0;
     fReserved = deleteS0.reserved0; fPrecondition =
     (deleteS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (deleteS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length deleteS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::(('t'::('m'::('p'::[])))::[])))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('s'::('e'::('l'::('f'::[]))))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (while_0
             (let a = true in
              let b0 = fun w0 -> w0 in
              (fun c d e -> Exists ([],
              (Obj.magic (fun _ -> Exists ([], (fun n0 ->
                localsInvariant (fun v x -> Body
                  (Coq_Adt.lset' (Obj.magic n0)
                    (v ('s'::('e'::('l'::('f'::[]))))))) (fun v x r -> Body
                  (starB []
                    (Coq_Adt.lset' (Obj.magic n0)
                      (v ('s'::('e'::('l'::('f'::[])))))) (injB []))) a b0 c
                  d e))))))) { cOperand1 =
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[])))))); cTest =
             Ne; cOperand2 = (immInR (natToW O)) }
             (seq
               (seq
                 (assign' (regInL Rv) (Rvalue
                   (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                 (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
                   (lvalIn (fun x -> LvMem (Reg Rv))))))
               (if_0 { cOperand1 =
                 (lvalIn (variableSlot ('t'::('m'::('p'::[]))))); cTest =
                 Eq0; cOperand2 = (lvalIn (variableSlot ('n'::[]))) }
                 (seq (assign' (regInL Rv) (Rvalue (immInR (natToW (S O)))))
                   (seq
                     (assign' (regInL Rp) (Rvalue
                       (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                     (goto (lvalIn (regInL Rp)))))
                 (seq
                   (assign' (regInL Rv) (Bop
                     ((lvalIn (variableSlot ('s'::('e'::('l'::('f'::[])))))),
                     Plus, (immInR (natToW (S (S (S (S O)))))))))
                   (assign' (variableSlot ('s'::('e'::('l'::('f'::[])))))
                     (Rvalue (lvalIn (fun x -> LvMem (Reg Rv)))))))))
           (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
             (seq
               (assign' (regInL Rp) (Rvalue
                 (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
               (goto (lvalIn (regInL Rp))))))
     in
     { fName = ('m'::('e'::('m'::[]))); fVars = vars0; fReserved =
     memS0.reserved0; fPrecondition = (memS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (memS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length memS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::(('t'::('m'::('p'::[])))::[])))
     in
     let b' =
       seq
         (call_0 (Some (variableSlot ('t'::('m'::('p'::[])))))
           (labl ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
             ('m'::('e'::('m'::[]))))
           ((lvalIn
              (variableSlot
                ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))))::(
           (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))::((lvalIn
                                                                    (variableSlot
                                                                    ('n'::[])))::[])))
           (let inv0 = fun a b0 c d e -> Exists ([],
              (Obj.magic (fun _ ->
                localsInvariant (fun v r -> Body
                  (starB []
                    (starB [] (injB [])
                      (Coq_Adt.lset (v ('s'::('e'::('l'::('f'::[])))))))
                    (FreeList.mallocHeap (natToW O)))) (fun v r r' -> Body
                  (starB []
                    (starB [] (injB [])
                      (Coq_Adt.lset (v ('s'::('e'::('l'::('f'::[])))))))
                    (FreeList.mallocHeap (natToW O)))) a b0 c d e)))
            in
            fun ns ->
            inv0 true (fun w0 ->
              wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))) w0
                (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O))))))))))))))))))))))))))))))))
                  (plus (S (S (S (S O))))
                    (mult (S (S (S (S O)))) (length ns))))) ns))
         (if_0 { cOperand1 = (lvalIn (variableSlot ('t'::('m'::('p'::[])))));
           cTest = Eq0; cOperand2 = (immInR (natToW (S O))) }
           (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
             (seq
               (assign' (regInL Rp) (Rvalue
                 (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
               (goto (lvalIn (regInL Rp)))))
           (seq
             (call_0 (Some (variableSlot ('t'::('m'::('p'::[])))))
               (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
                 ('m'::('a'::('l'::('l'::('o'::('c'::[])))))))
               ((immInR (natToW O))::((immInR (natToW (S (S O))))::[]))
               (let inv0 = fun a b0 c d e -> Exists ([],
                  (Obj.magic (fun _ ->
                    localsInvariant (fun v r -> Body
                      (starB []
                        (starB []
                          (starB []
                            (starB [] (allocated r O (S (S O))) (injB []))
                            (injB [])) (injB []))
                        (Coq_Adt.lset (v ('s'::('e'::('l'::('f'::[]))))))))
                      (fun v r r' -> Body
                      (starB [] (injB [])
                        (Coq_Adt.lset (v ('s'::('e'::('l'::('f'::[])))))))) a
                      b0 c d e)))
                in
                fun ns ->
                inv0 true (fun w0 ->
                  wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))) w0
                    (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      O))))))))))))))))))))))))))))))))
                      (plus (S (S (S (S O))))
                        (mult (S (S (S (S O)))) (length ns))))) ns))
             (seq
               (seq
                 (assign' (regInL Rv) (Rvalue
                   (lvalIn (variableSlot ('t'::('m'::('p'::[])))))))
                 (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                   (lvalIn (variableSlot ('n'::[]))))))
               (seq
                 (seq
                   (assign' (regInL Rv) (Rvalue
                     (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                   (assign' (variableSlot ('n'::[])) (Rvalue
                     (lvalIn (fun x -> LvMem (Reg Rv))))))
                 (seq
                   (seq
                     (assign' (regInL Rv) (Bop
                       ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))),
                       Plus, (immInR (natToW (S (S (S (S O)))))))))
                     (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                       (lvalIn (variableSlot ('n'::[]))))))
                   (seq
                     (seq
                       (assign' (regInL Rv) (Rvalue
                         (lvalIn
                           (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                       (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                         (lvalIn (variableSlot ('t'::('m'::('p'::[]))))))))
                     (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
                       (seq
                         (assign' (regInL Rp) (Rvalue
                           (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                         (goto (lvalIn (regInL Rp)))))))))))
     in
     { fName = ('a'::('d'::('d'::[]))); fVars = vars0; fReserved =
     addS0.reserved0; fPrecondition = (addS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (addS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length addS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::(('t'::('m'::('p'::[])))::[])))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (while_0
             (let a = true in
              let b0 = fun w0 -> w0 in
              (fun c d e -> Exists ([],
              (Obj.magic (fun _ -> Exists ([], (fun n0 ->
                localsInvariant (fun v x -> Body
                  (starB []
                    (starB []
                      (ptsto32 [] (v ('s'::('e'::('l'::('f'::[])))))
                        (v ('t'::('m'::('p'::[])))))
                      (Coq_Adt.lset' (Obj.magic n0)
                        (v ('t'::('m'::('p'::[]))))))
                    (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
                  (starB [] (injB [])
                    (exB [] (fun p ->
                      exB [] (fun n' ->
                        starB []
                          (starB []
                            (ptsto32 [] (v ('s'::('e'::('l'::('f'::[]))))) p)
                            (Coq_Adt.lset' n' p))
                          (FreeList.mallocHeap (natToW O))))))) a b0 c d e)))))))
             { cOperand1 = (lvalIn (variableSlot ('t'::('m'::('p'::[])))));
             cTest = Ne; cOperand2 = (immInR (natToW O)) }
             (seq
               (seq
                 (assign' (regInL Rv) (Rvalue
                   (lvalIn (variableSlot ('t'::('m'::('p'::[])))))))
                 (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
                   (lvalIn (fun x -> LvMem (Reg Rv))))))
               (if_0 { cOperand1 =
                 (lvalIn (variableSlot ('t'::('m'::('p'::[]))))); cTest =
                 Eq0; cOperand2 = (lvalIn (variableSlot ('n'::[]))) }
                 (seq
                   (seq
                     (assign' (regInL Rv) (Rvalue
                       (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                     (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
                       (lvalIn (fun x -> LvMem (Reg Rv))))))
                   (seq
                     (seq
                       (assign' (regInL Rv) (Bop
                         ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))),
                         Plus, (immInR (natToW (S (S (S (S O)))))))))
                       (assign' (variableSlot ('n'::[])) (Rvalue
                         (lvalIn (fun x -> LvMem (Reg Rv))))))
                     (seq
                       (seq
                         (assign' (regInL Rv) (Rvalue
                           (lvalIn
                             (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                         (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                           (lvalIn (variableSlot ('n'::[]))))))
                       (seq
                         (call_0 None
                           (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
                             ('f'::('r'::('e'::('e'::[])))))
                           ((immInR (natToW O))::((lvalIn
                                                    (variableSlot
                                                      ('t'::('m'::('p'::[])))))::(
                           (immInR (natToW (S (S O))))::[])))
                           (let inv0 =
                              localsInvariant (fun x x0 -> Body (empB []))
                                (fun x x0 r -> Body (injB []))
                            in
                            fun ns ->
                            inv0 true (fun w0 ->
                              wminus (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S O))))))))))))))))))))))))))))))))
                                w0
                                (natToWord (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S
                                  O))))))))))))))))))))))))))))))))
                                  (plus (S (S (S (S O))))
                                    (mult (S (S (S (S O)))) (length ns)))))
                              ns))
                         (seq
                           (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
                           (seq
                             (assign' (regInL Rp) (Rvalue
                               (lvalIn (fun x -> LvMem (Indir (Sp,
                                 (natToW O)))))))
                             (goto (lvalIn (regInL Rp)))))))))
                 (seq
                   (seq
                     (assign' (regInL Rv) (Rvalue
                       (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                     (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
                       (lvalIn (fun x -> LvMem (Reg Rv))))))
                   (seq
                     (assign' (variableSlot ('s'::('e'::('l'::('f'::[])))))
                       (Bop ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))),
                       Plus, (immInR (natToW (S (S (S (S O)))))))))
                     (seq
                       (assign' (regInL Rv) (Rvalue
                         (lvalIn
                           (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                       (assign' (variableSlot ('t'::('m'::('p'::[]))))
                         (Rvalue (lvalIn (fun x -> LvMem (Reg Rv)))))))))))
           (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
             (seq
               (assign' (regInL Rp) (Rvalue
                 (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
               (goto (lvalIn (regInL Rp))))))
     in
     { fName = ('r'::('e'::('m'::('o'::('v'::('e'::[])))))); fVars = vars0;
     fReserved = removeS0.reserved0; fPrecondition =
     (removeS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (removeS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length removeS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('a'::('c'::('c'::[])))::[]))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('s'::('e'::('l'::('f'::[]))))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (assign' (variableSlot ('a'::('c'::('c'::[])))) (Rvalue
             (immInR (natToW O))))
           (seq
             (while_0
               (let a = true in
                let b0 = fun w0 -> w0 in
                (fun c d e -> Exists ([],
                (Obj.magic (fun _ -> Exists ([], (fun n0 ->
                  localsInvariant (fun v x -> Body
                    (Coq_Adt.lset' (Obj.magic n0)
                      (v ('s'::('e'::('l'::('f'::[]))))))) (fun v x r -> Body
                    (starB []
                      (Coq_Adt.lset' (Obj.magic n0)
                        (v ('s'::('e'::('l'::('f'::[])))))) (injB []))) a b0
                    c d e))))))) { cOperand1 =
               (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))));
               cTest = Ne; cOperand2 = (immInR (natToW O)) }
               (seq
                 (assign' (variableSlot ('a'::('c'::('c'::[])))) (Bop
                   ((lvalIn (variableSlot ('a'::('c'::('c'::[]))))), Plus,
                   (immInR (natToW (S O))))))
                 (seq
                   (assign' (regInL Rv) (Bop
                     ((lvalIn (variableSlot ('s'::('e'::('l'::('f'::[])))))),
                     Plus, (immInR (natToW (S (S (S (S O)))))))))
                   (assign' (variableSlot ('s'::('e'::('l'::('f'::[])))))
                     (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))))
             (seq
               (assign' (regInL Rv) (Rvalue
                 (lvalIn (variableSlot ('a'::('c'::('c'::[])))))))
               (seq
                 (assign' (regInL Rp) (Rvalue
                   (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                 (goto (lvalIn (regInL Rp)))))))
     in
     { fName = ('s'::('i'::('z'::('e'::[])))); fVars = vars0; fReserved =
     sizeS0.reserved0; fPrecondition = (sizeS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (sizeS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length sizeS0.formals)))))) })::[]))))))

(** val newS1 : (w list -> w -> hProp) -> nat -> spec0 **)

let newS1 p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::[]
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    localsInvariant (fun x x0 -> Body (FreeList.mallocHeap (natToW O)))
      (fun x x0 r -> Body
      (starB [] (p [] r) (FreeList.mallocHeap (natToW O)))) true (fun w0 ->
      w0) extras0 (minus res (minus (length extras0) (length vars0)))
  | None ->
    localsInvariant (fun x x0 -> Body (FreeList.mallocHeap (natToW O)))
      (fun x x0 r -> Body
      (starB [] (p [] r) (FreeList.mallocHeap (natToW O)))) false (fun w0 ->
      w0) vars0 res) }

(** val deleteS1 : (w list -> w -> hProp) -> nat -> spec0 **)

let deleteS1 p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e)))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e)))) }

(** val popS : (w list -> w -> hProp) -> nat -> spec0 **)

let popS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([], (fun x -> Exists ([], (fun ls ->
    localsInvariant (fun v x0 -> Body
      (starB []
        (Obj.magic p (x::(Obj.magic ls)) (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x0 r -> Body
      (starB []
        (starB [] (injB [])
          (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e)))))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([], (fun x -> Exists ([], (fun ls ->
    localsInvariant (fun v x0 -> Body
      (starB []
        (Obj.magic p (x::(Obj.magic ls)) (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x0 r -> Body
      (starB []
        (starB [] (injB [])
          (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e)))))) }

(** val emptyS : (w list -> w -> hProp) -> nat -> spec0 **)

let emptyS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e)))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e)))) }

(** val pushS : (w list -> w -> hProp) -> nat -> spec0 **)

let pushS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::[]))
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (p ((v ('n'::[]))::(Obj.magic ls))
            (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e)))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (p ((v ('n'::[]))::(Obj.magic ls))
            (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e)))) }

(** val copyS : (w list -> w -> hProp) -> nat -> spec0 **)

let copyS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
          (Obj.magic p ls r)) (FreeList.mallocHeap (natToW O)))) a b0 extras0
      d e)))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
          (Obj.magic p ls r)) (FreeList.mallocHeap (natToW O)))) a b0 vars0
      res e)))) }

(** val revS : (w list -> w -> hProp) -> nat -> spec0 **)

let revS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (p (rev (Obj.magic ls)) (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e)))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (p (rev (Obj.magic ls)) (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e)))) }

(** val lengthS : (w list -> w -> hProp) -> nat -> spec0 **)

let lengthS p res =
  let vars0 =
    ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
  in
  { reserved0 = res; formals = vars0; precondition = (fun extras ->
  match extras with
  | Some extras0 ->
    let a = true in
    let b0 = fun w0 -> w0 in
    let d = minus res (minus (length extras0) (length vars0)) in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 extras0 d e)))
  | None ->
    let a = false in
    let b0 = fun w0 -> w0 in
    (fun e -> Exists ([], (fun ls ->
    localsInvariant (fun v x -> Body
      (starB [] (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[]))))))
        (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
      (starB []
        (starB [] (injB [])
          (Obj.magic p ls (v ('s'::('e'::('l'::('f'::[])))))))
        (FreeList.mallocHeap (natToW O)))) a b0 vars0 res e)))) }

module type Coq0_ADT = 
 sig 
  val lseq : w list -> w -> hProp
  
  val lseq' : w list -> w -> hProp
 end

module Coq0_Adt = 
 struct 
  (** val lseq' : w list -> w -> hProp **)
  
  let rec lseq' ls p =
    match ls with
    | [] -> injB []
    | x::ls' ->
      starB [] (starB [] (injB []) (injB []))
        (exB [] (fun p' ->
          starB [] (ptsto32m [] p O (x::(p'::[]))) (lseq' ls' p')))
  
  (** val lseq : w list -> w -> hProp **)
  
  let lseq ls c =
    starB [] (starB [] (injB []) (injB []))
      (exB [] (fun p ->
        exB [] (fun junk ->
          starB [] (ptsto32m [] c O (p::(junk::[]))) (lseq' ls p))))
 end

(** val newS2 : spec0 **)

let newS2 =
  newS1 Coq0_Adt.lseq (S (S (S (S (S (S (S (S O))))))))

(** val deleteS2 : spec0 **)

let deleteS2 =
  deleteS1 Coq0_Adt.lseq (S (S (S (S (S (S (S O)))))))

(** val popS0 : spec0 **)

let popS0 =
  popS Coq0_Adt.lseq (S (S (S (S (S (S (S (S O))))))))

(** val emptyS0 : spec0 **)

let emptyS0 =
  emptyS Coq0_Adt.lseq O

(** val pushS0 : spec0 **)

let pushS0 =
  pushS Coq0_Adt.lseq (S (S (S (S (S (S (S (S O))))))))

(** val copyS0 : spec0 **)

let copyS0 =
  copyS Coq0_Adt.lseq (S (S (S (S (S (S (S (S (S (S O))))))))))

(** val revS0 : spec0 **)

let revS0 =
  revS Coq0_Adt.lseq (S (S O))

(** val lengthS0 : spec0 **)

let lengthS0 =
  lengthS Coq0_Adt.lseq (S O)

(** val m1 : module0 **)

let m1 =
  bmodule_0
    ((let x = 'm'::('a'::('l'::('l'::('o'::('c'::[]))))) in
      let y = 'm'::('a'::('l'::('l'::('o'::('c'::[]))))) in
      Pair ((Pair (x, y)), (mallocS.precondition None)))::((let x =
                                                              'm'::('a'::('l'::('l'::('o'::('c'::[])))))
                                                            in
                                                            let y =
                                                              'f'::('r'::('e'::('e'::[])))
                                                            in
                                                            Pair ((Pair (x,
                                                            y)),
                                                            (freeS.precondition
                                                              None)))::[]))
    ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
    ((let vars0 =
        ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('x'::[])::[])
      in
      let b' =
        seq
          (call_0 (Some (variableSlot ('x'::[])))
            (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
              ('m'::('a'::('l'::('l'::('o'::('c'::[])))))))
            ((immInR (natToW O))::((immInR (natToW (S (S O))))::[]))
            (let inv0 =
               localsInvariant (fun x r -> Body
                 (starB []
                   (starB [] (starB [] (allocated r O (S (S O))) (injB []))
                     (injB [])) (FreeList.mallocHeap (natToW O))))
                 (fun x r r' -> Body
                 (starB [] (Coq0_Adt.lseq [] r')
                   (FreeList.mallocHeap (natToW O))))
             in
             fun ns ->
             inv0 true (fun w0 ->
               wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))) w0
                 (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O))))))))))))))))))))))))))))))))
                   (plus (S (S (S (S O))))
                     (mult (S (S (S (S O)))) (length ns))))) ns))
          (seq
            (seq
              (assign' (regInL Rv) (Rvalue
                (lvalIn (variableSlot ('x'::[])))))
              (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                (immInR (natToW O)))))
            (seq
              (assign' (regInL Rv) (Rvalue
                (lvalIn (variableSlot ('x'::[])))))
              (seq
                (assign' (regInL Rp) (Rvalue
                  (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                (goto (lvalIn (regInL Rp))))))
      in
      { fName = ('n'::('e'::('w'::[]))); fVars = vars0; fReserved =
      newS2.reserved0; fPrecondition = (newS2.precondition None); fBody =
      (seq
        (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
          (lvalIn (regInL Rp))))
        (seq (fun x x0 -> Structured ([], (fun im mn _ ->
          assert_ im mn (newS2.precondition (Some vars0))))) (fun ns res ->
          b' ns (minus res (minus (length vars0) (length newS2.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('l'::('s'::[]))::[]))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('l'::('s'::[]))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (call_0 None
             (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
               ('f'::('r'::('e'::('e'::[])))))
             ((immInR (natToW O))::((lvalIn
                                      (variableSlot
                                        ('s'::('e'::('l'::('f'::[]))))))::(
             (immInR (natToW (S (S O))))::[])))
             (let inv0 = fun a b0 c d e -> Exists ([], (fun s ->
                localsInvariant (fun v x -> Body
                  (starB []
                    (Coq0_Adt.lseq' (Obj.magic s) (v ('l'::('s'::[]))))
                    (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
                  (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a b0
                  c d e))
              in
              fun ns ->
              inv0 true (fun w0 ->
                wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))) w0
                  (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O))))))))))))))))))))))))))))))))
                    (plus (S (S (S (S O))))
                      (mult (S (S (S (S O)))) (length ns))))) ns))
           (seq
             (while_0
               (let a = true in
                let b0 = fun w0 -> w0 in
                (fun c d e -> Exists ([], (fun s ->
                localsInvariant (fun v x -> Body
                  (starB []
                    (Coq0_Adt.lseq' (Obj.magic s) (v ('l'::('s'::[]))))
                    (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
                  (starB [] (injB []) (FreeList.mallocHeap (natToW O)))) a b0
                  c d e)))) { cOperand1 =
               (lvalIn (variableSlot ('l'::('s'::[])))); cTest = Ne;
               cOperand2 = (immInR (natToW O)) }
               (seq
                 (seq
                   (assign' (regInL Rv) (Bop
                     ((lvalIn (variableSlot ('l'::('s'::[])))), Plus,
                     (immInR (natToW (S (S (S (S O)))))))))
                   (assign' (variableSlot ('s'::('e'::('l'::('f'::[])))))
                     (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                 (seq
                   (call_0 None
                     (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
                       ('f'::('r'::('e'::('e'::[])))))
                     ((immInR (natToW O))::((lvalIn
                                              (variableSlot ('l'::('s'::[]))))::(
                     (immInR (natToW (S (S O))))::[])))
                     (let inv0 = fun a b0 c d e -> Exists ([], (fun s ->
                        localsInvariant (fun v x -> Body
                          (starB []
                            (Coq0_Adt.lseq' (Obj.magic s)
                              (v ('s'::('e'::('l'::('f'::[]))))))
                            (FreeList.mallocHeap (natToW O)))) (fun v x r ->
                          Body
                          (starB [] (injB [])
                            (FreeList.mallocHeap (natToW O)))) a b0 c d e))
                      in
                      fun ns ->
                      inv0 true (fun w0 ->
                        wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          O)))))))))))))))))))))))))))))))) w0
                          (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S O))))))))))))))))))))))))))))))))
                            (plus (S (S (S (S O))))
                              (mult (S (S (S (S O)))) (length ns))))) ns))
                   (assign' (variableSlot ('l'::('s'::[]))) (Rvalue
                     (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[])))))))))))
             (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
               (seq
                 (assign' (regInL Rp) (Rvalue
                   (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                 (goto (lvalIn (regInL Rp)))))))
     in
     { fName = ('d'::('e'::('l'::('e'::('t'::('e'::[])))))); fVars = vars0;
     fReserved = deleteS2.reserved0; fPrecondition =
     (deleteS2.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (deleteS2.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length deleteS2.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('t'::('m'::('p'::[])))::(('r'::[])::[])))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (seq
             (assign' (regInL Rv) (Rvalue
               (lvalIn (variableSlot ('t'::('m'::('p'::[])))))))
             (assign' (variableSlot ('r'::[])) (Rvalue
               (lvalIn (fun x -> LvMem (Reg Rv))))))
           (seq
             (seq
               (assign' (regInL Rv) (Bop
                 ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))), Plus,
                 (immInR (natToW (S (S (S (S O)))))))))
               (assign'
                 (variableSlot
                   ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))
                 (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
             (seq
               (seq
                 (assign' (regInL Rv) (Rvalue
                   (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                 (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                   (lvalIn
                     (variableSlot
                       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))))))
               (seq
                 (call_0 None
                   (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
                     ('f'::('r'::('e'::('e'::[])))))
                   ((immInR (natToW O))::((lvalIn
                                            (variableSlot
                                              ('t'::('m'::('p'::[])))))::(
                   (immInR (natToW (S (S O))))::[])))
                   (let inv0 =
                      localsInvariant (fun v x -> Body (empB []))
                        (fun v x r -> Body (injB []))
                    in
                    fun ns ->
                    inv0 true (fun w0 ->
                      wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        O)))))))))))))))))))))))))))))))) w0
                        (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S O))))))))))))))))))))))))))))))))
                          (plus (S (S (S (S O))))
                            (mult (S (S (S (S O)))) (length ns))))) ns))
                 (seq
                   (assign' (regInL Rv) (Rvalue
                     (lvalIn (variableSlot ('r'::[])))))
                   (seq
                     (assign' (regInL Rp) (Rvalue
                       (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                     (goto (lvalIn (regInL Rp)))))))))
     in
     { fName = ('p'::('o'::('p'::[]))); fVars = vars0; fReserved =
     popS0.reserved0; fPrecondition = (popS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (popS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length popS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::[])
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('s'::('e'::('l'::('f'::[]))))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (if_0 { cOperand1 =
           (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[])))))); cTest =
           Eq0; cOperand2 = (immInR (natToW O)) }
           (seq (assign' (regInL Rv) (Rvalue (immInR (natToW (S O)))))
             (seq
               (assign' (regInL Rp) (Rvalue
                 (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
               (goto (lvalIn (regInL Rp)))))
           (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
             (seq
               (assign' (regInL Rp) (Rvalue
                 (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
               (goto (lvalIn (regInL Rp))))))
     in
     { fName = ('e'::('m'::('p'::('t'::('y'::[]))))); fVars = vars0;
     fReserved = emptyS0.reserved0; fPrecondition =
     (emptyS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (emptyS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length emptyS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::[])::(('t'::('m'::('p'::[])))::[])))
     in
     let b' =
       seq
         (call_0 (Some (variableSlot ('t'::('m'::('p'::[])))))
           (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
             ('m'::('a'::('l'::('l'::('o'::('c'::[])))))))
           ((immInR (natToW O))::((immInR (natToW (S (S O))))::[]))
           (let inv0 = fun a b0 c d e -> Exists ([], (fun p ->
              localsInvariant (fun v r -> Body
                (starB []
                  (ptsto32 [] (v ('s'::('e'::('l'::('f'::[])))))
                    (Obj.magic p)) (allocated r O (S (S O))))) (fun v r r' ->
                Body
                (starB []
                  (starB [] (injB [])
                    (ptsto32 [] (v ('s'::('e'::('l'::('f'::[]))))) r))
                  (ptsto32m [] r O ((v ('n'::[]))::((Obj.magic p)::[]))))) a
                b0 c d e))
            in
            fun ns ->
            inv0 true (fun w0 ->
              wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))) w0
                (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O))))))))))))))))))))))))))))))))
                  (plus (S (S (S (S O))))
                    (mult (S (S (S (S O)))) (length ns))))) ns))
         (seq
           (seq
             (assign' (regInL Rv) (Rvalue
               (lvalIn (variableSlot ('t'::('m'::('p'::[])))))))
             (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
               (lvalIn (variableSlot ('n'::[]))))))
           (seq
             (seq
               (assign' (regInL Rv) (Rvalue
                 (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
               (assign'
                 (variableSlot
                   ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))
                 (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
             (seq
               (seq
                 (assign' (regInL Rv) (Bop
                   ((lvalIn (variableSlot ('t'::('m'::('p'::[]))))), Plus,
                   (immInR (natToW (S (S (S (S O)))))))))
                 (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                   (lvalIn
                     (variableSlot
                       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))))))
               (seq
                 (seq
                   (assign' (regInL Rv) (Rvalue
                     (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                   (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                     (lvalIn (variableSlot ('t'::('m'::('p'::[]))))))))
                 (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
                   (seq
                     (assign' (regInL Rp) (Rvalue
                       (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                     (goto (lvalIn (regInL Rp)))))))))
     in
     { fName = ('p'::('u'::('s'::('h'::[])))); fVars = vars0; fReserved =
     pushS0.reserved0; fPrecondition = (pushS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (pushS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length pushS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('n'::('e'::('w'::[])))::(('a'::('c'::('c'::[])))::(('t'::('m'::('p'::[])))::[]))))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('s'::('e'::('l'::('f'::[]))))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (call_0 (Some (variableSlot ('n'::('e'::('w'::[])))))
             (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
               ('m'::('a'::('l'::('l'::('o'::('c'::[])))))))
             ((immInR (natToW O))::((immInR (natToW (S (S O))))::[]))
             (let inv0 = fun a b0 c d e -> Exists ([], (fun ls ->
                localsInvariant (fun v r -> Body
                  (starB []
                    (starB []
                      (Coq0_Adt.lseq' (Obj.magic ls)
                        (v ('s'::('e'::('l'::('f'::[]))))))
                      (allocated r O (S O)))
                    (FreeList.mallocHeap (natToW O)))) (fun v r r' -> Body
                  (starB []
                    (starB [] (injB [])
                      (Coq0_Adt.lseq' (Obj.magic ls)
                        (v ('s'::('e'::('l'::('f'::[])))))))
                    (exB [] (fun p ->
                      starB []
                        (starB [] (ptsto32 [] r p)
                          (Coq0_Adt.lseq' (Obj.magic ls) p))
                        (FreeList.mallocHeap (natToW O)))))) a b0 c d e))
              in
              fun ns ->
              inv0 true (fun w0 ->
                wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))) w0
                  (natToWord (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O))))))))))))))))))))))))))))))))
                    (plus (S (S (S (S O))))
                      (mult (S (S (S (S O)))) (length ns))))) ns))
           (seq
             (assign' (variableSlot ('a'::('c'::('c'::[])))) (Rvalue
               (lvalIn (variableSlot ('n'::('e'::('w'::[])))))))
             (seq
               (while_0
                 (let a = true in
                  let b0 = fun w0 -> w0 in
                  (fun c d e -> Exists ([], (fun ls ->
                  localsInvariant (fun v x -> Body
                    (starB []
                      (starB []
                        (Coq0_Adt.lseq' (Obj.magic ls)
                          (v ('s'::('e'::('l'::('f'::[]))))))
                        (allocated (v ('a'::('c'::('c'::[])))) O (S O)))
                      (FreeList.mallocHeap (natToW O)))) (fun v x r -> Body
                    (starB []
                      (starB [] (injB [])
                        (Coq0_Adt.lseq' (Obj.magic ls)
                          (v ('s'::('e'::('l'::('f'::[])))))))
                      (exB [] (fun p ->
                        starB []
                          (starB []
                            (ptsto32 [] (v ('a'::('c'::('c'::[])))) p)
                            (Coq0_Adt.lseq' (Obj.magic ls) p))
                          (FreeList.mallocHeap (natToW O)))))) a b0 c d e))))
                 { cOperand1 =
                 (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))));
                 cTest = Ne; cOperand2 = (immInR (natToW O)) }
                 (seq
                   (seq
                     (assign' (regInL Rv) (Rvalue
                       (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                     (assign' (variableSlot ('t'::('m'::('p'::[])))) (Rvalue
                       (lvalIn (fun x -> LvMem (Reg Rv))))))
                   (seq
                     (seq
                       (assign' (regInL Rv) (Bop
                         ((lvalIn
                            (variableSlot ('s'::('e'::('l'::('f'::[])))))),
                         Plus, (immInR (natToW (S (S (S (S O)))))))))
                       (assign' (variableSlot ('s'::('e'::('l'::('f'::[])))))
                         (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                     (seq
                       (call_0 (Some
                         (variableSlot
                           ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))))
                         (labl ('m'::('a'::('l'::('l'::('o'::('c'::[]))))))
                           ('m'::('a'::('l'::('l'::('o'::('c'::[])))))))
                         ((immInR (natToW O))::((immInR (natToW (S (S O))))::[]))
                         (let inv0 = fun a b0 c d e -> Exists ([], (fun ls ->
                            localsInvariant (fun v r -> Body
                              (starB []
                                (starB []
                                  (starB []
                                    (starB []
                                      (starB [] (allocated r O (S (S O)))
                                        (injB [])) (injB []))
                                    (Coq0_Adt.lseq' (Obj.magic ls)
                                      (v ('s'::('e'::('l'::('f'::[])))))))
                                  (allocated (v ('a'::('c'::('c'::[])))) O (S
                                    O))) (FreeList.mallocHeap (natToW O))))
                              (fun v r r' -> Body
                              (starB []
                                (starB [] (injB [])
                                  (Coq0_Adt.lseq' (Obj.magic ls)
                                    (v ('s'::('e'::('l'::('f'::[])))))))
                                (exB [] (fun p ->
                                  starB []
                                    (starB []
                                      (ptsto32 [] (v ('a'::('c'::('c'::[]))))
                                        p)
                                      (Coq0_Adt.lseq'
                                        ((v ('t'::('m'::('p'::[]))))::
                                        (Obj.magic ls)) p))
                                    (FreeList.mallocHeap (natToW O)))))) a b0
                              c d e))
                          in
                          fun ns ->
                          inv0 true (fun w0 ->
                            wminus (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S O)))))))))))))))))))))))))))))))) w0
                              (natToWord (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S
                                O))))))))))))))))))))))))))))))))
                                (plus (S (S (S (S O))))
                                  (mult (S (S (S (S O)))) (length ns))))) ns))
                       (seq
                         (seq
                           (assign' (regInL Rv) (Rvalue
                             (lvalIn (variableSlot ('a'::('c'::('c'::[])))))))
                           (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                             (lvalIn
                               (variableSlot
                                 ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))))))
                         (seq
                           (seq
                             (assign' (regInL Rv) (Rvalue
                               (lvalIn
                                 (variableSlot
                                   ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))))))
                             (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                               (lvalIn
                                 (variableSlot ('t'::('m'::('p'::[]))))))))
                           (assign' (variableSlot ('a'::('c'::('c'::[]))))
                             (Bop
                             ((lvalIn
                                (variableSlot
                                  ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))),
                             Plus, (immInR (natToW (S (S (S (S O)))))))))))))))
               (seq
                 (seq
                   (assign' (regInL Rv) (Rvalue
                     (lvalIn (variableSlot ('a'::('c'::('c'::[])))))))
                   (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                     (immInR (natToW O)))))
                 (seq
                   (assign' (regInL Rv) (Rvalue
                     (lvalIn (variableSlot ('n'::('e'::('w'::[])))))))
                   (seq
                     (assign' (regInL Rp) (Rvalue
                       (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                     (goto (lvalIn (regInL Rp)))))))))
     in
     { fName = ('c'::('o'::('p'::('y'::[])))); fVars = vars0; fReserved =
     copyS0.reserved0; fPrecondition = (copyS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (copyS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length copyS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('a'::('c'::('c'::[])))::[]))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('s'::('e'::('l'::('f'::[]))))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (assign' (variableSlot ('a'::('c'::('c'::[])))) (Rvalue
             (immInR (natToW O))))
           (seq
             (while_0
               (let a = true in
                let b0 = fun w0 -> w0 in
                (fun c d e -> Exists ([], (fun ls ->
                localsInvariant (fun v x -> Body
                  (Coq0_Adt.lseq' (Obj.magic ls)
                    (v ('s'::('e'::('l'::('f'::[]))))))) (fun v x r -> Body
                  (starB [] (injB [])
                    (Coq0_Adt.lseq' (Obj.magic ls)
                      (v ('s'::('e'::('l'::('f'::[])))))))) a b0 c d e))))
               { cOperand1 =
               (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))));
               cTest = Ne; cOperand2 = (immInR (natToW O)) }
               (seq
                 (assign' (variableSlot ('a'::('c'::('c'::[])))) (Bop
                   ((lvalIn (variableSlot ('a'::('c'::('c'::[]))))), Plus,
                   (immInR (natToW (S O))))))
                 (seq
                   (assign' (regInL Rv) (Bop
                     ((lvalIn (variableSlot ('s'::('e'::('l'::('f'::[])))))),
                     Plus, (immInR (natToW (S (S (S (S O)))))))))
                   (assign' (variableSlot ('s'::('e'::('l'::('f'::[])))))
                     (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))))
             (seq
               (assign' (regInL Rv) (Rvalue
                 (lvalIn (variableSlot ('a'::('c'::('c'::[])))))))
               (seq
                 (assign' (regInL Rp) (Rvalue
                   (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                 (goto (lvalIn (regInL Rp)))))))
     in
     { fName = ('l'::('e'::('n'::('g'::('t'::('h'::[])))))); fVars = vars0;
     fReserved = lengthS0.reserved0; fPrecondition =
     (lengthS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (lengthS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length lengthS0.formals)))))) })::(
    (let vars0 =
       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))::(('s'::('e'::('l'::('f'::[]))))::(('f'::('r'::('o'::('m'::[]))))::(('t'::('o'::[]))::[])))
     in
     let b' =
       seq
         (seq
           (assign' (regInL Rv) (Rvalue
             (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
           (assign' (variableSlot ('f'::('r'::('o'::('m'::[]))))) (Rvalue
             (lvalIn (fun x -> LvMem (Reg Rv))))))
         (seq
           (assign' (variableSlot ('t'::('o'::[]))) (Rvalue
             (immInR (natToW O))))
           (seq
             (while_0
               (let a = true in
                let b0 = fun w0 -> w0 in
                (fun c d e -> Exists ([], (fun ls -> Exists ([], (fun ls' ->
                localsInvariant (fun v x -> Body
                  (starB []
                    (starB []
                      (allocated (v ('s'::('e'::('l'::('f'::[]))))) O (S O))
                      (Coq0_Adt.lseq' (Obj.magic ls)
                        (v ('f'::('r'::('o'::('m'::[])))))))
                    (Coq0_Adt.lseq' (Obj.magic ls') (v ('t'::('o'::[]))))))
                  (fun v x r -> Body
                  (starB [] (injB [])
                    (exB [] (fun p ->
                      starB []
                        (ptsto32 [] (v ('s'::('e'::('l'::('f'::[]))))) p)
                        (Coq0_Adt.lseq'
                          (rev_append (Obj.magic ls) (Obj.magic ls')) p)))))
                  a b0 c d e)))))) { cOperand1 =
               (lvalIn (variableSlot ('f'::('r'::('o'::('m'::[]))))));
               cTest = Ne; cOperand2 = (immInR (natToW O)) }
               (seq
                 (seq
                   (assign' (regInL Rv) (Bop
                     ((lvalIn (variableSlot ('f'::('r'::('o'::('m'::[])))))),
                     Plus, (immInR (natToW (S (S (S (S O)))))))))
                   (assign'
                     (variableSlot
                       ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[]))))))))))))
                     (Rvalue (lvalIn (fun x -> LvMem (Reg Rv))))))
                 (seq
                   (seq
                     (assign' (regInL Rv) (Bop
                       ((lvalIn
                          (variableSlot ('f'::('r'::('o'::('m'::[])))))),
                       Plus, (immInR (natToW (S (S (S (S O)))))))))
                     (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                       (lvalIn (variableSlot ('t'::('o'::[])))))))
                   (seq
                     (assign' (variableSlot ('t'::('o'::[]))) (Rvalue
                       (lvalIn (variableSlot ('f'::('r'::('o'::('m'::[]))))))))
                     (assign' (variableSlot ('f'::('r'::('o'::('m'::[])))))
                       (Rvalue
                       (lvalIn
                         (variableSlot
                           ('e'::('x'::('t'::('r'::('a'::('_'::('s'::('t'::('a'::('c'::('k'::[])))))))))))))))))))
             (seq
               (seq
                 (assign' (regInL Rv) (Rvalue
                   (lvalIn (variableSlot ('s'::('e'::('l'::('f'::[]))))))))
                 (assign' (fun x -> LvMem (Reg Rv)) (Rvalue
                   (lvalIn (variableSlot ('t'::('o'::[])))))))
               (seq (assign' (regInL Rv) (Rvalue (immInR (natToW O))))
                 (seq
                   (assign' (regInL Rp) (Rvalue
                     (lvalIn (fun x -> LvMem (Indir (Sp, (natToW O)))))))
                   (goto (lvalIn (regInL Rp))))))))
     in
     { fName = ('r'::('e'::('v'::[]))); fVars = vars0; fReserved =
     revS0.reserved0; fPrecondition = (revS0.precondition None); fBody =
     (seq
       (assign' (fun x -> LvMem (Indir (Sp, (natToW O)))) (Rvalue
         (lvalIn (regInL Rp))))
       (seq (fun x x0 -> Structured ([], (fun im mn _ ->
         assert_ im mn (revS0.precondition (Some vars0))))) (fun ns res ->
         b' ns (minus res (minus (length vars0) (length revS0.formals)))))) })::[]))))))))

(** val rep_inv0 : w -> aDTValue -> hProp **)

let rep_inv0 p = function
| List ls -> Coq0_Adt.lseq ls p
| Junk -> injB []
| FEnsemble -> Coq_Adt.lset p

module Ri = 
 struct 
  type coq_RepInv = w -> Adt.coq_ADTValue -> hProp
  
  (** val rep_inv : w -> aDTValue -> hProp **)
  
  let rep_inv =
    rep_inv0
 end

module Made = Coq40_Make(Adt)(Ri)

(** val m2 : module0 **)

let m2 =
  Made.wrapper_module ('A'::('D'::('T'::[])))
    ((let x = 's'::('y'::('s'::[])) in
      let y = 'a'::('b'::('o'::('r'::('t'::[])))) in
      Pair ((Pair (x, y)), (abortS.precondition None)))::((let x =
                                                             'L'::('i'::('s'::('t'::('S'::('e'::('t'::[]))))))
                                                           in
                                                           let y =
                                                             'n'::('e'::('w'::[]))
                                                           in
                                                           Pair ((Pair (x,
                                                           y)),
                                                           (newS0.precondition
                                                             None)))::(
    (let x = 'L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))) in
     let y = 'd'::('e'::('l'::('e'::('t'::('e'::[]))))) in
     Pair ((Pair (x, y)), (deleteS0.precondition None)))::((let x =
                                                              'L'::('i'::('s'::('t'::('S'::('e'::('t'::[]))))))
                                                            in
                                                            let y =
                                                              'm'::('e'::('m'::[]))
                                                            in
                                                            Pair ((Pair (x,
                                                            y)),
                                                            (memS0.precondition
                                                              None)))::(
    (let x = 'L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))) in
     let y = 'a'::('d'::('d'::[])) in
     Pair ((Pair (x, y)), (addS0.precondition None)))::((let x =
                                                           'L'::('i'::('s'::('t'::('S'::('e'::('t'::[]))))))
                                                         in
                                                         let y =
                                                           'r'::('e'::('m'::('o'::('v'::('e'::[])))))
                                                         in
                                                         Pair ((Pair (x, y)),
                                                         (removeS0.precondition
                                                           None)))::(
    (let x = 'L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))) in
     let y = 's'::('i'::('z'::('e'::[]))) in
     Pair ((Pair (x, y)), (sizeS0.precondition None)))::((let x =
                                                            'L'::('i'::('s'::('t'::('S'::('e'::('q'::[]))))))
                                                          in
                                                          let y =
                                                            'n'::('e'::('w'::[]))
                                                          in
                                                          Pair ((Pair (x,
                                                          y)),
                                                          (newS2.precondition
                                                            None)))::(
    (let x = 'L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))) in
     let y = 'd'::('e'::('l'::('e'::('t'::('e'::[]))))) in
     Pair ((Pair (x, y)), (deleteS2.precondition None)))::((let x =
                                                              'L'::('i'::('s'::('t'::('S'::('e'::('q'::[]))))))
                                                            in
                                                            let y =
                                                              'p'::('o'::('p'::[]))
                                                            in
                                                            Pair ((Pair (x,
                                                            y)),
                                                            (popS0.precondition
                                                              None)))::(
    (let x = 'L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))) in
     let y = 'e'::('m'::('p'::('t'::('y'::[])))) in
     Pair ((Pair (x, y)), (emptyS0.precondition None)))::((let x =
                                                             'L'::('i'::('s'::('t'::('S'::('e'::('q'::[]))))))
                                                           in
                                                           let y =
                                                             'p'::('u'::('s'::('h'::[])))
                                                           in
                                                           Pair ((Pair (x,
                                                           y)),
                                                           (pushS0.precondition
                                                             None)))::(
    (let x = 'L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))) in
     let y = 'c'::('o'::('p'::('y'::[]))) in
     Pair ((Pair (x, y)), (copyS0.precondition None)))::((let x =
                                                            'L'::('i'::('s'::('t'::('S'::('e'::('q'::[]))))))
                                                          in
                                                          let y =
                                                            'r'::('e'::('v'::[]))
                                                          in
                                                          Pair ((Pair (x,
                                                          y)),
                                                          (revS0.precondition
                                                            None)))::(
    (let x = 'L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))) in
     let y = 'l'::('e'::('n'::('g'::('t'::('h'::[]))))) in
     Pair ((Pair (x, y)), (lengthS0.precondition None)))::[])))))))))))))))
    ((Pair ((Pair ((Pair (('s'::('E'::('m'::('p'::('t'::('y'::[])))))),
    fEnsemble_sEmpty)), (S (S (S (S (S (S (S (S O)))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
      ('n'::('e'::('w'::[]))))))::((Pair ((Pair ((Pair
    (('s'::('D'::('e'::('l'::('e'::('t'::('e'::[]))))))),
    fEnsemble_sDelete)), (S (S (S (S (S (S (S O))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
      ('d'::('e'::('l'::('e'::('t'::('e'::[])))))))))::((Pair ((Pair ((Pair
    (('s'::('A'::('d'::('d'::[])))), fEnsemble_sAdd)), (S (S (S (S (S (S (S
    (S (S O))))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
      ('a'::('d'::('d'::[]))))))::((Pair ((Pair ((Pair
    (('s'::('R'::('e'::('m'::('o'::('v'::('e'::[]))))))),
    fEnsemble_sRemove)), (S (S (S (S (S (S (S O))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
      ('r'::('e'::('m'::('o'::('v'::('e'::[])))))))))::((Pair ((Pair ((Pair
    (('s'::('I'::('n'::[]))), fEnsemble_sIn)), (S O))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
      ('m'::('e'::('m'::[]))))))::((Pair ((Pair ((Pair
    (('s'::('S'::('i'::('z'::('e'::[]))))), fEnsemble_sSize)), (S O))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('t'::[])))))))
      ('s'::('i'::('z'::('e'::[])))))))::((Pair ((Pair ((Pair
    (('n'::('e'::('w'::[]))), list_new)), (S (S (S (S (S (S (S (S
    O)))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('n'::('e'::('w'::[]))))))::((Pair ((Pair ((Pair
    (('d'::('e'::('l'::('e'::('t'::('e'::[])))))), list_delete)), (S (S (S (S
    (S (S (S O))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('d'::('e'::('l'::('e'::('t'::('e'::[])))))))))::((Pair ((Pair ((Pair
    (('p'::('o'::('p'::[]))), list_pop)), (S (S (S (S (S (S (S (S
    O)))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('p'::('o'::('p'::[]))))))::((Pair ((Pair ((Pair
    (('e'::('m'::('p'::('t'::('y'::[]))))), list_empty)), O)),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('e'::('m'::('p'::('t'::('y'::[]))))))))::((Pair ((Pair ((Pair
    (('p'::('u'::('s'::('h'::[])))), list_push)), (S (S (S (S (S (S (S (S
    O)))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('p'::('u'::('s'::('h'::[])))))))::((Pair ((Pair ((Pair
    (('c'::('o'::('p'::('y'::[])))), list_copy)), (S (S (S (S (S (S (S (S (S
    (S O)))))))))))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('c'::('o'::('p'::('y'::[])))))))::((Pair ((Pair ((Pair
    (('r'::('e'::('v'::[]))), list_rev)), (S (S O)))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('r'::('e'::('v'::[]))))))::((Pair ((Pair ((Pair
    (('l'::('e'::('n'::('g'::('t'::('h'::[])))))), list_length)), (S O))),
    (labl ('L'::('i'::('s'::('t'::('S'::('e'::('q'::[])))))))
      ('l'::('e'::('n'::('g'::('t'::('h'::[])))))))))::[]))))))))))))))

(** val m3 : module0 **)

let m3 =
  link m0 m2

(** val m4 : module0 **)

let m4 =
  link m1 m3

(** val m5 : module0 **)

let m5 =
  link m m4

module FA = Coq49_Make(Adt)(Ri)

module Coq_sumUnique = 
 struct 
  (** val input : fullySharpenedFacadeProgramOnListReturningWord **)
  
  let input =
    sumUniqueImpl FiniteSetADTMSetRBT.coq_FiniteSetImpl
  
  (** val output : FA.CompileOutMake.coq_CompileOut **)
  
  let output =
    FA.compile input
  
  (** val m1 : module0 **)
  
  let m1 =
    output.FA.CompileOutMake.bedrock_module
  
  (** val m2 : module0 **)
  
  let m2 =
    output.FA.CompileOutMake.bedrock_module_impl
  
  (** val all1 : module0 **)
  
  let all1 =
    link m1 m2
  
  (** val all : module0 **)
  
  let all =
    link all1 m5
 end

(** val compiled : char list LabelMap.t **)

let compiled =
  moduleS Coq_sumUnique.all


let rec printTree = function
  | LabelMap.Raw.Leaf -> ()
  | LabelMap.Raw.Node (t1, _, s, t2, _) ->
      printTree t1;
      List.iter print_char s;
      printTree t2

let _ = printTree compiled
