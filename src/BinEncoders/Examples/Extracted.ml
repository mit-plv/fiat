type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,y -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| x,y -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| y::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

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

type 'a sumor =
| Inleft of 'a
| Inright

(** val pred : nat -> nat **)

let pred n0 = match n0 with
| O -> n0
| S u -> u

(** val plus : nat -> nat -> nat **)

let rec plus n0 m =
  match n0 with
  | O -> m
  | S p -> S (plus p m)

(** val minus : nat -> nat -> nat **)

let rec minus n0 m =
  match n0 with
  | O -> n0
  | S k ->
    (match m with
     | O -> n0
     | S l -> minus k l)

(** val min : nat -> nat -> nat **)

let rec min n0 m =
  match n0 with
  | O -> O
  | S n' ->
    (match m with
     | O -> O
     | S m' -> S (min n' m'))

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  match n0 with
  | O -> x
  | S n' -> f (nat_iter n' f x)

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

type ('data_t, 'bin_t) decoder =
  'bin_t -> 'data_t
  (* singleton inductive, whose constructor was Build_decoder *)

(** val decode : ('a1 -> 'a2) -> ('a1, 'a2) decoder -> 'a2 -> 'a1 **)

let decode encode decoder0 =
  decoder0

(** val decode_unpack :
    ('a1 -> 'a3) -> (('a3*'a2) -> 'a2) -> ('a1 -> 'a2) -> ('a3*'a2, 'a2)
    decoder -> ('a3 -> ('a1, 'a2) decoder) -> ('a1, 'a2) decoder **)

let decode_unpack project encode1 encode2 decoder1 decoder2 bin =
  let proj,ext = decode encode1 decoder1 bin in
  decode encode2 (decoder2 proj) ext

(** val strengthen_Decoder :
    ('a1 -> 'a2) -> ('a1, 'a2) decoder -> ('a1, 'a2) decoder **)

let strengthen_Decoder encode_data data_decoder =
  decode encode_data data_decoder

(** val nested_decoder :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) decoder -> ('a2, 'a3)
    decoder -> ('a1, 'a3) decoder **)

let nested_decoder encodeA encodeB a_decoder b_decoder c =
  decode encodeA a_decoder (decode encodeB b_decoder c)

(** val unprod_decoder :
    ('a1 -> 'a2) -> ('a1, 'a2) decoder -> ('a1*'a3, 'a2*'a3) decoder **)

let unprod_decoder encodeA a_decoder bundle =
  (decode encodeA a_decoder (fst bundle)),(snd bundle)

type bin_t = bool list

(** val bin_encode_transform_pair :
    ('a1 -> bin_t) -> ('a1*bin_t) -> bool list **)

let bin_encode_transform_pair encode = function
| _data,_bin -> app (encode _data) _bin

(** val bin_encode_transform_pair_Decoder :
    ('a1 -> bin_t) -> (bin_t -> 'a1*bin_t) -> ('a1*bin_t, bool list)
    decoder **)

let bin_encode_transform_pair_Decoder encode decode0 =
  decode0

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

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

  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

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
    | IsPos z -> z
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x

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

  (** val compare_cont :
      positive -> positive -> comparison -> comparison **)

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
      (positive -> positive) -> (positive -> positive) -> (positive*mask)
      -> positive*mask **)

  let sqrtrem_step f g = function
  | s,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then (XI s),(sub_mask r' s') else (XO s),(IsPos r')
     | _ -> (XO s),(sub_mask (g (f XH)) (XO (XO XH))))

  (** val sqrtrem : positive -> positive*mask **)

  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> XH,(IsPos (XO XH)))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b

  (** val ggcdn :
      nat -> positive -> positive -> positive*(positive*positive) **)

  let rec ggcdn n0 a b =
    match n0 with
    | O -> XH,(a,b)
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a,(XH,XH)
             | Lt ->
               let g,p = ggcdn n1 (sub b' a') a in
               let ba,aa = p in g,(aa,(add aa (XO ba)))
             | Gt ->
               let g,p = ggcdn n1 (sub a' b') b in
               let ab,bb = p in g,((add bb (XO ab)),bb))
          | XO b0 ->
            let g,p = ggcdn n1 a b0 in let aa,bb = p in g,(aa,(XO bb))
          | XH -> XH,(a,XH))
       | XO a0 ->
         (match b with
          | XI p ->
            let g,p0 = ggcdn n1 a0 b in let aa,bb = p0 in g,((XO aa),bb)
          | XO b0 -> let g,p = ggcdn n1 a0 b0 in (XO g),p
          | XH -> XH,(a,XH))
       | XH -> XH,(XH,b))

  (** val ggcd : positive -> positive -> positive*(positive*positive) **)

  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b

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

  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)

  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1

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
    | IsPos z -> z
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x

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

  (** val compare_cont :
      positive -> positive -> comparison -> comparison **)

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
      (positive -> positive) -> (positive -> positive) -> (positive*mask)
      -> positive*mask **)

  let sqrtrem_step f g = function
  | s,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then (XI s),(sub_mask r' s') else (XO s),(IsPos r')
     | _ -> (XO s),(sub_mask (g (f XH)) (XO (XO XH))))

  (** val sqrtrem : positive -> positive*mask **)

  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> XH,(IsPos (XO XH)))
  | XO p0 ->
    (match p0 with
     | XI p1 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b

  (** val ggcdn :
      nat -> positive -> positive -> positive*(positive*positive) **)

  let rec ggcdn n0 a b =
    match n0 with
    | O -> XH,(a,b)
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a,(XH,XH)
             | Lt ->
               let g,p = ggcdn n1 (sub b' a') a in
               let ba,aa = p in g,(aa,(add aa (XO ba)))
             | Gt ->
               let g,p = ggcdn n1 (sub a' b') b in
               let ab,bb = p in g,((add bb (XO ab)),bb))
          | XO b0 ->
            let g,p = ggcdn n1 a b0 in let aa,bb = p in g,(aa,(XO bb))
          | XH -> XH,(a,XH))
       | XO a0 ->
         (match b with
          | XI p ->
            let g,p0 = ggcdn n1 a0 b in let aa,bb = p0 in g,((XO aa),bb)
          | XO b0 -> let g,p = ggcdn n1 a0 b0 in (XO g),p
          | XH -> XH,(a,XH))
       | XH -> XH,(XH,b))

  (** val ggcd : positive -> positive -> positive*(positive*positive) **)

  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b

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

  (** val peano_rect :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

  let rec peano_rect a f p =
    let f2 =
      peano_rect (f XH a) (fun p0 x -> f (succ (XO p0)) (f (XO p0) x))
    in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)

  (** val peano_rec :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)

  let peano_rec =
    peano_rect

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView

  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rect f f0 p1 p2)

  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p1, p2) -> f0 p1 p2 (coq_PeanoView_rec f f0 p1 p2)

  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XO p0)), (PeanoSucc ((XO p0),
      (peanoView_xO p0 q0))))

  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)

  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p0, q0) ->
    PeanoSucc ((succ (XI p0)), (PeanoSucc ((XI p0),
      (peanoView_xI p0 q0))))

  (** val peanoView : positive -> coq_PeanoView **)

  let rec peanoView = function
  | XI p0 -> peanoView_xI p0 (peanoView p0)
  | XO p0 -> peanoView_xO p0 (peanoView p0)
  | XH -> PeanoOne

  (** val coq_PeanoView_iter :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)

  let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p0, q0) -> f p0 (coq_PeanoView_iter a f p0 q0)

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
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
        -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
        -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : positive -> positive -> bool **)

    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false

    (** val min_case_strong :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
        -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case :
        positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
        -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : positive -> positive -> bool **)

    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end

  (** val max_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : positive -> positive -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)

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

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Eq
       | Npos m' -> Lt)
    | Npos n' ->
      (match m with
       | N0 -> Gt
       | Npos m' -> Coq_Pos.compare n' m')

  (** val eqb : n -> n -> bool **)

  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m with
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

  (** val pos_div_eucl : positive -> n -> n*n **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then (succ_double q),(sub r' b) else (double q),r'
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then (succ_double q),(sub r' b) else (double q),r'
    | XH ->
      (match b with
       | N0 -> N0,(Npos XH)
       | Npos p ->
         (match p with
          | XH -> (Npos XH),N0
          | _ -> N0,(Npos XH)))

  (** val div_eucl : n -> n -> n*n **)

  let div_eucl a b =
    match a with
    | N0 -> N0,N0
    | Npos na ->
      (match b with
       | N0 -> N0,a
       | Npos p -> pos_div_eucl na b)

  (** val div : n -> n -> n **)

  let div a b =
    fst (div_eucl a b)

  (** val modulo : n -> n -> n **)

  let modulo a b =
    snd (div_eucl a b)

  (** val gcd : n -> n -> n **)

  let gcd a b =
    match a with
    | N0 -> b
    | Npos p ->
      (match b with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))

  (** val ggcd : n -> n -> n*(n*n) **)

  let ggcd a b =
    match a with
    | N0 -> b,(N0,(Npos XH))
    | Npos p ->
      (match b with
       | N0 -> a,((Npos XH),N0)
       | Npos q ->
         let g,p0 = Coq_Pos.ggcd p q in
         let aa,bb = p0 in (Npos g),((Npos aa),(Npos bb)))

  (** val sqrtrem : n -> n*n **)

  let sqrtrem = function
  | N0 -> N0,N0
  | Npos p ->
    let s,m = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> (Npos s),(Npos r)
     | _ -> (Npos s),N0)

  (** val sqrt : n -> n **)

  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.sqrt p)

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
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

  let iter n0 f x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f x

  (** val eq_dec : n -> n -> bool **)

  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos x ->
      (match m with
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
       let rec f = function
       | XI p1 -> fS2' p1 (f p1)
       | XO p1 -> f2' p1 (f p1)
       | XH -> fS2 N0 f0
       in f p)

  (** val binary_rec :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)

  let binary_rec =
    binary_rect

  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)

  let peano_rect f0 f n0 =
    let f' = fun p -> f (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f N0 f0) f' p)

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

  let lcm a b =
    mul a (div b (gcd a b))

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
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
        'a1) -> 'a1 **)

    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))

    (** val max_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : n -> n -> bool **)

    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) true false

    (** val min_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
        'a1) -> 'a1 **)

    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))

    (** val min_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : n -> n -> bool **)

    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) true false
   end

  (** val max_case_strong :
      n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : n -> n -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0

  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : n -> n -> bool **)

  let min_dec =
    Private_Dec.min_dec
 end

(** val exp2' : nat -> positive **)

let rec exp2' = function
| O -> XH
| S l' -> XO (exp2' l')

(** val exp2 : nat -> n **)

let exp2 l =
  Npos (exp2' l)

(** val exp2_nat : nat -> nat **)

let exp2_nat l =
  N.to_nat (exp2 l)

(** val encode'' : positive -> bin_t -> bool list **)

let rec encode'' pos acc =
  match pos with
  | XI pos' -> encode'' pos' (true::acc)
  | XO pos' -> encode'' pos' (false::acc)
  | XH -> true::acc

(** val encode' : n -> bool list **)

let encode' = function
| N0 -> []
| Npos pos -> encode'' pos []

(** val pad : bin_t -> nat -> bin_t **)

let rec pad b = function
| O -> b
| S l' -> false::(pad b l')

(** val fixInt_encode : nat -> n -> bin_t **)

let fixInt_encode size0 n0 =
  let b = encode' n0 in pad b (minus size0 (length b))

(** val decode'' : bin_t -> nat -> positive -> positive*bin_t **)

let rec decode'' b l acc =
  match l with
  | O -> acc,b
  | S l' ->
    (match b with
     | [] -> acc,[]
     | b0::b' ->
       if b0 then decode'' b' l' (XI acc) else decode'' b' l' (XO acc))

(** val decode' : bin_t -> nat -> n*bin_t **)

let rec decode' b = function
| O -> N0,b
| S l' ->
  (match b with
   | [] -> N0,[]
   | b0::b' ->
     if b0
     then let pos,b'' = decode'' b' l' XH in (Npos pos),b''
     else decode' b' l')

(** val fixInt_decode : nat -> bin_t -> n*bin_t **)

let fixInt_decode size0 b =
  (fst (decode' b size0)),(snd (decode' b size0))

type 'a data_t = 'a list

(** val encode'0 : 'a1 -> (('a1*'a2) -> 'a2) -> 'a1 list -> 'a2 -> 'a2 **)

let rec encode'0 halt0 encode_A data ext =
  match data with
  | [] -> encode_A (halt0,ext)
  | s::data' -> encode_A (s,(encode'0 halt0 encode_A data' ext))

(** val steppingList_encode :
    'a1 -> nat -> (('a1*'a2) -> 'a2) -> ('a1 data_t*'a2) -> 'a2 **)

let steppingList_encode halt0 fuel encode_A = function
| _a,_bin -> encode'0 halt0 encode_A _a _bin

(** val decode'0 :
    'a1 -> ('a1 -> bool) -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder
    -> 'a2 -> nat -> 'a1 list*'a2 **)

let rec decode'0 halt0 halt_dec0 encode_A decoder_A b f =
  let x,b' = decode encode_A decoder_A b in
  if halt_dec0 x
  then [],b'
  else (match f with
        | O -> [],b'
        | S f' ->
          let xs,b'' = decode'0 halt0 halt_dec0 encode_A decoder_A b' f'
          in
          (x::xs),b'')

(** val steppingList_decode :
    'a1 -> ('a1 -> bool) -> nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2)
    decoder -> 'a2 -> 'a1 data_t*'a2 **)

let steppingList_decode halt0 halt_dec0 fuel encode_A decoder_A b =
  (fst (decode'0 halt0 halt_dec0 encode_A decoder_A b fuel)),(snd
                                                               (decode'0
                                                                 halt0
                                                                 halt_dec0
                                                                 encode_A
                                                                 decoder_A
                                                                 b fuel))

(** val steppingList_decoder :
    'a1 -> ('a1 -> bool) -> nat -> (('a1*bin_t) -> bin_t) -> ('a1*bin_t,
    bin_t) decoder -> ('a1 data_t*bin_t, bin_t) decoder **)

let steppingList_decoder halt0 halt_dec0 fuel encode_A decoder_A =
  steppingList_decode halt0 halt_dec0 fuel encode_A decoder_A

type 'a data_t0 = 'a list

(** val fixList_getlength : nat -> 'a1 data_t0 -> n **)

let fixList_getlength size0 ls =
  N.of_nat (length ls)

(** val encode'1 : (('a1*'a2) -> 'a2) -> 'a1 list -> 'a2 -> 'a2 **)

let rec encode'1 encode_A xs ext =
  match xs with
  | [] -> ext
  | x::xs0 -> encode_A (x,(encode'1 encode_A xs0 ext))

(** val fixList_encode :
    nat -> (('a1*'a2) -> 'a2) -> ('a1 data_t0*'a2) -> 'a2 **)

let fixList_encode size0 encode_A bundle =
  encode'1 encode_A (fst bundle) (snd bundle)

(** val decode'1 :
    (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> nat -> 'a2 -> 'a1
    list*'a2 **)

let rec decode'1 encode_A decoder_A len b =
  match len with
  | O -> [],b
  | S size' ->
    let _data,_bin = decode encode_A decoder_A b in
    let _rest,_bin' = decode'1 encode_A decoder_A size' _bin in
    (_data::_rest),_bin'

(** val fixList_decode :
    nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> nat -> 'a2 ->
    'a1 data_t0*'a2 **)

let fixList_decode size0 encode_A decoder_A len b =
  (fst (decode'1 encode_A decoder_A (min (pred (exp2_nat size0)) len) b)),
    (snd (decode'1 encode_A decoder_A len b))

(** val fixList_decoder :
    nat -> n -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> ('a1
    data_t0*'a2, 'a2) decoder **)

let fixList_decoder size0 len encode_A decoder_A =
  fixList_decode size0 encode_A decoder_A (N.to_nat len)

type 'a data_t1 = 'a list

(** val encode'2 : (('a1*'a2) -> 'a2) -> 'a1 list -> 'a2 -> 'a2 **)

let rec encode'2 encode_A xs ext =
  match xs with
  | [] -> ext
  | x::xs0 -> encode_A (x,(encode'2 encode_A xs0 ext))

(** val fixList2_encode :
    nat -> (('a1*'a2) -> 'a2) -> ('a1 data_t1*'a2) -> 'a2 **)

let fixList2_encode size0 encode_A bundle =
  encode'2 encode_A (fst bundle) (snd bundle)

(** val decode'2 :
    (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> nat -> 'a2 -> 'a1
    list*'a2 **)

let rec decode'2 encode_A decoder_A len b =
  match len with
  | O -> [],b
  | S size' ->
    let _data,_bin = decode encode_A decoder_A b in
    let _rest,_bin' = decode'2 encode_A decoder_A size' _bin in
    (_data::_rest),_bin'

(** val fixList2_decode :
    nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> 'a2 -> 'a1
    data_t1*'a2 **)

let fixList2_decode size0 encode_A decoder_A b =
  (fst (decode'2 encode_A decoder_A size0 b)),(snd
                                                (decode'2 encode_A
                                                  decoder_A size0 b))

(** val fixList2_decoder :
    nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> ('a1
    data_t1*'a2, 'a2) decoder **)

let fixList2_decoder size0 encode_A decoder_A =
  fixList2_decode size0 encode_A decoder_A

(** val zero0 : char **)

let zero0 =
  '\000'

(** val one0 : char **)

let one0 =
  '\001'

(** val shift : bool -> char -> char **)

let shift c a =
  (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a1 a2 a3 a4 a5 a6 a7 a8 ->
    (* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
    (c, a1, a2, a3, a4, a5, a6,
    a7))
    a

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

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b::l' ->
  N.add (if b then Npos XH else N0)
    (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *) (fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[])))))))))
    a

(** val char_encode : char -> bin_t **)

let char_encode c =
  fixInt_encode (S (S (S (S (S (S (S (S O)))))))) (n_of_ascii c)

(** val char_decode : bin_t -> char*bin_t **)

let char_decode b =
  let n0,ext = fixInt_decode (S (S (S (S (S (S (S (S O)))))))) b in
  (ascii_of_N n0),ext

(** val bool_encode : bool -> bin_t **)

let bool_encode b =
  b::[]

(** val bool_decode : bin_t -> bool*bin_t **)

let bool_decode = function
| [] -> false,[]
| x::xs -> x,xs

type word_t = char list

(** val halt : word_t **)

let halt =
  []

(** val halt_dec : word_t -> bool **)

let halt_dec = function
| [] -> true
| a0::l -> false

type name_t = word_t list

(** val encode_word : (word_t*bin_t) -> bool list **)

let encode_word bundle =
  bin_encode_transform_pair
    (fixInt_encode (S (S (S (S (S (S (S (S O)))))))))
    ((fixList_getlength (S (S (S (S (S (S (S (S O)))))))) (fst bundle)),
    (fixList_encode (S (S (S (S (S (S (S (S O))))))))
      (bin_encode_transform_pair char_encode) bundle))

(** val word_decoder : (word_t*bin_t, bool list) decoder **)

let word_decoder =
  decode_unpack (fun data ->
    fixList_getlength (S (S (S (S (S (S (S (S O)))))))) (fst data))
    (bin_encode_transform_pair
      (fixInt_encode (S (S (S (S (S (S (S (S O))))))))))
    (fixList_encode (S (S (S (S (S (S (S (S O))))))))
      (bin_encode_transform_pair char_encode))
    (bin_encode_transform_pair_Decoder
      (fixInt_encode (S (S (S (S (S (S (S (S O)))))))))
      (fixInt_decode (S (S (S (S (S (S (S (S O)))))))))) (fun proj ->
    strengthen_Decoder
      (fixList_encode (S (S (S (S (S (S (S (S O))))))))
        (bin_encode_transform_pair char_encode))
      (fixList_decoder (S (S (S (S (S (S (S (S O)))))))) proj
        (bin_encode_transform_pair char_encode)
        (bin_encode_transform_pair_Decoder char_encode char_decode)))

(** val encode_name : (word_t data_t*bin_t) -> bin_t **)

let encode_name =
  steppingList_encode halt (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    encode_word

(** val name_decoder : (word_t data_t*bin_t, bin_t) decoder **)

let name_decoder =
  steppingList_decoder halt halt_dec (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    encode_word word_decoder

type type_t =
| A
| CNAME
| NS
| MX

type class_t =
| IN
| CH
| HS

(** val fixInt_of_type : type_t -> n **)

let fixInt_of_type = function
| A -> Npos XH
| CNAME -> Npos (XI (XO XH))
| NS -> Npos (XO XH)
| MX -> Npos (XI (XI (XI XH)))

(** val fixInt_of_class : class_t -> n **)

let fixInt_of_class = function
| IN -> Npos XH
| CH -> Npos (XI XH)
| HS -> Npos (XO (XO XH))

(** val type_to_FixInt_decoder : (type_t, n) decoder **)

let type_to_FixInt_decoder n0 =
  if N.eq_dec n0 (Npos XH)
  then A
  else if N.eq_dec n0 (Npos (XI (XO XH)))
       then CNAME
       else if N.eq_dec n0 (Npos (XO XH)) then NS else MX

(** val class_to_FixInt_decoder : (class_t, n) decoder **)

let class_to_FixInt_decoder n0 =
  if N.eq_dec n0 (Npos XH)
  then IN
  else if N.eq_dec n0 (Npos (XI XH)) then CH else HS

type question_t = { qname : name_t; qtype : type_t; qclass : class_t }

(** val qname : question_t -> name_t **)

let qname x = x.qname

(** val qtype : question_t -> type_t **)

let qtype x = x.qtype

(** val qclass : question_t -> class_t **)

let qclass x = x.qclass

(** val encode_question : (question_t*bin_t) -> bin_t **)

let encode_question bundle =
  encode_name
    ((fst bundle).qname,(bin_encode_transform_pair
                          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S O)))))))))))))))))
                          ((fixInt_of_type (fst bundle).qtype),(bin_encode_transform_pair
                                                                 (fixInt_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O)))))))))))))))))
                                                                 (
                                                                 (fixInt_of_class
                                                                 (fst
                                                                 bundle).qclass),
                                                                 (snd
                                                                 bundle))))))

(** val question_decoder : (question_t*bin_t, bin_t) decoder **)

let question_decoder =
  decode_unpack (fun data -> (fst data).qname) encode_name (fun data ->
    bin_encode_transform_pair
      (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))
      ((fixInt_of_type (fst data).qtype),(bin_encode_transform_pair
                                           (fixInt_encode (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S
                                             (S O)))))))))))))))))
                                           ((fixInt_of_class
                                              (fst data).qclass),(snd
                                                                 data)))))
    name_decoder (fun proj ->
    decode_unpack (fun data -> (fst data).qtype) (fun bundle ->
      bin_encode_transform_pair
        (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))) ((fixInt_of_type (fst bundle)),(snd bundle)))
      (fun data ->
      bin_encode_transform_pair
        (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))
        ((fixInt_of_class (fst data).qclass),(snd data)))
      (nested_decoder (fun data -> (fixInt_of_type (fst data)),(snd data))
        (bin_encode_transform_pair
          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))
        (unprod_decoder fixInt_of_type type_to_FixInt_decoder)
        (bin_encode_transform_pair_Decoder
          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))
          (fixInt_decode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))) (fun proj0 ->
      decode_unpack (fun data -> (fst data).qclass) (fun bundle ->
        bin_encode_transform_pair
          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))
          ((fixInt_of_class (fst bundle)),(snd bundle))) (fun data ->
        let x,y = data in y)
        (nested_decoder (fun data ->
          (fixInt_of_class (fst data)),(snd data))
          (bin_encode_transform_pair
            (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))
          (unprod_decoder fixInt_of_class class_to_FixInt_decoder)
          (bin_encode_transform_pair_Decoder
            (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))
            (fixInt_decode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))) (fun proj1 b -> { qname = proj; qtype =
        proj0; qclass = proj1 },b)))

type packet_t = { pid : bool list; pmask : bool list;
                  pquestion : question_t list; panswer : question_t list;
                  pauthority : question_t list;
                  padditional : question_t list }

(** val pid : packet_t -> bool list **)

let pid x = x.pid

(** val pmask : packet_t -> bool list **)

let pmask x = x.pmask

(** val pquestion : packet_t -> question_t list **)

let pquestion x = x.pquestion

(** val panswer : packet_t -> question_t list **)

let panswer x = x.panswer

(** val pauthority : packet_t -> question_t list **)

let pauthority x = x.pauthority

(** val padditional : packet_t -> question_t list **)

let padditional x = x.padditional

(** val packet_decoder : (packet_t*bin_t, bin_t) decoder **)

let packet_decoder =
  decode_unpack (fun data -> (fst data).pid)
    (fixList2_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))) (bin_encode_transform_pair bool_encode))
    (fun data ->
    fixList2_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))) (bin_encode_transform_pair bool_encode)
      ((fst data).pmask,(bin_encode_transform_pair
                          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S O)))))))))))))))))
                          ((fixList_getlength (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S O))))))))))))))))
                             (fst data).pquestion),(bin_encode_transform_pair
                                                     (fixInt_encode (S (S
                                                       (S (S (S (S (S (S
                                                       (S (S (S (S (S (S
                                                       (S (S
                                                       O)))))))))))))))))
                                                     ((fixList_getlength
                                                        (S (S (S (S (S (S
                                                        (S (S (S (S (S (S
                                                        (S (S (S (S
                                                        O))))))))))))))))
                                                        (fst data).panswer),
                                                     (bin_encode_transform_pair
                                                       (fixInt_encode (S
                                                         (S (S (S (S (S (S
                                                         (S (S (S (S (S (S
                                                         (S (S (S
                                                         O)))))))))))))))))
                                                       ((fixList_getlength
                                                          (S (S (S (S (S
                                                          (S (S (S (S (S
                                                          (S (S (S (S (S
                                                          (S
                                                          O))))))))))))))))
                                                          (fst data).pauthority),
                                                       (bin_encode_transform_pair
                                                         (fixInt_encode (S
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           O)))))))))))))))))
                                                         ((fixList_getlength
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S
                                                            O))))))))))))))))
                                                            (fst data).padditional),
                                                         (fixList_encode
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           (S
                                                           O))))))))))))))))
                                                           encode_question
                                                           ((fst data).pquestion,
                                                           (fixList_encode
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             O))))))))))))))))
                                                             encode_question
                                                             ((fst data).panswer,
                                                             (fixList_encode
                                                               (S (S (S (S
                                                               (S (S (S (S
                                                               (S (S (S (S
                                                               (S (S (S (S
                                                               O))))))))))))))))
                                                               encode_question
                                                               ((fst data).pauthority,
                                                               (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 (
                                                                 (fst
                                                                 data).padditional,
                                                                 (snd
                                                                 data)))))))))))))))))))
    (fixList2_decoder (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))) (bin_encode_transform_pair bool_encode)
      (bin_encode_transform_pair_Decoder bool_encode bool_decode))
    (fun proj ->
    decode_unpack (fun data -> (fst data).pmask)
      (fixList2_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) (bin_encode_transform_pair bool_encode))
      (fun data ->
      bin_encode_transform_pair
        (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))
        ((fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S O)))))))))))))))) (fst data).pquestion),(bin_encode_transform_pair
                                                        (fixInt_encode (S
                                                          (S (S (S (S (S
                                                          (S (S (S (S (S
                                                          (S (S (S (S (S
                                                          O)))))))))))))))))
                                                        ((fixList_getlength
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           (S
                                                           O))))))))))))))))
                                                           (fst data).panswer),
                                                        (bin_encode_transform_pair
                                                          (fixInt_encode
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S
                                                            O)))))))))))))))))
                                                          ((fixList_getlength
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             O))))))))))))))))
                                                             (fst data).pauthority),
                                                          (bin_encode_transform_pair
                                                            (fixInt_encode
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              O)))))))))))))))))
                                                            ((fixList_getlength
                                                               (S (S (S (S
                                                               (S (S (S (S
                                                               (S (S (S (S
                                                               (S (S (S (S
                                                               O))))))))))))))))
                                                               (fst data).padditional),
                                                            (fixList_encode
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              O))))))))))))))))
                                                              encode_question
                                                              ((fst data).pquestion,
                                                              (fixList_encode
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S
                                                                O))))))))))))))))
                                                                encode_question
                                                                ((fst
                                                                 data).panswer,
                                                                (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 ((fst
                                                                 data).pauthority,
                                                                 (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 ((fst
                                                                 data).padditional,
                                                                 (snd
                                                                 data)))))))))))))))))
      (fixList2_decoder (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) (bin_encode_transform_pair bool_encode)
        (bin_encode_transform_pair_Decoder bool_encode bool_decode))
      (fun proj0 ->
      decode_unpack (fun data ->
        fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) (fst data).pquestion)
        (bin_encode_transform_pair
          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))) (fun data ->
        bin_encode_transform_pair
          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))
          ((fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S O)))))))))))))))) (fst data).panswer),(bin_encode_transform_pair
                                                        (fixInt_encode (S
                                                          (S (S (S (S (S
                                                          (S (S (S (S (S
                                                          (S (S (S (S (S
                                                          O)))))))))))))))))
                                                        ((fixList_getlength
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           (S (S (S (S (S
                                                           (S
                                                           O))))))))))))))))
                                                           (fst data).pauthority),
                                                        (bin_encode_transform_pair
                                                          (fixInt_encode
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S
                                                            O)))))))))))))))))
                                                          ((fixList_getlength
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             (S (S (S (S
                                                             O))))))))))))))))
                                                             (fst data).padditional),
                                                          (fixList_encode
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            (S
                                                            O))))))))))))))))
                                                            encode_question
                                                            ((fst data).pquestion,
                                                            (fixList_encode
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              O))))))))))))))))
                                                              encode_question
                                                              ((fst data).panswer,
                                                              (fixList_encode
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S
                                                                O))))))))))))))))
                                                                encode_question
                                                                ((fst
                                                                 data).pauthority,
                                                                (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 ((fst
                                                                 data).padditional,
                                                                 (snd
                                                                 data)))))))))))))))
        (bin_encode_transform_pair_Decoder
          (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))
          (fixInt_decode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))) (fun proj1 ->
        decode_unpack (fun data ->
          fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S O)))))))))))))))) (fst data).panswer)
          (bin_encode_transform_pair
            (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))) (fun data ->
          bin_encode_transform_pair
            (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))
            ((fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S O)))))))))))))))) (fst data).pauthority),(bin_encode_transform_pair
                                                                (fixInt_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O)))))))))))))))))
                                                                ((fixList_getlength
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 (fst
                                                                 data).padditional),
                                                                (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 ((fst
                                                                 data).pquestion,
                                                                 (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 ((fst
                                                                 data).panswer,
                                                                 (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 ((fst
                                                                 data).pauthority,
                                                                 (fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 ((fst
                                                                 data).padditional,
                                                                 (snd
                                                                 data)))))))))))))
          (bin_encode_transform_pair_Decoder
            (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))
            (fixInt_decode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))) (fun proj2 ->
          decode_unpack (fun data ->
            fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S O)))))))))))))))) (fst data).pauthority)
            (bin_encode_transform_pair
              (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S O)))))))))))))))))) (fun data ->
            bin_encode_transform_pair
              (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S O)))))))))))))))))
              ((fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S O)))))))))))))))) (fst data).padditional),
              (fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S O)))))))))))))))) encode_question
                ((fst data).pquestion,(fixList_encode (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S
                                        O)))))))))))))))) encode_question
                                        ((fst data).panswer,(fixList_encode
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              O))))))))))))))))
                                                              encode_question
                                                              ((fst data).pauthority,
                                                              (fixList_encode
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S
                                                                O))))))))))))))))
                                                                encode_question
                                                                ((fst
                                                                 data).padditional,
                                                                (snd data)))))))))))
            (bin_encode_transform_pair_Decoder
              (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S O)))))))))))))))))
              (fixInt_decode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S O)))))))))))))))))) (fun proj3 ->
            decode_unpack (fun data ->
              fixList_getlength (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S O)))))))))))))))) (fst data).padditional)
              (bin_encode_transform_pair
                (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S O)))))))))))))))))) (fun data ->
              fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S O)))))))))))))))) encode_question
                ((fst data).pquestion,(fixList_encode (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S
                                        O)))))))))))))))) encode_question
                                        ((fst data).panswer,(fixList_encode
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              (S (S (S (S
                                                              O))))))))))))))))
                                                              encode_question
                                                              ((fst data).pauthority,
                                                              (fixList_encode
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S (S (S
                                                                (S
                                                                O))))))))))))))))
                                                                encode_question
                                                                ((fst
                                                                 data).padditional,
                                                                (snd data)))))))))
              (bin_encode_transform_pair_Decoder
                (fixInt_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S O)))))))))))))))))
                (fixInt_decode (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S O)))))))))))))))))) (fun proj4 ->
              decode_unpack (fun data -> (fst data).pquestion)
                (fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S O)))))))))))))))) encode_question) (fun data ->
                fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S O)))))))))))))))) encode_question
                  ((fst data).panswer,(fixList_encode (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S
                                        O)))))))))))))))) encode_question
                                        ((fst data).pauthority,(fixList_encode
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S (S (S
                                                                 (S
                                                                 O))))))))))))))))
                                                                 encode_question
                                                                 (
                                                                 (fst
                                                                 data).padditional,
                                                                 (snd
                                                                 data)))))))
                (fixList_decoder (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S O)))))))))))))))) proj1 encode_question
                  question_decoder) (fun proj5 ->
                decode_unpack (fun data -> (fst data).panswer)
                  (fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S O)))))))))))))))) encode_question)
                  (fun data ->
                  fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S O)))))))))))))))) encode_question
                    ((fst data).pauthority,(fixList_encode (S (S (S (S (S
                                             (S (S (S (S (S (S (S (S (S (S
                                             (S O))))))))))))))))
                                             encode_question
                                             ((fst data).padditional,
                                             (snd data)))))
                  (fixList_decoder (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S O)))))))))))))))) proj2 encode_question
                    question_decoder) (fun proj6 ->
                  decode_unpack (fun data -> (fst data).pauthority)
                    (fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S O)))))))))))))))) encode_question)
                    (fun data ->
                    fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S O)))))))))))))))) encode_question
                      ((fst data).padditional,(snd data)))
                    (fixList_decoder (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S O)))))))))))))))) proj3 encode_question
                      question_decoder) (fun proj7 ->
                    decode_unpack (fun data -> (fst data).padditional)
                      (fixList_encode (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S O)))))))))))))))) encode_question) snd
                      (fixList_decoder (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S O)))))))))))))))) proj4
                        encode_question question_decoder) (fun proj8 b ->
                      { pid = proj; pmask = proj0; pquestion = proj5;
                      panswer = proj6; pauthority = proj7; padditional =
                      proj8 },b))))))))))

let packet_bin = [true; true; false; true; true; false; true; true; false; true;
  false; false; false; false; true; false; false; false; false; false;
  false; false; false; true; false; false; false; false; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; false; false; false; false; false; true; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; true; true; false; true; true; true; false; true;
  true; true; false; true; true; true; false; true; true; true;
  false; true; true; true; false; true; true; true; false; false;
  false; false; true; true; false; false; false; true; true; false;
  true; true; true; false; false; true; true; false; true; true;
  true; true; false; true; true; true; false; false; true; false;
  false; true; true; true; false; true; false; false; false; true;
  true; false; true; false; false; false; false; true; true; false;
  false; true; false; true; false; true; true; false; false; false;
  false; true; false; true; true; true; false; false; true; true;
  false; true; true; true; false; true; false; false; false; true;
  true; false; false; true; false; true; false; true; true; true;
  false; false; true; false; false; true; true; false; true; true;
  true; false; false; false; false; false; false; false; true; true;
  false; true; true; false; false; true; false; true; false; true;
  true; false; false; true; false; false; false; true; true; true;
  false; true; false; true; false; false; false; false; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; false; false; false; false; false; true; false; false;
  false; false; false; false; false; false; false; false; false; false;
  false; false; false; true; ];;

let answer = packet_decoder packet_bin;;
