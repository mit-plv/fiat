type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a sumor =
| Inleft of 'a
| Inright

val pred : nat -> nat

val plus : nat -> nat -> nat

val minus : nat -> nat -> nat

val min : nat -> nat -> nat

val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

type ('data_t, 'bin_t) decoder =
  'bin_t -> 'data_t
  (* singleton inductive, whose constructor was Build_decoder *)

val decode : ('a1 -> 'a2) -> ('a1, 'a2) decoder -> 'a2 -> 'a1

val unpacking_decoder :
  ('a1 -> 'a3) -> (('a3*'a2) -> 'a2) -> ('a1 -> 'a2) -> ('a3*'a2, 'a2)
  decoder -> ('a3 -> ('a1, 'a2) decoder) -> ('a1, 'a2) decoder

val strengthening_decoder :
  ('a1 -> 'a2) -> ('a1, 'a2) decoder -> ('a1, 'a2) decoder

val nesting_decoder :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) decoder -> ('a2, 'a3) decoder
  -> ('a1, 'a3) decoder

val unproding_decoder :
  ('a1 -> 'a2) -> ('a1, 'a2) decoder -> ('a1*'a3, 'a2*'a3) decoder

type bin_t = bool list

val bin_encode_transform_pair : ('a1 -> bin_t) -> ('a1*bin_t) -> bool list

val bin_encode_transform_pair_decoder :
  ('a1 -> bin_t) -> (bin_t -> 'a1*bin_t) -> ('a1*bin_t, bool list) decoder

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive*mask) ->
    positive*mask
  
  val sqrtrem : positive -> positive*mask
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn : nat -> positive -> positive -> positive*(positive*positive)
  
  val ggcd : positive -> positive -> positive*(positive*positive)
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
 end

module Coq_Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont : positive -> positive -> comparison -> comparison
  
  val compare : positive -> positive -> comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive*mask) ->
    positive*mask
  
  val sqrtrem : positive -> positive*mask
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn : nat -> positive -> positive -> positive*(positive*positive)
  
  val ggcd : positive -> positive -> positive*(positive*positive)
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
  
  val eq_dec : positive -> positive -> bool
  
  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  val coq_PeanoView_rect :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val coq_PeanoView_rec :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : positive -> coq_PeanoView
  
  val coq_PeanoView_iter :
    'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val eqb_spec : positive -> positive -> reflect
  
  val switch_Eq : comparison -> comparison -> comparison
  
  val mask2cmp : mask -> comparison
  
  val leb_spec0 : positive -> positive -> reflect
  
  val ltb_spec0 : positive -> positive -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
      -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
      -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : positive -> positive -> bool
    
    val min_case_strong :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
      -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      positive -> positive -> (positive -> positive -> __ -> 'a1 -> 'a1)
      -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : positive -> positive -> bool
   end
  
  val max_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : positive -> positive -> bool
  
  val min_case_strong :
    positive -> positive -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : positive -> positive -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : positive -> positive -> bool
 end

module N : 
 sig 
  type t = n
  
  val zero : n
  
  val one : n
  
  val two : n
  
  val succ_double : n -> n
  
  val double : n -> n
  
  val succ : n -> n
  
  val pred : n -> n
  
  val succ_pos : n -> positive
  
  val add : n -> n -> n
  
  val sub : n -> n -> n
  
  val mul : n -> n -> n
  
  val compare : n -> n -> comparison
  
  val eqb : n -> n -> bool
  
  val leb : n -> n -> bool
  
  val ltb : n -> n -> bool
  
  val min : n -> n -> n
  
  val max : n -> n -> n
  
  val div2 : n -> n
  
  val even : n -> bool
  
  val odd : n -> bool
  
  val pow : n -> n -> n
  
  val square : n -> n
  
  val log2 : n -> n
  
  val size : n -> n
  
  val size_nat : n -> nat
  
  val pos_div_eucl : positive -> n -> n*n
  
  val div_eucl : n -> n -> n*n
  
  val div : n -> n -> n
  
  val modulo : n -> n -> n
  
  val gcd : n -> n -> n
  
  val ggcd : n -> n -> n*(n*n)
  
  val sqrtrem : n -> n*n
  
  val sqrt : n -> n
  
  val coq_lor : n -> n -> n
  
  val coq_land : n -> n -> n
  
  val ldiff : n -> n -> n
  
  val coq_lxor : n -> n -> n
  
  val shiftl_nat : n -> nat -> n
  
  val shiftr_nat : n -> nat -> n
  
  val shiftl : n -> n -> n
  
  val shiftr : n -> n -> n
  
  val testbit_nat : n -> nat -> bool
  
  val testbit : n -> n -> bool
  
  val to_nat : n -> nat
  
  val of_nat : nat -> n
  
  val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : n -> n -> bool
  
  val discr : n -> positive sumor
  
  val binary_rect :
    'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val binary_rec :
    'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val leb_spec0 : n -> n -> reflect
  
  val ltb_spec0 : n -> n -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  module Private_OrderTac : 
   sig 
    module IsTotal : 
     sig 
      
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : n -> n
  
  val log2_up : n -> n
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : n -> n -> n
  
  val eqb_spec : n -> n -> reflect
  
  val b2n : bool -> n
  
  val setbit : n -> n -> n
  
  val clearbit : n -> n -> n
  
  val ones : n -> n
  
  val lnot : n -> n -> n
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
      -> 'a1
    
    val max_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : n -> n -> bool
    
    val min_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
      -> 'a1
    
    val min_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : n -> n -> bool
   end
  
  val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : n -> n -> bool
  
  val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : n -> n -> bool
 end

val exp2' : nat -> positive

val exp2 : nat -> n

val exp2_nat : nat -> nat

val encode'' : positive -> bin_t -> bool list

val encode' : n -> bool list

val pad : bin_t -> nat -> bin_t

val fixInt_encode_inner : nat -> n -> bin_t

val decode'' : bin_t -> nat -> positive -> positive*bin_t

val decode' : bin_t -> nat -> n*bin_t

val fixInt_decode : nat -> bin_t -> n*bin_t

val fixInt_eq_dec : nat -> n -> n -> bool

val fixInt_encode : nat -> (n*bin_t) -> bool list

val fixInt_decoder : nat -> (n*bin_t, bool list) decoder

type 'a data_t = 'a list

val encode'0 : 'a1 -> (('a1*'a2) -> 'a2) -> 'a1 list -> 'a2 -> 'a2

val steppingList_encode :
  'a1 -> nat -> (('a1*'a2) -> 'a2) -> ('a1 data_t*'a2) -> 'a2

val decode'0 :
  'a1 -> ('a1 -> bool) -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder ->
  'a2 -> nat -> 'a1 list*'a2

val steppingList_decode :
  'a1 -> ('a1 -> bool) -> nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2)
  decoder -> 'a2 -> 'a1 data_t*'a2

val steppingList_decoder :
  'a1 -> ('a1 -> bool) -> nat -> (('a1*bin_t) -> bin_t) -> ('a1*bin_t,
  bin_t) decoder -> ('a1 data_t*bin_t, bin_t) decoder

type 'a data_t0 = 'a list

val fixList_getlength : nat -> 'a1 data_t0 -> n

val encode'1 : (('a1*'a2) -> 'a2) -> 'a1 list -> 'a2 -> 'a2

val fixList_encode : nat -> (('a1*'a2) -> 'a2) -> ('a1 data_t0*'a2) -> 'a2

val decode'1 :
  (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> nat -> 'a2 -> 'a1
  list*'a2

val fixList_decode :
  nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> nat -> 'a2 -> 'a1
  data_t0*'a2

val fixList_decoder :
  nat -> n -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> ('a1
  data_t0*'a2, 'a2) decoder

type 'a data_t1 = 'a list

val encode'2 : (('a1*'a2) -> 'a2) -> 'a1 list -> 'a2 -> 'a2

val fixList2_encode :
  nat -> (('a1*'a2) -> 'a2) -> ('a1 data_t1*'a2) -> 'a2

val decode'2 :
  (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> nat -> 'a2 -> 'a1
  list*'a2

val fixList2_decode :
  nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> 'a2 -> 'a1
  data_t1*'a2

val fixList2_decoder :
  nat -> (('a1*'a2) -> 'a2) -> ('a1*'a2, 'a2) decoder -> ('a1 data_t1*'a2,
  'a2) decoder

val zero0 : char

val one0 : char

val shift : bool -> char -> char

val ascii_of_pos : positive -> char

val ascii_of_N : n -> char

val n_of_digits : bool list -> n

val n_of_ascii : char -> n

val char_encode_inner : char -> bin_t

val char_decode : bin_t -> char*bin_t

val char_encode : (char*bin_t) -> bool list

val char_decoder : (char*bin_t, bool list) decoder

val bool_encode_inner : bool -> bin_t

val bool_decode : bin_t -> bool*bin_t

val bool_encode : (bool*bin_t) -> bool list

val bool_decoder : (bool*bin_t, bool list) decoder

type type_t =
| A
| CNAME
| NS
| MX

type class_t =
| IN
| CH
| HS

type word_t =
  char list
  (* singleton inductive, whose constructor was Build_word_t *)

val word_attr : word_t -> char list

val halt : word_t

val halt_dec : word_t -> bool

type name_t =
  word_t list
  (* singleton inductive, whose constructor was Build_name_t *)

val name_attr : name_t -> word_t list

type question_t = { qname : name_t; qtype : type_t; qclass : class_t }

val qname : question_t -> name_t

val qtype : question_t -> type_t

val qclass : question_t -> class_t

type resource_t = { rname : name_t; rtype : type_t; rclass : class_t;
                    rttl : n; rdata : bool list }

val rname : resource_t -> name_t

val rtype : resource_t -> type_t

val rclass : resource_t -> class_t

val rttl : resource_t -> n

val rdata : resource_t -> bool list

type packet_t = { pid : bool list; pmask : bool list;
                  pquestion : question_t list; panswer : resource_t list;
                  pauthority : resource_t list;
                  padditional : resource_t list }

val pid : packet_t -> bool list

val pmask : packet_t -> bool list

val pquestion : packet_t -> question_t list

val panswer : packet_t -> resource_t list

val pauthority : packet_t -> resource_t list

val padditional : packet_t -> resource_t list

val fixInt_of_type : type_t -> n

val fixInt_of_class : class_t -> n

val encode_word : (word_t*bin_t) -> bool list

val encode_name : (name_t*bin_t) -> bin_t

val encode_question : (question_t*bin_t) -> bin_t

val encode_resource : (resource_t*bin_t) -> bin_t

val encode_packet : (packet_t*bin_t) -> bin_t

val type_to_FixInt_decoder : (type_t, n) decoder

val class_to_FixInt_decoder : (class_t, n) decoder

val word_decoder : (word_t*bin_t, bool list) decoder

val name_decoder : (name_t*bin_t, bin_t) decoder

val question_decoder : (question_t*bin_t, bin_t) decoder

val resource_decoder : (resource_t*bin_t, bin_t) decoder

val packet_decoder : (packet_t*bin_t, bin_t) decoder

val packet1 : bool list

