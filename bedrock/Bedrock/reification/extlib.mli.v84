
(** Interface with Coq where we define some handlers for Coq's API,
    and we import several definitions from Coq's standard library.

    This general purpose library could be reused by other plugins.
   
    Some salient points:
    - we use Caml's module system to mimic Coq's one, and avoid cluttering
    the namespace;
    - we also provide several handlers for standard coq tactics, in
    order to provide a unified setting (we replace functions that
    modify the evar_map by functions that operate on the whole
    goal, and repack the modified evar_map with it).

*)

(** {2 Getting Coq terms from the environment}  *)

val init_constant : string list -> string -> Term.constr

(** {2 General purpose functions} *)

type goal_sigma =  Proof_type.goal Tacmach.sigma
val goal_update : goal_sigma -> Evd.evar_map -> goal_sigma
val resolve_one_typeclass : Proof_type.goal Tacmach.sigma -> Term.types -> Term.constr * goal_sigma
val cps_resolve_one_typeclass: ?error:string -> Term.types -> (Term.constr  -> Proof_type.tactic) -> Proof_type.tactic
val nf_evar : goal_sigma -> Term.constr -> Term.constr
val fresh_evar :goal_sigma -> Term.types ->  Term.constr* goal_sigma
val evar_unit :goal_sigma ->Term.constr ->  Term.constr* goal_sigma
val evar_binary: goal_sigma -> Term.constr -> Term.constr* goal_sigma
val evar_relation: goal_sigma -> Term.constr -> Term.constr* goal_sigma
val cps_evar_relation : Term.constr -> (Term.constr -> Proof_type.tactic) -> Proof_type.tactic
(** [cps_mk_letin name v] binds the constr [v] using a letin tactic  *)
val cps_mk_letin : string -> Term.constr -> ( Term.constr -> Proof_type.tactic) -> Proof_type.tactic


val decomp_term : Term.constr -> (Term.constr , Term.types) Term.kind_of_term
val lapp : Term.constr lazy_t -> Term.constr array -> Term.constr

type t = { body : Term.constr; 
	   ty : Term.types}

(** {2 Bindings with Coq' Standard Library}  *)

(** Coq lists *)
module List:
sig
  val _nil : Term.constr lazy_t
  val _cons : Term.constr lazy_t

  (** [of_list ty l]  *)
  val of_list:Term.constr ->Term.constr list ->Term.constr
   
  (** [type_of_list ty] *)
  val type_of_list:Term.constr ->Term.constr
    
  val of_constr : Term.constr -> Term.constr list * Term.types
end

module Tuple : sig
  val of_list : (Term.constr * Term.types) list -> Term.constr * Term.types       
end

module Logic : sig 
  val _not : Term.constr lazy_t
  val _false : Term.constr lazy_t
  val is_not : Term.constr -> bool
  val exists : unit -> Term.constr
  val conj : unit -> Term.constr 
  val and_ : unit -> Term.constr 
  val get_body_not : Term.constr -> Term.constr 
end

(** Coq pairs *)
module Pair:
sig
  val prod:Term.constr lazy_t
  val pair:Term.constr lazy_t
  val fst :Term.constr lazy_t
  val snd :Term.constr lazy_t
  val of_pair : Term.constr -> Term.constr ->  Term.constr * Term.constr -> Term.constr
  val of_pair' :  t * t -> t
end

module Bool : sig
  val typ : Term.constr lazy_t
  val of_bool : bool -> Term.constr
  val _true : Term.constr lazy_t
  val _false : Term.constr lazy_t

end


module Comparison : sig
  val typ : Term.constr lazy_t
  val eq : Term.constr lazy_t
  val lt : Term.constr lazy_t
  val gt : Term.constr lazy_t
end

module Leibniz : sig
  val eq_refl : Term.types -> Term.constr -> Term.constr
  val _eq : Term.constr lazy_t
  val _eq_refl : Term.constr lazy_t
  val eq : Term.types -> Term.constr -> Term.constr -> Term.constr 
  val match_eq : Term.constr ->  (Term.constr * Term.constr) option 
end

module Option : sig
  val _some : Term.constr lazy_t
  val _none : Term.constr lazy_t
  val typ : Term.constr lazy_t
  val some : Term.constr -> Term.constr -> Term.constr
  val none : Term.constr -> Term.constr
  val of_option : Term.constr -> Term.constr option -> Term.constr
  val of_option' : Term.types -> Term.constr option -> t
end   

(** Coq positive numbers (pos) *)
module Pos:
sig
  val typ:Term.constr lazy_t
  val of_int: int ->Term.constr
end

(** Coq unary numbers (peano) *)
module Nat:
sig
  val typ:Term.constr lazy_t
  val of_int: int ->Term.constr
  val _S : Term.constr lazy_t  
  val _O : Term.constr lazy_t
end

(** Sum  *)
module Sum : sig
  val sum : Term.constr -> Term.constr -> Term.constr
  val inl : Term.constr -> Term.constr -> Term.constr -> Term.constr
  val inr : Term.constr -> Term.constr -> Term.constr -> Term.constr
end

module Pair2  : sig
  val pair :  Term.constr -> Term.constr -> Term.constr * Term.constr -> Term.constr
  val prod : Term.constr -> Term.constr -> Term.constr
  
end


(** Coq typeclasses *)
module Classes:
sig
  val mk_morphism: Term.constr -> Term.constr -> Term.constr -> Term.constr
  val mk_equivalence: Term.constr ->  Term.constr -> Term.constr
  val mk_reflexive: Term.constr ->  Term.constr -> Term.constr
  val mk_transitive: Term.constr ->  Term.constr -> Term.constr
end

module Relation : sig
  type t = {carrier : Term.constr; r : Term.constr;}	
  val make : Term.constr -> Term.constr -> t
  val split : t -> Term.constr * Term.constr
end
   
module Transitive : sig
  type t =
      {
	carrier : Term.constr;
	leq : Term.constr;
	transitive : Term.constr;
      }
  val make : Term.constr -> Term.constr -> Term.constr -> t
  val infer : goal_sigma -> Term.constr -> Term.constr -> t  * goal_sigma
  val from_relation : goal_sigma -> Relation.t -> t * goal_sigma
  val cps_from_relation : Relation.t -> (t -> Proof_type.tactic) -> Proof_type.tactic
  val to_relation : t -> Relation.t
end
	
module Equivalence : sig
  type t =
      {
	carrier : Term.constr;
	eq : Term.constr;
	equivalence : Term.constr;	     
      } 
  val make  : Term.constr -> Term.constr -> Term.constr -> t
  val infer  : goal_sigma -> Term.constr -> Term.constr -> t  * goal_sigma
  val from_relation : goal_sigma -> Relation.t -> t * goal_sigma
  val cps_from_relation : Relation.t -> (t -> Proof_type.tactic) -> Proof_type.tactic
  val to_relation : t -> Relation.t
  val split : t -> Term.constr * Term.constr * Term.constr
end

(** [match_as_equation ?context goal c] try to decompose c as a
    relation applied to two terms. An optionnal rel_context can be
    provided to ensure that the term remains typable *)
val match_as_equation  : ?context:Term.rel_context -> goal_sigma -> Term.constr -> (Term.constr * Term.constr * Relation.t) option

(** {2 Some tacticials}  *)

(** time the execution of a tactic *)
val tclTIME : string -> Proof_type.tactic -> Proof_type.tactic

(** emit debug messages to see which tactics are failing *)
val tclDEBUG : string -> Proof_type.tactic -> Proof_type.tactic

(** print the current goal *)
val tclPRINT : Proof_type.tactic -> Proof_type.tactic


(** {2 Error related mechanisms}  *)

val anomaly : string -> 'a
val user_error : string -> 'a
val warning : string -> unit

