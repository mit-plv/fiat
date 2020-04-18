(** Interface with Coq *)
type constr = Term.constr

open Term
open Names
open Coqlib

(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "bedrock"

(* Getting constrs (primitive Coq terms) from existing Coq
   libraries. *)
let find_constant contrib dir s =
  Libnames.constr_of_global (Coqlib.find_reference contrib dir s)

let init_constant dir s = find_constant contrib_name dir s

(* A clause specifying that the [let] should not try to fold anything
   in the goal *)
let nowhere =
  { Tacexpr.onhyps = Some [];
    Tacexpr.concl_occs = false, []
  }

let cps_mk_letin
    (name:string)
    (c: constr)
    (k : constr -> Proof_type.tactic)
: Proof_type.tactic =
  fun goal ->
    let name = (Names.id_of_string name) in
    let name =  Tactics.fresh_id [] name goal in
    let letin = (Tactics.letin_tac None  (Name name) c None nowhere) in
      Tacticals.tclTHEN letin (k (mkVar name)) goal

(** {2 General functions}  *)

type goal_sigma =  Proof_type.goal Tacmach.sigma
let goal_update (goal : goal_sigma) evar_map : goal_sigma=
  let it = Tacmach.sig_it goal in
    Tacmach.re_sig it evar_map

let fresh_evar goal ty : constr * goal_sigma =
  let env = Tacmach.pf_env goal in
  let evar_map = Tacmach.project goal in
  let (em,x) = Evarutil.new_evar evar_map env ty in
    x,( goal_update goal em)
     
let resolve_one_typeclass goal ty : constr*goal_sigma=
  let env = Tacmach.pf_env goal in
  let evar_map = Tacmach.project goal in
  let em,c = Typeclasses.resolve_one_typeclass env evar_map ty in
    c, (goal_update goal em)

let general_error =
  "Cannot resolve a typeclass : please report"

let cps_resolve_one_typeclass ?error : Term.types -> (Term.constr  -> Proof_type.tactic) -> Proof_type.tactic = fun t k  goal  ->
  Tacmach.pf_apply
    (fun env em -> let em ,c =  
		  try Typeclasses.resolve_one_typeclass env em t
		  with Not_found ->
		    begin match error with
		      | None -> Util.anomaly  "Cannot resolve a typeclass : please report"
		      | Some x -> Util.error x
		    end
		in
		Tacticals.tclTHENLIST [Refiner.tclEVARS em; k c] goal
    )	goal


let nf_evar goal c : Term.constr=
  let evar_map = Tacmach.project goal in
    Evarutil.nf_evar evar_map c

let evar_unit (gl : goal_sigma) (x : constr) : constr * goal_sigma =
  let env = Tacmach.pf_env gl in
  let evar_map = Tacmach.project gl in
  let (em,x) = Evarutil.new_evar evar_map env x in
    x,(goal_update gl em)
     
let evar_binary (gl: goal_sigma) (x : constr) =
  let env = Tacmach.pf_env gl in
  let evar_map = Tacmach.project gl in
  let ty = mkArrow x (mkArrow x x) in
  let (em,x) = Evarutil.new_evar evar_map env  ty in
    x,( goal_update gl em)

let evar_relation (gl: goal_sigma) (x: constr) =
  let env = Tacmach.pf_env gl in
  let evar_map = Tacmach.project gl in
  let ty = mkArrow x (mkArrow x (mkSort prop_sort)) in
  let (em,r) = Evarutil.new_evar evar_map env  ty in
    r,( goal_update gl em)

let cps_evar_relation (x: constr) k = fun goal -> 
  Tacmach.pf_apply
    (fun env em ->
      let ty = mkArrow x (mkArrow x (mkSort prop_sort)) in
      let (em,r) = Evarutil.new_evar em env  ty in 	
      Tacticals.tclTHENLIST [Refiner.tclEVARS em; k r] goal
    )	goal

(* decomp_term :  constr -> (constr, types) kind_of_term *)
let decomp_term c = kind_of_term (strip_outer_cast c)
   
let lapp c v  = mkApp (Lazy.force c, v)

type t = { body : Term.constr; 
	   ty : Term.types
	 }

(** {2 Bindings with Coq' Standard Library}  *)
module Std = struct  		
(* Here we package the module to be able to use List, later *)


module Pair = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let prod = lazy (init_constant path "prod")
  let pair = lazy (init_constant path "pair")
  let of_pair' (x,y) = 
    {body = mkApp (Lazy.force pair, [| x.ty ; y.ty ; x.body; y.body |]); 
     ty = mkApp (Lazy.force prod,  [|x.ty ; y.ty |])}


  let of_pair t1 t2 (x,y) =
    mkApp (Lazy.force pair,  [| t1; t2; x ; y|] )
  let type_of_pair t1 t2 =
    mkApp (Lazy.force prod,  [| t1; t2 |])
  let fst = lazy (init_constant path "fst")
  let snd = lazy (init_constant path "snd")
end



module Tuple = struct 

  let path = ["Coq"; "Init"; "Datatypes"]
  let tt = lazy (init_constant path "tt")
  let unit =  lazy (init_constant path "unit")

  let rec of_list = function 
    | [] -> Lazy.force tt, Lazy.force unit
    | (e,t) :: q -> 
      let (q,t') = of_list q in 
      Pair.of_pair t t' (e,q), Pair.type_of_pair t t'
end

module Bool = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "bool")
  let _true = lazy (init_constant path "true")
  let _false = lazy (init_constant path "false")
  let of_bool  b =
    if b then Lazy.force _true else Lazy.force _false
end

module Comparison = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "comparison")
  let eq = lazy (init_constant path "Eq")
  let lt = lazy (init_constant path "Lt")
  let gt = lazy (init_constant path "Gt")
end

module Sum = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let init x = init_constant path x   
  let (@@) x l = Term.mkApp (x, Array.of_list l)
  let sum a b = (init "sum") @@ [a;b]
  let inl a b x = (init "inl") @@ [a ; b ; x] 
  let inr a b x = (init "inr") @@ [a ; b ; x]    
end

module Pair2 = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let init x = init_constant path x   
  let (@@) x l = Term.mkApp (x, Array.of_list l)
  let pair a b (x,y) = (init "pair") @@ [a;b;x;y]
  let prod a b = (init "prod") @@ [a;b]
end

module Leibniz = struct
  let path = ["Coq"; "Init"; "Logic"]
  let _eq_refl = lazy (init_constant path "eq_refl")
  let eq_refl ty x = lapp _eq_refl [| ty;x|]
  let _eq = lazy (init_constant path "eq")
  let match_eq (t : Term.constr) =
    begin  match decomp_term t with 
      | Term.App (hd, args) when (hd = Lazy.force _eq) -> Some (args.(1),args.(2))
      | _ -> None
    end
  let eq ty x y = lapp _eq [|ty ; x ; y|]
end


module Logic = struct  
  let path = ["Coq"; "Init"; "Logic"]
  let _not = lazy (init_constant path "not")
  let _false = lazy (init_constant path "False")

  let conj () = (init_constant path "conj") 
  let and_ () = (init_constant path "and") 

  let exists () = (init_constant path "ex")
  let is_not t = match decomp_term t with 
    | Term.App (hd, args) -> 
      Term.eq_constr hd (Lazy.force _not) 
    | Term.Prod (_,arg,body) -> 
      Term.eq_constr body (Lazy.force _false) 
    | _ -> false

  let get_body_not t = match decomp_term t with 
    | Term.App (hd, args) -> 
      args.(0)
    | Term.Prod (_,arg,body) -> 
      arg
    | _ -> assert false

end

module Option = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "option")
  let _some = lazy (init_constant path "Some")
  let _none = lazy (init_constant path "None")
  let some t x = mkApp (Lazy.force _some, [| t ; x|])
  let none t = mkApp (Lazy.force _none, [| t |])
  let of_option t x = match x with
    | Some x -> some t x
    | None -> none t
  let of_option' t x = match x with
    | Some x -> {body = some t x ; ty = lapp typ [| t |]}
    | None -> {body = none t ; ty = lapp typ [| t |]}

end   

module Pos = struct
   
    let path = ["Coq" ; "NArith"; "BinPos"]
    let typ = lazy (init_constant path "positive")
    let xI =      lazy (init_constant path "xI")
    let xO =      lazy (init_constant path "xO")
    let xH =      lazy (init_constant path "xH")

    (* A coq positive from an int *)
    let of_int n =
      let rec aux n =
	begin  match n with
	  | n when n < 1 -> assert false
	  | 1 -> Lazy.force xH
	  | n -> mkApp
	      (
		(if n mod 2 = 0
		 then Lazy.force xO
		 else Lazy.force xI
		),  [| aux (n/2)|]
	      )
	end
      in
	aux n
end
   
module Nat = struct
  let path = ["Coq" ; "Init"; "Datatypes"]
  let typ = lazy (init_constant path "nat")
  let _S =      lazy (init_constant  path "S")
  let _O =      lazy (init_constant  path "O")
    (* A coq nat from an int *)
  let of_int n =
    let rec aux n =
      begin  match n with
	| n when n < 0 -> assert false
	| 0 -> Lazy.force _O
	| n -> mkApp
	    (
	      (Lazy.force _S
	      ),  [| aux (n-1)|]
	    )
      end
    in
      aux n
end
   
(** Lists from the standard library*)
module List = struct
  let path = ["Coq"; "Init" ; "Datatypes";]
  let typ = lazy (init_constant path "list")
  let _nil = lazy (init_constant path "nil")
  let _cons = lazy (init_constant path "cons")
  let cons ty h t =
    mkApp (Lazy.force _cons, [|  ty; h ; t |])
  let nil ty =
    (mkApp (Lazy.force _nil, [|  ty |]))
  let rec of_list ty = function
    | [] -> nil ty
    | t::q -> cons ty t (of_list  ty q)
  let type_of_list ty =
    mkApp (Lazy.force typ, [|ty|])
  let of_constr e = 
    let rec aux e = 
      match decomp_term e with 
	| Term.App (hd, args) when Term.eq_constr hd (Lazy.force _cons) -> 
	  args.(1) :: aux args.(2)
	| Term.App (hd, args) when Term.eq_constr hd (Lazy.force _nil) -> 
	  []
	| _ -> Util.anomaly "parsing an ill-formed list "
    in 
    let ty = match decomp_term e with 
	Term.App (_, args) -> args.(0)
      | _ -> Util.anomaly "parsing an ill-formed list "
    in
    aux e, ty	
end
   
(** Morphisms *)
module Classes =
struct
  let classes_path = ["Coq";"Classes"; ]
  let morphism = lazy (init_constant (classes_path@["Morphisms"]) "Proper")
  let equivalence = lazy (init_constant (classes_path@ ["RelationClasses"]) "Equivalence")
  let reflexive = lazy (init_constant (classes_path@ ["RelationClasses"]) "Reflexive")
  let transitive = lazy (init_constant (classes_path@ ["RelationClasses"]) "Transitive")

  (** build the type [Equivalence ty rel]  *)
  let mk_equivalence ty rel =
    mkApp (Lazy.force equivalence, [| ty; rel|])


  (** build the type [Reflexive ty rel]  *)
  let mk_reflexive ty rel =
    mkApp (Lazy.force reflexive, [| ty; rel|])

  (** build the type [Proper rel t] *)
  let mk_morphism ty rel t =
    mkApp (Lazy.force morphism, [| ty; rel; t|])

  (** build the type [Transitive ty rel]  *)
  let mk_transitive ty rel =
    mkApp (Lazy.force transitive, [| ty; rel|])
end

module Relation = struct
  type t =
      {
	carrier : constr;
	r : constr;
      }
	
  let make ty r = {carrier = ty; r = r }
  let split t = t.carrier, t.r
end
   
module Transitive = struct
  type t =
      {
	carrier : constr;
	leq : constr;
	transitive : constr;
      }
  let make ty leq transitive = {carrier = ty; leq = leq; transitive = transitive}
  let infer goal ty leq  =
    let ask = Classes.mk_transitive ty leq in
    let transitive , goal = resolve_one_typeclass goal ask in
      make ty leq transitive, goal
  let from_relation goal rlt =
    infer goal (rlt.Relation.carrier) (rlt.Relation.r)
  let cps_from_relation rlt k =
    let ty =rlt.Relation.carrier in
    let r = rlt.Relation.r in
    let ask = Classes.mk_transitive  ty r in
    cps_resolve_one_typeclass ask
      (fun trans -> k (make ty r trans) )
  let to_relation t =
    {Relation.carrier = t.carrier; Relation.r = t.leq}

end
	
module Equivalence = struct
  type t =
      {
	carrier : constr;
	eq : constr;
	equivalence : constr;	
      }
  let make ty eq equivalence = {carrier = ty; eq = eq; equivalence = equivalence}
  let infer goal ty eq  =
    let ask = Classes.mk_equivalence ty eq in
    let equivalence , goal = resolve_one_typeclass goal ask in
      make ty eq equivalence, goal 	 
  let from_relation goal rlt =
    infer goal (rlt.Relation.carrier) (rlt.Relation.r)
  let cps_from_relation rlt k =
    let ty =rlt.Relation.carrier in
    let r = rlt.Relation.r in
    let ask = Classes.mk_equivalence  ty r in
    cps_resolve_one_typeclass ask (fun equiv -> k (make ty r equiv) )
  let to_relation t =
    {Relation.carrier = t.carrier; Relation.r = t.eq}
  let split t =
    t.carrier, t.eq, t.equivalence
end
end
(**[ match_as_equation goal eqt] see [eqt] as an equation. An
   optionnal rel_context can be provided to ensure taht the term
   remains typable*)
let match_as_equation ?(context = Term.empty_rel_context) goal equation : (constr*constr* Std.Relation.t) option  =
  let env = Tacmach.pf_env goal in
  let env =  Environ.push_rel_context context env in
  let evar_map = Tacmach.project goal in
  begin
    match decomp_term equation with
      | App(c,ca) when Array.length ca >= 2 ->
	let n = Array.length ca  in
	let left  =  ca.(n-2) in
	let right =  ca.(n-1) in
	let r = (mkApp (c, Array.sub ca 0 (n - 2))) in
	let carrier =  Typing.type_of env evar_map left in
	let rlt =Std.Relation.make carrier r
	in
	Some (left, right, rlt )
      | _ -> None
  end


(** {1 Tacticals}  *)

let tclTIME msg tac = fun gl ->
  let u = Sys.time () in
  let r = tac gl in
  let _ = Pp.msgnl (Pp.str (Printf.sprintf "%s:%fs" msg (Sys.time ()-.  u))) in
    r

let tclDEBUG msg tac = fun gl ->
  let _ = Pp.msgnl (Pp.str msg) in
    tac gl

let tclPRINT  tac = fun gl ->
  let _ = Pp.msgnl (Printer.pr_constr (Tacmach.pf_concl gl)) in
    tac gl


(** {1 Error related mechanisms}  *)
(* functions to handle the failures of our tactic. Some should be
   reported [anomaly], some are on behalf of the user [user_error]*)
let anomaly msg =
  Util.anomaly ("[aac_tactics] " ^ msg)

let user_error msg =
  Util.error ("[aac_tactics] " ^ msg)

let warning msg =
  Pp.msg_warning (Pp.str ("[aac_tactics]" ^ msg))


include Std
