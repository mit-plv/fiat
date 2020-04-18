(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

let debug = false

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
let pp_list pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a; " pp x) l
let pp_list_nl pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a;\n" pp x) l
let pp_constrs fmt l = (pp_list pp_constr) fmt l

let debug_type env evar t msg =
  if debug then
  try ignore (let ty = Typing.type_of env evar t in
	      let s = "*******" in
	      let s = s^msg^s in
	      Format.printf "%s\nTyped %a : %a \n" s pp_constr t  pp_constr ty
  )
  with e -> let s = "@@@@@@@@" in
	    let s = s^msg^s in
	    Format.printf "%s\nUnable to type %a\n" s pp_constr t

let debug_type_gl gl t msg =
  let env = Tacmach.pf_env gl in
  let evar = Tacmach.project gl in
  debug_type env evar t msg

let debug s = if debug then Format.printf s else Format.ifprintf (Format.std_formatter) s


let unifies gl a b = Tacmach.pf_conv_x gl a b

(** Building tactics that accept other tactics as arguments  *)
let dummy_loc = Util.dummy_loc
(* Calling a global tactic *)
let ltac_call tac (args:Tacexpr.glob_tactic_arg list) =
  Tacexpr.TacArg(dummy_loc,Tacexpr.TacCall(dummy_loc, Glob_term.ArgArg(dummy_loc, Lazy.force tac),args))

(* Calling a locally bound tactic *)
let ltac_lcall tac args =
  Tacexpr.TacArg(dummy_loc,Tacexpr.TacCall(dummy_loc, Glob_term.ArgVar(dummy_loc, Names.id_of_string tac),args))

let ltac_letin (x, e1) e2 =
  Tacexpr.TacLetIn(false,[(dummy_loc,Names.id_of_string x),e1],e2)

let ltac_apply (f:Tacexpr.glob_tactic_expr) (args:Tacexpr.glob_tactic_arg list) =
  Tacinterp.eval_tactic
    (ltac_letin ("F", Tacexpr.Tacexp f) (ltac_lcall "F" args))

let carg c = Tacexpr.TacDynamic(dummy_loc,Pretyping.constr_in c)



(** [recompose_prod C args f t] assumes that [f : C,t] and [args : C] *)
let recompose_prod
    (context : Term.rel_context) (args : Term.constr array) (c : Term.constr) return_type=
  let subst_rel_context k cstr ctx =
    let (_, ctx') =
      List.fold_left (fun (k, ctx') (id, b, t) -> (succ k, (id, Option.map
	(Term.substnl [cstr] k) b, Term.substnl [cstr] k t) :: ctx')) (k, [])
	ctx in List.rev ctx'
  in
  let rec depend_on k ctx =
    match ctx with
      | [] -> not (Term.noccurn k return_type)
      | (id,Some b,t) :: ctx ->
	not (Term.noccurn k b)	|| not (Term.noccurn k t) || depend_on (succ k) ctx
      | (id,None,t) :: ctx ->
	not (Term.noccurn k t) || depend_on (succ k) ctx
  in
  let len = List.length context in
  let args = Array.to_list args in
  let context = List.rev context in
  (* we can type the args statically *)
  let rec dependent = function
    | [] -> false
    | _ :: q ->  (depend_on 1 q) || dependent q
  in
  (* [app] corresponds to the arguments in the body of the function;
     [ctxt] corresponds to the remaining lambdas in the definition of the function;
     [rest] correspond to the arguments that are left outside
     [args] correspond to the arguments to the function that remain to be dispatched.
  *)
  let rec aux sign n next app ctxt rest args  =
    match sign with
      | [] ->
	List.rev app, List.rev ctxt, List.rev rest
      | l when  not (dependent sign) ->
	List.rev (List.map (Term.lift (- (List.length sign))) app),
	List.rev ctxt ,
	List.rev (rest) @ args
      | decl :: sign ->
	try
	  if depend_on (1) sign
	  then
	    begin
	      assert (0 <= n - 1);
	      let term = List.hd args  in
	      aux (subst_rel_context 0 term sign) (pred n) (succ next)
		(term::List.map (Term.lift (-1)) app) ctxt rest (List.tl args)
	    end
	  else  raise Not_found 	(* non-dependent *)
	with  _ ->
	  let term = Term.mkRel (len - next) in
	  aux sign (pred n) (succ next) (term::app) (decl :: ctxt) (List.hd args :: rest) (List.tl args)
  in

  let app,ctxt,rest = aux context len 0 [] [] [] args in
  Term.it_mkLambda_or_LetIn (Term.applistc c (app) ) (ctxt), rest


let reify_application env evar term  =
  debug "reify_application:%a\n" pp_constr term;
  let refl_app env evar  term f args =
    let ty = Typing.type_of env evar f in
    let (rel_context, return_type) = Term.decompose_prod_assum ty in
    let f, args = recompose_prod rel_context args f return_type in
    (* This extra bit of typing is a bit painful... *)
    let ty = Typing.type_of env evar f in
    let (rel_context, return_type) = Term.decompose_prod_assum ty in
    let types = List.fold_left (fun acc (_,_,ty) -> ty :: acc ) [] rel_context in
    Some (f, types , args, return_type )
  in

  begin match Extlib.decomp_term term with
    | Term.App (f,args) ->
      refl_app env evar  term f args
    | Term.Lambda (name, typ, body) ->
      let env = Environ.push_rel (name, None, typ) env in
      begin match Extlib.decomp_term body with
	| Term.App (f,args) ->
	  begin match refl_app env evar  body f args  with
	    | Some (f, types, args, ret) ->
	      let args = List.map (fun x -> Term.mkLambda  (name,typ,x) ) args in
	      Some (f, types, args, ret)
	    | None -> None
	  end
	| _ -> Some (term, [], [], Typing.type_of env evar term)
      end
    | _ -> Some (term, [], [], Typing.type_of env evar term)
  end

let reify_application2 env evar term  =
  debug "reify_application:%a\n" pp_constr term;
  let refl_app env evar  term f args =
    let ty = Typing.type_of env evar f in
    let (rel_context, return_type) = Term.decompose_prod_assum ty in
    let f, args = recompose_prod rel_context args f return_type in
    (* This extra bit of typing is a bit painful... *)
    let types = List.map (Typing.type_of env evar) args in
    Some (f, types , args )
  in

  begin match Extlib.decomp_term term with
    | Term.App (f,args) ->
      refl_app env evar  term f args
    | _ -> Some (term, [], [])
  end

let (@@) f l = Extlib.lapp f l

    module Pattern = struct
      type t =
	  App of Term.constr * t array
	| Const of Term.constr
	| Var of string
	| Hole

      let __ = Hole
      let (!) x = Var x
      let (&) x = Const x
      let app x y = App (x,y)

      type env = (string * Term.constr) list

      let get env x =
	try List.assoc x env
	with Not_found -> Format.printf "Could not find %s\n%!" x; raise Not_found

      let rec eval p t env : env option =
	match p with
	  | Const x -> if Term.eq_constr x t then Some env else None
	  | Var s -> Some ((s,t) :: env)
	  | Hole -> Some env
	  | App (hd, args) ->
	    begin match Extlib.decomp_term t with
	      | Term.App (hd', args') ->
		if Array.length args = Array.length args' then
		  let rec aux i env =
		    if i = Array.length args then Some env
		    else
		      match eval args.(i) args'.(i) env with
			| None -> None
			| Some env -> aux (i+1) env
		  in
		  aux 0 env
		else None
	      | _ -> None
	    end

      let rec matcho t l =
	match l with
	  | [] -> None
	  | (p,k)::q ->
	    begin match eval p t [] with
	      | None -> matcho t q
	      | Some env -> Some  (k env)
	    end

      let matchf t l =
	match matcho t l with
	  | Some x -> x
	  | None -> Format.printf "Anomaly matching %a\n%!" pp_constr t; assert false

      let rec shallow_match (t: Term.constr) (l : (Term.constr * int * (Term.constr array -> 'a)) list):
	  'a =
	match Extlib.decomp_term t, l with
	  | Term.App (hd, args), (hd',ar,k) :: q when Term.eq_constr hd hd' ->
	    if not (Array.length args = ar)
	    then Util.anomaly "Incorrect arity of an application in reification";
	    k args
	  | _ , _ :: q -> shallow_match t q
	  | _ ,[] ->
	    Format.printf "Unable to reify %a" pp_constr t;
	    Util.anomaly "Unable to reify"

    end

    let app = Pattern.app
    let var x = Pattern.Var x
    let __ = Pattern.Hole
    let const x = Pattern.Const x
    let get = Pattern.get


module Bedrock = struct

  (* bedrock [type]. We do not inspect it *)
  type typ = Term.constr


  type func = int
  type tvar = int option

  let path = ["Bedrock"]

  (* a decorated tvar *)
  type rtype = (Term.types * tvar)

  let pp_rtype fmt = function
    | (t,Some n) -> Format.fprintf fmt "%a@@%i" pp_constr t n
    | (t,None) -> Format.fprintf fmt "%a@@Prop" pp_constr t

  let pp_func fmt (f,l,r) = Format.fprintf fmt "%a : [%a] -> %a"
    pp_constr f (pp_list pp_rtype) l pp_rtype r

  let pp_pred fmt (f,l) = Format.fprintf fmt "%a : [%a] -> HPROP"
    pp_constr f (pp_list pp_rtype) l

  let pp_uvar fmt (v,t) = Format.fprintf fmt "%a:%a" pp_constr v pp_rtype t

  let tvar = lazy (Extlib.init_constant ["Bedrock"; "Expr"] "tvar")
  let mk_tvar : int option ->  Term.constr =
    let tvProp = lazy (Extlib.init_constant ["Bedrock" ; "Expr"] "tvProp") in
    let tvType = lazy (Extlib.init_constant ["Bedrock" ; "Expr"] "tvType") in
      fun r ->
	match r with
	  | Some x -> tvType @@ [| Extlib.Nat.of_int x |]
	  | None ->
	    Lazy.force tvProp


  module ReificationHint = struct
    let path = ["Bedrock" ; "Expr" ; "ReificationHint"]
    let pkg = lazy (Extlib.init_constant path "Pkg")
    let mk_pkg = lazy (Extlib.init_constant path "mk_Pkg")
    let mk_pkg (t : Term.types) : Term.constr =
      mk_pkg @@ [| t |]

    let path = ["Bedrock" ; "ReifyExpr"]
    (** * Checks if there is a reification hint associated with the type [t], and builds a [type]  *)
    let build_default_type env evar  (ty : Term.constr) : Term.constr =
      try
	let query = mk_pkg ty in
	let _, pkg = Typeclasses.resolve_one_typeclass env evar query in
	let f = lazy (Extlib.init_constant path "type_of_ReificationHint") in
	f @@  [| ty ; pkg |]
      with
	  _ ->
	    (* build the default type *)
	    let default_type = lazy (Extlib.init_constant path "default_type") in
	    default_type @@ [| ty |]
  end

  module Renv = struct
    type t =
	{
	  (* a Bedrock [type] *)
	  types : (Term.types * typ)  list;
	  uvars : (Term.constr * rtype) list;
	  funcs : (Term.constr * rtype list * rtype)list;
	  preds : (Term.constr * rtype list) list;
	  level : int 			(* the current de Bruijn level *)
	}

    let push renv = {renv with level = renv.level + 1}
    let pop renv = {renv with level = renv.level - 1}

    let empty = {level = 0; types = []; uvars = []; funcs = [] ; preds = []}




    let pose gl renv
	(k : Term.constr -> Term.constr ->Term.constr ->Term.constr -> Proof_type.tactic) =
      let pc_type = mk_tvar (Some 0) in
      let state_type = mk_tvar (Some 1) in
      let tvar = Lazy.force tvar in
      let ty = Extlib.init_constant ["Bedrock"; "Expr"] "type" in
      let types = Extlib.List.of_list ty  (List.map snd renv.types) in
      debug_type_gl gl types "pose/types";
      Extlib.cps_mk_letin "types" types (fun types gl ->
	(* Functions *)
	let ty = Extlib.init_constant ["Bedrock"; "Expr"] "signature" in
	let mk = Extlib.init_constant ["Bedrock"; "Expr"] "Sig" in
	let mk_function (denotation, domain, range) =
	  let domain = Extlib.List.of_list tvar (List.map (fun x -> mk_tvar (snd x)) domain) in
	  let range  = mk_tvar (snd range) in
	  debug_type_gl gl range "range";
	  debug_type_gl gl denotation "denotation";
	  debug_type_gl gl domain "domain";
	  debug_type_gl gl (Term.mkApp (mk,[| types |])) "papp 1";
	  debug_type_gl gl (Term.mkApp (mk,[| types ; domain; |])) "papp 1";
	  debug_type_gl gl (Term.mkApp (mk,[| types ; domain; range|])) "papp 1";
	  Term.mkApp (mk, [| types; domain; range; denotation |])
	in
	let ty = (Term.mkApp (ty,[|types|])) in
	let funcs = Extlib.List.of_list ty (List.map mk_function renv.funcs) in
	debug_type_gl gl funcs "FUNCS";
	Extlib.cps_mk_letin "funcs" funcs (fun funcs gl ->
	(* Preds *)
	let ty = Extlib.init_constant ["Bedrock"; "SepIL"; "SEP"] "predicate" in
	let mk = Extlib.init_constant ["Bedrock"; "SepIL"; "SEP"] "PSig" in
	let mk_predicate (denotation, domain) =
	  let domain = Extlib.List.of_list tvar (List.map (fun x -> mk_tvar (snd x)) domain) in
	  Term.mkApp (mk, [| types ; pc_type ; state_type ; domain; denotation |])
	in
	let ty = Term.mkApp (ty, [| types ; pc_type ; state_type|]) in
	let preds = Extlib.List.of_list ty (List.map mk_predicate renv.preds) in
	debug_type_gl gl preds "PREDS";
	Extlib.cps_mk_letin "preds" preds (fun preds gl ->

	  (* uvars *)
	  (* (@sigT Expr.tvar (fun t : Expr.tvar => Expr.tvarD typesV t)) *)
	  let sigt = Extlib.init_constant ["Coq" ; "Init"; "Specif"] "sigT" in
	  debug_type_gl gl sigt "sigt";
	  let existT = Extlib.init_constant ["Coq" ; "Init"; "Specif"] "existT" in
	  debug_type_gl gl existT "existT";
	  let tvarD = Extlib.init_constant ["Bedrock"; "Expr"] "tvarD" in
	  let f =
	    Term.mkLambda (Names.Anonymous, tvar, Term.mkApp (tvarD, [| types ; Term.mkRel 1|])) in
	  debug_type_gl gl f "f";
	  let ty = Term.mkApp (sigt, [| tvar ; f ;  |])   in
	  debug_type_gl gl ty "ty";
	  let mk (e,x) =
	    let t = mk_tvar (snd x) in
	    debug_type_gl gl e "e";
	    let x = Term.mkApp (existT, [| tvar ; f ; t ; e |])  in
	    debug_type_gl gl x "x";
	    x
	  in
	  let uvars = Extlib.List.of_list ty (List.map mk renv.uvars) in
	  (* debug_type_gl gl uvars "UVARS"; *)
	  (* Extlib.cps_mk_letin "uvars" uvars (fun uvars -> *)
	    k types funcs preds uvars
	gl ) gl )gl ) gl


    let pp fmt renv =
      let pp_type fmt (_,y) = pp_constr fmt y in
      Format.fprintf fmt "types:\t%a\n" (pp_list pp_type) renv.types;
      Format.fprintf fmt "uvars:\t%a\n" (pp_list pp_uvar) renv.uvars;
      Format.fprintf fmt "funcs:\t%a\n" (pp_list_nl pp_func) renv.funcs;
      Format.fprintf fmt "preds:\t%a\n" (pp_list_nl pp_pred) renv.preds


    exception Length of int

    let exists env evar f x l =
      try
	begin let rec aux eq n = function
	  | [] -> raise (Length n)
	  | t :: q -> if eq (f t) x  then n else aux eq (n+1) q
	      in
	      try aux Term.eq_constr 0 l
	      with
      		| Length _ -> aux (Reductionops.is_conv env evar) 0 l
	end
      with
	| Length n -> raise (Length n)
	| Util.UserError (func, e) ->
	  debug "exists exception function %s has failed with message : %s\n%!" func
	    (Pp.string_of_ppcmds e);
	  raise (Length (List.length l))
	| e ->
	  debug "exists exception %s\n%!" (Printexc.to_string e);
	  raise (Length (List.length l))

    let c_exists env evar f x l =
      let rec aux eq n = function
	| [] -> raise (Length n)
	| t :: q -> if eq (f t) x  then n else aux eq (n+1) q
      in
      aux Term.eq_constr 0 l

      (* aux Term.eq_constr 0 l *)

    (* add a bedrock [type] to the environment *)
    let add_type env evar (renv : t) ty : t * tvar =
      debug "call add_type %a\n" pp_constr ty;
      if Term.is_Prop ty then renv, None
      else
	try renv, Some (exists env evar fst ty renv.types)
	with Length n ->
	  debug "Adding a new type %a\n%!" pp_constr ty;
	  let typ = ReificationHint.build_default_type env evar ty in
	  {renv with types = renv.types @ [ty, typ]}, Some (n)

    (* assume that the type of [e] is [ty] *)
    let add_var env evar renv e (ty : rtype) : t * int =
      try renv, exists env evar fst e renv.uvars
      with Length n -> {renv with  uvars = renv.uvars@[e,ty]}, (n)

    let add_func env evar renv (f : Term.constr) (types : Term.types list) (return : Term.types):
	t * int =
      debug "Call add_func %a\n" pp_constr f;
      (* if not (Term.closed0 f) then  Util.error "Unable to reify higher-order existentials" *)
      (* else *)
	try renv, exists env evar (fun (f,_,_) -> f) f renv.funcs
	with Length n ->
	  debug "Adding a new fun %a with type %a to %a \n%!" pp_constr f pp_constrs types pp_constr return;
	  let renv,types = List.fold_right (fun ty (renv,acc) ->
	    let renv, i =  (add_type env evar renv ty)
	    in renv, (ty,i) :: acc
	  )  types (renv,[]) in
	  let renv, returni = add_type env evar renv return in
 	  {renv with funcs = renv.funcs @ [f, types, (return,returni)]}, n
	  | e -> Format.printf "add_func exception %s\n%!" (Printexc.to_string e); Util.anomaly "should not happen"

    let add_pred env evar renv (f : Term.constr) (types : Term.types list) :
	t * int =
      (* if not (Term.closed0 f) then  Util.error "Unable to reify higher-order existentials" *)
      (* else *)
	try renv, exists env evar fst f renv.preds
	with Length n ->
	  debug "Adding a new preds %a with type %a \n%!" pp_constr f pp_constrs types;
	  let renv,types = List.fold_right (fun ty (renv,acc) ->
	    let renv, i =  (add_type env evar renv ty)
	    in renv, (ty,i) :: acc
	  )  types (renv,[]) in
 	  {renv with preds = renv.preds @ [f, types ]}, n



    (* to detect "constants" *)
    let is_const e =
      let init p x = Extlib.init_constant  p x in
      let f x = init ["Bedrock"; "IL"] x in

      (* Boolean constants need separate handling, until such time as we extend
       * the reified type environment with an equality test for Booleans. *)
      let bool_constants = [Lazy.force Extlib.Bool._true;
			    Lazy.force Extlib.Bool._false] in

      let constants = [f "Rp" ; f "Rv"; f "Sp";
					 Lazy.force Extlib.Nat._O;
					 init ["Coq"; "Strings"; "String"] "EmptyString";
		      ]  in

      let string = (init ["Coq"; "Strings"; "String"] "String") in
      let ascii = (init ["Coq"; "Strings"; "Ascii"] "Ascii") in
    let rec is_const e =
	List.exists (Term.eq_constr e) constants
	||
	  match Extlib.decomp_term e with
	    | Term.App (hd, args) when Term.eq_constr hd (Lazy.force Extlib.Nat._S) ->
	      is_const args.(0)
	    | Term.App (hd, args) when
		Term.eq_constr hd string ->
	       is_const args.(0) && is_const args.(1)
	    | Term.App (hd, args) when
		Term.eq_constr hd ascii ->
	      Array.fold_left (fun acc x -> acc && List.exists (Term.eq_constr x) bool_constants) true args
	    | _ -> false
      in
      let r = is_const e in
      (* debug "is_const %a\t:%b\n" (pp_constr) e r; *)
      r

    let init types = {level = 0; types = types; funcs = [] ; preds = []; uvars = []}

  end



  module Expr = struct
    let path = ["Bedrock"; "Expr"]

    type expr =
      | Const of tvar * Term.constr
      | UVar of int
      | Var of int
      | Func of func * expr list
      | Not of expr
      | Equal of tvar * expr * expr

    let init x = Extlib.init_constant path x

    let dump_expr types e =
      let const = init "Const" and var = init "Var" and func = init "Func" and equal = init "Equal"
      and not = init "Not" and uvar = init "UVar" in
      let (@@) f l = Term.mkApp (f,Array.of_list (types :: l))  in
      let ty = (init "expr") @@ [] in
      let rec aux = function
	| Const (t,d) -> const @@ [mk_tvar t; d]
	| Var v -> var @@ [Extlib.Nat.of_int v]
	| UVar v -> uvar @@ [Extlib.Nat.of_int v]
	| Func (f,l) ->
	  let l = Extlib.List.of_list ty (List.map aux l) in
	  func @@ [Extlib.Nat.of_int f; l]
	| Not e -> not @@ [aux e]
	| Equal (t,e,f) -> equal @@ [mk_tvar t; aux e; aux f]
      in
      aux e

    let dump_expr_list gl types l =
      let ty = Term.mkApp (init "expr", [| types |]) in
      let proofs,pures = List.fold_right (fun (h,hty, e) (proofs,pures) ->
	(h,hty)::proofs, (dump_expr types e :: pures)
      ) l ([],[])
      in
      let pures = Extlib.List.of_list ty pures in
      let rec aux = function
	| [] ->
	  let pf = Extlib.init_constant ["Coq"; "Init" ; "Logic"] "I" in
	  let ty = Extlib.init_constant ["Coq"; "Init" ; "Logic"] "True" in
	  ty, pf
	  | (h,hty) :: q ->
	    debug_type_gl gl h "h";
	    debug_type_gl gl hty "hty";

	    let ty,pf = aux q in
	    let ty2 = Term.mkApp (Extlib.Logic.and_ (), [| h; ty|]) in
	    let pf2 = Term.mkApp (Extlib.Logic.conj (), [| h ; ty ; hty ; pf|]) in
	    ty2, pf2
      in
      let _,proofs = aux proofs  in
      proofs, pures






    let rec pp_expr fmt = function
      | Const (Some i,t) -> Format.fprintf fmt "$%a" pp_constr t
      | Const (None,t) -> Format.fprintf fmt "(%a:Prop)"pp_constr t
      | UVar i -> Format.fprintf fmt "uvar_%i" i
      | Var i -> Format.fprintf fmt "var_%i" i
      | Func (f,l) ->
	Format.fprintf fmt "f_%i [|%a|]"
	  f (fun fmt -> List.iter (fun x -> Format.fprintf fmt "%a;" pp_expr x)) l
      | Not e -> Format.fprintf fmt "not (%a)" pp_expr e
      | Equal (None, e1, e2) -> Format.fprintf fmt "(%a == %a)" pp_expr e1 pp_expr e2
      | Equal (Some i, e1, e2) -> Format.fprintf fmt "(%a == %a)" pp_expr e1  pp_expr e2

    (*  *)
    let reify_expr env evar renv e =
      let rec reify_expr renv e =
	debug "reify_expr %a\n%!" pp_constr e;
	match Extlib.decomp_term e with
	  | Term.Rel i ->
	    if renv.Renv.level - i >= 0 then
	      renv, Var (i - 1)
	    else assert false
	  | Term.Evar _ ->
	    let ty = Typing.type_of env evar e in
	    let renv, nty = Renv.add_type env evar renv ty in
	    let renv, v = Renv.add_var env evar renv e (ty,nty) in
	    renv, UVar v
	  | Term.App (hd, args) when Term.eq_constr hd (Lazy.force Extlib.Leibniz._eq) ->
	    let renv, tn = Renv.add_type env evar renv (args.(0)) in
	    let renv, l = reify_expr renv (args.(1)) in
	    let renv, r = reify_expr renv (args.(2)) in
	    renv, Equal (tn,l,r)
	  | Term.App (hd, args') when Term.eq_constr hd (Lazy.force Extlib.Logic._not) ->
	    let renv, e = reify_expr renv args'.(0) in
	    renv, Not e
	  | Term.Prod (_,s,t) when Term.eq_constr t (Lazy.force Extlib.Logic._false) ->
	    let renv, e = reify_expr renv s in
	    renv, Not e
	  (* special case to add a constant. May fail later. *)
	  | Term.App (hd,_) when Term.eq_constr hd (Extlib.Logic.exists ()) ->
	    let renv, f = Renv.add_func env evar renv e [] (Typing.type_of env evar e) in
	    renv, Func (f,[])
	  | _ when Renv.is_const e ->
	    let ty = Typing.type_of env evar e in
	    let renv, nty = Renv.add_type env evar renv ty in
	    renv, Const (nty,e)
	  | Term.App (hd, args) ->
	    debug "Call reify_application with %a in reify_expr\n" pp_constr e;
	    begin match reify_application env evar e with
	      | Some (f,types, args, return) ->
		let args, renv = List.fold_right (fun x (args, renv) ->
		  let renv, x = reify_expr renv x in
		  (x::args, renv)
		) args ([], renv) in
		let renv, f = Renv.add_func env evar renv f types return in
		renv, Func (f, args)
	      | None -> assert false
	    end
	  | _ ->
	    let s = Termops.free_rels e in
	    if Util.Intset.cardinal s <> 0 then
	      (* the term is not closed (like [if ?1 then x else ?2]) *)
	      let s =
		List.map (fun x -> x, Term.lookup_rel x (Environ.rel_context env))
		  (Util.Intset.elements s) in
	      (* [findi i l] returns [n,x] if x is associated to i in [l] at position n *)
	      let findi i l =
		let rec findi i n = function
		  | [] -> raise Not_found
		  | (t,x) :: q -> if t = i then (n,x) else findi i (n+1) q
		in
		findi i 1 l
	      in
	      let rec fold k e =
		match Extlib.decomp_term e with
		  | Term.Rel i ->
		    begin
		      try let (n,x) = findi (i - k) s in
			  Term.mkRel (n+k)
		      with _ -> e
		    end
		  | _ -> Term.map_constr_with_binders succ fold k e
	      in
	      let e = Termops.it_mkLambda_or_LetIn (fold 0 e) (List.map snd s) in
	      let renv, f = reify_expr renv e in
	      let args = (List.fold_left (fun acc x -> Term.mkRel x:: acc) [] (List.map fst s)) in
	      let args, renv = List.fold_right (fun x (args,renv) ->
		let renv, x = reify_expr renv x in
		(x::args, renv)
	      ) args ([],renv) in
	      begin renv, match f with
		| Func (f, args') -> Func (f, args'@args)
		| _ -> Util.anomaly "Trying to reify an expression applied to an expression"
	      end
	    else  			(* The term is closed *)
	      (
		let ty = Typing.type_of env evar e in
		let (rel_context, return) = Term.decompose_prod_assum ty in
		let types = List.fold_left (fun acc (_,_,ty) -> ty:: acc) [] rel_context in
		(* let f, args = recompose_prod rel_context [||] e return in  *)
		(* let types = List.map (Typing.type_of env evar) args in   *)
		let renv, f = Renv.add_func env evar renv e types return in
		renv, Func (f, [])
	      )


      in reify_expr renv e

    let reify_exprs env evar renv t =
      debug "@@@@@@@@@@@@@\n@@@@@@@@@@@@@\nreify_exprs : %a\n\n" pp_constr t;
      let tt =  Extlib.init_constant ["Coq"; "Init"; "Datatypes";]  "tt" in
      let pair =  Extlib.init_constant ["Coq"; "Init"; "Datatypes";]  "pair" in
      let rec aux t =
	Pattern.matchf t
	  [
	    const tt,
	    (fun _ -> renv, []);

	    app pair [| var "A" ; var "B" ; var "a" ; var "b" |],
	    (fun e  ->
	      let renv, q = aux (get e "b") in
	      let a = get e "a"  in
	      debug "reifying the pure %a\n" pp_constr a;
	      let at = match Extlib.decomp_term (get e "a")  with
		| Term.Var v -> Environ.named_type v env
		| _ -> assert false
	      in
	      let renv, t = reify_expr env evar renv at in
	      renv, (get e "A", a,  t) :: q)
	  ]
      in
      aux t
      (* let l, _ = Extlib.List.of_constr l in  *)
      (* List.fold_right (fun e (renv,acc) ->  *)
      (* 	let renv, e = reify_expr env evar renv e in  *)
      (* 	renv, e :: acc *)
      (* ) l (renv, []) *)
  end

  type hprop = Term.constr

  module PropX = struct
    (* injection of pure facts *)
    let path = ["Bedrock" ; "PropX"]

    let inj = lazy (Extlib.init_constant path "Inj")
  end

  module SepExpr = struct
    (* let path = ["Bedrock" ; "reification"; "Sep"] *)
    (* let emp = lazy (Extlib.init_constant path "emp") *)
    (* let inj = lazy (Extlib.init_constant path "inj") *)
    (* let star = lazy (Extlib.init_constant path "star") *)
    (* let ex = lazy (Extlib.init_constant path "ex") *)

    let path = ["Bedrock" ; "SepIL"; "ST"]
    let emp = lazy (Extlib.init_constant path "emp")
    let inj = lazy (Extlib.init_constant path "inj")
    let star = lazy (Extlib.init_constant path "star")
    let ex = lazy (Extlib.init_constant path "ex")

    type sexpr =
      | Emp
      | Inj of Expr.expr
      | Star of sexpr * sexpr
      | Exists of tvar * sexpr
      | Func of func * (Expr.expr) list
      | Const of hprop


    let dump_sexpr gl types se =
      let path = ["Bedrock"; "SepIL"; "SEP"] in
      let init x = Extlib.init_constant path x in
      let pcT = mk_tvar (Some 0) in
      let stT = mk_tvar (Some 1) in
      let emp = init "Emp" and inj = init "Inj" and star = init "Star" and exists = init "Exists" and func = init "Func" and const = init "Const" in
      let (@@) f l = Term.mkApp (f,Array.of_list (types :: pcT :: stT :: l))  in
      let ty = Term.mkApp (Extlib.init_constant ["Bedrock"; "Expr"] "expr", [|types|]) in
      let check x = debug_type_gl gl x ""; x in
      let rec aux = function
	| Const d -> check (const @@ [d])
	| Func (f, l) ->
	  let l = Extlib.List.of_list ty (List.map (Expr.dump_expr types) l) in
	  check (func @@ [Extlib.Nat.of_int f; l])
	| Exists (t,e) ->  check (exists @@ [mk_tvar t; aux e])
	| Star (a,b) -> check (star @@ [ aux a ; aux b])
	| Inj e -> check (inj @@ [Expr.dump_expr types e])
	| Emp -> check (emp @@ [])
      in
      aux se


    let rec pp_sexpr fmt = function
      | Emp -> Format.fprintf fmt "#"
      | Const t -> Format.fprintf fmt "$%a" pp_constr t
      | Inj e -> Format.fprintf fmt "inj (%a)" Expr.pp_expr e
      | Func (f,l) ->
	Format.fprintf fmt "f_%i [|%a|]"
	  f (fun fmt -> List.iter (fun x -> Expr.pp_expr fmt x)) l
      | Star (a,b) ->
	Format.fprintf fmt  "(%a * %a)" pp_sexpr a pp_sexpr b
      | Exists (None, body) ->
	Format.fprintf fmt  "exists (Prop, %a)"  pp_sexpr body
      | Exists (Some tv, body) ->
	Format.fprintf fmt  "exists (%i, %a)" tv pp_sexpr body

    let rec reify_sexpr env evar renv e =
      debug "reify_sexpr %a\n%!" pp_constr e;
      match Extlib.decomp_term e with
	(* | Term.Lambda (name,ty,body) ->  *)
	(*   let env = Environ.push_rel (name, None, ty) env in *)
	(*   let renv = Renv.push renv in  *)
	(*   let renv, e = reify_sexpr env evar renv body in  *)
	(*   Renv.pop renv, e *)
	| Term.App (hd, args) when Term.eq_constr hd (Lazy.force emp) ->
	  renv, Emp
	| Term.App (hd, args) when Term.eq_constr hd (Lazy.force inj) ->
	  begin
	    let p = args.(3) in
	    begin match Extlib.decomp_term p with
	      | Term.App (hd, args) when Term.eq_constr hd (Lazy.force PropX.inj) ->
		let renv, p = Expr.reify_expr env evar renv args.(3) in
		renv, Inj p
	      | _ ->
		let renv = assert false in (* add the type *)
		renv, Const p
	    end
	  end
	| Term.App (hd, args) when Term.eq_constr hd (Lazy.force star) ->
	  let renv, l = reify_sexpr env evar renv (args.(3)) in
	  let renv, r = reify_sexpr env evar renv (args.(4)) in
	  renv, Star (l,r)
	| Term.App (hd, args) when Term.eq_constr hd (Lazy.force ex) ->
	  let body = args.(4) in
	  let renv, body = begin match Extlib.decomp_term body with
	    | Term.Lambda (name,ty,body) ->
	      let env = Environ.push_rel (name, None, ty) env in
	      let renv = Renv.push renv in
	      let renv, e = reify_sexpr env evar renv body in
	      Renv.pop renv, e
	    | _ -> assert false
	  end in

	  (* let renv, body = reify_sexpr env evar renv args.(4) in   *)
	  let renv, ty = Renv.add_type env evar renv args.(3) in
	  renv, Exists (ty, body)
	| Term.App (hd, _) ->
	  debug ":hd %a\n" pp_constr hd;
	  begin match reify_application env evar e with
	    | Some (f, types, args, return) ->
	      let args, renv = List.fold_right (fun x (args,renv) ->
		let renv, x = Expr.reify_expr env evar renv x in
		(x::args, renv)
	      ) args ([],renv) in
	      let renv, f = Renv.add_pred env evar renv f types  in (* assert return = hprop *)
	      renv, Func (f, args)
	    | None -> assert false
	  end
	| _ ->

	  begin match reify_application env evar e with
	    | Some (f, types, args, return) ->
	      let args, renv = List.fold_right (fun x (args,renv) ->
		let renv, x = Expr.reify_expr env evar renv x in
		(x::args, renv)
	      ) args ([],renv) in
	      let renv, f = Renv.add_pred env evar renv f types in (* assert return = hprop *)
	      renv, Func (f, args)
	    | None -> assert false
	  end

  end

  module SymIL = struct

    type reg = Term.constr  		(* IL : Sp | Rp | Rv*)
    type label = Term.constr
    type binop = Term.constr 		(* Plus | Minus  | Times *)
    type test = Term.constr 		(* Eq | Ne | Lt | Le *)
    type state = Term.constr

    type loc =
      | Reg of reg
      | Imm of Expr.expr
      | Indir of reg * Expr.expr

    type lvalue =
      | LvReg of reg
      | LvMem of loc
      | LvMem8 of loc

    type rvalue =
      | RvLval of lvalue
      | RvImm of Expr.expr
      | RvLabel of label

  (* Non-control-flow instructions *)
    type instr =
      | Assign of lvalue * rvalue
      | Binop of lvalue * rvalue * binop * rvalue

    type assertion = rvalue * test * rvalue * (Term.constr ) (* the last term is an option bool *)

    type ('a, 'b) sum = Inl of 'a | Inr of 'b

    type istream =
	(instr list * state option, assertion) sum  list

    (* the proof that is build from the hypothesis, and corresponds to
       the denotation of the reification *)
    type proof = (Names.identifier * Term.constr) list * Term.constr option

    let dump_istream gl types (is : istream) (ispf : proof) st =
      let path = ["Bedrock"; "SymIL"] in
      let init x = Extlib.init_constant path x in
      let (@@) f l = Term.mkApp (f,Array.of_list (types :: l)) in

      (* dump_loc *)
      let reg = init  "SymReg" and imm = init "SymImm" and indir = init "SymIndir" in
      let dump_loc = function
	| Reg r -> reg @@ [r]
	| Imm e -> imm @@ [Expr.dump_expr types e]
	| Indir (r,e) -> indir @@ [r; Expr.dump_expr types e]
      in

      (* dump_lvalue *)
      let lvreg = init  "SymLvReg" and lvmem = init "SymLvMem" and lvmem8 = init "SymLvMem8" in
      let dump_lvalue = function
      | LvReg r -> lvreg @@ [r]
      | LvMem l -> lvmem @@ [dump_loc l]
      | LvMem8 l -> lvmem8 @@ [dump_loc l]
      in

      (* dump_lvalue *)
      let rvlval = init  "SymRvLval" and rvimm = init "SymRvImm"  and rvlabel = init "SymRvLabel" in
      let dump_rvalue r = match r with
	| RvLval l -> rvlval @@ [dump_lvalue l]
	| RvImm e -> rvimm @@ [Expr.dump_expr types e]
	| RvLabel l -> rvlabel @@ [l]
      in

      let assign = init "SymAssign" and binop = init "SymBinop" in
      let dump_instr (i : instr) : Term.constr = match i with
	| Assign (l,r) -> assign @@ [dump_lvalue l; dump_rvalue r]
	| Binop (l,r1,op,r2) -> binop @@ [dump_lvalue l; dump_rvalue r1; op; dump_rvalue r2]
      in

      let pcT = mk_tvar (Some 0) in
      let stT = mk_tvar (Some 1) in
      let (@@) f l = Term.mkApp (f,Array.of_list (types :: l)) in
      let cond r t l e =
	let x = (init "SymAssertCond") @@ [dump_rvalue r; t; dump_rvalue l; e]
	in x
      (* debug_type_gl gl x "cond" ; x *)
      in
      let state = Extlib.init_constant ["Bedrock"; "IL"] "state" in
      let option_state = Extlib.lapp Extlib.Option.typ [| state |] in
      let stateo so = Extlib.Option.of_option state so in
      let sym_instr = Term.mkApp (init "sym_instr" , [| types |]) in
      let list_sym_instr = Extlib.List.type_of_list sym_instr in
      (* debug_type_gl gl list_sym_instr "list_sym"; *)
      (* debug_type_gl gl option_state "option_state"; *)
      let ty_left = Extlib.Pair2.prod  list_sym_instr  option_state in
      let ty_right = Term.mkApp (init "sym_assert", [| types |]) in
      (* debug_type_gl gl ty_left "ty_left"; *)
      (* debug_type_gl gl ty_right "ty_right"; *)
      let mk i  = match (i : (instr list * state option, assertion) sum) with
	| Inl (is,st) ->
	  let l = Extlib.List.of_list sym_instr (List.map dump_instr is) in
	  let t = Extlib.Pair.of_pair list_sym_instr option_state (l,stateo st) in
	  let t = Extlib.Sum.inl ty_left ty_right t in
	  (* debug_type_gl gl t "mk inl"; *)
	  t
	| Inr (r,t,l,e) -> let x = Extlib.Sum.inr ty_left ty_right (cond r t l e) in
			   (* debug_type_gl gl x "mk inr";  *)
			   x

      in
      (* we rebuild the "proof" that corresponds to the instruction
	 list. This term is quadratic, because of the use of [conj] *)
      let isP =
	let t = Term.mkApp (Lazy.force Extlib.Option.typ,[|state|]) in
	let eq_refl = Lazy.force Extlib.Leibniz._eq_refl in
	let eq = Lazy.force Extlib.Leibniz._eq in
	let and' = Extlib.Logic.and_ () in
	let conj =	Extlib.Logic.conj () in
	let rec aux : proof -> Term.constr * Term.constr = function
	  | [], None -> assert false
	  | [], Some st ->
	    let some_st = Extlib.Option.some state st in
	    let pf = Term.mkApp (eq_refl , [| t; some_st |]) in
	    let ty = Term.mkApp (eq, [| t; some_st; some_st |]) in
	    ty, pf

	  | [h,hty], None ->  hty, Term.mkVar h
	  | (h,hty) :: q, o ->
	    let ty,pf = aux (q,o) in
	    let ty2 = Term.mkApp (and', [| hty ; ty|]) in
	    let pf2 = Term.mkApp (conj , [| hty ; ty ; Term.mkVar h  ; pf|])
	    in
	    ty2, pf2
	in
	snd (aux ispf)
      in
      let ty = Extlib.Sum.sum ty_left ty_right in
      Extlib.List.of_list ty (List.map mk is), isP


    let pp_lvalue fmt = function
      | LvReg r -> Format.fprintf fmt "reg %a" pp_constr r
      | LvMem l -> Format.fprintf fmt "<loc>"
      | LvMem8 l -> Format.fprintf fmt "<loc8>"

    let pp_rvalue fmt = function
      | RvLval l -> Format.fprintf fmt "val %a" pp_lvalue l
      | RvImm e -> Format.fprintf fmt "<expr: %a>" Expr.pp_expr e
      | RvLabel l -> Format.fprintf fmt "<label>"

    let pp_instr fmt = function
      | Assign (x,y) -> Format.fprintf fmt "%a := %a" pp_lvalue x pp_rvalue y
      | Binop (l,r1,op,r2) -> Format.fprintf fmt "%a <- %a %a %a" pp_lvalue l pp_rvalue r1
	pp_constr op pp_rvalue r2

    let pp_assertion fmt ((r1,t,r2,f) : assertion) =
      Format.fprintf fmt "assert (%a,%a,%a,%a)" pp_rvalue r1 pp_constr t pp_rvalue r2 pp_constr f

    let pp_istream fmt (l: istream)=
      List.iter (fun x ->
	match x with
	  | Inl (x,_) -> Format.fprintf fmt "Inl %a;" (pp_list pp_instr) x
	  | Inr x -> Format.fprintf fmt "Inr %a;" pp_assertion x
      ) l


    let reify_loc env evar renv l =
      let f x = Extlib.init_constant ["Bedrock"; "IL"] x in
      Pattern.shallow_match l
	[f "Reg", 1, (fun args -> renv, Reg args.(0));
	 f "Imm", 1, (fun args -> let renv, i = Expr.reify_expr env evar renv args.(0) in
				  renv, Imm i);
	 f "Indir", 2, (fun args -> let renv,i = Expr.reify_expr env evar renv args.(1) in
				    renv, Indir (args.(0), i));
	]

    let reify_lvalue env evar renv l =
      let f x = Extlib.init_constant ["Bedrock"; "IL"] x in
      Pattern.shallow_match l
	[
	  f "LvReg", 1, (fun args -> renv, LvReg args.(0));
	  f "LvMem", 1, (fun args -> let renv, l = reify_loc env evar renv args.(0) in
				     renv, LvMem l);
	  f "LvMem8", 1, (fun args -> let renv, l = reify_loc env evar renv args.(0) in
				     renv, LvMem8 l)
	]

    let reify_rvalue env evar renv r =
      let f x = Extlib.init_constant ["Bedrock"; "IL"] x in
      Pattern.shallow_match r
	[
	  f "RvLval", 1, (fun args -> let renv, l = reify_lvalue env evar renv args.(0) in
				      renv, RvLval l	  );
	  f "RvImm", 1, (fun args -> let renv, i = Expr.reify_expr env evar renv args.(0) in
				     renv, RvImm i);
	  f "RvLabel", 1, (fun args ->  renv, RvLabel args.(0));
	]

    let reify_instr env evar renv i =
      let f x = Extlib.init_constant ["Bedrock"; "IL"] x in
      Pattern.shallow_match i
	[
	  f "Assign", 2, (fun args -> let renv, l = reify_lvalue env evar renv args.(0) in
				      let renv, r = reify_rvalue env evar renv args.(1) in
				      renv, Assign (l,r) );
	  f "Binop", 4, (fun args -> let renv, l = reify_lvalue env evar renv args.(0) in
				     let renv, r1 = reify_rvalue env evar renv args.(1) in
				     let op = args.(2) in
				     let renv, r2 = reify_rvalue env evar renv args.(3) in
				     renv, Binop (l,r1,op,r2));
	]


    let reify_instrs env evar renv is =
      let nil = Lazy.force Extlib.List._nil in
      let cons = Lazy.force Extlib.List._cons in
      let rec aux renv is =
	Pattern.matchf is
	  [
	    app nil [| __ |], (fun _ -> renv, []);
	    app cons [| __ ; var "h" ; var "t"|],
	    (fun e -> let renv, i = reify_instr env evar renv (get e "h") in
		      let renv, is = aux renv (get e "t") in
		      renv, i :: is
	    )
	  ]
      in aux renv is


    (* DO NOT FORGET TO CLEAR THE HYPS *)
    let build_path env evar renv st hyps : Renv.t * Term.constr option * istream * proof =
      let eval_cond = Extlib.init_constant ["Bedrock"; "Structured"] "evalCond" in
      let eval_instr = Extlib.init_constant ["Bedrock"; "IL"] "evalInstrs" in
      let eq = Lazy.force (Extlib.Leibniz._eq) in
      let some = Lazy.force (Extlib.Option._some) in
      let none = Lazy.force (Extlib.Option._none) in
      let rec aux renv st l used =
	match l with
	  | [] -> renv, Some st, [], ([], Some st)
	  | (h,_)::q when List.mem h used -> aux renv st q used
	  | (h,ty):: q ->
	    Pattern.matchf ty
	      (* EVAL COND *)
	      [app eq [| __ ;
			 app eval_cond [|  var "l" ; var "t" ; var "r" ; __ ; const st |];
			 var "st'" |],
     	       (fun e ->
		 let renv,l = reify_rvalue env evar renv (get e "l") in
		 let renv,r = reify_rvalue env evar renv (get e "r") in
		 Pattern.matchf (get e "st'")
		   [
		     app none [| __ |],
		     (fun _ ->
		       let i = Inr (l, get e "t",r,(get e "st'")) in
		       renv, None, [i] , ([h,ty], None));
		     app some [| __ ; var "st2"|],
		     (fun _ -> 		(* st2 is not used in Gregory's code *)
		       let renv, stf , is , (ispf,ispfo) = aux renv st q (h::used) in
		       let i = Inr (l, get e "t", r, get e "st'" ) in
		       renv, stf, i:: is, ((h, ty) :: ispf, ispfo)
		     )
		   ]
	       );
	       (* EVAL INSTR *)
	       app eq [| __ ;
	     		 app eval_instr [| __ ; const st ;  var "i"  |];
	     		 var "st'"
	     	      |],
	       (fun e ->
		 let renv,sis = reify_instrs env evar renv (get e "i") in
		 Pattern.matchf (get e "st'")
	     	   [
	     	     app none [| __ |], (fun _ -> renv,None,[Inl (sis, None)] , ([h,ty], None));
	     	     app some [| __ ; var "st2"|],
	     	     (fun e' ->
		     (* recursive call on hyps, termination ensured by using [used] *)
		       debug "st2 is %a\n" pp_constr (get e' "st2");
		       let renv, stf, is , (ispf, ispfo)= aux renv (get e' "st2") hyps (h::used) in
		       let i = Inl (sis, Some (get e' "st2")) in
		       renv, stf, i:: is, ((h,ty) :: ispf, ispfo)
	     	     )
	     	   ]
	       );
	       __ , (fun _ -> aux renv st q (h :: used))
	      ]
      in
      aux renv st hyps []



    let reify gl l st =
      let renv = Renv.empty in
      let hyps = Tacmach.pf_hyps_types gl in
      let env = Tacmach.pf_env gl in
      let evar = Tacmach.project gl in
      let nil = Lazy.force Extlib.List._nil in
      let cons = Lazy.force Extlib.List._cons in
      let impl = Extlib.init_constant ["Bedrock"; "Expr"] "Impl" in
      let rec aux renv l =
	Pattern.matchf l
	  [
	    app nil [| __ |], (fun _ -> renv);
	    app cons [| __ ; var "h" ; var "t"|],
	    (fun e ->
	      let h = (get e "h") in
	      let h = Term.mkApp (impl,[| h|]) in
	      let renv, _ = Renv.add_type env evar renv h in
	      aux renv (get e "t")
	    )
	  ]
      in
      let l = match Extlib.decomp_term l with
	| Term.Const c -> Environ.constant_value env c
	| _ -> l
      in
      let renv = aux renv l in
      let renv, stf, is, ispf = build_path env evar renv st hyps in
      debug "Renv:\n%a\n%a" Renv.pp renv pp_istream is;
      Tacticals.tclIDTAC gl
  end


    let parse_types (types : Term.constr) =
      let impl = Extlib.init_constant ["Bedrock"; "Expr"] "Impl" in
      let types,_ = Extlib.List.of_constr types in
       List.map (fun x ->
	 let t = Term.mkApp (impl, [|x|]) in
	 Reduction.whd_betaiota t, x) types

    let parse_funcs env evar renv types (funcs : Term.constr) =
      try
	let denotation = Extlib.init_constant ["Bedrock"; "Expr"] "Denotation" in
	let funcs,_ = Extlib.List.of_constr funcs in
	let funcs = List.rev funcs in
	let funcs = List.map (fun x ->
	  Tacred.simpl env evar (Term.mkApp (denotation, [|types; x|]))
	) funcs in
	let renv = List.fold_right (fun f renv ->
	  debug "%a\n%!" pp_constr f;
	  let ty = Typing.type_of env evar f in
	  (* let ty = Tacred.hnf_constr env evar ty in  *)
      	  let (rel_context, return) = Term.decompose_prod_assum ty in
	  let types = List.fold_left (fun acc (_,_,ty) -> ty :: acc) [] rel_context in
	  let renv, _ = Renv.add_func env evar renv f types return in
	  renv
	) funcs renv in
	renv
      with e -> Format.printf "exception %s\n%!" (Printexc.to_string e); Util.anomaly "should not happen"

    let parse_preds env evar renv types  preds : Renv.t =
      let pcT = mk_tvar (Some 0) in
      let stT = mk_tvar (Some 1) in
      try
	let denotation = Extlib.init_constant ["Bedrock"; "SepIL"; "SEP" ] "SDenotation" in
	let preds , _ = Extlib.List.of_constr preds in
	let preds = List.rev preds in
	let preds = List.map (fun x ->
	  Tacred.simpl env evar (Term.mkApp (denotation, [|types; pcT; stT; x|]))
	) preds in
	let renv = List.fold_right (fun f (renv : Renv.t) ->
	  let ty = Typing.type_of env evar f in
	  (* let ty = Tacred.hnf_constr env evar ty in  *)
      	  let (rel_context, return) = Term.decompose_prod_assum ty in
	  let types = List.fold_left (fun acc (_,_,ty) -> ty :: acc) [] rel_context in
	  let renv,types = List.fold_right (fun ty (renv,acc) ->
	    let renv, t = Renv.add_type env evar renv ty in
	    renv, (ty,t)::acc
	  )  types (renv,[]) in
 	  {renv with Renv.preds = renv.Renv.preds @ [f, types ]}
	) preds renv in
	renv
      with e -> Format.printf "exception %s\n%!" (Printexc.to_string e); Util.anomaly "should not happen"

  (* types and funcs  *)
    let sym_eval_nosep gl (types : Term.constr) (funcs : Term.constr) preds (pures : Term.constr)
	(rp : Term.constr) (sp : Term.constr) (rv : Term.constr) st (k : Tacexpr.glob_tactic_expr) =
      let debug s = if false then Format.printf s else Format.ifprintf (Format.std_formatter) s in
      debug "I was here ! \n%!";
      let hyps = Tacmach.pf_hyps_types gl in
      let env = Tacmach.pf_env gl in
      let evar = Tacmach.project gl in
      let renv = Renv.init (parse_types types) in
      debug "Initialisation done ! \n%!";
      let renv = parse_funcs env evar renv types funcs in
      let renv = parse_preds env evar renv types preds in
      debug "Finished to parse the initial arguments ! \n%!";
      (* we start the actual reification *)
      debug "pure : %a\n%!" pp_constr pures;
      let renv, pures = Expr.reify_exprs env evar renv pures in
      debug "===> Reified the pure props \n %!";	let _ = debug_type_gl gl sp "sp "in

      (* we reify the registers *)
      let renv, rp = Expr.reify_expr env evar renv rp in
      let renv, sp = Expr.reify_expr env evar renv sp in
      let renv, rv = Expr.reify_expr env evar renv rv in
      debug "===> Reified the registers \n %!";
      (* we reify the instructions *)
      let renv, fin, is, ispf = SymIL.build_path env evar renv st hyps in
      debug "Reified the instructions \n %!";
      debug "Renv:\n%a\n%a" Renv.pp renv SymIL.pp_istream is;
      Renv.pose gl renv (fun types funcs preds uvars gl ->
	let rp,sp,rv = Expr.dump_expr types rp, Expr.dump_expr types sp, Expr.dump_expr types rv in
	(* we dump the istream, using [st] as the initial state *)
	let is,ispf = SymIL.dump_istream gl types is ispf st in
	let fin = Extlib.Option.of_option (Extlib.init_constant ["Bedrock"; "IL"] "state") fin in
	let proofs,pures = Expr.dump_expr_list gl types pures in
	let l = [types; funcs; uvars; preds; rp; sp; rv; is; ispf; fin; pures; proofs] in
	(* let _ = let i = ref 0 in List.iter ( fun x -> *)
	(*   debug_type_gl gl x (string_of_int !i); incr i *)
	(* ) l in  *)
	let l = List.map carg l  in
	ltac_apply k l gl
      )

    let sym_eval_sep gl types funcs preds pures rp sp rv  st sf k =
      debug "I was here ! \n%!";
      let hyps = Tacmach.pf_hyps_types gl in
      let env = Tacmach.pf_env gl in
      let evar = Tacmach.project gl in
      let renv = Renv.init (parse_types types) in
      debug "Initialisation done ! \n%!";
      let renv = parse_funcs env evar renv types funcs in
      let renv = parse_preds env evar renv types preds in
      debug "Finished to parse the initial arguments ! \n%!";
      (* we start the actual reification *)
      debug "pure : %a\n%!" pp_constr pures;
      let renv, pures = Expr.reify_exprs env evar renv pures in
      debug "Reified the pure props \n %!";	let _ = debug_type_gl gl sp "sp "in

      (* we reify the registers *)
      let renv, rp = Expr.reify_expr env evar renv rp in
      let renv, sp = Expr.reify_expr env evar renv sp in
      let renv, rv = Expr.reify_expr env evar renv rv in
      debug "Reified the registers \n %!";
      (* we reify the instructions *)
      let renv, fin, is, ispf = SymIL.build_path env evar renv st hyps in
      debug "Reified the instructions \n %!";
      (* we reify the separation logic formula *)
      debug "Reifying the separation logic formula %a\n %!" pp_constr sf;
      let renv, sf = SepExpr.reify_sexpr env evar renv sf in
      debug "Reified the separation logic formula as %a\n %!" SepExpr.pp_sexpr sf;

      debug "Renv:\n%a\n%a" Renv.pp renv SymIL.pp_istream is;
      Renv.pose gl renv (fun types funcs preds uvars gl ->
	let rp,sp,rv = Expr.dump_expr types rp, Expr.dump_expr types sp, Expr.dump_expr types rv in
	(* we dump the istream, using [st] as the initial state *)
	let sf = SepExpr.dump_sexpr gl types sf in
	let is,ispf = SymIL.dump_istream gl types is ispf st in
	let fin = Extlib.Option.of_option (Extlib.init_constant ["Bedrock"; "IL"] "state") fin in
	let proofs,pures = Expr.dump_expr_list gl types pures in
	let l = [types; funcs; uvars; preds; rp; sp; rv; is; ispf; fin; pures; proofs; sf] in
	let _ = let i = ref 0 in List.iter ( fun x ->
	  debug_type_gl gl x (string_of_int !i); incr i
	) l in
	let l = List.map carg l  in
	ltac_apply k l gl
      )

    (* hump cs l r *)
    let sep_canceler gl types funcs preds pures l r k =
      debug "Begin sep_canceler !\n%!";
      let hyps = Tacmach.pf_hyps_types gl in
      let env = Tacmach.pf_env gl in
      let evar = Tacmach.project gl in
      let renv = Renv.init (parse_types types) in
      debug "===> Initialisation done ! \n%!";
      let renv = parse_funcs env evar renv types funcs in
      let renv = parse_preds env evar renv types preds in
      debug "Finished to parse the initial arguments ! \n%!";
      (* we start the actual reification *)
      debug "===> pure : %a\n%!" pp_constr pures;
      let renv, pures = Expr.reify_exprs env evar renv pures in
      debug "===> Reified the pure props \n %!";
      let renv, l = SepExpr.reify_sexpr env evar renv l in
      debug "===> Reified the separation logic formula L\n %!";
      let renv, r = SepExpr.reify_sexpr env evar renv r in
      debug "===> Reified the separation logic formula R\n %!";
      Renv.pose gl renv (fun types funcs preds uvars gl ->
	let l = SepExpr.dump_sexpr gl types l in
	let r = SepExpr.dump_sexpr gl types r in
	let proofs,pures = Expr.dump_expr_list gl types pures in
	let l = [types; funcs; uvars; preds; l; r; pures; proofs ] in
	let _ = let i = ref 0 in List.iter ( fun x ->
	  debug_type_gl gl x (string_of_int !i); incr i
	) l in
	let l = List.map carg l  in
	ltac_apply k l gl)

end


let reify_application gl term k =
  let env = Tacmach.pf_env gl in
  let evar = Tacmach.project gl in
  match reify_application env evar term with
    | Some (f, types, args, _) ->
      let t  = Termops.new_Type () in
      let types = List.map (fun x -> (Term.mkCast (x, Term.DEFAULTcast ,t)))  types   in
      let args =  fst (Extlib.Tuple.of_list (List.combine args types)) in
      let types = Extlib.List.of_list t types in
      begin
	try
	  ltac_apply k [carg f; carg types; carg args] gl
	with
	    _ -> Util.anomaly "ltac apply failed"
      end
    | None -> Util.anomaly "reify_application failed"


TACTIC EXTEND start_timer
    | ["refl_app_cps" constr(term)  tactic(k)  ] ->
      [
	fun gl ->reify_application gl term k
      ]
	END;;

(* constr(types) constr(funcs) constr(uvars) constr(vars) tactic(k) *)
TACTIC EXTEND plugin_
    | ["reify_expr" constr(e)  ] ->
      [
	fun gl ->
	  let renv = Bedrock.Renv.empty in
	  let env = Tacmach.pf_env gl in
	  let evar = Tacmach.project gl in
	  let _ = Format.printf "%s\n%!" (String.make 6 '*') in
	  let renv, f = Bedrock.Expr.reify_expr env evar  renv e in
	  Format.printf "Env\n%a\nExpr:%a\nReification:%a\n"  Bedrock.Renv.pp renv pp_constr e Bedrock.Expr.pp_expr f ;
	  Bedrock.Renv.pose gl renv (fun types funcs preds uvars gl ->
	    let t = Bedrock.Expr.dump_expr types f in
	    debug_type_gl gl t "t";

	    Tacticals.tclIDTAC gl
	  )
      ]
	END;;



(* constr(types) constr(funcs) constr(uvars) constr(vars) tactic(k) *)
TACTIC EXTEND plugin_2
    | ["reify_sexpr" constr(e)  ] ->
      [
	fun gl ->
	  let renv = Bedrock.Renv.empty in
	  let env = Tacmach.pf_env gl in
	  let evar = Tacmach.project gl in
	  let _ = Format.printf "%s\n%!" (String.make 6 '*') in
	  let renv, f = Bedrock.SepExpr.reify_sexpr env evar  renv e in
	  Format.printf "Env\n%a\nSExpr:%a\nReification:%a\n" Bedrock.Renv.pp renv pp_constr e Bedrock.SepExpr.pp_sexpr f ;
	  Bedrock.Renv.pose gl renv (fun types funcs preds uvars gl ->
	    Tacticals.tclIDTAC gl
	  )
      ]
END;;

TACTIC EXTEND plugin_3
    | ["build_path_plugin" constr(l) constr(st)] -> [fun gl ->
      Bedrock.SymIL.reify gl l st						    ]
END;;

TACTIC EXTEND plugin_4
  | ["sym_eval_nosep" constr(types) constr(funcs) constr(preds) constr(pures) constr(rp) constr(sp) constr(rv) constr(st) tactic(k)] ->
    [fun gl ->
      Bedrock.sym_eval_nosep gl types funcs preds pures rp sp rv st k
    ]
END;;

TACTIC EXTEND plugin_5
  | ["sym_eval_sep" constr(types) constr(funcs) constr(preds) constr(pures) constr(rp) constr(sp) constr(rv) constr(st) constr(sf) tactic(k)] ->
    [fun gl ->
      (* ltac_apply k [carg f; carg types; carg args] *)
      Bedrock.sym_eval_sep gl types funcs preds pures rp sp rv st sf k
    ]
END;;


TACTIC EXTEND plugin_6
  | ["sep_canceler_plugin" constr(types) constr(funcs) constr(preds) constr(pures) constr(l) constr(r) tactic(k)] ->
    [fun gl ->
      (* ltac_apply k [carg f; carg types; carg args] *)
      Bedrock.sep_canceler gl types funcs preds pures l r k
    ]
END;;
