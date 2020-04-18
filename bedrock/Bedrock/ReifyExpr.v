Require Import Coq.Lists.List.
Require Import Bedrock.EqdepClass.
Require Import Bedrock.Word.
Require Import Coq.Bool.Bool Bedrock.Folds.
Require Import Bedrock.Reflection.
Require Import Bedrock.Expr.


(** Tactics **)
Require Import Bedrock.Reflect.

(*
Ltac lift_signature s nt :=
  let d := eval simpl Domain in (Domain s) in
  let r := eval simpl Range in (Range s) in
  let den := eval simpl Denotation in (Denotation s) in
  constr:(@Sig nt d r den).

Ltac lift_signatures fs nt :=
  let f sig :=
    lift_signature sig nt
  in
  map_tac (signature nt) f fs.
*)

Definition default_type (T : Type) : type.
Proof.
  refine ({| Impl := T
             ; Eqb := fun _ _ => false
             ; Eqb_correct := _
          |}). abstract (discriminate).
Defined.

(* (* TODO: remove this type-class... *) *)
(* Global Instance SemiDec_nat : SemiDec nat.  *)
(* constructor. intros. *)
(* destruct (Peano_dec.eq_nat_dec a b). refine (Some e). refine (None).  *)
(* Defined.  *)

Definition type_of_ReificationHint T : ReificationHint.Pkg T -> type.
intros [Eqb EqbH]; apply (@Typ T Eqb EqbH).
Defined.

Global Instance ReificationHintNat : ReificationHint.Pkg nat :=
           ReificationHint.mk_Pkg EqNat.beq_nat EqNat.beq_nat_true.

Ltac build_default_type T :=
  match goal with
    | [ |- _ ] => let C := constr:(_ : ReificationHint.Pkg T) in
                 let t := constr:(type_of_ReificationHint C) in
                   t
    | [ |- _ ] => constr:(default_type T)
  end.

Ltac extend_type T types :=
  match T with
    | Prop => types
    | _ =>
      let rec find types :=
        match types with
          | nil => constr:(false)
          | ?a :: ?b =>
            match unifies (Impl a) T with
              | true => constr:(true)
              | false => find b
            end
        end
      in
      match find types with
        | true => types
        | _ =>
          let D := build_default_type T in
          eval simpl app in (types ++ (D :: @nil type))
      end
  end.

(* extend a reflected type list with new raw types
 * - Ts is a list of raw types
 * - types is a list of reflected types
 *)
Ltac extend_all_types Ts types :=
  match Ts with
    | Tnil => types
    | Tcons ?a ?b =>
      let types := extend_type a types in
      extend_all_types b types
  end.

Record VarType (t : Type) : Type :=
  { open : t }.
Definition openUp T U (f : T -> U) (vt : VarType T) : U :=
  f (open _ vt).

(** collect the raw types from the given expression.
 ** - e is the expression to collect types from
 ** - types is a value of type [list Type]
 **   (make sure it is NOT [list Set])
 **)
Ltac collectTypes_expr isConst e Ts K :=
  match e with
    | fun x => (@openUp _ ?T _ _) =>
        let p := cons_uniq T Ts in
        K p
    | fun x => ?e =>
      collectTypes_expr isConst e Ts K
    | _ =>
      let rec bt_args args Ts K :=
        match args with
          | tt => K Ts
          | (?a, ?b) =>
            collectTypes_expr isConst a Ts ltac:(fun Ts => bt_args b Ts  K)
        end
      in
      let cc _ Ts' args :=
        let T :=
          match e with
            | fun x : VarType _ => _ =>
              match type of e with
                | _ -> ?T => T
              end
            | _ => type of e
          end
        in
        let Ts := cons_uniq T Ts in
        let Ts := append_uniq Ts' Ts in
        bt_args args Ts K
      in
      refl_app cc e
  end.

Ltac collectAllTypes_expr isConst Ts goals K :=
  match goals with
    | tt => K Ts
    | (?a, ?b) =>
      collectTypes_expr isConst a Ts ltac:(fun ts => collectAllTypes_expr isConst ts b K)
  end.

Ltac collectAllTypes_func Ts T :=
  match T with
    | ?t -> ?T =>
      let t := constr:(t : Type) in
      let Ts := cons_uniq t Ts in
      collectAllTypes_func Ts T
    | forall x , _ =>
        (** Can't reflect types for dependent function **)
      fail 100 "can't reflect types for dependent function!"
    | ?t =>
      let t := constr:(t : Type) in
      cons_uniq t Ts
  end.

Ltac collectAllTypes_funcs Ts Fs :=
  match Fs with
    | tt => Ts
    | (?Fl, ?Fr) =>
      let Ts := collectAllTypes_funcs Ts Fl in
      collectAllTypes_funcs Ts Fr
    | ?F =>
      let T := type of F in
      collectAllTypes_func Ts T
  end.

Ltac collect_props shouldReflect :=
  let rec collect skip :=
    match goal with
      | [ H : ?X |- _ ] =>
        match shouldReflect X with
          | true =>
            match skip with
              | context [H] => fail 1
              | _ =>
                let skip := constr:((H, skip)) in
                collect skip
            end
        end
      | _ => skip
    end
  in collect tt.

Ltac props_types ls :=
  match ls with
    | tt => constr:(@nil Prop)
    | (?H, ?ls) =>
      let P := type of H in
      let rr := props_types ls in
      constr:(P :: rr)
  end.

Ltac props_proof ls :=
  match ls with
    | tt => I
    | (?H, ?ls) =>
      let rr := props_proof ls in
      constr:(conj H rr)
  end.

(*
Ltac collectAllTypes_props shouldReflect isConst Ts :=
  let rec collect Ts skip :=
    match goal with
      | [ H : ?X |- _ ] =>
        match reflectable shouldReflect X with
          | true =>
            match hcontains H skip with
              | false =>
                let Ts := collectTypes_expr isConst X Ts in
                let skip := constr:((H, skip)) in
                collect Ts skip
            end
        end
      | _ => Ts
    end
  in collect Ts tt.
*)

(*
(** find x inside (map proj xs) and return its position as a natural number.
 ** This tactic fails if x does not occur in the list
 ** - proj is a gallina function.
 **)
Ltac indexOf_nat proj x xs :=
  let rec search xs :=
    match xs with
      | ?X :: ?XS =>
        match unifies (proj X) x with
          | true => constr:(0)
          | false =>
            let r := search XS in
              constr:(S r)
        end
      | _ =>
        let xs := eval hnf in xs in
        search xs
    end
  in search xs.
*)

(** specialization of indexOf_nat to project from type **)
Ltac typesIndex x types :=
  let rec search xs :=
    match xs with
      | ?X :: ?XS =>
        match unifies (Impl X) x with
          | true => constr:(0)
          | false =>
            let r := search XS in
              constr:(S r)
        end
      | _ =>
        let xs := eval hnf in xs in
        search xs
    end
  in search types.

(** given the list of types (of type [list type]) and a raw type
 ** (of type [Type]), return the [tvar] that corresponds to the
 ** given raw type.
 **)
Ltac reflectType types t :=
  match t with
    | Prop => constr:(tvProp)
    | _ =>
      let i := typesIndex t types in
      let r := constr:(tvType i) in
      r
    | _ =>
      fail 10000 "couldn't find " t " inside types " types
  end.

(** essentially this is [map (reflectType types) ts] **)
Ltac reflectTypes_toList types ts :=
  match eval hnf in ts with
    | nil => constr:(@nil tvar)
    | ?T :: ?TS =>
      let i := typesIndex T types in
      let rest := reflectTypes_toList types TS in
      constr:(@cons tvar (tvType i) rest)
  end.

(** Build a signature for the given function
 ** - types is a list of reflected types, i.e. type [list type]
 ** the type of f can NOT be dependent, i.e. it must be of the
 ** form,
 **   _ -> ... -> _
 **)
Ltac reify_function types f :=
  let T := type of f in
  let rec refl dom T :=
    match T with
        (* no dependent types *)
      | ?A -> ?B =>
        let A := reflectType types A in
        let dom := constr:(A :: dom) in
        refl dom B
      | ?R =>
        let R := reflectType types R in
        let dom := eval simpl rev in (rev dom) in
        constr:(@Sig types dom R f)
    end
  in refl (@nil tvar) T.

(** lookup a function in a list of reflected functions.
 ** if the function does not exist in the list, the list is extended.
 ** - k is the continutation and is passed the resulting list of functions
 **   and the index of f in the list.
 **   (all elements passed into funcs' are preserved in order)
 **)
Ltac getFunction types f funcs' k :=
  let rec lookup funcs acc :=
    match funcs with
      | nil =>
        let F := reify_function types f in
        let funcs := eval simpl app in (funcs' ++ (F :: nil)) in
        k funcs acc
      | ?F :: _ =>
        guard_unifies f (Denotation F) ;
        k funcs' acc
      | _ :: ?FS =>
        let acc := constr:(S acc) in
        lookup FS acc
      | _ =>
        idtac "had to hnf in funcs" funcs ;
        let funcs := eval hnf in funcs in
        lookup funcs acc
    end
  in
  lookup funcs' 0.

Ltac getAllFunctions types funcs' fs :=
  match fs with
    | tt => funcs'
    | ?F =>
      getFunction types F funcs' ltac:(fun funcs _ => funcs)
    | ( ?fl , ?fr ) =>
      let funcs := getAllFunctions types funcs' fl in
      getAllFunctions types funcs fr
  end.

Ltac getVar' idx :=
  match idx with
    | fun x => x => constr:(0)
    | fun x => @openUp _ _ (@snd _ _) (@?X x) =>
      let r := getVar' X in
      constr:(S r)
    | _ => idtac "couldn't find variable! [1]" idx
  end.

Ltac getVar idx :=
  (** NOTE: reification as indicies **)
  match idx with
    | fun x => @openUp _ _ (@fst _ _) (@?X x) =>
      getVar' X
    | fun x => @openUp _ _ (@snd _ _) (@?X x) =>
      let r := getVar X in
      constr:(S r)
    | _ => idtac "couldn't find variable! [2]" idx
  end.

Ltac get_or_extend_var types all t v k :=
  let rec doIt rem acc :=
    match rem with
      | nil =>
        (** NOTE: reification as levels **)
        let all :=
          eval simpl app in (all ++ (@existT tvar (tvarD types) t v) :: nil)
        in
        k all acc
      | @existT _ _ _ ?v' :: _ => constr_eq v v' ; k all acc
      | _ :: ?rem =>
        let acc := constr:(S acc) in
        doIt rem acc
    end
  in
  doIt all 0.

(** reflect an expression gathering the functions at the same time.
 ** - k is the continuation and is passed the list of reflected
 **   uvars, functions, and the reflected expression.
 **  currently, vars and isConst are not used
 **)
Ltac reify_expr isConst e types funcs uvars vars k :=
  let rec reflect e funcs uvars k :=
    match e with
      | ?X => is_evar X ;
        (** this is a unification variable **)
        let t := type of X in
        let T := reflectType types t in
        get_or_extend_var types uvars T X ltac:(fun uvars v =>
          let r := constr:(@UVar types v) in
          k uvars funcs r)
      | fun _ => ?X => is_evar X ;
        (** TODO : test this **)
        (** this is a unification variable **)
        let t := type of X in
        let T := reflectType types t in
        get_or_extend_var types uvars T X ltac:(fun uvars v =>
          let r := constr:(@UVar types v) in
          k uvars funcs r)
      | fun x => (@openUp _ _ _ _) =>
        (** this is a variable **)
        let v := getVar e in
        let r := constr:(@Var types v) in
        (k uvars funcs r)

      | @eq ?T ?e1 ?e2 =>
        let T := reflectType types T in
          reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
            reflect e2 funcs uvars ltac:(fun uvars funcs e2 =>
              (k uvars funcs (Equal T e1 e2))))
      | fun x => @eq ?T (@?e1 x) (@?e2 x) =>
        let T := reflectType types T in
          reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
            reflect e2 funcs uvars ltac:(fun uvars funcs e2 =>
              (k uvars funcs (Equal T e1 e2))))
      | not ?e1 =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          (k uvars funcs (Not e1)))
      | ?e1 -> False =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          k uvars funcs (Not e1))
      | fun x => not (@?e1 x) =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          k uvars funcs (Not e1))
      | fun x => @?e1 x -> False =>
        reflect e1 funcs uvars ltac:(fun uvars funcs e1 =>
          k uvars funcs (Not e1))

      | fun _ => ?e =>
        (** NOTE: it is important for this to be an _ **)
        (reflect e funcs uvars k)

      | _ =>
        let rec bt_args uvars funcs args k :=
          match args with
            | tt =>
              let v := constr:(@nil (@expr types)) in
              k uvars funcs v
            | (?a, ?b) =>
              reflect a funcs uvars ltac:(fun uvars funcs a =>
                bt_args uvars funcs b ltac:(fun uvars funcs b =>
                  let r := constr:(@cons (@expr types) a b) in
                  k uvars funcs r))
          end
        in
        let cc f Ts args :=
          getFunction types f funcs ltac:(fun funcs F =>
            bt_args uvars funcs args ltac:(fun uvars funcs args =>
              let r := constr:(@Func types F args) in
              k uvars funcs r))
        in
        match e with
          | _ =>
            match isConst e with
              | true =>
                let ty := type of e in
                let ty := reflectType types ty in
                let r := constr:(@Const types ty e) in
                k uvars funcs r
              | false => refl_app cc e
            end
          | _ => (refl_app cc e)
        end
    end
  in match e with
       | context[fun x : ?T => _] =>
         match T with
           | VarType _ => fail 1
           | _ => getFunction types e funcs ltac:(fun funcs F =>
             let r := constr:(@Func types F nil) in
               k uvars funcs r)
         end
       | _ => reflect e funcs uvars k
     end.

(** collect all the types in es into a list.
 ** it return a value of type [list Type]
 ** NOTE: this function accepts either a tuple or a list for es
 **)
Ltac collectTypes_exprs isConst es Ts K :=
  match es with
    | tt => K Ts
    | nil => K Ts
    | (?e, ?es) =>
      collectTypes_expr ltac:(isConst) e Ts ltac:(fun Ts =>
        collectTypes_exprs ltac:(isConst) es Ts K)
    | ?e :: ?es =>
      collectTypes_expr ltac:(isConst) e Ts ltac:(fun Ts =>
        collectTypes_exprs ltac:(isConst) es Ts K)

  end.

(** reflect all the expressions in a list.
 ** - k :: env types -> functions types -> list (expr types)
 ** NOTE: this function accepts either a tuple or a list for es
 **)
Ltac reify_exprs isConst es types funcs uvars vars k :=
  match es with
    | tt => k uvars funcs (@nil (expr types))
    | nil => k uvars funcs (@nil (expr types))
    | (?e, ?es) =>
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
          let res := constr:(e :: es) in
          k uvars funcs res))
    | ?e :: ?es =>
      reify_expr ltac:(isConst) e types funcs uvars vars ltac:(fun uvars funcs e =>
        reify_exprs ltac:(isConst) es types funcs uvars vars ltac:(fun uvars funcs es =>
          let res := constr:(e :: es) in
          k uvars funcs res))
  end.
