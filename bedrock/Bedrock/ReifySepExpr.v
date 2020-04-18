Require Import Bedrock.Expr Bedrock.ReifyExpr.
Require Import Bedrock.Reflect.
Require Import Bedrock.SepExpr.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Module ReifySepExpr (Import SEP : SepExpr).

  (** Reflection **)
  Import Reflect.

(*
  Ltac lift_predicate s nt pc st :=
    let d := eval simpl SDomain in (SDomain s) in
    let f := eval simpl SDenotation in (SDenotation s) in
    let res := constr:(@PSig nt pc st d f) in
    eval simpl in res.

  Ltac lift_predicates fs nt :=
    match type of fs with
      | list (predicate _ ?pc ?st) =>
        let f sig :=
          lift_predicate sig nt pc st
        in
        map_tac (predicate nt pc st) f fs
    end.
*)

  (** collect the types from an hprop expression.
   ** - s is an expression of type hprop
   ** - types is a list of raw types, i.e. of type [list Type]
   ** - k is the continuation, it must be an ltac function
   **   that takes a single argument of type [list Type]
   **)
  Ltac collectTypes_sexpr isConst s types k :=
    match s with
      | fun x : ReifyExpr.VarType ?T => @ST.star _ _ _ (@?L x) (@?R x) =>
        collectTypes_sexpr isConst L types ltac:(fun types =>
          collectTypes_sexpr isConst R types k)
      | fun x : ?T => @ST.ex _ _ _ ?T' (fun y : ?T' => @?B x y) =>
        let v := constr:(fun x : ReifyExpr.VarType (T * T') =>
          B (@openUp _ T (@fst _ _) x) (@openUp _ T' (@snd _ _) x)) in
        let v := eval simpl in v in
        collectTypes_sexpr isConst v types k
      | fun x : ?T => @ST.inj _ _ _ (PropX.Inj (@?P x)) =>
         collectTypes_expr isConst P types k
      | fun x : ?T => @ST.emp _ _ _ => k types
      | @ST.emp _ _ _ => k types
      | @ST.inj _ _ _ (PropX.Inj ?P) =>
        collectTypes_expr isConst P types k
      | @ST.inj _ _ _ ?PX => k types
      | @ST.star _ _ _ ?L ?R =>
        collectTypes_sexpr isConst L types
          ltac:(fun Ltypes => collectTypes_sexpr isConst R Ltypes k)
      | @ST.ex _ _ _ ?T (fun x : ?T => @?B x) =>
        let v := constr:(fun x : ReifyExpr.VarType T => B (@openUp _ T (fun x => x) x)) in
        let v := eval simpl in v in
        collectTypes_sexpr isConst v types k
      | ?X =>
        let rec bt_args args types k :=
          match args with
            | tt => k types
            | (?a,?b) =>
              collectTypes_expr isConst a types ltac:(fun ts =>  bt_args b ts k)
          end
        in
        let cc _ Ts args :=
          let types := append_uniq Ts types in
          bt_args args types k
        in
        refl_app cc X
    end.

  (** collect types from all of the separation logic goals given
   ** in goals.
   ** - goals is a gallina list of type [list hprop]
   ** - types is a list of raw types.
   ** - isConst determines when an expression should be treated as a constant.
   **)
  Ltac collectAllTypes_sexpr isConst types goals k :=
    match goals with
      | nil => k types
      | ?a :: ?b =>
        collectTypes_sexpr isConst a types ltac:(fun ts =>
          collectAllTypes_sexpr isConst ts b k)
    end.

  Ltac collectAllTypes_sfunc Ts T :=
    match T with
      | ?t -> ?T =>
        let t := constr:(t : Type) in
        let Ts := cons_uniq t Ts in
        collectAllTypes_sfunc Ts T
      | forall x , _ =>
        (** Can't reflect types for dependent function **)
        fail 100 "can't reflect types for dependent function!"
          "type is " T
      | _ => Ts (** assume we are at the end **)
    end.

  Ltac collectAllTypes_sfuncs Ts Fs :=
    match Fs with
      | tt => Ts
      | (?Fl, ?Fr) =>
        let Ts := collectAllTypes_sfuncs Ts Fl in
        collectAllTypes_sfuncs Ts Fr
      | ?F =>
        let T := type of F in
        collectAllTypes_sfunc Ts T
    end.

  (** reflect a separation logic predicate. this is analagous
   ** to reify_function except that it works on separation logic functions.
   **)
  Ltac reify_sfunction pcT stT types f :=
    match f with
      | fun _ => _ =>
        constr:(@PSig types pcT stT (@nil tvar) f)
      | _ =>
        let T := type of f in
          let rec refl dom T :=
            match T with
        (* no dependent types *)
              | ?A -> ?B =>
                let A := reflectType types A in
                  let dom := constr:(A :: dom) in
                    refl dom B
              | _ =>
                let dom := eval simpl rev in (rev dom) in
                  constr:(@PSig types pcT stT dom f)
            end
            in refl (@nil tvar) T
    end.

  (** get the index for a separation logic predicate. this is analagous
   ** to getFunction.
   ** - k is the continutation which accepts the, possibly extended,
   **  list of separation logic predicates and the index of the desired
   **  predicate.
   **)
  Ltac getSFunction pcT stT types f sfuncs k :=
    let rec lookup sfuncs' acc :=
      match sfuncs' with
        | nil =>
          (let F := reify_sfunction pcT stT types f in
           let sfuncs := eval simpl app in (sfuncs ++ (F :: nil)) in
           k sfuncs acc) || fail 10000 "ERROR!"
        | ?F :: ?FS =>
          (** NOTE: you can not use the primitive 'unify' or anything based on it b/c
           ** it instantiates unification variables that should not be instantiated
           **)
          match F with
            | @PSig _ _ _ _ ?F =>
              match F with
                | f => k sfuncs acc
                | _ =>
                  let acc := constr:(S acc) in
                  lookup FS acc
              end
            | _ =>
              match eval hnf in F with
                | @PSig _ _ _ _ ?F =>
                  match F with
                    | f => k sfuncs acc
                    | _ =>
                      let acc := constr:(S acc) in
                        lookup FS acc
                  end
                | _ => fail 100000 "something bad happened!"
              end
          end
      end
    in lookup sfuncs 0.

  Ltac getAllSFunctions pcT stT types sfuncs' fs :=
    match fs with
      | tt => sfuncs'
      | ( ?fl , ?fr ) =>
        let sfuncs := getAllSFunctions pcT stT types sfuncs' fl in
        getAllSFunctions pcT stT types sfuncs fr
      | ?F =>
        getSFunction pcT stT types F sfuncs' ltac:(fun sfuncs _ => sfuncs)
    end.

  (** reflect sexprs. simultaneously gather the unification variables, funcs and sfuncs
   ** k is called with the unification variables, functions, separation logic predicats and the reflected
   ** sexpr.
   **)
  Ltac reify_sexpr isConst s types funcs pcType stateType sfuncs uvars vars k :=
    let implicits ctor :=
      constr:(ctor types pcType stateType)
    in
    let rec reflect s funcs sfuncs uvars vars k :=
      match s with
        | fun _ => ?s =>
          reflect s funcs sfuncs uvars vars k
        | fun x : ReifyExpr.VarType ?T => @ST.star _ _ _ (@?L x) (@?R x) =>
          reflect L funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs L =>
            reflect R funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs R =>
              let r := constr:(@Star types pcType stateType L R) in
              k uvars funcs sfuncs r))
        | fun x : ?T => @ST.ex _ _ _ ?T' (fun y => @?B x y) =>
          let v := constr:(fun x : ReifyExpr.VarType (T' * T) =>
            B (@openUp _ T (@snd _ _) x) (@openUp _ T' (@fst _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T' in
          reflect v funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs B =>
            let r := constr:(@Exists types pcType stateType nv B) in
            k uvars funcs sfuncs r)
        | fun x : ?T => @ST.emp _ _ _ =>
          let r := constr:(@Emp types pcType stateType) in
          k uvars funcs sfuncs r

        | fun x : ?T => @ST.inj _ _ _ (PropX.Inj (@?P x)) =>
          reify_expr isConst P types funcs uvars vars ltac:(fun uvars funcs P =>
            let r := constr:(@Inj types pcType stateType P) in
            k uvars funcs sfuncs r)

        | @ST.emp _ _ _ =>
          let r := constr:(@Emp types pcType stateType) in
          k uvars funcs sfuncs r

        | @ST.inj _ _ _ (PropX.Inj ?P) =>
          reify_expr isConst P types funcs uvars vars ltac:(fun uvars funcs P =>
            let r := constr:(@Inj types pcType stateType P) in
            k uvars funcs sfuncs r)
        | @ST.inj _ _ _ ?PX =>
          let r := constr:(@Const types pcType stateType PX) in
          k uvars funcs sfuncs r
        | @ST.star _ _ _ ?L ?R =>
          reflect L funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs L =>
            reflect R funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs R =>
              let r := constr:(@Star types pcType stateType L R) in
              k uvars funcs sfuncs r))
        | @ST.ex _ _ _ ?T (fun x => @?B x) =>
          let v := constr:(fun x : ReifyExpr.VarType (T * unit) => B (@openUp _ T (@fst _ _) x)) in
          let v := eval simpl in v in
          let nv := reflectType types T in
          reflect v funcs sfuncs uvars vars ltac:(fun uvars funcs sfuncs B =>
            let r := constr:(@Exists types pcType stateType nv B) in
            k uvars funcs sfuncs r)
        | ?X =>
          let rec bt_args args uvars funcs k :=
            match args with
              | tt =>
                let v := constr:(@nil (@expr types)) in
                k uvars funcs v
              | (?a,?b) =>
                reify_expr isConst a types funcs uvars vars ltac:(fun uvars funcs a =>
                  bt_args b uvars funcs ltac:(fun uvars funcs b =>
                  let v := constr:(@cons (@expr types) a b) in
                  k uvars funcs v))
            end
          in
          let cc f Ts As :=
            getSFunction pcType stateType types f sfuncs ltac:(fun sfuncs F =>
            bt_args As uvars funcs ltac:(fun uvars funcs args =>
            let r := constr:(@Func types pcType stateType F args) in
            k uvars funcs sfuncs r))
          in
          refl_app cc X
      end
    in
    reflect s funcs sfuncs uvars vars k.

End ReifySepExpr.
