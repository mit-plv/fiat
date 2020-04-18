Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.FModule.
Require Import Bedrock.Platform.Facade.CompileDFacade.
Require Import Bedrock.Platform.Facade.DFacade.
Require Import Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.WordMap Bedrock.Platform.Cito.GLabelMap Coq.Strings.String Coq.Lists.List Bedrock.Platform.Cito.ListFacts3 Bedrock.Platform.Cito.NameDecoration.
Local Open Scope string_scope.

Notation module_name := "dfmodule".
Notation fun_name := "dffun".
Notation argvar1 := "arg1".
Notation argvar2 := "arg2".
Notation argvars := (argvar1 :: argvar2 :: nil).
Notation retvar := "ret".
Local Open Scope bool_scope.

Section TopSection.

  Variable ADTValue : Type.
  (* pre_cond arg1 arg2 *)
  Variable pre_cond : Value ADTValue -> Value ADTValue -> Prop.
  (* post_cond arg1 arg2 ret *)
  Variable post_cond : Value ADTValue -> Value ADTValue -> Value ADTValue -> Prop.

  Record CompileUnit :=
    {
      (* the DFacade program *)
      prog : Stmt;
      (* syntax checks, can be discharged by eq_refl for concrete prog *)
      no_assign_to_args : is_disjoint (assigned prog) (StringSetFacts.of_list argvars) = true;
      syntax_ok : is_syntax_ok prog = true;
      compile_syntax_ok : FModule.is_syntax_ok (CompileDFacade.compile_op (Build_OperationalSpec argvars retvar prog eq_refl eq_refl no_assign_to_args eq_refl eq_refl syntax_ok)) = true;
      (* imported axiomatic specs *)
      imports : GLabelMap.t (AxiomaticSpec ADTValue);
      import_module_names_ok : let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements imports) in
        forallb (fun x => negb (string_bool module_name x)) imported_module_names &&
        forallb Cito.NameDecoration.is_good_module_name imported_module_names = true;
      (* correctness conditions *)
      pre_safe :
        forall st value1 value2,
          StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) ->
          pre_cond value1 value2 ->
          DFacade.Safe (GLabelMap.map (@Axiomatic _) imports) prog st;
      pre_runsto_post :
        forall st st' value1 value2,
          StringMap.Equal st (StringMapFacts.make_map (argvar1 :: argvar2 :: nil) (value1 :: value2 :: nil)) ->
          pre_cond value1 value2 ->
          DFacade.RunsTo (GLabelMap.map (@Axiomatic _) imports) prog st st' ->
          exists ret, StringMapFacts.Submap (StringMapFacts.make_map (retvar :: nil) (ret :: nil)) st' /\ (forall x, x <> retvar -> not_mapsto_adt x st' = true) /\ post_cond value1 value2 ret
    }.

End TopSection.
