Set Implicit Arguments.

Require Import AxSpec.
Require Import DFModule.
Require Import DFacade.

Require Import String.
Require Import List.
Require Import Bedrock.Platform.Cito.NameDecoration.
Require Import GLabelMap.
Require Import Bedrock.Platform.Cito.GLabelMapFacts.
Require Import ListFacts3.
Require Import StringMap.
Import StringMap.
Require Import Bedrock.Platform.Cito.StringMapFacts.
Import FMapNotations.
Local Open Scope fmap_scope.

Section TopSection.

  Variable ADTValue : Type.
  (* exported axiomatic specs *)
  Variable exports : StringMap.t (AxiomaticSpec ADTValue).

  Definition AxSafe spec args (st : State ADTValue) :=
    exists input,
      length input = length args /\
      st == make_map args input /\
      PreCond spec input.

  Definition get_output st2 (arg_input : String.string * Value ADTValue) : option ADTValue :=
    let (x, i) := arg_input in
    match i with
        ADT _ =>
        match find x st2 with
            Some (ADT a) => Some a
          | _ => None
        end
      | SCA _ => None
    end.

  (* st1 : pre-call state *)
  (* st2 : post-call state *)
  Definition AxRunsTo spec args rvar (st st' : State ADTValue) :=
    exists inputs ret,
      length inputs = length args /\
      st == make_map args inputs /\
      let outputs := List.map (get_output st') (combine args inputs) in
      let inputs_outputs := combine inputs outputs in
      PostCond spec inputs_outputs ret /\
      find rvar st' = Some ret /\
      no_adt_leak inputs args rvar st'.

  Definition op_refines_ax (ax_env : Env _) (op_spec : OperationalSpec) (ax_spec : AxiomaticSpec _) :=
    let args := ArgVars op_spec in
    let rvar := RetVar op_spec in
    let s := Body op_spec in
    (exists (is_ret_adt : bool),
       forall in_out ret,
         PostCond ax_spec in_out ret ->
         if is_ret_adt then exists a : ADTValue, ret = ADT a
         else exists w, ret = SCA _ w) /\
    (forall ins,
       PreCond ax_spec ins ->
       length args = length ins) /\
    (forall st,
       AxSafe ax_spec args st ->
       Safe ax_env s st) /\
    forall st st',
      AxSafe ax_spec args st ->
      RunsTo ax_env s st st' ->
      AxRunsTo ax_spec args rvar st st'.

  Definition ops_refines_axs ax_env (op_specs : StringMap.t OperationalSpec) (ax_specs : StringMap.t (AxiomaticSpec _)) :=
    forall x ax_spec,
      find x ax_specs = Some ax_spec ->
      exists op_spec,
        find x op_specs = Some op_spec /\
        op_refines_ax ax_env op_spec ax_spec.

  Definition aug_mod_name (m_name s : String.string) := (m_name, s).
  Definition map_aug_mod_name elt m_name (m : StringMap.t elt) := GLabelMapFacts.of_list (List.map (fun p => (aug_mod_name m_name (fst p), (snd p))) (StringMap.elements m)).

  Require Import GLabelMapFacts.
  Import FMapNotations.

  (* the whole environment of callable functions with their specs, including
         (1) functions defined in 'module' with op. specs
         (2) functions defined in 'module' with ax. specs given by 'exports'
         (3) imports of 'module'
   *)
  Definition get_env op_mod_name (exports : StringMap.t (AxiomaticSpec ADTValue)) module : Env ADTValue :=
    GLabelMap.map (fun (f : DFFun) => Operational _ f) (map_aug_mod_name op_mod_name (Funs module)) +
    GLabelMap.map (@Axiomatic _) (map_aug_mod_name op_mod_name exports) +
    GLabelMap.map (@Axiomatic _) (Imports module).

  Require Import StringMapFacts.

  Record CompileUnit :=
    {
      module : DFModule ADTValue;
      (* the name of the module that contains axiomatic export specs *)
      ax_mod_name : String.string;
      (* the name of the module that contains operational export specs *)
      op_mod_name : String.string;
      exports_in_domain : is_sub_domain exports (Funs module) = true;
      op_mod_name_ok : is_good_module_name op_mod_name = true;
      op_mod_name_not_in_imports :
        let imported_module_names := List.map (fun x => fst (fst x)) (GLabelMap.elements (Imports module)) in
        List.forallb (fun x => negb (string_bool op_mod_name x)) imported_module_names = true;
      name_neq : negb (string_bool ax_mod_name op_mod_name) = true;
      proof : ops_refines_axs (get_env op_mod_name exports module) (StringMap.map Core (Funs module)) exports
    }.

End TopSection.
