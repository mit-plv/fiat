Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.GLabel Bedrock.Platform.Cito.GLabelMap Bedrock.Platform.Cito.GLabelMapFacts Bedrock.Platform.Cito.ConvertLabel Bedrock.Platform.Cito.GoodModule Bedrock.Platform.Cito.GoodFunction Bedrock.Platform.Cito.NameDecoration Bedrock.Platform.Cito.Label2Word.
Export GLabel GLabelMap GLabelMapFacts ConvertLabel GoodModule GoodFunction Cito.NameDecoration Label2Word.
Import GLabelMap.

Section TopSection.

  Variable ADTValue : Type.

  Variable modules : list GoodModule.

  Require Import Bedrock.Platform.Cito.Semantics.
  Require Import Bedrock.Platform.Cito.AxSpec.

  Variable imports : GLabelMap.t (AxiomaticSpec ADTValue).

  Notation FName := SyntaxFunc.Name.
  Notation MName := GoodModule.Name.

  Definition label_in (lbl : glabel) :=
    (exists m f,
       List.In m modules /\
       List.In f (Functions m) /\
       lbl = (MName m, FName f)) \/
    In lbl imports.

  Notation Internal := (@Internal ADTValue).

  Definition label_mapsto lbl spec :=
    (exists ispec m f,
       spec = Internal ispec /\
       List.In m modules /\
       List.In f (Functions m) /\
       ispec = f /\
       lbl = (MName m, FName f)) \/
    (exists fspec,
       spec = Foreign fspec /\
       find lbl imports = Some fspec).

  Definition stn_good_to_use (stn : settings) :=
    forall lbl : glabel,
      label_in lbl ->
      Labels stn lbl <> None.

  Notation Callee := (@Callee ADTValue).

  Definition fs_good_to_use (fs : settings -> W -> option Callee) (stn : settings) :=
    forall p spec,
      fs stn p = Some spec <->
      exists lbl : glabel,
        Labels stn lbl = Some p /\
        label_mapsto lbl spec.

  Definition glabel2w (stn : settings) (lbl : glabel) : option W := Labels stn lbl.

  Definition env_good_to_use stn fs :=
    stn_good_to_use stn /\
    stn_injective label_in (glabel2w stn) /\
    fs_good_to_use fs stn.

  Definition func_export_IFS m (f : GoodFunction) := ((MName m, FName f), f : InternalFuncSpec).

  Definition module_exports_IFS m :=
    List.map (func_export_IFS m) (Functions m).

  Require Import Bedrock.Platform.Cito.ListFacts1.

  Definition exports_IFS :=
    to_map
      (app_all
         (List.map module_exports_IFS modules)).

  Section fs.

    Variable stn : settings.

    Definition is_export := find_by_word (glabel2w stn) (elements exports_IFS).

    Definition is_import := find_by_word (glabel2w stn) (elements imports).

    Definition fs (p : W) : option Callee :=
      match is_export p with
        | Some spec => Some (Internal spec)
        | None =>
          match is_import p with
            | Some spec => Some (Foreign spec)
            | None => None
          end
      end.

  End fs.

End TopSection.

Definition name_marker (id : glabel) : PropX W (settings * state) := (Ex s, [| s = id |])%PropX.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Make E.
  Export Semantics SemanticsMake.

  Require Import Bedrock.Platform.Cito.RepInv.

  Module Make (Import M : RepInv E).

    Require Import Bedrock.Platform.Cito.CompileFuncSpec.
    Module Import CompileFuncSpecMake := Make E M.
    Import InvMake2.
    Export CompileFuncSpec CompileFuncSpecMake InvMake2.

    Section TopSection.

      Variable modules : list GoodModule.

      Variable imps : t ForeignFuncSpec.

      Notation fs := (fs modules imps).

      (* the exported Bedrock spec format *)
      Definition func_spec (id : glabel) f : assert := (st ~> name_marker id /\ [| env_good_to_use modules imps (fst st) fs |] ---> spec_without_funcs_ok f fs st)%PropX.

      (* the imported Bedrock spec format *)
      Definition foreign_func_spec id spec : assert :=
        st ~> name_marker id /\ ExX, foreign_spec _ spec st.

      (* the imported Bedrock specs *)
      Definition imports := mapi (foreign_func_spec) imps.

      Notation FName := SyntaxFunc.Name.
      Notation MName := GoodModule.Name.

      Definition func_export module (f : GoodFunction) :=
        let lbl := (MName module, FName f) in
        (lbl, func_spec lbl f).

      Definition module_exports m :=
        of_list
          (List.map
             (func_export m)
             (Functions m)).

      (* the exported Bedrock specs (barring the exports from internal implementation, which shouldn't be used) *)
      Definition exports := update_all (List.map module_exports modules).

      Definition impl_label mod_name f_name : glabel := (impl_module_name mod_name, f_name).

      Definition func_impl_export m (f : GoodFunction) := (impl_label (MName m) (FName f), spec f).

      Definition module_impl_exports m :=
        of_list
          (List.map
             (func_impl_export m)
             (Functions m)).

      Definition impl_exports := update_all (List.map module_impl_exports modules).

      (* the imported Bedrock specs (including the exports from internal implementation, which shouldn't be used) *)
      Definition all_exports := update exports impl_exports.

    End TopSection.

  End Make.

End Make.
