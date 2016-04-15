Require Import Fiat.ADT.Core.
Require Import Bedrock.Platform.Facade.DFModule.
Require Import Fiat.ADTNotation.
Require Import Bedrock.Platform.Facade.CompileUnit2.
Require Import Fiat.Common.i3list.
Require Import Fiat.Common.ilist3.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.

Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import CertifiedExtraction.ADT2CompileUnit.

Definition DecomposeIndexedQueryStructure av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  Decomposei3list _ _ rWrap r.
Arguments DecomposeIndexedQueryStructure _ {_ _} _ _ /.

Definition DecomposeIndexedQueryStructurePost av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r r' : IndexedQueryStructure qs_schema Index) :=
  DecomposePosti3list _ _ rWrap r r'.

Definition DecomposeIndexedQueryStructurePre av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  DecomposePrei3list _ _ rWrap r.

Arguments DecomposeIndexedQueryStructurePost _ _ _ _ _ _ / .
Arguments DecomposeIndexedQueryStructurePre _ _ _ _ _ / .
