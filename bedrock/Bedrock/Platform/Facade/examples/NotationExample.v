Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.DFacade.
Require Import Bedrock.Platform.Facade.Notations.
Import Notations.OpenScopes.

Section ADTValue.

  Variable ADTValue : Type.
  Variables ArraySeq_newSpec ArraySeq_writeSpec ArraySeq_readSpec ArraySeq_deleteSpec ListSet_newSpec ListSet_addSpec ListSet_sizeSpec ListSet_deleteSpec : AxiomaticSpec ADTValue.

  Definition count_unique :=
    module
    import {
      "ADT"!"ArraySeq_new" ==> ArraySeq_newSpec;
      "ADT"!"ArraySeq_write" ==> ArraySeq_writeSpec;
      "ADT"!"ArraySeq_read" ==> ArraySeq_readSpec;
      "ADT"!"ArraySeq_delete" ==> ArraySeq_deleteSpec;
      "ADT"!"ListSet_new" ==> ListSet_newSpec;
      "ADT"!"ListSet_add" ==> ListSet_addSpec;
      "ADT"!"ListSet_size" ==> ListSet_sizeSpec;
      "ADT"!"ListSet_delete" ==> ListSet_deleteSpec
    }
    define {
      def "count" = func("arr", "len") {
        "set" <-- call_ "ADT"!"ListSet_new"();
        "i" <- 0;
        while_ ("i" < "len") {
          "e" <-- call_ "ADT"!"ArraySeq_read" ("arr", "i");
          call_ "ADT"!"ListSet_add"("set", "e");
          "i" <- "i" + 1
        };
        "ret" <-- call_ "ADT"!"ListSet_size"("set");
        call_ "ADT"!"ListSet_delete"("set")
      };
      def "main" = func() {
(*
        "arr" <-- call_ "ADT"!"ArraySeq_new"(3);;
        call_ "ADT"!"ArraySeq_write"("arr", 0, 10);;
        call_ "ADT"!"ArraySeq_write"("arr", 1, 20);;
        call_ "ADT"!"ArraySeq_write"("arr", 2, 10);;
        "ret" <-- call_ "count"!"count" ("arr", 3);;
        call_ "ADT"!"ArraySeq_delete"("arr")
*)
        "ret" <- 0
      }
    }.

  Require Import Bedrock.Platform.Facade.CompileDFModule.

  Definition gmodule := compile_to_gmodule count_unique "count_unique" eq_refl.

  (* test executability *)
  Require Import Bedrock.Platform.Cito.GoodModuleDec.
  Require Import Bedrock.Platform.Cito.IsGoodModule.

  Goal is_good_module gmodule = true. Proof. exact eq_refl. Qed.

End ADTValue.
