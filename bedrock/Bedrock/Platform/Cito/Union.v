Require Import Bedrock.StringSet.
Import StringSet.

Set Implicit Arguments.

Definition union_list ls := List.fold_right union empty ls.
