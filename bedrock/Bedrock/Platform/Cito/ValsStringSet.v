Require Import Bedrock.sep.Locals.
Require Import Bedrock.StringSet.
Import StringSet.

Set Implicit Arguments.

Definition agree_in a b := For_all (fun x => sel a x = sel b x).

Definition agree_except a b s := forall x, sel a x <> sel b x -> In x s.
