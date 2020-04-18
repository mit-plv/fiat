Require Import Coq.Strings.String Coq.Lists.List.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope string_scope.

Fixpoint list_of_string (s : string) : list Ascii.ascii
  := match s with
       | "" => nil
       | String ch s' => ch :: list_of_string s'
     end.

Fixpoint string_of_list (ls : list Ascii.ascii) : string
  := match ls with
       | nil => ""
       | ch :: ls' => String ch (string_of_list ls')
     end.

Fixpoint string_copy (n : nat) (ch : Ascii.ascii)
  := match n with
       | 0 => EmptyString
       | S n' => String.String ch (string_copy n' ch)
     end.
