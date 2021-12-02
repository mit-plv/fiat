Reserved Notation "'Either' t 'Or' e " (at level 100, right associativity).
Reserved Notation "x 'ThenC' y" (at level 100, right associativity).
Reserved Notation "x 'DoneC'"   (at level 99, right associativity).
Reserved Notation "format1 'ThenChecksum' c 'OfSize' sz 'ThenCarryOn' format2"
         (format2 at next level, at level 98, right associativity).
Reserved Notation "| ls |" (at level 200).

Declare Scope format_scope.
Delimit Scope format_scope with format.
