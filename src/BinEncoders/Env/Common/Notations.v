Reserved Notation "'Either' t 'Or' e " (at level 100, right associativity).
Reserved Notation "x 'ThenC' y" (at level 100, right associativity).
Reserved Notation "x 'DoneC'"   (at level 99, right associativity).
Reserved Notation "encode1 'ThenChecksum' c 'OfSize' sz 'ThenCarryOn' encode2"
         (encode2 at next level, at level 98, right associativity).
Reserved Notation "| ls |" (at level 200).

Delimit Scope binencoders_scope with bencode.
