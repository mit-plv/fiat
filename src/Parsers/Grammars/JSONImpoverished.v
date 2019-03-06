(** * Definition of grammar for JSON *)
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

(** Based on https://github.com/antlr/grammars-v4/blob/master/json/JSON.g4 *)

(**
<<
/** Taken from "The Definitive ANTLR 4 Reference" by Terence Parr */

// Derived from http://json.org
grammar JSON;
>> *)

Definition json'_pregrammar : pregrammar Ascii.ascii :=
  Eval grammar_red in
  [[[
       (**
<<
json
   : object
   | array
   ;
>> *)
       "json"
         ::== "object"
         || "array";;
              (**
<<
object
   : '{' pair (',' pair)* '}'
   | '{' '}'
   ;
>> *)
       "object"
         ::== "{" "WS*" "pair WS*" "(',' pair WS*)+" "}"
           || "{" "WS*" "pair WS*" "}"
           || "{" "WS*" "}";;
       "(',' pair WS*)+"
         ::== "," "WS*" "pair WS*"
           || "," "WS*" "pair WS*" "(',' pair WS*)+";;
  (**
<<
pair
   : STRING ':' value
   ;
>> *)
       "pair"
         ::== "STRING" "WS*" ":" "WS*" "value";;
       "pair WS*"
         ::== "STRING" "WS*" ":" "WS*" "value" "WS*";;
  (**
<<
array
   : '[' value (',' value)* ']'
   | '[' ']'
   ;
>> *)
       "array"
         ::== "[" "WS*" "value WS*" "(',' value WS*)+" "]"
           || "[" "WS*" "value WS*" "]"
           || "[" "WS*" "]";;
       "(',' value WS*)+"
         ::== "," "WS*" "value WS*"
           || "," "WS*" "value WS*" "(',' value WS*)+";;
  (**
<<
value
   : STRING
   | NUMBER
   | object
   | array
   | 'true'
   | 'false'
   | 'null'
   ;
>> *)
       "value"
         ::== "STRING"
           || "NUMBER"
           || "object"
           || "array"
           || "'true'"
           || "'false'"
           || "'null'";;
       "value WS*"
         ::== "value" "WS*";;
  (**
<<
STRING
   : '"' (ESC | ~ ["\\])* '"'
   ;
fragment ESC
   : '\\' (["\\/bfnrt] | UNICODE)
   ;
>> *)
       "STRING"
         ::== """" "INNER_STRING" """";;
       "INNER_STRING"
         ::== ""
           || "\" "special_character" "INNER_STRING"
           || "\" "UNICODE" "INNER_STRING"
           || "unspecial_character" "INNER_STRING";;
       "special_character"
         ::== ("""" || "\" || "/" || "b" || "f" || "n" || "r" || "t")%char;;
       "unspecial_character"
       (** We remove characters that we use as binary operations, namely, \s, ":", "{", "}", "[", "]", "," *)
         ::== ¬("""" || "\" || [\s] || ":" || "{" || "}" || "[" || "]" || ",");;
  (**
<<
fragment UNICODE
   : 'u' HEX HEX HEX HEX
   ;
>> *)
      "UNICODE"
        ::== "u" "HEX" "HEX" "HEX" "HEX";;
  (**
<<
fragment HEX
   : [0-9a-fA-F]
   ;
>> *)
     "HEX"
       ::== [0-9a-fA-F];;
  (**
<<
NUMBER
   : '-'? INT '.' [0-9] + EXP? | '-'? INT EXP | '-'? INT
   ;
>> *)
    "NUMBER"
      ::== "-?" "INT" "." "[0-9]+" "EXP?" || "-?" "INT" "EXP" || "-?" "INT";;
    "-?"
      ::== "" || "-";;
    "[0-9]+"
      ::== [0-9] || [0-9] "[0-9]+";;
    "EXP?"
      ::== "" || "EXP";;
  (**
<<
fragment INT
   : '0' | [1-9] [0-9]*
   ;
>> *)
    "INT"
      ::== "0" || [1-9] "[0-9]*";;
    "[0-9]*"
      ::== "" || [0-9] "[0-9]*";;
  (**
<<
// no leading zeros
fragment EXP
   : [Ee] [+\-]? INT
   ;
// \- since - means "range" inside [...]
>> *)
    "EXP"
      ::== ("E" || "e")%production "INT"
        || ("E" || "e")%production ("+" || "-")%production "INT";;
  (**
<<
WS
   : [ \t\n\r] + -> skip
   ;
>> *)
    "WS*"
      ::== "" || [\s] "WS*"

  ]]]%grammar.

Definition json'_grammar : grammar ascii := json'_pregrammar.
