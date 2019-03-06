Require Export Coq.extraction.ExtrOcamlIntConv.

Require Import Coq.ZArith.BinInt.

Require Import Coq.Strings.String.

Module Import Ocaml.
  Module Ocaml.
    Parameter Ocaml_array : Type -> Type.
    Notation array := Ocaml_array.
    Parameter string : Set.
    Parameter sequence : forall {A B}, A -> B -> B.
    Parameter explode : string -> String.string.
    Parameter implode : String.string -> string.
    Parameter float : Set.
    Bind Scope ocaml_float_scope with Ocaml.float.
    Parameter add_float : float -> float -> float.
    Parameter sub_float : float -> float -> float.
    Parameter mult_float : float -> float -> float.
    Parameter div_float : float -> float -> float.
    Parameter power : float -> float -> float.
    Parameter le_float : float -> float -> bool.
  End Ocaml.

  Delimit Scope ocaml_float_scope with ocaml_float.
  Infix "+" := Ocaml.add_float : ocaml_float_scope.
  Infix "-" := Ocaml.sub_float : ocaml_float_scope.
  Infix "*" := Ocaml.mult_float : ocaml_float_scope.
  Infix "**" := Ocaml.power (at level 30) : ocaml_float_scope.
  Infix "/" := Ocaml.div_float : ocaml_float_scope.
  Infix "<=" := Ocaml.le_float : ocaml_float_scope.

  Module Array.
    Parameter length : forall {a}, Ocaml.array a -> int.
    Parameter get : forall {a}, Ocaml.array a -> nat -> a.
  End Array.

  Module List.
    Parameter sort : forall {a}, (a -> a -> int) -> list a -> list a.
  End List.

  Module Sys.
    Parameter argv : Ocaml.array Ocaml.string.
    Parameter time : unit -> Ocaml.float.
  End Sys.

  Module Pervasives.
    Parameter in_channel : Set.
    Parameter out_channel : Set.
    Parameter open_in : Ocaml.string -> in_channel.
    Parameter close_in : in_channel -> unit.
    Parameter stdin : in_channel.
    Parameter stdout : out_channel.
    Parameter stderr : out_channel.
    Parameter at_exit : (unit -> unit) -> unit.
    Parameter exit : forall {T}, int -> T.
    Parameter input_line : in_channel -> Ocaml.string.
    Parameter float_of_nat : nat -> Ocaml.float.
    Parameter float_of_int : int -> Ocaml.float.
    Parameter compare : forall {a}, a -> a -> int.
  End Pervasives.

  Global Coercion Pervasives.float_of_nat : nat >-> Ocaml.float.
  Global Coercion Pervasives.float_of_int : int >-> Ocaml.float.

  Module String.
    Parameter length : Ocaml.string -> nat.
    Parameter get : Ocaml.string -> nat -> Ascii.ascii.
    Parameter sub : Ocaml.string -> nat -> nat -> Ocaml.string.
    Parameter safe_get : Ocaml.string -> nat -> option Ascii.ascii.
    Parameter compare : Ocaml.string -> Ocaml.string -> int.
  End String.

  (*Parameter explode : Ocaml.string -> String.string.
(*    := fun s =>
         (fix exp (i : nat) (l : String.string) :=
            let l' := String.String (Ocaml_String.get s i) l in
            match i with
              | 0 => l'
              | S i' => exp i' l'
            end)
           (Ocaml_String.length s)
           ""%string.*)
  Parameter implode : String.string -> Ocaml.string.*)
End Ocaml.

Module ExtrOcaml.
  Extract Constant Ocaml.Ocaml_array "'a" => "'a array".
  Extract Inlined Constant Ocaml.sequence => "(fun x y -> x; y)".
  Extract Inlined Constant Ocaml.string => "string".
  Extract Inlined Constant Ocaml.float => "float".
  Extract Inlined Constant Ocaml.add_float => "(+.)".
  Extract Inlined Constant Ocaml.sub_float => "(-.)".
  Extract Inlined Constant Ocaml.mult_float => "( *. )".
  Extract Inlined Constant Ocaml.div_float => "(/.)".
  Extract Inlined Constant Ocaml.sub_float => "(-.)".
  Extract Inlined Constant Ocaml.power => "( **. )".
  Extract Inlined Constant Ocaml.le_float => "(<=.)".
  Extract Inlined Constant Array.get => "Array.get".
  Extract Inlined Constant Array.length => "Array.length".
  Extract Inlined Constant Sys.argv => "Sys.argv".
  Extract Inlined Constant Sys.time => "Sys.time".
  Extract Inlined Constant List.sort => "List.sort".
  Extract Inlined Constant String.length => "String.length".
  Extract Inlined Constant String.get => "String.get".
  Extract Inlined Constant String.sub => "String.sub".
  Extract Constant String.safe_get => "(fun s n -> try Some (String.get s n) with | Invalid_argument _ -> None)".
  Extract Inlined Constant String.compare => "String.compare".
  Extract Inlined Constant Pervasives.in_channel => "Pervasives.in_channel".
  Extract Inlined Constant Pervasives.out_channel => "Pervasives.out_channel".
  Extract Inlined Constant Pervasives.open_in => "Pervasives.open_in".
  Extract Inlined Constant Pervasives.close_in => "Pervasives.close_in".
  Extract Inlined Constant Pervasives.stdin => "Pervasives.stdin".
  Extract Inlined Constant Pervasives.stdout => "Pervasives.stdout".
  Extract Inlined Constant Pervasives.stderr => "Pervasives.stderr".
  Extract Inlined Constant Pervasives.at_exit => "Pervasives.at_exit".
  Extract Inlined Constant Pervasives.exit => "Pervasives.exit".
  Extract Inlined Constant Pervasives.input_line => "Pervasives.input_line".
  Extract Inlined Constant Pervasives.float_of_nat => "Pervasives.float_of_int".
  Extract Inlined Constant Pervasives.float_of_int => "Pervasives.float_of_int".
  Extract Inlined Constant Pervasives.compare => "Pervasives.compare".
  (* http://caml.inria.fr/pub/old_caml_site/FAQ/FAQ_EXPERT-eng.html#strings *)
  Extract Constant Ocaml.explode =>
  "(fun s ->
      let rec exp i l =
        if i < 0 then l else exp (i - 1) (s.[i] :: l) in
      exp (String.length s - 1) [])".
  Extract Constant Ocaml.implode =>
  "(fun l ->
      let res = String.create (List.length l) in
      let rec imp i = function
      | [] -> res
      | c :: l -> res.[i] <- c; imp (i + 1) l in
      imp 0 l)".
End ExtrOcaml.

Module Export OcamlProperties.
  Create HintDb ocaml discriminated.

  Module Import StringProperties.
    Axiom explode_implode : forall s, Ocaml.explode (Ocaml.implode s) = s.
    Axiom implode_explode : forall s, Ocaml.implode (Ocaml.explode s) = s.
    Axiom length_correct : forall s, String.length s = Coq.Strings.String.length (Ocaml.explode s).
    Axiom get_correct : forall s n ch, (String.get s n = ch) <-> (Coq.Strings.String.get n (Ocaml.explode s) = Some ch).
    Axiom safe_get_correct : forall s n, String.safe_get s n = Coq.Strings.String.get n (Ocaml.explode s).
    Axiom sub_correct : forall s start len, String.sub s start len = Ocaml.implode (Coq.Strings.String.substring start len (Ocaml.explode s)).
    Axiom compare_eq : forall s s', (z_of_int (String.compare s s') = 0%Z) <-> s = s'.
    Definition compare_eq' s s' (H : s = s')
    : z_of_int (String.compare s s') = 0%Z
      := proj2 (compare_eq s s') H.
  End StringProperties.

  Hint Rewrite explode_implode implode_explode length_correct safe_get_correct sub_correct compare_eq : ocaml.
  Hint Rewrite compare_eq' using reflexivity : ocaml.
End OcamlProperties.
