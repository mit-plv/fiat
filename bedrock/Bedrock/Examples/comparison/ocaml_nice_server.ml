(** * Parser combinators *)

type 'a parser = int * (int array -> int -> 'a option)

let parse (parser : 'a parser) (arr : int array) (pos : int) : (int * 'a) option =
  if pos + fst parser > Array.length arr then
    None
  else
    match snd parser arr pos with
    | None -> None
    | Some v -> Some (pos + fst parser, v)

let constant n : unit parser = (1, fun arr pos -> if arr.(pos) = n then Some () else None)
let variable : int parser = (1, fun arr pos -> Some arr.(pos))
let (++) (p1 : 'a parser) (p2 : 'b parser) : ('a * 'b) parser = (fst p1 + fst p2, fun arr pos ->
  match snd p1 arr pos with
  | None -> None
  | Some v1 -> match snd p2 arr (pos + fst p1) with
    | None -> None
    | Some v2 -> Some (v1, v2))


(** * Symbolic array querying *)

type exp =
    Index
  | Value
  | Const of int

type test =
    Eq
  | Ne
  | Lt
  | Le

type query =
    Test of exp * test * exp
  | And of query * query
  | Or of query * query
  | Not of query

let evalExp index value e =
  match e with
  | Index -> index
  | Value -> value
  | Const k -> k

let evalTest t =
  match t with
  | Eq -> (=)
  | Ne -> (<>)
  | Lt -> (<)
  | Le -> (<=)

let rec evalQuery index value q =
  match q with
  | Test (e1, t, e2) -> (evalTest t) (evalExp index value e1) (evalExp index value e2)
  | And (q1, q2) -> evalQuery index value q1 && evalQuery index value q2
  | Or (q1, q2) -> evalQuery index value q1 || evalQuery index value q2
  | Not q1 -> not (evalQuery index value q1)

let rec indexEquals q =
  match q with
  | Test (Index, Eq, Const k) -> Some k
  | And (q1, q2) -> begin match indexEquals q1 with
    | None -> indexEquals q2
    | x -> x
  end
  | _ -> None

let rec indexGe q =
  match q with
  | Test (Const k, Le, Index) -> Some k
  | And (q1, q2) -> begin match indexGe q1 with
    | None -> indexGe q2
    | x -> x
  end
  | _ -> None

let fold_lefti f i arr pos =
  let rec fold_lefti' pos acc =
    if pos >= Array.length arr then
      acc
    else
      fold_lefti' (pos+1) (f pos arr.(pos) acc) in
  fold_lefti' pos i
    

let query q f arr acc =
  match indexEquals q with
  | Some k ->
      if k >= Array.length arr then
        acc
      else
        f k arr.(k) acc
  | None ->
      let startPos = match indexGe q with
      | Some k -> k
      | None -> 0 in
      fold_lefti (fun index value acc -> if evalQuery index value q then f index value acc else acc) acc arr startPos


(** * Server *)

let server cmd data =
  let rec loop pos acc =
    match parse (constant 0 ++ variable ++ variable) cmd pos with
    | Some (pos, (((), index), valueLowerBound)) ->
        let acc' = query (And (Test (Index, Eq ,Const index), Test (Const valueLowerBound, Le, Value)))
            (fun _ value acc -> (if value >= valueLowerBound then 1 else 0) :: acc)
            data acc

        in loop pos acc'
    | None ->
        match parse (constant 1 ++ variable ++ variable) cmd pos with
        | Some (pos, (((), lowerBound), upperBound)) ->
            let highest = query (And (Test (Const lowerBound, Le, Value), Test (Value, Le, Const upperBound)))
                (fun _ -> max)
                data 0 in
            
            loop pos (highest :: acc)
        | None ->
            match parse (constant 2 ++ variable ++ variable) cmd pos with
            | Some (pos, (((), indexLowerBound), valueUpperBound)) ->
                let acc' = query (And (Test (Const indexLowerBound, Le, Index), Test (Value, Le, Const valueUpperBound)))
                    (fun _ value acc -> value :: acc)
                    data acc in
                
                loop pos acc'
            | None -> acc in

  loop 0 []
