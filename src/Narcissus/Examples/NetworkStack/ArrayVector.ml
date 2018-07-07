type idx_t = int

let zero _ = 0
let succ (_, n) = Pervasives.succ n

type 'a storage_t =
  { version: int;
    data: 'a array;
    latest_version: int ref }

let destruct _ _ _ =
  failwith "Not implemented: ArrayVector.destruct"

let throw_if_stale (fn: string) (arr: 'a storage_t) =
  if arr.version <> 0 then
    failwith (Printf.sprintf "Unexpected version in %s: %d" fn arr.version);
  if !(arr.latest_version) <> 0 then
    failwith (Printf.sprintf "Unexpected version in %s: %d" fn !(arr.latest_version));
  if arr.version <> !(arr.latest_version) then
    failwith (Printf.sprintf "ArrayVector: Array version mismatch in '%s': %d != %d."
                fn arr.version !(arr.latest_version))

let index (_: int) (_: int) (x: 'a) (arr: 'a storage_t) : idx_t option =
  throw_if_stale "index" arr;
  let rec loop x arr i =
    if i >= Array.length arr then None
    else if arr.(i) = x then Some i
    else loop x arr (i + 1)
  in loop x arr.data 0

let nth_opt _ (arr: 'a storage_t) (idx: idx_t) : 'a option =
  throw_if_stale "nth_opt" arr;
  if 0 <= idx && idx < Array.length arr.data then
    Some (Array.unsafe_get arr.data idx)
  else None

let cons ((hd, _, tl): ('a * 'b * 'a storage_t)) : 'a storage_t =
  throw_if_stale "cons" tl;
  { version = 0;
    latest_version = ref 0;
    data = Array.append (Array.make 1 hd) tl.data }

let empty () : 'a storage_t =
  { version = 0;
    latest_version = ref 0;
    data = Array.init 0 (fun x -> failwith "never called") }
