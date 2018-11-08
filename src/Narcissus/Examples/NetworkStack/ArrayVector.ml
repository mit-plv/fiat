type idx_t = int

let zero _ = 0
let succ (_, n) = Pervasives.succ n

type 'a storage_t =
  { version: int;
    data: 'a array;
    latest_version: int ref }

let of_array (arr: 'a array) : 'a storage_t =
  { version = 0;
    data = arr;
    latest_version = ref 0 }

let to_array (arr: 'a storage_t) : 'a array =
  arr.data

let destruct_idx _ _ _ =
  failwith "Not implemented: ArrayVector.destruct_idx"

let destruct_storage _ _ _ =
  failwith "Not implemented: ArrayVector.destruct_storage"

let throw_if_stale (fn: string) (arr: 'a storage_t) =
  if arr.version <> !(arr.latest_version) then
    failwith (Printf.sprintf "ArrayVector: Array version mismatch in '%s': %d != %d."
                fn arr.version !(arr.latest_version))

let length (arr: 'a storage_t) =
  Array.length arr.data

let hd (_: int) (arr: 'a storage_t) : 'a =
  throw_if_stale "hd" arr;
  Array.unsafe_get arr.data 0

let tl (_: int) (arr: 'a storage_t) : 'a storage_t =
  throw_if_stale "tl" arr;
  of_array (Array.init (Array.length arr.data - 1) (fun i -> arr.data.(i + 1)))

let index (_: int) (_: int) (x: 'a) (arr: 'a storage_t) : idx_t option =
  throw_if_stale "index" arr;
  let rec loop x arr i =
    if i >= Array.length arr then None
    else if arr.(i) = x then Some i
    else loop x arr (i + 1)
  in loop x arr.data 0

let nth _ (arr: 'a storage_t) (idx: idx_t) : 'a =
  throw_if_stale "nth" arr;
  Array.unsafe_get arr.data idx

let nth_opt _ (arr: 'a storage_t) (idx: idx_t) : 'a option =
  throw_if_stale "nth_opt" arr;
  if idx < Array.length arr.data then
    Some (Array.unsafe_get arr.data idx)
  else None

let incr_version arr =
  let version = Pervasives.succ !(arr.latest_version) in
  arr.latest_version := version;
  { version = version;
    latest_version = arr.latest_version;
    data = arr.data }

let set_nth _ (arr: 'a storage_t) (idx: idx_t) (x: 'a) : 'a storage_t =
  throw_if_stale "set_nth" arr;
  Array.unsafe_set arr.data idx x;
  incr_version arr

let fold_left_pair (f: 'a -> 'a -> 'b -> 'a) _ n (arr: 'a storage_t) (init: 'b) (pad: 'a) =
  (* Printf.printf "Looping up to (min %d %d)\n%!" n (Array.length arr.data); *)
  let rec loop f arr acc pad len offset =
    if offset >= len then
      acc
    else if offset = len - 1  then
      f (arr.data.(offset)) pad acc
    else
      let acc = f (Array.unsafe_get arr.data offset)
                  (Array.unsafe_get arr.data (offset + 1))
                  acc in
      loop f arr acc pad len (offset + 2)
  in loop f arr init pad (min n (Array.length arr.data)) 0

let list_of_range _ (from: int) (len: int) (arr: 'a storage_t) =
  throw_if_stale "list_of_range" arr;
  let rec loop from idx data acc =
    if idx < from then
      acc
    else
      loop from (idx - 1) data (Array.unsafe_get data idx :: acc)
  in loop from (min (from + len) (length arr) - 1) arr.data []

let rec blit_list_unsafe start list data =
  match list with
  | [] -> data
  | h :: t ->
     Array.unsafe_set data start h;
     blit_list_unsafe (start + 1) t data

let blit_list _ start list arr =
  throw_if_stale "list_of_range" arr;
  let len = List.length list in
  if (start + len) <= length arr then
    let data' = blit_list_unsafe start list arr.data in
    Some (incr_version { arr with data = data' }, len)
  else None

let append _ _ (arr1: 'a storage_t) (arr2: 'a storage_t) : 'a storage_t =
  throw_if_stale "append" arr1;
  throw_if_stale "append" arr2;
  of_array (Array.append arr1.data arr2.data)

let to_list _ (arr: 'a storage_t) =
  throw_if_stale "to_list" arr;
  Array.to_list arr.data

let cons ((hd, _, tl): ('a * 'b * 'a storage_t)) : 'a storage_t =
  throw_if_stale "cons" tl;
  of_array (Array.append (Array.make 1 hd) tl.data)

let empty () : 'a storage_t =
  of_array [| |]
