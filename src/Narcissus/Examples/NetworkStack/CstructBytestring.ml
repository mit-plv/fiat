type idx_t = int
type data_t = Int64Word.t

let zero _ = 0
let succ (_, n) = Pervasives.succ n

type storage_t =
  { version: int;
    data: Cstruct.t;
    latest_version: int ref }

let of_cstruct (buf: Cstruct.t) : storage_t =
  { version = 0;
    data = buf;
    latest_version = ref 0 }

let to_cstruct (arr: storage_t) : Cstruct.t =
  arr.data

let throw_if_stale (fn: string) (arr: storage_t) =
  if arr.version <> !(arr.latest_version) then
    failwith (Printf.sprintf "CstructBytestring: Array version mismatch in '%s': %d != %d."
                fn arr.version !(arr.latest_version))

let create n =
  of_cstruct (Cstruct.create n)

let length (arr: storage_t) =
  Cstruct.len arr.data

let incr_version arr data =
  let version = Pervasives.succ !(arr.latest_version) in
  arr.latest_version := version;
  { version = version;
    latest_version = arr.latest_version;
    data = data }

let unsafe_getchar (buf: Cstruct.t) (idx: idx_t) =
  let open Cstruct in
  Bigarray.Array1.unsafe_get buf.buffer (buf.off + idx)

let unsafe_getdata (buf: Cstruct.t) (idx: idx_t) =
  Int64Word.of_char (unsafe_getchar buf idx)

let hd (_: int) (arr: storage_t) : Int64Word.t =
  throw_if_stale "hd" arr;
  unsafe_getdata arr.data 0

let sub arr off0 len =
  throw_if_stale "sub" arr; (* No version increment on slicing *)
  { arr with data = Cstruct.sub arr.data off0 len }

let tl (_: int) (arr: storage_t) : storage_t =
  throw_if_stale "tl" arr;
  sub arr 1 (length arr - 1)

let index (_: int) (_: int) (x: data_t) (arr: storage_t) : idx_t option =
  throw_if_stale "index" arr;
  let rec loop x buf i =
    if i >= Cstruct.len buf then None
    else if unsafe_getchar buf i = x then Some i
    else loop x buf (i + 1)
  in loop (Int64Word.to_char x) arr.data 0

let nth _ (arr: storage_t) (idx: idx_t) : data_t =
  throw_if_stale "nth" arr;
  unsafe_getdata arr.data idx

let nth_opt _ (arr: storage_t) (idx: idx_t) : 'a option =
  throw_if_stale "nth_opt" arr;
  if idx < length arr then
    Some (unsafe_getdata arr.data idx)
  else None

let unsafe_setchar (buf: Cstruct.t) (idx: idx_t) (x: char) : unit =
  let open Cstruct in
  Bigarray.Array1.unsafe_set buf.buffer (buf.off + idx) x

let unsafe_setdata (buf: Cstruct.t) (idx: idx_t) (x: data_t) : unit =
  unsafe_setchar buf idx (Int64Word.to_char x)

let set_nth _ (arr: storage_t) (idx: idx_t) (x: 'a) : storage_t =
  throw_if_stale "set_nth" arr;
  unsafe_setdata arr.data idx x;
  incr_version arr arr.data

(* let fold_left16 (f: 'a -> 'b -> 'b) _ n (arr: storage_t) (init: 'b) =
 *   (\* Printf.printf "Looping up to (min %d %d)\n%!" n (Array.length arr.data); *\)
 *   let rec loop f arr acc lastidx offset =
 *     if offset < lastidx then
 *       let acc = f (Int64Word.of_uint16 (Cstruct.BE.get_uint16 arr.data offset)) acc in
 *       loop f arr acc lastidx (offset + 2)
 *     else if offset = lastidx then
 *       f (Int64Word.combine 8 (Int64Word.wzero 16) 8 (unsafe_getdata arr.data offset)) acc
 *     else
 *       acc
 *   in loop f arr init (min n (length arr) - 1) 0 *)

let checksum_bound n _ (arr: storage_t) =
  (* fold_left16 (fun w acc -> Int64Word.onec_plus () w acc) () n arr (Int64Word.wzero 16) *)
  let rec loop arr acc lastidx offset =
    if offset < lastidx then
      let acc = Int64Word.onec_plus ()
                  (Int64Word.of_uint16 (Cstruct.BE.get_uint16 arr.data offset)) acc in
      loop arr acc lastidx (offset + 2)
    else if offset = lastidx then
      Int64Word.onec_plus ()
        (Int64Word.combine 8 (Int64Word.wzero 16) 8 (unsafe_getdata arr.data offset)) acc
    else
      acc
  in loop arr (Int64Word.wzero 16) (min n (length arr) - 1) 0

let slice_range _ (from: int) (len: int) (arr: storage_t) =
  sub arr from len

(* CPC why <=? *)
let blit_buffer _ _ start src dst =
  throw_if_stale "blit_buffer" src;
  throw_if_stale "blit_buffer" dst;
  let len = length src in
  let idx' = start + len in
  if idx' <= length dst then (
    Cstruct.blit src.data 0 dst.data start len;
    Some (incr_version dst dst.data, idx')
  ) else None

let append _ _ (arr1: storage_t) (arr2: storage_t) : storage_t =
  throw_if_stale "append" arr1;
  throw_if_stale "append" arr2;
  of_cstruct (Cstruct.append arr1.data arr2.data)

let to_list _ (arr: storage_t) : data_t list =
  throw_if_stale "to_list" arr;
  let ls = ref [] in
  for idx = length arr - 1 downto 0 do
    ls := unsafe_getdata arr.data idx :: !ls
  done;
  !ls

let cstruct_of_array (v: data_t array): Cstruct.t =
  let cs = Cstruct.create (Array.length v) in
  for idx = 0 to Array.length v - 1 do
    unsafe_setdata cs idx (Array.unsafe_get v idx)
  done;
  cs

let of_array (v: data_t array) : storage_t =
  of_cstruct (cstruct_of_array v)

let of_vector _ (v: data_t ArrayVector.storage_t) : storage_t =
  of_array (ArrayVector.to_array v)

let to_vector _ (arr: storage_t) : data_t ArrayVector.storage_t =
  throw_if_stale "to_vector" arr;
  let v = Array.make (length arr) Int64Word.w0 in
  for idx = 0 to length arr - 1 do
    Array.unsafe_set v idx (unsafe_getdata arr.data idx)
  done;
  ArrayVector.of_array v

let cons ((hd, _, tl): ('a * 'b * storage_t)) : storage_t =
  throw_if_stale "cons" tl;
  let hdbuf = Cstruct.create 1 in
  unsafe_setdata hdbuf 0 hd;
  of_cstruct (Cstruct.append hdbuf tl.data)

let empty () : storage_t =
  of_cstruct Cstruct.empty
