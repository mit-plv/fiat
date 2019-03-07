(* This is the same as what Coq would do, but extraction of vectors is broken… *)
type 'a t =
  { len: int;
    arr: 'a ArrayVector.storage_t }

let empty () =
  { len = 0;
    arr = ArrayVector.of_array [| |] }

let of_rev_array arr =
  { len = Array.length arr;
    arr = ArrayVector.of_array arr }

let full v =
  v.len = ArrayVector.length v.arr

let dup_push v x =
  (* Printf.printf "Growing from size %d\n" v.len; *)
  let data = Array.make (2 * v.len + 6) x in
  Array.blit v.arr.ArrayVector.data 0 data 0 v.len;
  { len = v.len + 1; arr = ArrayVector.of_array data }

let cons ((hd, _, tl): ('a * 'b * 'a t)) : 'a t =
  if full tl then
    dup_push tl hd
  else
    { len = tl.len + 1;
      arr = ArrayVector.set_nth' tl.arr tl.len hd }

let nth' (v: 'a t) (idx: ArrayVector.idx_t) : 'a =
  ArrayVector.nth' v.arr (v.len - idx - 1)

let nth _ (v: 'a t) (idx: ArrayVector.idx_t) : 'a =
  nth' v idx

let nth_opt' (v: 'a t) (idx: ArrayVector.idx_t) : 'a option =
  if idx < v.len then Some (nth' v idx) else None

let nth_opt _ (v: 'a t) (idx: ArrayVector.idx_t) : 'a option =
  nth_opt' v idx


let index (_: int) (_: int) (x: 'a) (v: 'a t) : ArrayVector.idx_t option =
  match ArrayVector.index' x v.arr.ArrayVector.data 0 v.len with
  | Some idx -> Some (v.len - idx - 1)
  | None -> None
