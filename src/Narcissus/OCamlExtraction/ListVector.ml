type 'a t = ('a * int) list
let empty () = []
let cons (hd, n, tl) = (hd, n) :: tl
let destruct fNil fCons = function
  | [] -> fNil ()
  | (h, n) :: t -> fCons h n t
let nth _ ls idx = fst (List.nth ls idx)
let nth_opt _ ls idx = try Some (fst (List.nth ls idx)) with Not_found -> None
let rec ith_loop ils idx =
  if idx = 0 then
    fst (Obj.magic ils)
  else
    ith_loop (snd (Obj.magic ils)) (pred idx)
let ith _m _As ils idx =
    ith_loop ils idx
let ith2 _m _As ils idx =
    ith_loop ils idx
