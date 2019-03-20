(* Invariant:
   word sz has all bits past the sz-th position set to 0
   (i.e. wmask sz w = w) *)

module Int64 = struct
  type t = int
  let zero = 0
  let one = 1
  let add x y = x + y
  let sub x y = x - y
  let mul x y = x * y
  let div x y = x / y
  let shift_left x y = x lsl y
  let shift_right_logical x y = x lsr y
  let logand x y = x land y
  let logor x y = x lor y
  let lognot x = lnot x
  let to_string x = string_of_int x
  let to_int x = x
  let of_int x = x
  let to_int32 x = Int32.of_int x
  let of_int32 x = Int32.to_int x
end

type t = Int64.t

let w0 =
  Int64.zero

let ws (b, _, w') =
  Int64.add (if b then Int64.one else Int64.zero) (Int64.shift_left w' 1)

let bits w =
  let open Int64 in
  let rec loop i acc =
    if i >= 64 then acc
    else loop (i + 1) ((if logand (shift_left one i) w <> zero then one else zero) :: acc)
  in String.concat "" (List.map Int64.to_string (loop 0 []))

let sane w =
  (Int64.zero <= w) && (w < Int64.shift_left Int64.one 32)

(* let throw_invalid_word fn w =
 *   failwith (Printf.sprintf "Result of %s is too large: %s" fn (Int64.to_string w))
 *
 * let validate fn w =
 *   if sane w then w
 *   else throw_invalid_word fn w *)

let destruct _ _ _ =
  failwith "Not implemented: Int64Word.destruct"

let wones sz =
  Int64.sub (Int64.shift_left Int64.one sz) Int64.one

let wmask sz w =
  Int64.logand (wones sz) w

let of_int w =
  Int64.of_int w

let to_int w =
  Int64.to_int w

let of_char w =
  Int64.of_int (Char.code w)

let to_char w =
  Char.unsafe_chr (Int64.to_int w)

let of_uint16 i16 =
  wmask 16 (Int64.of_int i16)

let of_uint32 i32 =
  wmask 32 (Int64.of_int32 i32)

let to_uint32 i32 =
  Int64.to_int32 i32

let whd _ w =
  (Int64.logand Int64.one w) = Int64.one

let wtl _ w =
  Int64.shift_right_logical w 1

let zext _ w _ =
  w

let wplus _ w w' =
  Int64.add w w'

let wmult _ w w' =
  Int64.mul w w'

let wminus _ _w _w' =
  failwith "Unimplemented: wminus"

let weq _ w w' =
  w = w'

let weqb _ w w' =
  w = w'

let wlt _ w w' =
  w < w'

let wlt_dec _ w w' =
  w < w'

let wand _ w w' =
  Int64.logand w w'

let wor _ w w' =
  Int64.logor w w'

let wnot sz w =
  wmask sz (Int64.lognot w)

let wneg _ _w _w' =
  failwith "Unimplemented: wneg"

let wordToNat _ w =
  Int64.to_int w

let natToWord _ (n: int) =
  Int64.of_int n

let wzero _ =
  Int64.zero

let wzero' _ =
  Int64.zero

let word_split_hd sz w =
  Int64.logand (Int64.shift_left Int64.one (sz - 1)) w <> Int64.zero

let word_split_tl sz w =
  wmask sz w

let split1' _sz sz' w =
  Int64.shift_right_logical w sz'

let split2' _sz sz' w =
  wmask sz' w

let split1 sz sz' w =
  split2' sz' sz w

let split2 sz sz' w =
  split1' sz' sz w

let sw_word sz b w =
  if b then Int64.logor (Int64.shift_left Int64.one sz) w else w

let combine sz w _sz' w' =
  Int64.logor (Int64.shift_left w' sz) w

let append sz _sz' w w' =
  Int64.logor (Int64.shift_left w' sz) w

let onec_plus _ w w' =
  let sum = Int64.add w w' in
  let mask = Int64.of_int 65535 in
  (Int64.add (Int64.logand sum mask)
     (Int64.shift_right_logical sum 16))
