(* Invariant:
   word sz has all bits past the sz-th position set to 0
   (i.e. wmask sz w = w) *)

type t = Int64.t

let w0 =
  Int64.zero

let ws (b, _, w') =
  Int64.add (if b then Int64.one else Int64.zero) (Int64.shift_left w' 1)

let destruct _ _ _ =
  failwith "Not implemented: Int64Word.destruct"

let wones sz =
  Int64.sub (Int64.shift_left Int64.one sz) Int64.one

let wmask sz w =
  Int64.logand (wones sz) w

let whd _ w =
  (Int64.logand Int64.one w) = Int64.one

let wtl _ w =
  Int64.shift_right_logical w 1

let wplus _ w w' =
  Int64.add w w'

let wmult _ w w' =
  Int64.mul w w'

let wminus _ w w' =
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

let wneg _ w w' =
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

let split1' sz sz' w =
  Int64.shift_right_logical w sz'

let split2' sz sz' w =
  wmask sz' w

let split1 sz sz' w =
  split2' sz' sz w

let split2 sz sz' w =
  split1' sz' sz w

let sw_word sz b w =
  if b then Int64.logor (Int64.shift_left Int64.one sz) w else w

let combine sz w sz' w' =
  Int64.logor (Int64.shift_left w' sz) w

let append sz sz' w w' =
  Int64.logor (Int64.shift_left w' sz) w
