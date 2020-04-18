let server cmd data =
  let rec loop pos acc =
    if pos >= Array.length cmd then
      acc
    else match cmd.(pos) with
      0 ->
        let index = cmd.(pos+1) in
        let valueLowerBound = cmd.(pos+2) in
        if index >= Array.length data then
          assert false
        else
          loop (pos+3) ((if data.(index) >= valueLowerBound then 1 else 0) :: acc)
    | 1 ->
        let lowerBound = cmd.(pos+1) in
        let upperBound = cmd.(pos+2) in

        let rec loop' i acc =
          if i >= Array.length data then
            acc
          else if lowerBound <= data.(i) && data.(i) <= upperBound then
            loop' (i+1) (max acc data.(i))
          else
            loop' (i+1) acc in

        loop (pos+3) (loop' 0 0 :: acc)
    | 2 ->
        let indexLowerBound = cmd.(pos+1) in
        let valueUpperBound = cmd.(pos+2) in
        
        let rec loop' i acc =
          if i >= Array.length data then
            acc
          else if data.(i) <= valueUpperBound then
            loop' (i+1) (data.(i) :: acc)
          else
            loop' (i+1) acc in

        loop (pos+3) (loop' indexLowerBound acc)
    | _ -> assert false in

  loop 0 []
