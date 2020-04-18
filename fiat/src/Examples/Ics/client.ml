let rec nat_of_int = function
  | 0 -> O
  | n -> S (nat_of_int (n - 1))

let num n = Z.of_nat (nat_of_int n)

module DetInterp = struct
  let state = ref (num 0)

  let init n = state := Det.coq_new (num n)
  let update n =
    let Pair (state', Tt) = Det.update !state (num n) in
    state := state'
  let timestep n =
    let Pair (state', act) = Det.timestep !state (num n) in
    state := state';
    act
end

type req = {targetLevel : int;
            fillRate : int;
            emptyRate : int}

module NondetInterp = struct
  let state = ref { Coq_N.coq_Min = num 0; Coq_N.coq_Max = num 0 }

  let init n = state := Nondet.coq_new (num n)
  let update n =
    let Pair (state', Tt) = Nondet.update !state (num n) in
    state := state'
  let timestep r =
    let Pair (state', act) = Nondet.timestep !state
        {Coq_N.coq_TargetLevel = num r.targetLevel;
         Coq_N.coq_FillRate = num r.fillRate;
         Coq_N.coq_EmptyRate = num r.emptyRate} in
    state := state';
    act
end
