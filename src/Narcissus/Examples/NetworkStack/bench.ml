open Core_bench.Std
open Fiat4Mirage

let () =
  Core.Command.run (Bench.make_command [
    Bench.Test.create ~name:"fiat_ipv4_decode"
      (fun () -> ignore (fiat_ipv4_decode_bench ()));
    Bench.Test.create ~name:"fiat_ipv4_encode"
      (fun () -> ignore (fiat_ipv4_encode_bench ()));
  ])
