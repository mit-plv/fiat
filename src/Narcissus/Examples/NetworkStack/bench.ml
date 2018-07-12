open Core_bench.Std
open Fiat4Mirage

let test () =
  oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))
    (oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))
      (oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))
        (oneC_plus (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))))
           0L
           0L)
        (Int64Word.zext (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))))) 7L (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))))))))) 50L) 0L


let test_nosucc () =
  oneC_plus 16
    (oneC_plus 16
      (oneC_plus 16
        (oneC_plus 16
           0L
           0L)
        (Int64Word.zext 8 7L 8)) 50L) 0L

let () =
  Core.Command.run (Bench.make_command [
    Bench.Test.create ~name:"succ"
      (fun () -> ignore (test ()));
    Bench.Test.create ~name:"nosucc"
      (fun () -> ignore (test_nosucc ()));
    (* Bench.Test.create ~name:"fiat_ipv4_decode"
     *   (fun () -> ignore (fiat_ipv4_decode_bench ()));
     * Bench.Test.create ~name:"fiat_ipv4_encode"
     *   (fun () -> ignore (fiat_ipv4_encode_bench ())); *)
  ])
