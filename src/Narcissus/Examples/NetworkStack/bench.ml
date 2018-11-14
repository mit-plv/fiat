open Core_bench.Std
open Fiat4Mirage

(*
# -p turns profiling on
# Compile and run with this:
  ocamlfind ocamlopt -p -linkpkg -thread -package core -package core_bench Int64Word.ml ArrayVector.ml OCamlNativeInt.ml Fiat4Mirage.ml bench.ml -o bench
  ./bench -quota 10 -ci-absolute +time


 *)

module CstructBytestring = ArrayVector

let buflen = 4096
let buf = Array.make buflen Int64Word.w0
let must = function Some x -> x | None -> failwith "Unexpected: 'None'"

let mk_arrayvect x = ArrayVector.of_array x (* (Array.map Int64Word.of_int64 x) *)

(* let ntp_response_udp_decode_56_input = mk_arrayvect [|0L;123L;0L;123L;0L;56L;247L;218L;28L;1L;13L;227L;0L;0L;0L;16L;0L;0L;0L;32L;78L;73L;83L;84L;222L;241L;102L;203L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L;222L;241L;103L;36L;241L;94L;157L;42L;222L;241L;103L;36L;241L;94L;166L;251L|]
 *
 * let ntp_response_udp_encode_56_input = must (Fiat4Mirage.fiat_udp_decode 56 ntp_response_udp_decode_56_input (mk_arrayvect [|132L;163L;97L;1L|]) (mk_arrayvect [|192L;168L;1L;109L|]) (Int64Word.of_uint 56))
 *
 * let bench () =
 *   Fiat4Mirage.fiat_udp_encode buflen ntp_response_udp_encode_56_input (mk_arrayvect [|132L;163L;97L;1L|]) (mk_arrayvect [|192L;168L;1L;109L|]) (Int64Word.of_uint 56) (ArrayVector.of_array buf) *)

let http_response_tcp_decode_338_input = CstructBytestring.of_array [|0L;80L;144L;42L;243L;111L;68L;47L;19L;125L;121L;60L;128L;24L;0L;55L;33L;1L;0L;0L;1L;1L;8L;10L;80L;206L;41L;115L;228L;110L;2L;137L;72L;84L;84L;80L;47L;49L;46L;49L;32L;51L;48L;49L;32L;77L;111L;118L;101L;100L;32L;80L;101L;114L;109L;97L;110L;101L;110L;116L;108L;121L;13L;10L;83L;101L;114L;118L;101L;114L;58L;32L;86L;97L;114L;110L;105L;115L;104L;13L;10L;82L;101L;116L;114L;121L;45L;65L;102L;116L;101L;114L;58L;32L;48L;13L;10L;67L;111L;110L;116L;101L;110L;116L;45L;76L;101L;110L;103L;116L;104L;58L;32L;48L;13L;10L;76L;111L;99L;97L;116L;105L;111L;110L;58L;32L;104L;116L;116L;112L;115L;58L;47L;47L;119L;119L;119L;46L;110L;121L;116L;105L;109L;101L;115L;46L;99L;111L;109L;47L;13L;10L;65L;99L;99L;101L;112L;116L;45L;82L;97L;110L;103L;101L;115L;58L;32L;98L;121L;116L;101L;115L;13L;10L;68L;97L;116L;101L;58L;32L;84L;104L;117L;44L;32L;49L;50L;32L;74L;117L;108L;32L;50L;48L;49L;56L;32L;48L;49L;58L;52L;54L;58L;49L;57L;32L;71L;77L;84L;13L;10L;88L;45L;83L;101L;114L;118L;101L;100L;45L;66L;121L;58L;32L;99L;97L;99L;104L;101L;45L;98L;111L;115L;56L;50L;51L;48L;45L;66L;79L;83L;13L;10L;88L;45L;67L;97L;99L;104L;101L;58L;32L;72L;73L;84L;13L;10L;88L;45L;67L;97L;99L;104L;101L;45L;72L;105L;116L;115L;58L;32L;48L;13L;10L;88L;45L;70L;114L;97L;109L;101L;45L;79L;112L;116L;105L;111L;110L;115L;58L;32L;68L;69L;78L;89L;13L;10L;67L;111L;110L;110L;101L;99L;116L;105L;111L;110L;58L;32L;99L;108L;111L;115L;101L;13L;10L;88L;45L;65L;80L;73L;45L;86L;101L;114L;115L;105L;111L;110L;58L;32L;70L;45L;48L;13L;10L;13L;10L|]

let http_response_tcp_encode_338_input = must (Fiat4Mirage.fiat_tcp_decode 338 http_response_tcp_decode_338_input (CstructBytestring.of_array [|151L;101L;129L;164L|]) (CstructBytestring.of_array [|192L;168L;1L;109L|]) (338L))

let bench_dec () =
  (Fiat4Mirage.fiat_tcp_decode 338 http_response_tcp_decode_338_input (CstructBytestring.of_array [|151L;101L;129L;164L|]) (CstructBytestring.of_array [|192L;168L;1L;109L|]) (338L))

let bench_enc () =
  (Fiat4Mirage.fiat_tcp_encode 4096 http_response_tcp_encode_338_input (CstructBytestring.of_array [|151L;101L;129L;164L|]) (CstructBytestring.of_array [|192L;168L;1L;109L|]) (338L) (CstructBytestring.of_array buf))

let string_of_chars chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let _ =
  let pkt = must (bench_dec ()) in
  print_string (string_of_chars (List.map Int64Word.to_char pkt.payload));
  print_newline ()

let _ = must (bench_enc ())

(* FIXME benchmarks should fail on exceptions *)

let () =
  Core.Command.run (Bench.make_command [
    (* Bench.Test.create ~name:"ntp_response_udp_encode_56" *)
    Bench.Test.create ~name:"http_response_tcp_decode_338"
      (fun () -> ignore (bench_dec ()));
    Bench.Test.create ~name:"http_response_tcp_encode_338"
      (fun () -> ignore (bench_enc ()))
  ])
