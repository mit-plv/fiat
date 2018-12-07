open Core_bench.Std
open Fiat4Mirage

(*
# -p turns profiling on
# Compile and run with this:
  ocamlfind ocamlopt -p -linkpkg -thread -package core -package core_bench Int64Word.ml ArrayVector.ml OCamlNativeInt.ml Fiat4Mirage.ml bench.ml -o bench
  ./bench -quota 10 -ci-absolute +time


 *)

let buflen = 4096

let array_to_buffer arr = CstructBytestring.cstruct_of_array (Array.map Int64Word.of_int arr)
let version_buffer buf = CstructBytestring.of_cstruct buf
let buf = Cstruct.create buflen

(* module CstructBytestring = ArrayVector
 * let array_to_buffer x = Array.map Int64Word.of_int x
 * let version_buffer buf = ArrayVector.of_array buf
 * let buf = Array.make buflen Int64Word.w0 *)

let must = function Some x -> x | None -> failwith "Unexpected: 'None'"

(* let mk_arrayvect x = ArrayVector.of_array x (* (Array.map Int64Word.of_int64 x) *) *)

(* let ntp_response_udp_decode_56_input = mk_arrayvect [|0L;123L;0L;123L;0L;56L;247L;218L;28L;1L;13L;227L;0L;0L;0L;16L;0L;0L;0L;32L;78L;73L;83L;84L;222L;241L;102L;203L;0L;0L;0L;0L;222L;241L;103L;36L;233L;43L;107L;49L;222L;241L;103L;36L;241L;94L;157L;42L;222L;241L;103L;36L;241L;94L;166L;251L|]
 *
 * let ntp_response_udp_encode_56_input = must (Fiat4Mirage.fiat_udp_decode 56 ntp_response_udp_decode_56_input (mk_arrayvect [|132L;163L;97L;1L|]) (mk_arrayvect [|192L;168L;1L;109L|]) (Int64Word.of_uint 56))
 *
 * let bench () =
 *   Fiat4Mirage.fiat_udp_encode buflen ntp_response_udp_encode_56_input (mk_arrayvect [|132L;163L;97L;1L|]) (mk_arrayvect [|192L;168L;1L;109L|]) (Int64Word.of_uint 56) (ArrayVector.of_array buf) *)

let ntp_request_ether_decode_90_input = CstructBytestring.of_array (Array.map Int64Word.of_int [|80;199;191;62;218;205;72;81;183;14;152;89;8;0;69;0;0;76;42;91;64;0;64;17;104;140;192;168;1;109;132;163;97;1;0;123;0;123;0;56;213;93;227;0;3;250;0;1;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;222;241;103;36;233;43;107;49|])

let ntp_request_ether_encode_90_input = must (Fiat4Mirage.fiat_ethernet_decode 90 ntp_request_ether_decode_90_input 90)

let http_response_tcp_decode_338_input = array_to_buffer [|0;80;144;42;243;111;68;47;19;125;121;60;128;24;0;55;33;1;0;0;1;1;8;10;80;206;41;115;228;110;2;137;72;84;84;80;47;49;46;49;32;51;48;49;32;77;111;118;101;100;32;80;101;114;109;97;110;101;110;116;108;121;13;10;83;101;114;118;101;114;58;32;86;97;114;110;105;115;104;13;10;82;101;116;114;121;45;65;102;116;101;114;58;32;48;13;10;67;111;110;116;101;110;116;45;76;101;110;103;116;104;58;32;48;13;10;76;111;99;97;116;105;111;110;58;32;104;116;116;112;115;58;47;47;119;119;119;46;110;121;116;105;109;101;115;46;99;111;109;47;13;10;65;99;99;101;112;116;45;82;97;110;103;101;115;58;32;98;121;116;101;115;13;10;68;97;116;101;58;32;84;104;117;44;32;49;50;32;74;117;108;32;50;48;49;56;32;48;49;58;52;54;58;49;57;32;71;77;84;13;10;88;45;83;101;114;118;101;100;45;66;121;58;32;99;97;99;104;101;45;98;111;115;56;50;51;48;45;66;79;83;13;10;88;45;67;97;99;104;101;58;32;72;73;84;13;10;88;45;67;97;99;104;101;45;72;105;116;115;58;32;48;13;10;88;45;70;114;97;109;101;45;79;112;116;105;111;110;115;58;32;68;69;78;89;13;10;67;111;110;110;101;99;116;105;111;110;58;32;99;108;111;115;101;13;10;88;45;65;80;73;45;86;101;114;115;105;111;110;58;32;70;45;48;13;10;13;10|]

let ip1, ip2 = array_to_buffer [|151;101;129;164|], array_to_buffer [|192;168;1;109|]

(* let bench_dec () =
 *   (Fiat4Mirage.fiat_tcp_decode 338
 *      (version_buffer http_response_tcp_decode_338_input)
 *      (version_buffer ip1)
 *      (version_buffer ip2)
 *      (Int64Word.of_int 338))
 *
 * let http_response_tcp_encode_338_input =
 *   must (bench_dec ())
 *
 * let bench_enc () =
 *   (Fiat4Mirage.fiat_tcp_encode 4096
 *      http_response_tcp_encode_338_input
 *      (version_buffer ip1)
 *      (version_buffer ip2)
 *      (Int64Word.of_int 338) (version_buffer buf))
 *
 * let _ = must (bench_enc ())
 *
 * let string_of_chars chars =
 *   let buf = Buffer.create 16 in
 *   List.iter (Buffer.add_char buf) chars;
 *   Buffer.contents buf
 *
 * let _ =
 *   let pkt = must (bench_dec ()) in
 *   print_string (string_of_chars (List.map Int64Word.to_char (CstructBytestring.to_list () (projT2 pkt.payload))));
 *   print_newline ()
 *
 * let _ = must (bench_enc ()) *)

(* CPC benchmarks should fail on exceptions *)

(* let repeat (f, n) =
 *   for i = 0 to n - 1 do
 *     ignore (f ())
 *   done
 *
 * let time f x =
 *   let start = Unix.time () in
 *   ignore (f x);
 *   let elapsed = Unix.time () -. start in
 *   Printf.printf "Elapsed: %.4f\n" elapsed
 *
 * let () =
 *   time repeat (bench_enc, 500_000); *)

let () =
  Core.Command.run (Bench.make_command [
    Bench.Test.create ~name:"ntp_request_ether_encode_90"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_encode 4096 ntp_request_ether_encode_90_input (CstructBytestring.of_cstruct buf))));
    Bench.Test.create ~name:"ntp_request_ether_decode_90"
      (fun () -> ignore (must (Fiat4Mirage.fiat_ethernet_decode 90 ntp_request_ether_decode_90_input 90)));
    (* Bench.Test.create ~name:"http_response_tcp_decode_338"
     *   (fun () -> ignore (bench_dec ()));
     * Bench.Test.create ~name:"http_response_tcp_encode_338"
     *   (fun () -> ignore (bench_enc ())) *)
  ])
