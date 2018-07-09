Printexc.record_backtrace true;;

#thread;;
#require "core.top";;
#require "async";;
#require "core_bench";;

#load "ArrayVector.cmo";;
#load "Int64Word.cmo";;
#load "OcamlNativeInt.cmo";;
#use "Fiat4Mirage.ml";;

(* open Core.Std;;
 * open Core_bench.Std;;
 *
 * let () =
 *   Command.run (Bench.make_command [
 *     Bench.Test.create ~name:"id"
 *       (fun () -> ());
 *     Bench.Test.create ~name:"fiat_ipv4_decode"
 *       (fun () -> ignore (fiat_ipv4_decode (Array.length bin_pkt) bin_pkt));
 *   ]);; *)
