type bparams = {
    nb_open_connections: int
  }

type bytes = (int, CstructBytestring.storage_t) Tcpfilter.sigT

type bdata = {
    packets: bytes list
  }

let _ =
  Random.init 0

let random_ui32 () =
  Int64.to_int (Random.int64 4294967295L)

let random_ui16 () =
  Int64.to_int (Random.int64 65535L)

let random_packet () =
  let Some bs =
    Tcpfilter.make_tcp_syn_packet
      (random_ui32 ())
      (random_ui32 ())
      (random_ui16 ())
      (random_ui16 ()) in
  bs

let generate_benchmark_data bparams =
  let rec loop n acc =
    if n = 0 then acc
    else loop (pred n) (random_packet () :: acc) in
  { packets = loop bparams.nb_open_connections [] }

let prepare_db bdata db =
  List.fold_left (fun db pkt ->
      fst (Tcpfilter.guard_process_packet pkt db))
    db bdata.packets

let bench_pkt = random_packet ()

let corebench_main () =
  let open Core_bench.Std in

  let bparams, argv =
    match Array.to_list Sys.argv with
    | _ :: ("-help" | "--help" | "-h") :: _ ->
       Core.Command.run (Bench.make_command []);
       exit 1
    | exe :: nb_open_connections :: argv ->
       { nb_open_connections = int_of_string nb_open_connections },
       (exe :: argv)
    | _ -> Printf.printf "Usage:
./guard.ml nb_open_connections ...args\n";
           exit 1 in

  let bdata = generate_benchmark_data bparams in
  let init_db = Tcpfilter.guard_init in
  let db = ref init_db in

  Printf.printf "Initializing... %!";
  let base_db = prepare_db bdata init_db in
  Printf.printf "done\n%!";

  let benchmarks = [
      Bench.Test.create ~name:"[guard.ml] Processing one packet" (fun () ->
          db := base_db; Tcpfilter.guard_process_packet bench_pkt !db)
    ] in

  Core.Command.run ~argv (Bench.make_command benchmarks)

let _ =
  corebench_main ()
