open Classifier_unopt;;
open Str;;

(* Gc.set { (Gc.get ()) with Gc.verbose = 0x01 };; *)
(*  Gc.tune ~minor_heap_size:(262144 * 2) () ;; *)

let extract (Some x) = x;;
let now () = int_of_float (Unix.time ());;

let kwd_matcher = regexp "\\([^\" ]+\\)\\|\"\\([^\"]+\\)\"";;

let rec extract_group haystack groups =
  match groups with
  | [] -> raise Not_found
  | group :: more ->
    try
      matched_group group haystack
    with Not_found ->
      extract_group haystack more;;

let read_keyword haystack offset =
  let _ = search_forward kwd_matcher haystack offset in
  let matched_text = extract_group haystack [1; 2] in
  (matched_text, match_end ())
;;

let read_arguments command nb_arguments haystack offset =
  let rec aux nb_arguments haystack offset =
    if nb_arguments = 0 then []
    else
      let word, next_offset = read_keyword haystack offset in
      word :: aux (pred nb_arguments) haystack next_offset
  in try
       aux nb_arguments haystack offset
    with Not_found -> (
      Printf.printf "Invalid input: command %s expects %d arguments!\n" command nb_arguments;
      raise Not_found
    );;

let run query store =
  let store', output = query in
  store := store';
  output;;

let print_success success truepart falsepart =
  if success then
    print_string truepart
  else
    print_string falsepart
;;

let toCharList str =
  let rec aux acc pos =
    if pos < 0 then acc
    else aux (str.[pos] :: acc) (pos - 1) in
  aux [] (String.length str - 1);;

let toString chars =
  let buffer = String.create (List.length chars) in
  let _ = List.fold_left (fun pos char -> buffer.[pos] <- char; succ pos) 0 chars in
  buffer;;

let random_string length =
  let buffer = String.create length in
  for pos = 0 to length - 1 do
    buffer.[pos] <- Char.chr (Random.int 256)
  done;
  buffer;;

let stats start_time iterations =
  let elapsed_time_s = Unix.gettimeofday () -. start_time in
  let elapsed_time_ms = 1000.0 *. elapsed_time_s in
  Printf.printf "  %d transactions completed in %.2f ms.\n" iterations elapsed_time_ms;
  Printf.printf "  %.2f TPS.\n" (float_of_int iterations /. elapsed_time_s);
  flush stdout;
  (elapsed_time_ms /. float_of_int iterations)
;;

let gc () =
  Gc.compact ();;

let benchmark nb_rules nb_classify_queries msg_db  =
  Printf.printf "Initialization\n";
  msg_db        := initClassifier;
  let priorities    = Random.init 1; Array.init nb_rules (fun _ -> Random.int 100) in
  let destinations  = Random.init 2; Array.init nb_rules (fun _ ->
  match (Random.int 4) with
  | 0 -> [Random.int 255];
  | 1 -> [Random.int 255; Random.int 255];
  | 2 -> [Random.int 255; Random.int 255; Random.int 255];
  | 3 -> [Random.int 255; Random.int 255; Random.int 255; Random.int 255] ) in
  let protocols = Random.init 6; Array.init nb_rules (fun _ ->
  match (Random.int 3) with
  | 0 -> Wildcard;
  | 1 -> Enforce Tcp;
  | 2 -> Enforce Udp) in
  let actions  = Random.init 7; Array.init nb_rules (fun _ -> Random.bool ()) in
  let rel_query_dest  = Random.init 7; Array.init nb_classify_queries (fun _ -> destinations.(Random.int nb_rules)) in
  let rel_query_proto  = Random.init 8; Array.init nb_classify_queries (fun _ ->
match (Random.int 2) with
  | 0 -> Tcp;
  | 1 -> Udp) in
  gc ();

  Printf.printf "Adding contacts...\n";
  let contacts_start = Unix.gettimeofday () in
  for iteration = 0 to nb_rules - 1 do
  let _ = run (addRule priorities.(iteration) destinations.(iteration) protocols.(iteration) actions.(iteration)!msg_db) msg_db in ()
  done;
  let contacts_duration = stats contacts_start nb_rules in

  gc ();

  Printf.printf "Querying Rules\n";
  let contact_queries_start = Unix.gettimeofday () in
  for iteration = 0 to nb_classify_queries - 1 do
    let _ = run (classify rel_query_dest.(iteration) rel_query_proto.(iteration)!msg_db) msg_db in ()
    (* List.iter (fun x -> Printf.printf "%s\n" (toString x)) a *)
  done;
  let rel_classify_duration = stats contacts_start nb_classify_queries in
  gc ();

  Printf.fprintf stderr "%d\t%d\t%.6f\t%.6f\n"
    nb_rules nb_classify_queries contacts_duration rel_classify_duration;
  flush stderr
;;

let _for _start _step _end _repeat body =
  let n = ref _start in
  while !n <= _end do
    for iteration = 0 to _repeat - 1 do
      body !n
    done;
    n := !n + _step
  done;;

let msg_db = ref (initClassifier);;

let repeat = 5;;

try
  while true do
    (try (
      print_string "# ";
      flush stdout;
      let input_line = input_line stdin in
      let command, offset = read_keyword input_line 0 in
      try (
        match command with
	| "reset"       -> msg_db := initClassifier;
          print_string "Msg_Db successfully reset\n"

        | "benchmark" -> let [nb_rules; nb_classify_queries] =
                            map int_of_string (read_arguments command 2 input_line offset) in
                          benchmark nb_rules nb_classify_queries msg_db;
                          Printf.printf "Benchmark completed\n";

			  | "benchmark*msgs" -> let [nb_rules_start; nb_rules_step; nb_rules_end; nb_classify_queries] =
                                 map int_of_string (read_arguments command 4 input_line offset) in
                               _for nb_rules_start nb_rules_step nb_rules_end repeat (fun nb_rules ->
benchmark nb_rules nb_classify_queries msg_db);
                               Printf.printf "Benchmark completed\n";

        | unknown      -> Printf.printf "Unknown command %s!\nExpecting any of\n+ reset\n+ add_book [author title isbn]\n+ place_order [isbn]\n+ get_titles [author]\n+ num_orders [author]\n+ benchmark [nb_authors nb_books nb_orders nb_titles_queries nb_orders_queries]\n" unknown;
          raise Not_found
      ) with
        Not_found -> ()
     ) with
      Not_found -> ()
    ); flush stdout
  done
with
  End_of_file -> ()
;;
