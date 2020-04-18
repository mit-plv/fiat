open MessagesUnoptimized;;
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

let benchmark nb_contacts nb_msgs nb_rel_queries nb_contact_queries msg_db  =
  Printf.printf "Initialization\n";
  msg_db        := initMessages;
  let names    = Random.init 1; Array.init nb_contacts (fun _ -> toCharList (random_string 10)) in
  let numbers  = Random.init 2; Array.init nb_contacts (fun _ -> Random.int 10000) in
  let msg_nums = Random.init 3; Array.init nb_msgs   (fun _ -> numbers.(Random.int nb_contacts)) in
  let times    = Random.init 4; Array.init nb_msgs  (fun _ -> Random.int 500) in
  let keywords = Random.init 5; Array.init 400 (fun _ -> toCharList (random_string 10)) in
  let msgs     = Random.init 6; Array.init nb_msgs (fun _ -> [keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400) ]) in
  let name_query = Random.init 6; Array.init nb_contact_queries (fun _ -> names.(Random.int nb_contacts)) in
  let rel_query  = Random.init 7; Array.init nb_rel_queries (fun _ -> [keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400)]) in
  gc ();

  Printf.printf "Adding contacts...\n";
  let contacts_start = Unix.gettimeofday () in
  for iteration = 0 to nb_contacts - 1 do
  let _ = run (addContact numbers.(iteration) names.(iteration) !msg_db) msg_db in ()
  done;
  let contacts_duration = stats contacts_start nb_contacts in

  gc ();

  Printf.printf "Adding Messages...\n";
  let messages_start = Unix.gettimeofday () in
  for iteration = 0 to nb_msgs - 1 do
    let _ = run (addMessage msg_nums.(iteration) times.(iteration) msgs.(iteration) !msg_db) msg_db in ()
  done;
  let messages_duration = stats messages_start nb_msgs in

  gc ();

  Printf.printf "Querying Contacts\n";
  let contact_queries_start = Unix.gettimeofday () in
  for iteration = 0 to nb_contact_queries - 1 do
    let _ = run (contactMessages name_query.(iteration) !msg_db) msg_db in ()
    (* List.iter (fun x -> Printf.printf "%s\n" (toString x)) a *)
  done;
  let contact_queries_duration = stats contact_queries_start nb_contact_queries in

  gc ();

  Printf.printf "Searching Messages\n";
  let rel_queries_start = Unix.gettimeofday () in
  for iteration = 0 to nb_rel_queries - 1 do
    let _ = run (relevantMessages rel_query.(iteration) !msg_db) msg_db in ()
    (* Printf.printf "%d\n" count *)
  done;
  let rel_queries_duration = stats rel_queries_start nb_rel_queries in

  gc ();

  Printf.fprintf stderr "%d\t%d\t%d\t%d\t%.6f\t%.6f\t%.6f\t%.6f\n"
    nb_contacts nb_msgs nb_rel_queries nb_contact_queries
    contacts_duration messages_duration contact_queries_duration rel_queries_duration;
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

let msg_db = ref (initMessages);;

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
	| "reset"       -> msg_db := initMessages;
          print_string "Msg_Db successfully reset\n"

        | "benchmark" -> let [nb_contacts; nb_msgs; nb_rel_queries; nb_contact_queries] =
                            map int_of_string (read_arguments command 4 input_line offset) in
                          benchmark nb_contacts nb_msgs nb_rel_queries nb_contact_queries msg_db;
                          Printf.printf "Benchmark completed\n";

        | "benchmark*msgs" -> let [nb_contacts; nb_msgs_start; nb_msgs_step; nb_msgs_end; nb_rel_queries; nb_contact_queries]
                                 = map int_of_string (read_arguments command 6 input_line offset) in
                               _for nb_msgs_start nb_msgs_step nb_msgs_end repeat (fun nb_msgs ->
benchmark nb_contacts nb_msgs nb_rel_queries nb_contact_queries msg_db);
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
