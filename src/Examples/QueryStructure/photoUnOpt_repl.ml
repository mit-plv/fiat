open PhotoalbumUnOpt;;
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

let benchmark nb_events nb_photos nb_date_queries nb_persons_queries album_db  =
  Printf.printf "Initialization\n";
  album_db        := initAlbum;
  let names    = Random.init 1; Array.init nb_events (fun _ -> toCharList (random_string 10)) in
  let dates  = Random.init 2; Array.init nb_events (fun _ -> Random.int 2000) in
  let images = Random.init 3; Array.init nb_photos   (fun _ -> toCharList (random_string 10) ) in
  let event_names = Random.init 4; Array.init nb_photos  (fun _ -> names.(Random.int nb_events)) in
  let keywords = Random.init 5; Array.init 400 (fun _ -> toCharList (random_string 10)) in
  let persons     = Random.init 6; Array.init nb_photos (fun _ -> [keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400) ]) in
  let date_query = Random.init 6; Array.init nb_persons_queries (fun _ -> Random.int nb_events) in
  let persons_query  = Random.init 7; Array.init nb_date_queries (fun _ -> [keywords.(Random.int 400); keywords.(Random.int 400); keywords.(Random.int 400)]) in
  gc ();

  Printf.printf "Adding events...\n";
  let contacts_start = Unix.gettimeofday () in
  for iteration = 0 to nb_events - 1 do
  let _ = run (addEvent  names.(iteration) dates.(iteration) !album_db) album_db in ()
  done;
  let contacts_duration = stats contacts_start nb_events in

  gc ();

  Printf.printf "Adding Photos...\n";
  let messages_start = Unix.gettimeofday () in
  for iteration = 0 to nb_photos - 1 do
    let _ = run (addPhoto images.(iteration) persons.(iteration) event_names.(iteration) !album_db) album_db in ()
  done;
  let messages_duration = stats messages_start nb_photos in

  gc ();

  Printf.printf "Querying Dates\n";
  let contact_queries_start = Unix.gettimeofday () in
  for iteration = 0 to nb_persons_queries - 1 do
    let _ = run (photosByDateRange date_query.(iteration) (date_query.(iteration) + (Random.int 30)) !album_db) album_db in ()
    (* List.iter (fun x -> Printf.printf "%s\n" (toString x)) a *)
  done;
  let contact_queries_duration = stats contact_queries_start nb_persons_queries in

  gc ();

  Printf.printf "Searching Persons\n";
  let rel_queries_start = Unix.gettimeofday () in
  for iteration = 0 to nb_date_queries - 1 do
    let _ = run (photosByPersons persons_query.(iteration) !album_db) album_db in ()
    (* Printf.printf "%d\n" count *)
  done;
  let rel_queries_duration = stats rel_queries_start nb_date_queries in

  gc ();

  Printf.fprintf stderr "%d\t%d\t%d\t%d\t%.6f\t%.6f\t%.6f\t%.6f\n"
    nb_events nb_photos nb_date_queries nb_persons_queries
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

let album_db = ref (initAlbum);;

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
	| "reset"       -> album_db := initAlbum;
          print_string "Album_Db successfully reset\n"

        | "benchmark" -> let [nb_events; nb_photos; nb_date_queries; nb_persons_queries] =
                            map int_of_string (read_arguments command 4 input_line offset) in
                          benchmark nb_events nb_photos nb_date_queries nb_persons_queries album_db;
                          Printf.printf "Benchmark completed\n";

			  | "benchmark*photos" -> let [nb_events; nb_photos_start; nb_photos_step; nb_photos_end; nb_date_queries; nb_persons_queries] =
                                 map int_of_string (read_arguments command 6 input_line offset) in
                               _for nb_photos_start nb_photos_step nb_photos_end repeat (fun nb_photos ->
benchmark nb_events nb_photos nb_date_queries nb_persons_queries album_db);
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
