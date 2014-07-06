open Bookstore;;
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
  let store', output = extract (query !store) in
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

let benchmark nb_authors nb_books nb_orders nb_titles_queries nb_orders_queries store  =
  Printf.printf "Initialization\n";
  store        := extract (init_bookstore ());
  let names    = Random.init 1; Array.init nb_authors (fun _ -> toCharList (random_string 25)) in
  let authors  = Random.init 2; Array.init nb_books   (fun _ -> names.(Random.int nb_authors)) in
  let titles   = Random.init 3; Array.init nb_books   (fun _ -> toCharList (random_string 50)) in
  let isbns    = Random.init 4; Array.init nb_orders  (fun _ -> Random.int nb_books) in
  let title_authors = Random.init 5; Array.init nb_titles_queries (fun _ -> names.(Random.int nb_authors)) in
  let order_authors = Random.init 6; Array.init nb_orders_queries (fun _ -> names.(Random.int nb_authors)) in

  gc ();

  Printf.printf "Adding books...\n";
  let books_start = Unix.gettimeofday () in
  for iteration = 0 to nb_books - 1 do
    let _ = run (add_book authors.(iteration) titles.(iteration) iteration) store in ()
  done;
  let books_duration = stats books_start nb_books in 

  gc ();

  Printf.printf "Placing orders\n";
  let orders_start = Unix.gettimeofday () in
  for iteration = 0 to nb_orders - 1 do
    let _ = run (place_order isbns.(iteration) iteration) store in ()
  done;
  let orders_duration = stats orders_start nb_orders in

  gc ();

  Printf.printf "Getting titles\n";
  let titles_start = Unix.gettimeofday () in
  for iteration = 0 to nb_titles_queries - 1 do
    let _ = run (get_titles title_authors.(iteration)) store in ()
    (* List.iter (fun x -> Printf.printf "%s\n" (toString x)) a *)
  done;
  let get_titles_duration = stats titles_start nb_titles_queries in 

  gc ();

  Printf.printf "Counting orders\n";
  let orders_start = Unix.gettimeofday () in
  for iteration = 0 to nb_orders_queries - 1 do
    let _ = run (num_orders order_authors.(iteration)) store in ()
    (* Printf.printf "%d\n" count *)
  done;
  let num_orders_duration = stats orders_start nb_orders_queries in

  gc ();

  Printf.fprintf stderr "%d\t%d\t%d\t%.6f\t%.6f\t%.6f\t%.6f\n" 
    nb_authors nb_books nb_orders 
    books_duration orders_duration get_titles_duration num_orders_duration;
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

let store = ref (extract (init_bookstore ()));;

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
        | "reset"       -> store := extract (init_bookstore ());
          print_string "Store successfully reset\n"

        | "add_book"    -> let [author; title; isbn] = read_arguments command 3 input_line offset in
                           let success = run (add_book
                                                (toCharList author)
                                                (toCharList title)
                                                (int_of_string isbn)) store in
                           print_success success "Book successfully added\n" "Failed to add book\n"

        | "place_order" -> let [isbn] = read_arguments command 1 input_line offset in
                           let success = run (place_order
                                                (int_of_string isbn)
                                                (now ())) store in
                           print_success success "Order successfully placed\n" "Failed to place order\n"

        | "get_titles" -> let [author] = read_arguments command 1 input_line offset in
                          let titles = run (get_titles
                                              (toCharList author)) store in
                          Printf.printf "Books by %s:\n" author;
                          List.iter (fun title -> Printf.printf "+ %s \n" (toString title)) titles

        | "num_orders" -> let [author] = read_arguments command 1 input_line offset in
                          let num = run (num_orders
                                           (toCharList author)) store in
                          Printf.printf "Found %d orders for author %s\n" num author

        | "benchmark*books" -> let [nb_authors; nb_books_start; nb_books_step; nb_books_end;
                                    nb_orders; nb_titles_queries; nb_orders_queries] =
                                 map int_of_string (read_arguments command 7 input_line offset) in
                               _for nb_books_start nb_books_step nb_books_end repeat (fun nb_books ->
                                 benchmark nb_authors nb_books nb_orders 
                                   nb_titles_queries nb_orders_queries store);
                               Printf.printf "Benchmark completed\n";

        | "benchmark*orders" -> let [nb_authors; nb_books; nb_orders_start; nb_orders_step; nb_orders_end;
                                     nb_titles_queries; nb_orders_queries] =
                                 map int_of_string (read_arguments command 7 input_line offset) in
                               _for nb_orders_start nb_orders_step nb_orders_end repeat (fun nb_orders ->
                                 benchmark nb_authors nb_books nb_orders 
                                   nb_titles_queries nb_orders_queries store);
                               Printf.printf "Benchmark completed\n";

        | "benchmark" -> let [nb_authors; nb_books; nb_orders; nb_titles_queries; nb_orders_queries] =
                            map int_of_string (read_arguments command 5 input_line offset) in
                          benchmark nb_authors nb_books nb_orders nb_titles_queries nb_orders_queries store;
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
