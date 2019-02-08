open Bookstore
open Str

(* Gc.set { (Gc.get ()) with Gc.verbose = 0x01 } *)
(*  Gc.tune ~minor_heap_size:(262144 * 2) ()  *)

let extract (Some x) = x
let now () = int_of_float (Unix.time ())

let kwd_matcher = regexp "\\([^\" ]+\\)\\|\"\\([^\"]+\\)\""

let rec extract_group haystack groups =
  match groups with
  | [] -> raise Not_found
  | group :: more ->
    try
      matched_group group haystack
    with Not_found ->
      extract_group haystack more

let read_keyword haystack offset =
  let _ = search_forward kwd_matcher haystack offset in
  let matched_text = extract_group haystack [1; 2] in
  (matched_text, match_end ())


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
    )

let run query store =
  let store', output = query !store in
  store := store';
  output

let print_success success truepart falsepart =
  if success then
    print_string truepart
  else
    print_string falsepart


let toCharList str =
  let rec aux acc pos =
    if pos < 0 then acc
    else aux (str.[pos] :: acc) (pos - 1) in
  aux [] (String.length str - 1)

let toString chars =
  let buffer = Bytes.create (List.length chars) in
  let _ = List.fold_left (fun pos char -> Bytes.set buffer pos char; succ pos) 0 chars in
  Bytes.to_string buffer

let random_bytes length =
  let buffer = Bytes.create length in
  for pos = 0 to length - 1 do
    Bytes.set buffer pos (Char.chr (Random.int 256))
  done;
  buffer

let random_string length =
  Bytes.to_string (random_bytes length)

let stats start_time iterations =
  let elapsed_time_s = Unix.gettimeofday () -. start_time in
  let elapsed_time_ms = 1000.0 *. elapsed_time_s in
  Printf.printf "  %d transactions completed in %.2f ms.\n" iterations elapsed_time_ms;
  Printf.printf "  %.2f TPS.\n" (float_of_int iterations /. elapsed_time_s);
  flush stdout;
  (elapsed_time_ms /. float_of_int iterations)


let gc () =
  Gc.compact ()

type bench_params = {
    nb_authors: int;
    nb_books: int;
    nb_orders: int;
    nb_titles_queries: int;
    nb_orders_queries: int;
  }

type bench_data = {
    names: char list array;
    authors: char list array;
    titles: char list array;
    isbns: int array;
    title_authors: char list array;
    order_authors: char list array;
  }

let bench_init { nb_authors; nb_books; nb_orders; nb_titles_queries; nb_orders_queries } =
  let names    = Random.init 1; Array.init nb_authors (fun _ -> toCharList (random_string 25)) in
  let authors  = Random.init 2; Array.init nb_books   (fun _ -> names.(Random.int nb_authors)) in
  let titles   = Random.init 3; Array.init nb_books   (fun _ -> toCharList (random_string 50)) in
  let isbns    = Random.init 4; Array.init nb_orders  (fun _ -> Random.int nb_books) in
  let title_authors = Random.init 5; Array.init nb_titles_queries (fun _ -> names.(Random.int nb_authors)) in
  let order_authors = Random.init 6; Array.init nb_orders_queries (fun _ -> names.(Random.int nb_authors)) in
  { names; authors; titles; isbns; title_authors; order_authors }

let bench_add_books bparams bdata store =
  for iteration = 0 to bparams.nb_books - 1 do
    ignore (run (add_book bdata.authors.(iteration) bdata.titles.(iteration) iteration) store)
  done

let bench_place_orders bparams bdata store =
  for iteration = 0 to bparams.nb_orders - 1 do
    ignore (run (place_order bdata.isbns.(iteration) iteration) store)
  done

let bench_get_titles bparams bdata store =
  for iteration = 0 to bparams.nb_titles_queries - 1 do
    ignore (run (get_titles bdata.title_authors.(iteration)) store)
  done

let bench_count_orders bparams bdata store =
  for iteration = 0 to bparams.nb_orders_queries - 1 do
    ignore (run (num_orders bdata.order_authors.(iteration)) store)
  done

let benchmark bparams bdata store  =
  store        := init_bookstore;

  gc ();

  Printf.printf "Adding books...\n";
  let books_start = Unix.gettimeofday () in
  bench_add_books bparams bdata store;
  let books_duration = stats books_start bparams.nb_books in

  gc ();

  Printf.printf "Placing orders\n";
  let orders_start = Unix.gettimeofday () in
  bench_place_orders bparams bdata store;
  let orders_duration = stats orders_start bparams.nb_orders in

  gc ();

  Printf.printf "Getting titles\n";
  let titles_start = Unix.gettimeofday () in
  bench_get_titles bparams bdata store;
  let get_titles_duration = stats titles_start bparams.nb_titles_queries in

  gc ();

  Printf.printf "Counting orders\n";
  let orders_start = Unix.gettimeofday () in
  bench_count_orders bparams bdata store;
  let num_orders_duration = stats orders_start bparams.nb_orders_queries in

  gc ();

  Printf.fprintf stderr "%d\t%d\t%d\t%.6f\t%.6f\t%.6f\t%.6f\n" 
    bparams.nb_authors bparams.nb_books bparams.nb_orders
    books_duration orders_duration get_titles_duration num_orders_duration;
  flush stderr

let _for _start _step _end _repeat body =
  let n = ref _start in
  while !n <= _end do
    for iteration = 0 to _repeat - 1 do
      body !n
    done;
    n := !n + _step
  done

let store = ref init_bookstore

let repeat = 5

let repl_main () =
  try
    while true do
      (try (
        print_string "# ";
        flush stdout;
        let input_line = input_line stdin in
        let command, offset = read_keyword input_line 0 in
        try (
          match command with
          | "reset"       -> store := init_bookstore;
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
                                   List.map int_of_string (read_arguments command 7 input_line offset) in
                                 _for nb_books_start nb_books_step nb_books_end repeat
                                   (fun nb_books ->
                                     let bparams = { nb_authors; nb_books; nb_orders;
                                                     nb_titles_queries; nb_orders_queries } in
                                     let bdata = bench_init bparams in
                                     benchmark bparams bdata store);
                                 Printf.printf "Benchmark completed\n";

          | "benchmark*orders" -> let [nb_authors; nb_books; nb_orders_start; nb_orders_step; nb_orders_end;
                                       nb_titles_queries; nb_orders_queries] =
                                    List.map int_of_string (read_arguments command 7 input_line offset) in
                                  _for nb_orders_start nb_orders_step nb_orders_end repeat
                                    (fun nb_orders ->
                                      let bparams = { nb_authors; nb_books; nb_orders;
                                                      nb_titles_queries; nb_orders_queries } in
                                      let bdata = bench_init bparams in
                                      benchmark bparams bdata store);
                                  Printf.printf "Benchmark completed\n";

          | "benchmark" -> let [nb_authors; nb_books; nb_orders; nb_titles_queries; nb_orders_queries] =
                             List.map int_of_string (read_arguments command 5 input_line offset) in
                           let bparams = { nb_authors; nb_books; nb_orders;
                                           nb_titles_queries; nb_orders_queries } in
                           let bdata = bench_init bparams in
                           benchmark bparams bdata store;
                           Printf.printf "Benchmark completed\n";

          | unknown      -> Printf.printf "Unknown command %s!
Expecting any of
+ reset
+ add_book [author title isbn]
+ place_order [isbn]
+ get_titles [author]
+ num_orders [author]
+ benchmark [nb_authors nb_books nb_orders nb_titles_queries nb_orders_queries]
" unknown;
                            raise Not_found
        ) with
          Not_found -> ()
       ) with
         Not_found -> ()
      ); flush stdout
    done
  with
    End_of_file -> ()

let corebench_main () =
  let open Core_bench.Std in

  let bparams, argv =
    match Array.to_list Sys.argv with
    | _ :: ("-help" | "--help" | "-h") :: _ ->
       Core.Command.run (Bench.make_command []);
       exit 1
    | exe :: nb_authors :: nb_books ::
        nb_orders :: nb_titles_queries ::
          nb_orders_queries :: argv ->
       { nb_authors = int_of_string nb_authors;
         nb_books = int_of_string nb_books;
         nb_orders = int_of_string nb_orders;
         nb_titles_queries = int_of_string nb_titles_queries;
         nb_orders_queries = int_of_string nb_orders_queries },
       (exe :: argv)
    | _ -> Printf.printf "Usage:
./bookstore_repl nb_authors nb_books nb_orders nb_titles_queries nb_orders_queries ...args\n";
           exit 1 in

  let bdata =
    bench_init bparams in

  Printf.printf "Initializing... %!";

  store := init_bookstore;
  let add_books_store = !store in
  bench_add_books bparams bdata store;
  let place_orders_store = !store in
  bench_place_orders bparams bdata store;
  let get_titles_store = !store in
  bench_get_titles bparams bdata store;
  let count_orders_store = !store in
  bench_count_orders bparams bdata store;

  Printf.printf "done\n%!";
  (* benchmark bparams bdata store; *)

  let benchmarks = [
      Bench.Test.create ~name:"Adding books" (fun () ->
          store := add_books_store; bench_add_books bparams bdata store);

      Bench.Test.create ~name:"Placing orders" (fun () ->
          store := place_orders_store; bench_place_orders bparams bdata store);

      Bench.Test.create ~name:"Getting titles" (fun () ->
          store := get_titles_store; bench_get_titles bparams bdata store);

      Bench.Test.create ~name:"Counting orders" (fun () ->
          store := count_orders_store; bench_count_orders bparams bdata store);
    ] in

  Core.Command.run ~argv (Bench.make_command benchmarks)

let _ =
  corebench_main ()
