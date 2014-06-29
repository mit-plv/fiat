open Bookstore;;
open Str;;

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

let store = ref (extract (init_bookstore ()));;

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
 
try
  while true do
    (try (
      print_string "# "; 
      flush stdout;
      let input_line = input_line stdin in
      let command, offset = read_keyword input_line 0 in
      try (
        match command with
        | "reset"     -> store := extract (init_bookstore ());
                           print_string "Store successfully reset\n"

        | "add_book"  -> let [author; title; isbn] = read_arguments command 3 input_line offset in
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

        | unknown      -> Printf.printf "Unknown command %s!\nExpecting any of\n+ reset\n+ add_book [author title isbn]\n+ place_order [isbn]\n+ get_titles [author]\n+ num_orders [author]\n" unknown;
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
