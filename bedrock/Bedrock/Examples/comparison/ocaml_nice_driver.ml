open Ocaml_data
open Ocaml_nice_server

let main () =
  let output = server cmd data in
  List.iter (Printf.printf "%d\n") output

let () = main ()
