let rline () = try Some (read_line ()) with End_of_file -> None
let sfor needle haystack = try Some (Str.search_forward (Str.regexp_string needle) haystack 0) with Not_found -> None
let locify = Str.global_replace (Str.regexp_string "black-box") "localhost"

let rec loop n =
  match rline () with
    None -> ()
  | Some line ->
      let line = locify line in
      let pos = sfor "POST" line in

      match pos with
        None -> loop n
      | Some pos ->
          let outf = open_out (string_of_int n ^ ".txt") in

          let rec loop' () =
            match rline () with
              None -> ()
            | Some line ->
                let line = locify line in

                output_string outf line;
                output_char outf '\n';

                match sfor "</methodCall>" line with
                  None -> loop' ()
                | Some _ ->
                    close_out outf;
                    loop (n + 1)
          in

          output_string outf (String.sub line pos (String.length line - pos));
          output_char outf '\n';
          loop' ()

let () = loop 0
