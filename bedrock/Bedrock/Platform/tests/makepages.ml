let extension file =
  match Str.split (Str.regexp "\\.") file with
  | [] -> failwith "Empty filename"
  | parts -> List.hd (List.rev parts)

let bufsize = 1024 * 1024 * 10

let read_file file =
  let inf = open_in_bin file in
  let buf = String.create bufsize in

  let rec loop pos =
    if pos >= bufsize then
      failwith "Buffer wasn't big enough"
    else
      match input inf buf pos (bufsize - pos) with
      | 0 -> close_in inf; String.sub buf 0 pos
      | size -> loop (pos + size)

  in loop 0

let mimeTypes = Hashtbl.create 1000

let readMimeTypes () =
  let inf = open_in "/etc/mime.types" in

  let rec loop () =
    let line = try
      Some (input_line inf)
    with End_of_file -> None in

    match line with
    | None -> close_in inf
    | Some line ->
        begin if String.length line > 0 && line.[0] <> '#' then
          match Str.split (Str.regexp "[ \t]") line with
          | mtype :: exts ->
              List.iter (fun s -> if String.length s > 0 then Hashtbl.add mimeTypes s mtype) exts
          | _ -> ()
        end;
        loop ()

   in loop ()

let rec doFile path microPath =
  if Sys.is_directory path then
    Array.iter (fun path' -> doFile (Filename.concat path path') (Filename.concat microPath path')) (Sys.readdir path)
  else
    let data = read_file path in
    let fullData = Printf.sprintf "HTTP/1.1 200 OK\r\nContent-type: %s\r\nContent-length: %d\r\n\r\n%s"
        (try
	   Hashtbl.find mimeTypes (extension microPath)
	 with Not_found -> "text/html")
        (String.length data)
        data in

    Printf.printf "\t.int %d\n\t.ascii \"%s\"\n\t.int %d\n\t.byte "
      (String.length microPath)
      microPath
      (String.length fullData);

    let r = ref false in
    String.iter (fun ch ->
      Printf.printf "%s%d" (if !r then "," else "") (int_of_char ch);
      r := true) fullData;

    Printf.printf "\n\n"

let main () =
  readMimeTypes ();

  if Array.length Sys.argv < 2 then
    failwith "Not enough command-line arguments"
  else
    print_endline "\t.global pages";
    print_endline "\t.data";
    print_endline "pages:";
    doFile Sys.argv.(1) "/";
    print_endline "\t.int 0"

let _ = main ()
