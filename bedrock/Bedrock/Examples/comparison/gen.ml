let data_bound = 999999999

let main () =
  let dataSize = int_of_string Sys.argv.(1) in
  let cmdSize = int_of_string Sys.argv.(2) in

  let data = Array.init dataSize (fun _ -> Random.int data_bound) in
  let cmd = Array.init cmdSize (fun _ ->
    let code = Random.int 3 in
    code, Random.int (if code = 1 then data_bound else dataSize), Random.int data_bound) in

  let out = open_out "data.c" in
  output_string out "unsigned dataArray[] = {";
  Array.iter (Printf.fprintf out "%d,") data;
  output_string out "};\n";
  output_string out "unsigned cmdArray[] = {";
  Array.iter (fun (code, v1, v2) -> Printf.fprintf out "%d,%d,%d," code v1 v2) cmd;
  output_string out "};\n";
  output_string out "unsigned *data = dataArray, dataSize = sizeof(dataArray) / sizeof(unsigned);\n";
  output_string out "unsigned *cmd = cmdArray, cmdSize = sizeof(cmdArray) / sizeof(unsigned);\n";
  close_out out;

  let out = open_out "ocaml_data.ml" in
  output_string out "let data = [|";
  Array.iter (Printf.fprintf out "%d;") data;
  output_string out "|]\n";
  output_string out "let cmd = [|";
  Array.iter (fun (code, v1, v2) -> Printf.fprintf out "%d;%d;%d;" code v1 v2) cmd;
  output_string out "|]\n";
  close_out out;

  let out = open_out "bedrock_data.s" in
  output_string out "\t.global data\n";
  output_string out "\t.global dataLen\n";
  output_string out "\t.global cmd\n";
  output_string out "\t.global cmdLen\n";
  output_string out "\t.data\n";
  output_string out "data:\n";
  output_string out "\t.int ";
  Array.iter (Printf.fprintf out "%d,") data;
  output_string out "0\n";
  output_string out "dataLen:\n";
  output_string out "\t.int (dataLen-data)/4 - 1\n";
  output_string out "cmd:\n";
  output_string out "\t.int ";
  Array.iter (fun (code, v1, v2) -> Printf.fprintf out "%d, %d, %d, " code v1 v2) cmd;
  output_string out "0\n";
  output_string out "cmdLen:\n";
  output_string out "\t.int (cmdLen-cmd)/4 - 1\n";
  close_out out

let () = main ()
