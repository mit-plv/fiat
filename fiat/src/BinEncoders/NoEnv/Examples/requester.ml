open Bytes
open Extlib
open Unix

let char_of_bools b1 b2 b3 b4 b5 b6 b7 b8 =
  let int_of_bool b = if b then 1 else 0
  in  Char.chr (128 * (int_of_bool b1) +
	         64 * (int_of_bool b2) +
       		 32 * (int_of_bool b3) +
	         16 * (int_of_bool b4) +
      		  8 * (int_of_bool b5) +
		  4 * (int_of_bool b6) +
		  2 * (int_of_bool b7) +
		  1 * (int_of_bool b8))

let bools_of_char c =
  let bool_of_int i = if i = 0 then false else true in
  let rec aux n t acc = if t = 0 then acc else aux (n/2) (t-1) (bool_of_int (n mod 2)::acc) in
  aux (Char.code c) 8 []

let rec bytes_of_bools = function
  | b1::b2::b3::b4::b5::b6::b7::b8::xs -> let b = Bytes.extend (bytes_of_bools xs) 1 0
					  in  Bytes.set b 0 (char_of_bools b1 b2 b3 b4 b5 b6 b7 b8); b
  | [] -> Bytes.empty
  | _ -> assert false

let bools_of_bytes s =
  let rec aux i l = if i < 0 then l else aux (i - 1) (s.[i] :: l) in
  List.fold_right (fun c acc -> (bools_of_char c) @ acc) (aux (String.length s - 1) []) []

let dns_request boolmsg =
  let msg = bytes_of_bools boolmsg in
  let socket = Unix.socket Unix.PF_INET Unix.SOCK_DGRAM (Unix.getprotobyname "udp").Unix.p_proto in
  let portaddr = ADDR_INET (inet_addr_of_string "8.8.8.8", 53) in
  ignore (Unix.sendto socket msg 0 (String.length msg) [] portaddr);
  let res = Bytes.create 1000 in
  let reslen, _ = Unix.recvfrom socket res 0 1000 [] in
  bools_of_bytes (String.sub res 0 reslen)

let packet1 =
  { pid         = [false; false; false; false; false; false; false; false;
		   false; false; false; false; false; false; false; false];
    pmask       = [false; false; false; false; false; false; false; true;
		   false; false; false; false; false; false; false; true];
    pquestion   = [{ qname = [['w'; 'w'; 'w'];
			      ['n'; 'o'; 'r'; 't'; 'h'; 'e'; 'a'; 's'; 't'; 'e'; 'r'; 'n'];
			      ['e'; 'd'; 'u']];
		     qtype = A;
		     qclass = IN; }];
    panswer     = [];
    pauthority  = [];
    padditional = [];
  }

let packet_encoded = encode_packet (packet1, [])

open BatPervasives
let () =
  let print data = print_endline (dump data) in
  print packet1;
  print (packet_decoder (dns_request packet_encoded))
