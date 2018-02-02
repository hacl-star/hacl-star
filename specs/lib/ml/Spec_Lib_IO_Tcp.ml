open FStar_Error
open Unix

type networkStream = file_descr
type tcpListener = file_descr

let listen s i =
  let i = Z.to_int i in
  let server_sock = socket PF_INET SOCK_STREAM 0 in
  Correct (setsockopt server_sock SO_REUSEADDR true ;
   let address = inet_addr_of_string s in
   bind server_sock (ADDR_INET (address, i)) ;
   listen server_sock 10;
   server_sock)

let accept s =
  let (client_sock, client_addr) = accept s in
  Correct client_sock

let acceptTimeout t s = accept s

let stop s = Correct (shutdown s SHUTDOWN_ALL)

let connect s i =
  let i = Z.to_int i in
  let client_sock = socket PF_INET SOCK_STREAM 0 in
  let hentry = gethostbyname s in
  connect client_sock (ADDR_INET (hentry.h_addr_list.(0), i)) ;
  Correct client_sock

let connectTimeout t s i = connect s i

let sock_send sock l b =
  let str = FStar_String.string_of_list b in
  let b = FStar_String.list_of_string str in
  List.iter (Printf.printf "%02x ") b;
  Printf.printf "\n";
  send sock str 0 l []

let sock_recv sock maxlen =
  let str = String.create maxlen in
  let recvlen = recv sock str 0 maxlen [] in
  let str = String.sub str 0 recvlen in
  str

(* type 'a recv_result =
 *   | RecvWouldBlock
 *   | RecvError of string
 *   | Received of (int * bytes)
 *
 * let recv_async s i =
 *   let i = Z.to_int i in
 *   try Received (sock_recv s i) with
 *   | Unix_error ((EAGAIN | EWOULDBLOCK),_,_) -> RecvWouldBlock
 *   | Unix_error (e,s1,s2) -> RecvError (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2) *)

let set_nonblock = set_nonblock
let clear_nonblock = clear_nonblock

let recv s i =
  let i = Z.to_int i in
  try
    let b = sock_recv s i in
    Correct (String.length b, b)
  with Unix_error (e,s1,s2) ->
    Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

let rec send s l b =
  let l' = Z.to_int l in
  try (
    let n = sock_send s l' b in
    let m = List.length b in
    if n < m
    then
      (* send s (String.sub str n (m - n) *)
      Error(Printf.sprintf "Network error, wrote %d bytes" n)
    else Correct())
  with
  | Unix_error ((EAGAIN | EWOULDBLOCK),_,_) -> send s l b
  | Unix_error (e,s1,s2) -> Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

let close s =
  close s
