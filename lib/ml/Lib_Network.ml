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

let uint8s_to_bytes s =
  let b = Bytes.create (List.length s) in
  List.iteri (fun i c -> Bytes.set b i (Char.chr c)) s;
  b

let uint8s_from_bytes s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) ((Char.code s.[i]) :: l) in
  exp (Bytes.length s - 1) []

let sock_send sock s =
  let l = List.length s in
  let b = uint8s_to_bytes s in
  send sock b 0 l []

let sock_recv sock maxlen =
  let str = String.create maxlen in
  let recvlen = recv sock str 0 maxlen [] in
  recvlen,str

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
    let (l,output) = sock_recv s i in
    let lr = Z.of_int l in
    let outr = uint8s_from_bytes output in
    Correct (lr,outr)
  with Unix_error (e,s1,s2) ->
    Error (Printf.sprintf "%s: %s(%s)" (error_message e) s1 s2)

let rec send s l b =
  try (
    let n = sock_send s b in
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
