(** * Programs of the NSL store case study

A client and a server agree on a session key with the NSL handshake of
[examples/nsl/impl.v], then the client stores values on the server and loads one
back.

- [conn_send] and [conn_recv] exchange messages encrypted under the session
  key.  Each message carries the sender's role and a counter, so a receiver
  accepts each message of the other side once and in order.
- [rpc_call] sends a request and waits for its reply.  [rpc_server] answers
  the requests of one connection, one at a time.
- [store_store] and [store_load] are the client's requests, and
  [store_handle] is the server's handler.  The server keeps its data in an
  AVL map from keys to values.
- [game ops k] runs the stores [ops] and then loads [k], sending the result
  to the attacker. *)

From stdpp Require Import namespaces.
From iris.heap_lang Require Import notation.
From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From cryptis.examples.nsl Require Import impl.

Abbreviation storeN := (nroot.@"store").
Abbreviation connN := (storeN.@"conn").

Definition conn_new : val := λ: "c" "k" "rl",
  let: "sent" := ref #0 in
  let: "received" := ref #0 in
  ("sent", "received", "k", "c", "rl").

Definition conn_sent : val := λ: "cs", Fst (Fst (Fst (Fst "cs"))).
Definition conn_received : val := λ: "cs", Snd (Fst (Fst (Fst "cs"))).
Definition conn_key : val := λ: "cs", Snd (Fst (Fst "cs")).
Definition conn_channel : val := λ: "cs", Snd (Fst "cs").
Definition conn_role : val := λ: "cs", Snd "cs".

Definition conn_send : val := λ: "cs" "t",
  let: "n" := conn_sent "cs" in
  let: "m" := term_of_list [tint (conn_role "cs"); tint !"n"; "t"] in
  send (conn_channel "cs") (senc (conn_key "cs") (Tag connN) "m");;
  "n" <- !"n" + #1.

Definition conn_recv : val := λ: "cs",
  do_until (λ: <>,
    let: "t" := recv (conn_channel "cs") in
    let: "r" := conn_received "cs" in
    bind: "t" := sdec (conn_key "cs") (Tag connN) "t" in
    bind: "t" := list_of_term "t" in
    list_match: ["rl'"; "r'"; "t"] := "t" in
    bind: "rl'" := to_int "rl'" in
    bind: "r'" := to_int "r'" in
    guard: (conn_role "cs" ≠ "rl'") && (!"r" = "r'") in
    "r" <- !"r" + #1;;
    SOME "t").

Definition rpc_call : val := λ: "cs" "N" "t",
  conn_send "cs" (tag "N" "t");;
  conn_recv "cs".

Definition rpc_server : val := rec: "loop" "cs" "f" "st" :=
  let: "m" := conn_recv "cs" in
  match: "f" "st" "m" with
    SOME "res" =>
    conn_send "cs" (Fst "res");;
    "loop" "cs" "f" (Snd "res")
  | NONE => "loop" "cs" "f" "st"
  end.

Definition store_store : val := λ: "cs" "k" "v",
  rpc_call "cs" (Tag $ storeN.@"store") (term_of_list [tint "k"; tint "v"]);;
  #().

Definition store_load : val := λ: "cs" "k",
  rpc_call "cs" (Tag $ storeN.@"load") (tint "k").

Definition store_handle_store : val := λ: "db" "req",
  bind: "req" := list_of_term "req" in
  list_match: ["k"; "v"] := "req" in
  bind: "k" := to_int "k" in
  bind: "v" := to_int "v" in
  avl_insert "k" "v" "db";;
  SOME (TInt 0, "db").

Definition store_handle_load : val := λ: "db" "k",
  bind: "k" := to_int "k" in
  let: "v" := match: avl_lookup "k" "db" with NONE => #0 | SOME "v" => "v" end in
  SOME (tint "v", "db").

Definition store_handle : val := λ: "db" "m",
  match: untag (Tag $ storeN.@"store") "m" with
    SOME "req" => store_handle_store "db" "req"
  | NONE =>
    bind: "k" := untag (Tag $ storeN.@"load") "m" in
    store_handle_load "db" "k"
  end.

Definition client : val := λ: "c" "skI" "pkR",
  match: init "c" "skI" "pkR" with
    SOME "k" => SOME (conn_new "c" "k" #0)
  | NONE => NONE
  end.

Definition server : val := λ: "c" "skR" "pkI",
  match: resp "c" "skR" with
    SOME "res" =>
    if: eq_term (Fst "res") "pkI" then
      rpc_server (conn_new "c" (Snd "res") #1) store_handle (avl_new #())
    else #()
  | NONE => #()
  end.

Definition store_all : val := rec: "loop" "cs" "ops" :=
  match: "ops" with
    NONE => #()
  | SOME "p" =>
    store_store "cs" (Fst (Fst "p")) (Snd (Fst "p"));;
    "loop" "cs" (Snd "p")
  end.

Definition op_val (p : Z * Z) : val := (#p.1, #p.2)%V.

Definition game (ops : list (Z * Z)) (k : Z) : val := λ: "c",
  let: "skI" := mk_aenc_key #() in
  let: "skR" := mk_aenc_key #() in
  send "c" (pkey "skI");;
  send "c" (pkey "skR");;
  Fork (server "c" "skR" (pkey "skI"));;
  match: client "c" "skI" (pkey "skR") with
    SOME "cs" =>
    store_all "cs" (repr (map op_val ops));;
    send "c" (store_load "cs" #k)
  | NONE => #()
  end.
