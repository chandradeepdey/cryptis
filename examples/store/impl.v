From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics rpc.
From cryptis.examples Require Import alist.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Notation dbN := (nroot.@"db").

Module Client.

Section Client.

Definition connect : val := λ: "c" "skA" "pkB",
  RPC.connect "c" "skA" "pkB".

Definition store : val := λ: "cs" "k" "v",
  RPC.call "cs" (Tag $ dbN.@"store") (term_of_list ["k"; "v"]);; #().

Definition load : val := λ: "cs" "k",
  RPC.call "cs" (Tag $ dbN.@"load") "k".

Definition create : val := λ: "cs" "k" "v",
  RPC.call "cs" (Tag $ dbN.@"create") (term_of_list ["k"; "v"]);; #().

Definition close : val := λ: "cs", RPC.close "cs".

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition start : val := λ: "k",
  let: "accounts" := AList.new #() in
  ("k", "accounts").

Definition handle_store : val :=
λ: "db" "req",
  bind: "req" := list_of_term "req" in
  list_match: ["k"; "v"] := "req" in
  AList.insert "db" "k" "v";;
  SOME (TInt 0).

Definition handle_load : val :=
λ: "db" "k",
  bind: "data" := AList.find "db" "k" in
  SOME "data".

Definition handle_create : val :=
λ: "db" "req",
  bind: "req" := list_of_term "req" in
  list_match: ["k"; "v"] := "req" in
  match: AList.find "db" "k" with
    SOME <> => NONE
  | NONE =>
    AList.insert "db" "k" "v";;
    SOME (TInt 0)
  end.

Definition conn_handler : val := λ: "cs" "db" "lock",
  RPC.server "cs" [
    RPC.handle (Tag $ dbN.@"store") (handle_store "db");
    RPC.handle (Tag $ dbN.@"load") (handle_load "db");
    RPC.handle (Tag $ dbN.@"create") (handle_create "db")
  ];;
  lock.release "lock".

Definition find_client : val := λ: "ss" "client_key",
  let: "clients" := Snd "ss" in
  match: AList.find "clients" "client_key" with
    NONE =>
    let: "db"   := AList.new #() in
    let: "lock" := newlock #()    in
    AList.insert "clients" "client_key" ("db", "lock");;
    ("db", "lock")
  | SOME "account" => "account"
  end.

Definition listen : val := λ: "c" "ss",
  let: "secret_key" := Fst "ss" in
  let: "clients" := Snd "ss" in
  let: "res" := RPC.listen "c" in
  let: "client_key" := Snd "res" in
  let: "account" := find_client "ss" "client_key" in
  let: "db" := Fst "account" in
  let: "lock" := Snd "account" in
  acquire "lock";;
  let: "cs" := RPC.confirm "c" "secret_key" "res" in
  Fork (conn_handler "cs" "db" "lock").

End Server.
