From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From stdpp Require Import namespaces.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import max_prefix_list.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import lock ticket_lock.
From cryptis Require Import lib term cryptis primitives tactics rpc.
From cryptis.store Require Import alist db.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance ticket_lock.

Module Client.

Section Client.

Variable N : namespace.

Definition connect : val := λ: "c" "skA" "vkB",
  RPC.connect N "c" "skA" "vkB".

Definition store : val := λ: "c" "cs" "k" "v",
  RPC.call N "store" "c" "cs" ["k"; "v"];; #().

Definition load : val := λ: "c" "cs" "k",
  let: "ts" := RPC.call N "load" "c" "cs" ["k"] in
  match: "ts" with
    NONE => TInt 0
  | SOME "ts" => Fst "ts"
  end.

Definition create : val := λ: "c" "cs" "k" "v",
  RPC.call N "create" "c" "cs" ["k"; "v"];; #().

Definition close : val := λ: "c" "cs",
  RPC.close N "c" "cs".

End Client.

End Client.

Module Server.

Implicit Types N : namespace.

Definition start : val := λ: "k",
  let: "accounts" := SAList.new #() in
  ("k", "accounts").

Definition handle_store : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"; "v"] := "req" in
  SAList.insert "db" "k" "v";;
  SOME [TInt 0].

Definition handle_load : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"] := "req" in
  bind: "data" := SAList.find "db" "k" in
  SOME ["data"].

Definition handle_create : val :=
λ: "c" "cs" "db" "req",
  list_match: ["k"; "v"] := "req" in
  match: SAList.find "db" "k" with
    SOME <> => NONE
  | NONE =>
    SAList.insert "db" "k" "v";;
    SOME [TInt 0]
  end.

Definition conn_handler N : val := λ: "c" "cs" "db" "lock",
  RPC.server N "c" "cs" [
    RPC.handle N "store" "c" (handle_store "c" "cs" "db");
    RPC.handle N "load" "c" (handle_load "c" "cs" "db");
    RPC.handle N "create" "c" (handle_create "c" "cs" "db")
  ];;
  lock.release "lock".

Definition find_client : val := λ: "ss" "client_key",
  let: "clients" := Snd "ss" in
  match: SAList.find "clients" "client_key" with
    NONE =>
    let: "db"   := SAList.new #() in
    let: "lock" := newlock #()    in
    SAList.insert "clients" "client_key" ("db", "lock");;
    ("db", "lock")
  | SOME "account" => "account"
  end.

Definition listen N : val := λ: "c" "ss",
  let: "secret_key" := Fst "ss" in
  let: "clients" := Snd "ss" in
  let: "res" := RPC.listen "c" in
  let: "client_key" := Snd "res" in
  let: "account" := find_client "ss" "client_key" in
  let: "db" := Fst "account" in
  let: "lock" := Snd "account" in
  acquire "lock";;
  let: "cs" := RPC.confirm N "c" "secret_key" "res" in
  Fork (conn_handler N "c" "cs" "db" "lock").

End Server.
