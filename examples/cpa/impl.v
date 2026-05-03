From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par nondet_bool.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.primitives Require Import attacker.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CPA.

Context `{!relocG Σ, !spawnG Σ}. (*, !relational_cryptisGS Σ}. *)
Notation iProp := (iProp Σ).

Implicit Types (t nonce : term).
Implicit Types (skA : aenc_key).

Variable N : namespace.

(*

* --> A: msg_0
* --> A: msg_1
A --> *: if b then {nonce, msg_0}@pkA else {nonce, msg_1}@pkA

*)

Definition alice : val := λ: "c" "skA",
  let: "pkA" := pkey "skA" in
  let: "nonce" := mk_nonce #() in
  bind: "msg_0" := recv "c" in
  bind: "msg_1" := recv "c" in
  if: nondet_bool #() then
  send "c" (aenc "pkA" (Tag $ N.@"m") (term_of_list ["nonce"; "msg_0"]));;
  SOME #false
  else
  send "c" (aenc "pkA" (Tag $ N.@"m") (term_of_list ["nonce"; "msg_1"]));;
  SOME #true.
