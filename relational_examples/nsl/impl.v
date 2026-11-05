(** Programs of the NSL real-or-random case study.  The initiator and the
    responder are those of [examples/nsl]:

      I --> R: {nI; pkI}@pkR
      R --> I: {nI; nR; pkR}@pkI
      I --> R: {nR}@pkR

    Each test runs one initiator, whose peer the attacker picks, and one
    responder.  [resp_test] tests R's session key when R's peer is I, and
    [init_test] tests I's session key when I's peer is R.  A test reveals a
    key derived from a hash of the session key, or a fresh key; the hash lets
    the fresh key stand in for the derived one. *)

From stdpp Require Import namespaces.
From iris.heap_lang Require Import notation.
From cryptis Require Import lib cryptis primitives.
From cryptis.examples.nsl Require Export impl.

Definition reveal (b : bool) : val := λ: "c" "k",
  send "c" (if: #b then derive_senc_key (hash "k") else mk_senc_key #()).

Definition setup : val := λ: "c",
  let: "skI" := mk_aenc_key #() in
  let: "skR" := mk_aenc_key #() in
  send "c" (pkey "skI");;
  send "c" (pkey "skR");;
  ("skI", "skR", recv "c").

Definition resp_test (b : bool) : val := λ: "c",
  let: "keys" := setup "c" in
  let: "skI" := Fst (Fst "keys") in
  let: "skR" := Snd (Fst "keys") in
  Fork (init "c" "skI" (Snd "keys");; #());;
  match: resp "c" "skR" with
    SOME "res" =>
    if: eq_term (Fst "res") (pkey "skI") then reveal b "c" (Snd "res") else #()
  | NONE => #()
  end.

Definition init_test (b : bool) : val := λ: "c",
  let: "keys" := setup "c" in
  let: "skI" := Fst (Fst "keys") in
  let: "skR" := Snd (Fst "keys") in
  let: "pkX" := Snd "keys" in
  Fork (resp "c" "skR";; #());;
  match: init "c" "skI" "pkX" with
    SOME "k" =>
    if: eq_term "pkX" (pkey "skR") then reveal b "c" "k" else #()
  | NONE => #()
  end.
