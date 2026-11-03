(** Programs of the NSL real-or-random case study.  The protocol is the one
    of [examples/nsl], except that the session key is derived from a hash of
    the transcript, so that a fresh key can stand in for it.

      I --> R: {nI; pkI}@pkR
      R --> I: {nI; nR; pkR}@pkI
      I --> R: {nR}@pkR

    Each test runs one initiator, whose peer the attacker picks, and one
    responder.  [resp_test] reveals R's session key when R's peer is I, and
    [init_test] reveals I's session key when I's peer is R.  Either reveals
    the key itself or a fresh one. *)

From stdpp Require Import namespaces.
From iris.heap_lang Require Import notation.
From cryptis Require Import lib cryptis primitives.

Abbreviation nslN := (nroot.@"nsl").

Definition session_key : val := λ: "pkI" "pkR" "nI" "nR",
  derive_senc_key (hash (term_of_list ["pkI"; "pkR"; "nI"; "nR"])).

Definition init : val := λ: "c" "skI" "pkR",
  let: "pkI" := pkey "skI" in
  let: "nI" := mk_nonce #() in
  send "c" (aenc "pkR" (Tag $ nslN.@"m1") (term_of_list ["nI"; "pkI"]));;
  bind: "m2" := adec "skI" (Tag $ nslN.@"m2") (recv "c") in
  bind: "m2" := list_of_term "m2" in
  list_match: ["nI'"; "nR"; "pkR'"] := "m2" in
  guard: eq_term "nI'" "nI" && eq_term "pkR'" "pkR" in
  send "c" (aenc "pkR" (Tag $ nslN.@"m3") "nR");;
  SOME (session_key "pkI" "pkR" "nI" "nR").

Definition resp : val := λ: "c" "skR",
  let: "pkR" := pkey "skR" in
  bind: "m1" := adec "skR" (Tag $ nslN.@"m1") (recv "c") in
  bind: "m1" := list_of_term "m1" in
  list_match: ["nI"; "pkI"] := "m1" in
  guard: is_aenc_key "pkI" in
  let: "nR" := mk_nonce #() in
  send "c" (aenc "pkI" (Tag $ nslN.@"m2") (term_of_list ["nI"; "nR"; "pkR"]));;
  bind: "m3" := adec "skR" (Tag $ nslN.@"m3") (recv "c") in
  guard: eq_term "m3" "nR" in
  SOME ("pkI", session_key "pkI" "pkR" "nI" "nR").

Definition reveal (b : bool) : val := λ: "c" "k",
  send "c" (if: #b then "k" else mk_senc_key #()).

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
