(** Programs of the NSL real-or-random case study.  The initiator and the
    responder are those of [examples/nsl]:

      I --> R: {nI; pkI}@pkR
      R --> I: {nI; nR; pkR}@pkI
      I --> R: {nR}@pkR

    Each test runs one initiator, whose peer the attacker picks, and one
    responder.  [resp_test] tests R's session key when R's peer is I, and
    [init_test] tests I's session key when I's peer is R.  A test reveals the
    session key or a fresh key. *)

From iris.heap_lang Require Import notation.
From cryptis Require Import primitives.
From cryptis.examples.nsl Require Export impl.

Definition reveal (b : bool) : val := λ: "c" "k",
  send "c" (if: #b then "k" else mk_senc_key #()).

Definition setup : val := λ: "network",
  let: "chan_init" := "network" #() in
  let: "chan_resp" := "network" #() in
  let: "skI" := mk_aenc_key #() in
  let: "skR" := mk_aenc_key #() in
  send "chan_init" (pkey "skI");;
  send "chan_resp" (pkey "skR");;
  (("chan_init", "chan_resp"), ("skI", "skR", recv "chan_init")).

Definition resp_test (b : bool) : val := λ: "network",
  let: "s" := setup "network" in
  let: "c_init" := Fst (Fst "s") in
  let: "c_resp" := Snd (Fst "s") in
  let: "keys" := Snd "s" in
  let: "skI" := Fst (Fst "keys") in
  let: "skR" := Snd (Fst "keys") in
  let: "pkX" := Snd "keys" in
  Fork (init "c_init" "skI" "pkX";; #());;
  match: resp "c_resp" "skR" with
    SOME "res" =>
    let: "k" := Snd "res" in
    if: eq_term (Fst "res") (pkey "skI") then reveal b "c_resp" "k" else #()
  | NONE => #()
  end.

Definition init_test (b : bool) : val := λ: "network",
  let: "s" := setup "network" in
  let: "c_init" := Fst (Fst "s") in
  let: "c_resp" := Snd (Fst "s") in
  let: "keys" := Snd "s" in
  let: "skI" := Fst (Fst "keys") in
  let: "skR" := Snd (Fst "keys") in
  let: "pkR" := pkey "skR" in
  let: "pkX" := Snd "keys" in
  Fork (resp "c_resp" "skR";; #());;
  match: init "c_init" "skI" "pkX" with
    SOME "k" =>
    if: eq_term "pkX" "pkR" then reveal b "c_init" "k" else #()
  | NONE => #()
  end.
