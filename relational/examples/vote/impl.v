(** Programs of the voting case study.  Keys are distributed out of band;
    T is the arbitrator and V_1, …, V_n the voters, with votes v_1, …, v_n
    drawn from the candidates.

      V_i --> *: {[n_i, v_i]@pkT}@skV_i
      T   --> *: [(c, #votes for c) | c a candidate]

    The arbitrator accepts one ballot per verification key, in any order, and
    publishes the tally once every voter's ballot is in.  The tally is an AVL
    map from candidates to counts; only its in-order listing is published. *)

From stdpp Require Import namespaces.
From iris.heap_lang Require Import notation.
From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.

Abbreviation voteN := (nroot.@"vote").
Abbreviation signedN := (voteN.@"signed").
Abbreviation ballotN := (voteN.@"ballot").
Abbreviation urnN := (voteN.@"urn").


Definition ballot : val := λ: "sk" "pkT" "v",
  sign "sk" (Tag $ voteN.@"ballot") (random_aenc "pkT" (Tag $ voteN.@"vote") "v").

Definition voter : val := λ: "c" "sk" "pkT" "v",
  send "c" (ballot "sk" "pkT" (tint "v")).

Definition record_ballot : val := rec: "loop" "m" "slots" :=
  match: "slots" with
    NONE => NONE
  | SOME "p" =>
    let: "pk" := Fst (Fst "p") in
    let: "slot" := Snd (Fst "p") in
    let: "rest" := Snd "p" in
    match: verify "pk" (Tag $ voteN.@"ballot") "m" with
      SOME "ct" => SOME (("pk", SOME "ct"), "rest")
    | NONE => SOME (("pk", "slot"), "loop" "m" "rest")
    end
  end.

Definition is_empty_slot : val := λ: "p",
  match: Snd "p" with NONE => #true | SOME <> => #false end.

Definition collect : val := rec: "loop" "c" "slots" :=
  match: find_list is_empty_slot "slots" with
    NONE => "slots"
  | SOME <> => "loop" "c" (record_ballot (recv "c") "slots")
  end.

Definition tally_vote : val := λ: "skT" "p" "t",
  match: Snd "p" with
    NONE => "t"
  | SOME "ct" =>
    match: random_adec "skT" (Tag $ voteN.@"vote") "ct" with
      NONE => "t"
    | SOME "v" =>
      match: to_int "v" with
        NONE => "t"
      | SOME "k" =>
        let: "n" := match: avl_lookup "k" "t" with NONE => #0 | SOME "n" => "n" end in
        avl_insert "k" ("n" + #1) "t"
      end
    end
  end.

Definition tally_slots : val := rec: "loop" "skT" "slots" "t" :=
  match: "slots" with
    NONE => "t"
  | SOME "p" => tally_vote "skT" (Fst "p") ("loop" "skT" (Snd "p") "t")
  end.

Definition seed_candidates : val := λ: "cands",
  foldr_list (λ: "k" "t", avl_insert "k" #0 "t") avl_empty "cands".

Definition pair_term : val := λ: "p", tuple (tint (Fst "p")) (tint (Snd "p")).

Definition arbitrator : val := λ: "c" "skT" "cands" "pks",
  let: "slots" := collect "c" (map_list (λ: "pk", ("pk", NONE)) "pks") in
  let: "t" := tally_slots "skT" "slots" (seed_candidates "cands") in
  send "c" (term_of_list (map_list pair_term (avl_to_list "t"))).

Definition mk_voters : val := rec: "loop" "votes" :=
  match: "votes" with
    NONE => NONE
  | SOME "p" =>
    let: "sk" := mk_sign_key #() in
    SOME (("sk", Fst "p"), "loop" (Snd "p"))
  end.

Definition fork_voters : val := rec: "loop" "c" "pkT" "voters" :=
  match: "voters" with
    NONE => #()
  | SOME "p" =>
    Fork (voter "c" (Fst (Fst "p")) "pkT" (Snd (Fst "p")));;
    "loop" "c" "pkT" (Snd "p")
  end.

Definition election_of (cands votes : list Z) : val := λ: "c",
  let: "skT" := mk_aenc_key #() in
  let: "pkT" := pkey "skT" in
  let: "voters" := mk_voters (repr votes) in
  let: "pks" := map_list (λ: "p", pkey (Fst "p")) "voters" in
  send "c" "pkT";;
  send "c" (term_of_list "pks");;
  fork_voters "c" "pkT" "voters";;
  arbitrator "c" "skT" (repr cands) "pks".

